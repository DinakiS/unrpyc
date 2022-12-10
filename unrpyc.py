#!/usr/bin/python3

# Copyright (c) 2012 Yuri K. Schlesner
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.


import sys
import argparse
from pathlib import Path as pt
from functools import partial
import struct
import traceback
import zlib


try:
    from multiprocessing import Lock, Pool, cpu_count
except ImportError:
    # Mock required support when multiprocessing is unavailable
    def cpu_count():
        return 1

    class Lock:
        def __enter__(self):
            pass

        def __exit__(self, type, value, traceback):
            pass

        def acquire(self, block=True, timeout=None):
            pass

        def release(self):
            pass


import decompiler
from decompiler import astdump, magic, translate
import _unrpyc_ver

__title__ = "unrpyc"
__version__ = _unrpyc_ver.__version__


# special definitions for special classes
class PyExpr(magic.FakeStrict, str):
    __module__ = "renpy.ast"

    def __new__(cls, s, filename, linenumber, py=3):
        self = str.__new__(cls, s)
        self.filename = filename
        self.linenumber = linenumber
        self.py = py
        return self

    def __getnewargs__(self):
        return str(self), self.filename, self.linenumber, self.py


class PyCode(magic.FakeStrict):
    __module__ = "renpy.ast"

    def __setstate__(self, state):
        if len(state) == 4:
            (_, self.source, self.location, self.mode) = state
            self.py = 2
        else:
            (_, self.source, self.location, self.mode, self.py) = state

        self.bytecode = None


# renpy 7.5/8 compat; change renpy.python to renpy.revertable 3times
class RevertableList(magic.FakeStrict, list):
    __module__ = "renpy.revertable"

    def __new__(cls):
        return list.__new__(cls)


class RevertableDict(magic.FakeStrict, dict):
    __module__ = "renpy.revertable"

    def __new__(cls):
        return dict.__new__(cls)


class RevertableSet(magic.FakeStrict, set):
    __module__ = "renpy.revertable"

    def __new__(cls):
        return set.__new__(cls)

    def __setstate__(self, state):
        if isinstance(state, tuple):
            self.update(state[0].keys())
        else:
            self.update(state)


class Sentinel(magic.FakeStrict):
    __module__ = "renpy.object"

    def __new__(cls, name):
        obj = object.__new__(cls)
        obj.name = name
        return obj


# renpy 7.5/8 compat
# - renpy removed frozenset
# - Let's create two instances of class_factory instead of redefining them on every error # due to revertable objects. renpy @7.5(also v8) is normaly used and @7.4 is fallback
cls_factory_75 = magic.FakeClassFactory(
    (set, PyExpr, PyCode, RevertableList, RevertableDict, RevertableSet, Sentinel), magic.FakeStrict)

RevertableList.__module__, RevertableDict.__module__, RevertableSet.__module__ = (
    "renpy.python", ) * 3
cls_factory_74 = magic.FakeClassFactory(
    (set, PyExpr, PyCode, RevertableList, RevertableDict, RevertableSet, Sentinel), magic.FakeStrict)

printlock = Lock()

# needs class_factory
import deobfuscate  # nopep8 # noqa


# API
def revertable_switch(raw_dat):
    """Switches in a way between two instances of cls_factory. If a error from possible old code appears, it uses renpy.python instead of the new renpy.revertable module name."""
    try:
        _, stmts = magic.safe_loads(raw_dat, cls_factory_75, {
            "_ast", "collections"})
    except TypeError as err:
        if 'Revertable' in err.args[0]:
            _, stmts = magic.safe_loads(raw_dat, cls_factory_74, {
                "_ast", "collections"})
    return stmts


def read_ast_from_file(in_file):
    # .rpyc files are just zlib compressed pickles of a tuple of some data and the actual AST of the file
    raw_contents = in_file.read()
    if raw_contents.startswith(b"RENPY RPC2"):
        # parse the archive structure
        position = 10
        chunks = {}
        while True:
            slot, start, length = struct.unpack("III", raw_contents[position: position + 12])
            if slot == 0:
                break
            position += 12

            chunks[slot] = raw_contents[start: start + length]

        raw_contents = chunks[1]

    # py3 compat: zlib should be enough, no need for codecs
    # raw_contents = raw_contents.decode('zlib')
    raw_contents = zlib.decompress(raw_contents)
    # renpy 7.5/8 compat; for revertable problem
    # data, stmts = magic.safe_loads(raw_contents, class_factory, {"_ast", "collections"})
    data, stmts = revertable_switch(raw_contents)
    return stmts


def decompile_rpyc(input_filename, overwrite=False, dump=False, decompile_python=False,
                   comparable=False, no_pyexpr=False, translator=None, tag_outside_block=False,
                   init_offset=False, try_harder=False):
    # Output filename is input filename but with .rpy extension
    # if dump:
    #     out_filename = input_filename.with_suffix('.txt')
    # elif input_filename.suffix == ('.rpyc'):
    #     out_filename = input_filename.with_suffix('.rpy')
    # elif input_filename.suffix == ('.rpymc'):
    #     out_filename = input_filename.with_suffix('.rpym')

    if input_filename.suffix == ('.rpyc'):
        ext = '.rpy'
    elif input_filename.suffix == ('.rpymc'):
        ext = '.rpym'
    elif dump:
        ext = '.txt'
    out_filename = input_filename.with_suffix(ext)

    with printlock:
        print(("Decompiling %s to %s..." % (input_filename, out_filename)))

        if not overwrite and out_filename.exists:
            return False  # Don't stop decompiling if one file already exists

    with input_filename.open('rb') as in_file:
        if try_harder:
            ast = deobfuscate.read_ast(in_file)
        else:
            ast = read_ast_from_file(in_file)

    # NOTE: PY3 compat: 'codecs' is not unnecessary
    with out_filename.open('w', encoding='utf-8') as out_file:
        if dump:
            astdump.pprint(out_file, ast, decompile_python=decompile_python,
                           comparable=comparable, no_pyexpr=no_pyexpr)
        else:
            decompiler.pprint(out_file, ast, decompile_python=decompile_python,
                              printlock=printlock, translator=translator, tag_outside_block=tag_outside_block,
                              init_offset=init_offset)
    return True


def extract_translations(input_filename, language):
    with printlock:
        print("Extracting translations from %s..." % input_filename)

    with input_filename.open('rb') as in_file:
        ast = read_ast_from_file(in_file)

    translator = translate.Translator(language, True)
    translator.translate_dialogue(ast)
    # we pickle and unpickle this manually because the regular unpickler will choke on it
    return magic.safe_dumps(translator.dialogue), translator.strings


def worker(args, filename):
    try:
        if args.write_translation_file:
            return extract_translations(filename, args.language)
        else:
            if args.translation_file is not None:
                translator = translate.Translator(None)
                translator.language, translator.dialogue, translator.strings = (
                    magic.loads(args.translations, cls_factory_75))
            else:
                translator = None
            return decompile_rpyc(filename, args.clobber, args.dump,
                                  decompile_python=args.decompile_python, no_pyexpr=args.no_pyexpr, comparable=args.comparable, translator=translator, tag_outside_block=args.tag_outside_block, init_offset=args.init_offset, try_harder=args.try_harder)
    except Exception:
        with printlock:
            print("Error while decompiling %s:" % filename)
            print(traceback.format_exc())
        return False


def sharelock(lock):
    global printlock
    printlock = lock


def check_inpath(inp, strict=True):
    """Helper to check if given path exist."""
    return pt(inp).resolve(strict)


def _parse_args():
    """python3 unrpyc.py [-c] [-d] [--python-screens|--ast-screens|--no-screens] file [file ...]"""

    cc_num = cpu_count()
    aps = argparse.ArgumentParser(description="Decompile .rpyc/.rpymc files")
    aps.add_argument('-c', '--clobber',
                     dest='clobber',
                     action='store_true',
                     help="overwrites existing output files")
    aps.add_argument('-d', '--dump',
                     dest='dump',
                     action='store_true',
                     help="instead of decompiling, pretty print the ast to a file")
    aps.add_argument('-p', '--processes',
                     dest='processes',
                     action='store',
                     type=int,
                     choices=range(1, cc_num),
                     default=cc_num - 1 if cc_num > 2 else -2 if cc_num > 8 else 1,
                     help="use the specified number or processes to decompile."
                     "Defaults to the amount of hw threads available minus one, disabled when muliprocessing is unavailable.")
    aps.add_argument('-t', '--translation-file',
                     dest='translation_file',
                     action='store',
                     type=check_inpath,
                     default=None,
                     help="use the specified file to translate during decompilation")
    aps.add_argument('-T', '--write-translation-file',
                     dest='write_translation_file',
                     action='store',
                     type=pt,
                     default=None,
                     help="store translations in the specified file instead of decompiling")
    aps.add_argument('-l', '--language',
                     dest='language',
                     action='store',
                     default='english',
                     help="if writing a translation file, the language of the translations to write")
    aps.add_argument('--sl1-as-python',
                     dest='decompile_python',
                     action='store_true',
                     help="Only dumping and for decompiling screen language 1 screens. "
                     "Convert SL1 Python AST to Python code instead of dumping it or converting it to screenlang.")
    aps.add_argument('--comparable',
                     dest='comparable',
                     action='store_true',
                     help="Only for dumping, remove several false differences when comparing dumps. "
                     "This suppresses attributes that are different even when the code is identical, such as file modification times. ")
    aps.add_argument('--no-pyexpr',
                     dest='no_pyexpr',
                     action='store_true',
                     help="Only for dumping, disable special handling of PyExpr objects, instead printing them as strings. "
                     "This is useful when comparing dumps from different versions of Ren'Py. "
                     "It should only be used if necessary, since it will cause loss of information such as line numbers.")
    aps.add_argument('--tag-outside-block',
                     dest='tag_outside_block',
                     action='store_true',
                     help="Always put SL2 'tag's on the same line as 'screen' rather than inside the block. "
                     "This will break compiling with Ren'Py 7.3 and above, but is needed to get correct line numbers "
                     "from some files compiled with older Ren'Py versions.")
    aps.add_argument('--init-offset',
                     dest='init_offset',
                     action='store_true',
                     help="Attempt to guess when init offset statements were used and insert them. "
                     "This is always safe to enable if the game's Ren'Py version supports init offset statements, "
                     "and the generated code is exactly equivalent, only less cluttered.")
    aps.add_argument('file',
                     type=check_inpath,
                     nargs='+',
                     help="The filenames to decompile. "
                     "All .rpyc files in any directories passed or their subdirectories will also be decompiled.")
    aps.add_argument('--try-harder',
                     dest="try_harder",
                     action="store_true",
                     help="Tries some workarounds against common obfuscation methods. This is a lot slower.")
    aps.add_argument('--version',
                     action='version',
                     version=f'%(prog)s : { __title__} {__version__}')

    return aps.parse_args()


def main(args):
    """Main execution..."""
    # NOTE: v1.2.0 refactoring: Code reworked to pathlib usage
    if not sys.version_info[:2] >= (3, 6):
        raise Exception("Must be executed in Python 3.6 or later.\n"
                        "You are running {}".format(sys.version))

    if (args.write_translation_file
        and not args.clobber
            and args.write_translation_file.exists()):
        # Fail early to avoid wasting time going through the files
        print("Output translation file already exists. Pass --clobber to overwrite.")
        return

    if args.translation_file:
        with args.translation_file.open('rb') as in_file:
            args.translations = in_file.read()

    # Check target path(s)
    # filesAndDirs = [check_inpath(x) for x in args.file]

    def rpyc_check(inp):
        return bool(inp.suffix in ('.rpyc', '.rpymc') and inp.is_file())

    files = list()
    for item in args.file:
        if item.is_dir():
            for entry in item.rglob('*'):
                if rpyc_check(entry):
                    files.append(entry)
        elif rpyc_check(item):
            files.append(item)

    # Check if we actually have files. Don't worry about no parameters passed,
    # since ArgumentParser catches that
    if not files:
        print("Found no script files to decompile.")
        return

    files.sort(key=lambda x: x.stat().st_size, reverse=True)

    # v1.2.0 changes:
    # contextmanager
    # passing filesize over is unneeded
    # code for single process removed - mostly unused in multicore age
    with Pool(args.processes, sharelock, [printlock]) as pool:
        results = pool.map(partial(worker, args), files, 1)

    # results = list(map(partial(worker, args), files))

    if args.write_translation_file:
        print("Writing translations to %s..." % args.write_translation_file)
        translated_dialogue = {}
        translated_strings = {}
        good = 0
        bad = 0
        for result in results:
            if not result:
                bad += 1
                continue
            good += 1
            translated_dialogue.update(magic.loads(result[0], cls_factory_75))
            translated_strings.update(result[1])
        with args.write_translation_file.open('wb') as out_file:
            magic.safe_dump((
                args.language, translated_dialogue, translated_strings), out_file)

    else:
        # Check per file if everything went well and report back
        good = results.count(True)
        bad = results.count(False)

    if bad == 0:
        print("Decompilation of %d script file%s successful" %
              (good, 's' if good > 1 else ''))
    elif good == 0:
        print("Decompilation of %d file%s failed" %
              (bad, 's' if bad > 1 else ''))
    else:
        print("Decompilation of %d file%s successful, but decompilation of %d file%s failed" % (good, 's' if good > 1 else '', bad, 's' if bad > 1 else ''))


if __name__ == '__main__':
    main(_parse_args())
