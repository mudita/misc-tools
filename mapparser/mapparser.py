#!/usr/bin/env python3

from binascii import unhexlify as uhx
import cxxfilt
import re
from os.path import abspath
from os import getcwd
import sys

ADDRLEN = 8
SIZELEN = 4

COL_SIZE_NAME = 16
COL_SIZE_SIZE = SIZELEN * 2 + len(" 0x")
COL_SIZE_ADDR = ADDRLEN * 2 + len(" 0x")

DEFAULT_FILE_NAME = "linker.map"
DEFAULT_SOURCE_PATH = getcwd()
DEFAULT_SYMBOLS_COUNT = 10

SECTION_NAME_WHITELIST = [".text", ".bss", ".data", ".rodata", ".exidx"]


def usage(appname):
    print("Usage: " + appname + " [<linker.map>]")
    sys.exit(1)


def map_add_unique_by_name(dir, value):
    if value.name not in dir.keys():
        dir[value.name] = value


def fn2nodelist(filename):
    parts = filename.strip().split("/")
    if parts[0] == "":
        if len(parts) == 1:
            return []
        else:
            parts = parts[1:]

    ofn = parts[-1]
    match = re.match(r"(.*)\((.*)\)", ofn)
    if match is not None:
        libname = match[1]
        objname = match[2]
        parts = parts[:-1] + [libname, objname]

    return parts


class MapEntity(object):
    def __init__(self, name, size):
        self.name = name
        self.size = size


class Symbol(MapEntity):
    def __init__(self, name, address, size):
        MapEntity.__init__(self, name, size)
        self.address = address

    @staticmethod
    def make(sname, saddress, ssize):
        return Symbol(sname, int(saddress, 16), int(ssize, 16))


class SymbolSet(MapEntity):
    def __init__(self, name):
        MapEntity.__init__(self, name, 0)
        self.symbols = {}

    def add_symbol(self, symbol):
        if symbol.name not in self.symbols.keys():
            self.symbols[symbol.name] = symbol
            self.size += symbol.size

    def recalculate_size(self):
        self.size = sum([symbol.size for symbol in self.symbols.values()])

    def get_symbols(self):
        return self.symbols.values()

    # return symbol list sorted by size starting with the largest
    def get_symbols_sorted(self):
        return sorted(self.symbols.values(), key=lambda s: s.size, reverse=True)


class Section(MapEntity):
    def __init__(self, name, address, size):
        MapEntity.__init__(self, name, size)
        self.address = address


class ObjectFile(SymbolSet):
    def __init__(self, filename):
        SymbolSet.__init__(self, filename)


class ObjectTreeNode(object):
    def __init__(self, parent, name, size=0):
        self.parent = parent
        self.name = name
        self.size = size
        self.total_size = self.size
        self.cached_size = 0
        self.children = []

    def add_node(self, node):
        if node in self.children:
            return
        self.increase_total_size(node.total_size)
        self.children.append(node)
        node.parent = self

    def increase_total_size(self, size):
        self.total_size += size
        if self.parent is not None:
            self.parent.increase_total_size(size)

    def __str__(self):
        return self.name + ": " + str(self.size)


class ObjectTree(object):
    def __init__(self, objectlist):
        self.objects = objectlist
        self.nodelist = {}
        self.root = ObjectTreeNode(None, "root", 0)
        self.index(self.objects)

    def index(self, objectlist):
        for o in objectlist:
            self.index_file(o)

    def index_file(self, objectfile):
        nodenames = fn2nodelist(objectfile.name)
        lastnode = ObjectTreeNode(None, nodenames[-1], objectfile.size)
        self.nodelist["/".join(nodenames)] = lastnode

        nodes = [self.root]
        key = ""
        for nn in nodenames[:-1]:
            key += "/" + nn
            if key not in self.nodelist.keys():
                node = ObjectTreeNode(None, nn)
                self.nodelist[key] = node
            else:
                node = self.nodelist[key]
            nodes.append(node)
        nodes.append(lastnode)

        for i in range(len(nodes) - 1, 0, -1):
            nodes[i - 1].add_node(nodes[i])


def output_tree_node(node, recursive=True, indentSize=0, parent_percentage=100.0):
    indent = " " * indentSize
    if node.parent is None:
        percentage = 100.00
    else:
        percentage = node.total_size / node.parent.total_size * parent_percentage

    print(
        indent
        + node.name
        + " "
        + str(node.total_size)
        + "\t("
        + format(percentage, ".2f")
        + "%)"
    )
    if recursive:
        for child in sorted(node.children, key=lambda ch: ch.total_size, reverse=True):
            output_tree_node(
                child, recursive, indentSize + 1, parent_percentage=percentage
            )


class MapFile(object):
    def __init__(self, filename):
        self.filename = filename
        self.sectionMap = {}
        self.fileMap = {}

    def add_section(self, section):
        map_add_unique_by_name(self.sectionMap, section)

    def get_sections(self):
        return self.sectionMap.values()

    def get_unique_file(self, filename):
        if filename not in self.fileMap.keys():
            file = ObjectFile(filename)
            self.fileMap[filename] = file
        else:
            file = self.fileMap[filename]

        return file

    def get_files(self):
        return self.fileMap.values()

    def get_files_sorted(self):
        return sorted(self.fileMap.values(), key=lambda f: f.size, reverse=True)

    def recalculate_sizes(self):
        for f in self.fileMap.values():
            f.recalculate_size()


class Parser(object):
    def __init__(self, source_path):
        self.lines = []
        self.index = 0
        self.source_path = source_path

    def parse_map_file(self, filename):
        try:
            with open(filename, "r") as fd:
                self.lines = fd.readlines()
        except:
            raise IOError()

        # look for memory map start
        while self.current_line() != "Linker script and memory map":
            self.index += 1
            if self.is_eof():
                raise RuntimeError("No mem map")

        self.mapfile = MapFile(filename)
        while self.index < len(self.lines):
            line = self.lines[self.index]

            # look for ".sectioname"
            if line.startswith("."):
                section = self.parse_section()

                if section is not None:
                    self.mapfile.add_section(section)

                self.index += 1
                continue

            self.index += 1

        self.mapfile.recalculate_sizes()

        return self.mapfile

    def read_entry(self):
        # empty line
        if self.is_empty_line():
            raise RuntimeError("Empty line passed.")

        line = self.current_line()
        self.index += 1

        # safe hexstring conversion
        def tryhex(x):
            try:
                return int(x, 16)
            except:
                return None

        # empty name
        if line[:COL_SIZE_NAME] == " " * COL_SIZE_NAME:
            name = ""

        # only short name
        if len(line) < COL_SIZE_NAME - 1:
            return (line, None, None, None)

        # long name
        elif line[COL_SIZE_NAME - 2] != " ":
            name = line
            line = self.lines[self.index].rstrip()
            self.index += 1

        else:
            name = line[:COL_SIZE_NAME].strip()

        i = COL_SIZE_NAME

        # read address
        address = tryhex(line[i : i + COL_SIZE_ADDR].strip())
        i += COL_SIZE_ADDR

        # read symbol size
        ssize = tryhex(line[i : i + COL_SIZE_SIZE].strip())
        i += COL_SIZE_SIZE

        # read description
        desc = line[i:].strip()

        return (name, address, ssize, desc)

    def is_empty_line(self):
        return self.is_eof() or (self.current_line() == "")

    def is_eof(self):
        return self.index == len(self.lines)

    def current_line(self):
        return self.lines[self.index].rstrip()

    def parse_section(self):
        name, address, size, _ = self.read_entry()

        def blacklisted(name):
            return not any(
                [whitelisted in name for whitelisted in SECTION_NAME_WHITELIST]
            )

        # skip parsing empty sections or blacklisted
        if size == 0 or blacklisted(name):
            while not self.is_empty_line():
                self.index += 1
            return None

        s = Section(name, address, size)

        lastfile = None
        lastsymbol = None
        lastsecsize = 0
        while not self.is_empty_line():
            # try to read included sections
            if self.current_line().startswith(" ") and self.current_line()[1] not in [
                "*",
                " ",
            ]:
                firstword = self.current_line().strip().split()[0]
                if firstword in ["FILL"]:
                    self.index += 1
                    continue

                # no explicit symbols in last parsed section, add bogus symbol
                if lastsecsize > 0 and lastsymbol is None:
                    name = self.demangle_section_name(name)
                    lastfile.add_symbol(Symbol(name, address, size))

                name, address, size, filepath = self.read_entry()

                # calculate size of last symbol in an included secion
                if lastsymbol is not None:
                    lastsymbol.size = address - lastsymbol.address

                lastsymbol = None
                symbols = []
                if not filepath.startswith("/"):
                    filepath = self.source_path + "/" + filepath

                filepath = abspath(filepath)
                lastfile = self.mapfile.get_unique_file(filepath)
                lastsecsize = size

            elif self.current_line().startswith(" " * COL_SIZE_NAME):
                _, address, _, symbolname = self.read_entry()

                if (
                    lastsymbol is not None
                    and lastsymbol.address == address
                    and lastsymbol.name == symbolname
                ):
                    continue

                # provide entry, etc
                if address is None or " = " in symbolname:
                    continue

                # check if included section has been reached
                if lastfile is None:
                    raise RuntimeError("Unexpected lines")

                if lastsymbol is not None:
                    lastsymbol.size = address - lastsymbol.address

                newsymbol = Symbol(symbolname, address, 0)
                symbols.append(newsymbol)

                lastsymbol = newsymbol

                # add symbol to file
                lastfile.add_symbol(newsymbol)

            else:
                self.index += 1

        # last symbol in whole section
        if lastsymbol is not None:
            lastsymbol.size = s.size - (lastsymbol.address - s.address)

        # no explicit symbols in last parsed section, add bogus symbol
        if lastsecsize > 0 and lastsymbol is None:
            name = self.demangle_section_name(name)
            lastfile.add_symbol(Symbol(name, address, size))

        return s

    def demangle_section_name(self, name):
        # expected something like .bss._ZN...
        fields = name.split(".", 2)
        if len(fields) < 2:
            return name

        symbolname = fields[-1]

        try:
            symbolname = cxxfilt.demangle(symbolname)
        except:
            symbolname = "(invalid name) " + symbolname

        return symbolname


def print_symbol_table(syms, sortkey=None, n=DEFAULT_SYMBOLS_COUNT):
    if n == 0 or len(syms) == 0:
        return

    if n > len(syms):
        n = len(syms)

    if sortkey != None:
        syms = sorted(syms, key=sortkey, reverse=True)

    for s in syms[:n]:
        print("%s\t\t0x%08x\t%s" % (str(s.size), s.address, s.name))


if __name__ == "__main__":
    if len(sys.argv) > 3:
        usage(sys.argv[0])

    if len(sys.argv) < 2:
        print("Using default filename: " + DEFAULT_FILE_NAME)
        filename = DEFAULT_FILE_NAME
    else:
        filename = sys.argv[1]

    if len(sys.argv) < 3:
        print("Using default source location: " + DEFAULT_SOURCE_PATH)
        source_path = DEFAULT_SOURCE_PATH
    else:
        source_path = sys.argv[2]

    parser = Parser(source_path)

    try:
        mapfile = parser.parse_map_file(filename)
    except IOError:
        print("Can't read file:", filename)
        sys.exit(2)

    tree = ObjectTree(mapfile.get_files())
    output_tree_node(tree.root)
