import gdb

import collections
import traceback

STACKHEALTH_DEFAULT_BLOCK_SIZE = 32


def get_int_by_name(varname):
    symbol, _ = gdb.lookup_symbol(varname)
    if symbol is None:
        raise RuntimeError("Can't find symbol: " + varname)

    return int(symbol.value())


AddressRange = collections.namedtuple(
    "AddressRange",
    ["low", "high", "name"]
)


class AddressRegistry(object):
    def __init__(self):
        self.entries = []

    def register(self, entry):
        self.entries.append(entry)
        self.entries.sort(key=lambda e: e.get_low_address())

    def match(self, address):
        return [entry for entry in self.entries if entry.get_low_address() <= address and entry.get_high_address() > address]


class AddressRegistree(object):
    def __init__(self):
        pass

    def get_range():
        return AddressRegistry(
            low=self.get_low_address(),
            high=self.get_high_address(),
            name=self.get_name()
        )

    def get_size(self):
        return self.get_high_address() - self.get_low_address()

    def __str__(self):
        return hex(self.get_low_address()) + " .. " + hex(self.get_high_address()) + " " + self.get_name()

    def get_name(self):
        raise NotImplementedError("AddressRegistree.get_name")

    def get_low_address(self):
        raise NotImplementedError("AddressRegistree.get_low_address")

    def get_high_address(self):
        raise NotImplementedError("AddressRegistree.get_high_address")


class StackError(Exception):
    def __init__(self, task, reason=""):
        self.task = task
        self.reason = reason

    def __str__(self):
        return self.reason


class PureTask(AddressRegistree):
    def __init__(self, inf, value):
        self.inf = inf
        self.v = value

    def get_name(self):
        try:
            return self.v['pcTaskName'].string()
        except gdb.MemoryError:
            raise StackError(self, "Can't read stack memory")

    def get_low_address(self):
        return int(self.v['pxStack'])

    def get_high_address(self):
        return int(self.v['pxEndOfStack'])

    def get_address(self):
        return int(self.v)

    def get_stack_size(self):
        return self.get_size()

    def read_stack_bottom(self, l):
        return self.inf.read_memory(int(self.v['pxStack']), l)

    def _check_stack_block_valid(self, address, bs):
        block = self.inf.read_memory(address, bs)
        return all([b == '\xa5' for b in block])

    def check_stack(self, bs=STACKHEALTH_DEFAULT_BLOCK_SIZE):
        try:
            return self._check_stack_block_valid(int(self.v['pxStack']), bs)
        except gdb.MemoryError:
            raise StackError(self, "Can't read stack memory")

    def get_free_stack_size(self, bs=STACKHEALTH_DEFAULT_BLOCK_SIZE):
        ptr = int(self.v['pxStack'])
        end = int(self.v['pxEndOfStack'])
        free = 0
        while ptr < (end - bs):
            if not self._check_stack_block_valid(ptr, bs):
                break
            ptr += bs
            free += bs

        return free

    @staticmethod
    def from_handle(handle, inf):
        tsktype = gdb.lookup_type('struct tskTaskControlBlock')
        val = gdb.Value(handle)
        val = val.cast(tsktype.pointer())
        return PureTask(inf, val)


HeapEntry = collections.namedtuple('HeapEntry', [
    'address', 'size', 'task', 'time'
])
heap_stats_entries = {
    "minimum_free": "Lowest size of heap",
    "free": "Free size",
    "size": "Overall heap size",
    "used": "Used size (block + metadata)",
    "taken": "Overall size of blocks (w/o metadata)",
    "free_block_count": "Free blocks count",
    "taken_block_count": "Taken blocks count"
}
HeapStats = collections.namedtuple(
    'HeapStats', heap_stats_entries.keys()
)


class HeapError(Exception):
    def __init__(self, entry, reason=""):
        self.entry = entry
        self.reason = reason
        self.address = int(entry.address)

    def __str__(self):
        return self.reason


class Heap(AddressRegistree):
    MARKER_ALLOCATED = 0xabababab
    MARKER_UNALLOCATED = 0xcdcdcdcd
    MARKER_FREED = 0xdddddddd
    MARKER_SPECIAL = 0xbaadc0de

    def __init__(self):
        self.start = gdb.lookup_symbol('xStart')[0].value()
        self.freeEnd = gdb.lookup_symbol('pxEnd')[0].value()
        ucHeap = gdb.lookup_symbol('ucHeap')[0].value()
        self.total_size = ucHeap.dynamic_type.sizeof
        self.address = int(ucHeap.address)
        self.taken_end = gdb.lookup_symbol('xTakenEnd')[0].value()

    def get_name(self):
        return "HEAP"

    def get_low_address(self):
        return self.address

    def get_high_address(self):
        return int(self.address + self.total_size)

    @staticmethod
    def _make_pod_entry(entry):
        entrySize = int(entry['xBlockSize']) & 0x7fffffff
        return HeapEntry(
            size=entrySize,
            address=int(entry.address),
            task=int(entry['xAllocatingTask'].address),
            time=int(entry['xTimeAllocated'])
        )

    def get_stats(self):
        free_bytes = get_int_by_name('xFreeBytesRemaining')
        return HeapStats(
            minimum_free=get_int_by_name('xMinimumEverFreeBytesRemaining'),
            free=free_bytes,
            size=self.total_size,
            used=self.total_size - free_bytes,
            taken=sum([entry.size for entry in self.taken()]),
            free_block_count=len(list(self.free())),
            taken_block_count=len(list(self.taken()))
        )

    def _check_ptr_invalid(self, pentry):
        return int(pentry) > (self.address + self.total_size) or int(pentry) < self.address

    def free(self):
        if int(self.start['ulMarker']) != Heap.MARKER_SPECIAL:
            raise HeapError(self.start, "Error in start block")

        pentry = self.start['pxNextFreeBlock']

        while pentry != self.freeEnd:
            entry = pentry.dereference()
            pentry = entry['pxNextFreeBlock']
            if self._check_ptr_invalid(pentry):
                raise HeapError(entry, "Invalid next free block")

            if int(entry['ulMarker']) != Heap.MARKER_UNALLOCATED and int(entry['ulMarker']) != Heap.MARKER_FREED:
                raise HeapError(entry, "Invalid marker")

            yield Heap._make_pod_entry(entry)

    def taken(self):
        if int(self.start['ulMarker']) != Heap.MARKER_SPECIAL:
            raise HeapError(self.start, "Error in start block")

        entry = self.start['pxNextTakenBlock']
        count = 0

        while entry.address != self.taken_end.address:
            if self._check_ptr_invalid(entry['pxNextTakenBlock']) and entry['pxNextTakenBlock'] != self.taken_end.address:
                raise HeapError(entry, "Invalid next taken block")

            if int(entry['ulMarker']) != Heap.MARKER_ALLOCATED:
                raise HeapError(entry, "Invalid marker")

            yield Heap._make_pod_entry(entry)

            entry = entry['pxNextTakenBlock'].dereference()

    def validate(self):
        try:
            try:
                for _ in self.free():
                    pass

            except HeapError as he:
                print "Error when iterating over heap's free entries"
                raise he

            try:
                for _ in self.taken():
                    pass
            except HeapError as he:
                print "Error when iterating over heap's taken entries"
                raise he

        except HeapError as he:
            print "Reason:", he
            print "Problematic entry at: ", hex(he.address)
            return False

        return True


class PureGDB(gdb.Command):
    def __init__(self):
        super(PureGDB, self).__init__("pure", gdb.COMMAND_USER)

        self.heap = Heap()

    def _get_inferior(self):
        infs = gdb.inferiors()
        if len(infs) != 1:
            print "Warning: Multiple inferiors"
        return infs[0]

    def _refresh_memory_map(self):
        self.address_registry = AddressRegistry()

        # register tasks
        for t in self._get_threads():
            self.address_registry.register(t)

        # register system heap
        self.address_registry.register(self.heap)

    def _get_threads(self):
        inf = self._get_inferior()

        return [PureTask.from_handle(t.ptid[1], inf) for t in inf.threads()]

    def cmd_memory(self, args=None):
        self._refresh_memory_map()

        def print_results(entries):
            if len(entries) == 0:
                return False
            print("\n".join(["\t" + str(e) for e in entries]))
            return True

        # no arguments, display memory map
        if args is None or len(args) == 0:
            print_results(self.address_registry.entries)
            return

        if len(args) > 1:
            print "Usage: pure memory [address] "

        try:
            address = int(args[0], 16)
        except:
            print "Invalid address: ", args[0]
            return False

        if not print_results(self.address_registry.match(address)):
            print "Can't match any of known memory regions to address", args[0]

    def cmd_heapcheck(self, args=None):
        if self.heap.validate():
            print "Heap check OK"

    def cmd_heapstats(self, args=None):
        stats = self.heap.get_stats()

        maxlen = max([len(desc) for desc in heap_stats_entries.values()])

        for field, desc in heap_stats_entries.iteritems():
            indent = (maxlen - len(desc)) * ' '
            print "\t" + desc + indent, ":", getattr(stats, field)

    def cmd_stackcheck(self, args=None):
        blocksize = STACKHEALTH_DEFAULT_BLOCK_SIZE
        if args is not None:
            if len(args) > 1:
                print "Usage: pure stackcheck [BLOCKSIZE]"
                return

            if len(args) == 1:
                try:
                    blocksize = int(args[0])
                except:
                    print "Invalid block size, defaulting to", blocksize

        valid = True
        for t in self._get_threads():
            try:
                if not t.check_stack(blocksize):
                    print "Stack check failed for:", t.get_name()
                    valid = False
            except StackError as se:
                print "Error when checking stack of a task at", hex(se.task.get_address())
                print "Reason:", se
                print "Check TCB blocks!"
                valid = False
            except:
                print "\nFatal error while checking stack!!!"
                return

        if valid:
            print "Stack check OK"

    def cmd_checkhealth(self, args=None):
        self.cmd_stackcheck()
        self.cmd_heapcheck()

    def cmd_stackstats(self, args=None):
        if args is None or len(args) == 0:
            stackdepth = STACKHEALTH_DEFAULT_BLOCK_SIZE
        elif len(args) == 1:
            stackdepth = int(args[0])
        else:
            print "Invalid arguments"
            print "Usage: pure stackcheck [stackdepth]"
            return

        threads = self._get_threads()

        data = []
        for t in threads:
            name = t.get_name()
            free = t.get_free_stack_size(stackdepth)
            size = t.get_stack_size()
            pfree = float(free)/float(size)*100.0
            data.append((name, size, free, pfree))

        print "\tFREE%\tFREE\tSIZE\tTASK"
        for d in sorted(data, key=lambda o: o[3]):
            print "\t", format(d[3], "3.2f"), "\t", d[2], "\t", d[1], "\t", d[0]

    def cmd_help(self, args=None):
        print "Valid commands:"
        for cmd in dir(PureGDB):
            if cmd.startswith("cmd_"):
                cmd = cmd.replace("cmd_", "")
                print "\t" + cmd

    def cmd_tasks(self, args=None):
        tasks = [(int(t.v['uxTCBNumber']), t) for t in self._get_threads()]
        print "\t#\tHandle\t\tPrio\tStack start\tStack end\tTask"
        for num, t in sorted(tasks, key=lambda p: p[0]):
            address = t.get_address()
            prio = int(t.v['uxPriority'])
            stack_start = int(t.v['pxStack'])
            stack_end = int(t.v['pxEndOfStack'])
            name = t.get_name()
            print "\t", num, "\t", hex(address), "\t", prio, "\t", hex(stack_start), "\t", hex(stack_end), "\t", name

    def invoke(self, arg, from_tty):
        if arg == "":
            self.cmd_help()
            return

        cmd = arg.split()[0]
        args = arg.split()[1:]
        try:
            handler = getattr(PureGDB, "cmd_" + cmd)
        except AttributeError:
            print "Unregistered subcommand: " + cmd
            self.cmd_help()
            return

        try:
            handler(self, args)
        except:
            print traceback.format_exc()


print("Registering 'pure' command")
PureGDB()
