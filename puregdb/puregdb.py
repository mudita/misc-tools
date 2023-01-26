# Copyright (c) 2017-2021, Mudita Sp. z.o.o. All rights reserved.
# For licensing, see https://github.com/mudita/MuditaOS/LICENSE.md

import collections
import traceback

import gdb

STACKHEALTH_DEFAULT_BLOCK_SIZE = 32
HEAP_STRUCT_SIZE = 32

AddressRange = collections.namedtuple("AddressRange", ["low", "high", "name"])


def get_int_by_name(varname):
    symbol, _ = gdb.lookup_symbol(varname)
    if symbol is None:
        raise RuntimeError("Can't find symbol: " + varname)

    return int(symbol.value())


class AddressRegistry:
    def __init__(self):
        self.entries = []

    def register(self, entry):
        self.entries.append(entry)
        self.entries.sort(key=lambda e: e.get_low_address())

    def match(self, address):
        return [
            entry
            for entry in self.entries
            if entry.get_low_address() <= address and entry.get_high_address() > address
        ]


class AddressRegistree:
    def __init__(self):
        pass

    def get_range(self):
        return AddressRegistry(
            low=self.get_low_address(),
            high=self.get_high_address(),
            name=self.get_name(),
        )

    def get_size(self):
        return self.get_high_address() - self.get_low_address()

    def __str__(self):
        return (
            hex(self.get_low_address())
            + " .. "
            + hex(self.get_high_address())
            + " "
            + self.get_name()
        )

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
            return self.v["pcTaskName"].string()
        except gdb.MemoryError:
            raise StackError(self, "Can't read stack memory")

    def get_low_address(self):
        return int(self.v["pxStack"])

    def get_high_address(self):
        return int(self.v["pxEndOfStack"])

    def get_address(self):
        return int(self.v)

    def get_stack_size(self):
        return self.get_size()

    def read_stack_bottom(self, l):
        return self.inf.read_memory(int(self.v["pxStack"]), l)

    def _check_stack_block_valid(self, address, bs):
        block = self.inf.read_memory(address, bs)
        return all([b == "\xa5" for b in block])

    def check_stack(self, bs=STACKHEALTH_DEFAULT_BLOCK_SIZE):
        try:
            return self._check_stack_block_valid(int(self.v["pxStack"]), bs)
        except gdb.MemoryError:
            raise StackError(self, "Can't read stack memory")

    def get_free_stack_size(self, bs=STACKHEALTH_DEFAULT_BLOCK_SIZE):
        ptr = int(self.v["pxStack"])
        end = int(self.v["pxEndOfStack"])
        free = 0
        while ptr < (end - bs):
            if not self._check_stack_block_valid(ptr, bs):
                break
            ptr += bs
            free += bs

        return free

    @staticmethod
    def from_handle(handle, inf):
        tsktype = gdb.lookup_type("struct tskTaskControlBlock")
        val = gdb.Value(handle)
        val = val.cast(tsktype.pointer())
        return PureTask(inf, val) if val else None


HeapEntry = collections.namedtuple("HeapEntry", ["address", "size", "task", "time"])
UserHeapEntry = collections.namedtuple("UserHeapEntry", ["address", "size"])
heap_stats_entries = {
    "minimum_free": "Lowest size of heap",
    "free": "Free size",
    "size": "Overall heap size",
    "used": "Used size (block + metadata)",
    "taken": "Overall size of blocks (w/o metadata)",
    "free_block_count": "Free blocks count",
    "taken_block_count": "Taken blocks count",
}
user_heap_stats_entries = {
    "minimum_free": "Lowest size of heap",
    "free": "Free size",
    "size": "Overall heap size",
    "used": "Used size (block + metadata)",
    "free_block_count": "Free blocks count",
}
HeapStats = collections.namedtuple("HeapStats", heap_stats_entries.keys())
UserHeapStats = collections.namedtuple("UserHeapStats", user_heap_stats_entries.keys())


class HeapError(Exception):
    def __init__(self, entry, reason="", prev=None):
        self.entry = entry
        self.prev = prev
        self.reason = reason
        self.address = int(entry.address)
        self.prev_address = int(prev.address)

    def __str__(self):
        return self.reason


class UserHeapError(Exception):
    def __init__(self, entry, reason="", prev=None):
        self.entry = entry
        self.prev = prev
        self.reason = reason
        self.useraddress = int(entry.address)

    def __str__(self):
        return self.reason


class Heap(AddressRegistree):
    MARKER_ALLOCATED = 0xABABABAB
    MARKER_UNALLOCATED = 0xCDCDCDCD
    MARKER_FREED = 0xDDDDDDDD
    MARKER_SPECIAL = 0xBAADC0DE

    def __init__(self):
        self.start = gdb.lookup_symbol("xStart")[0].value()
        self.freeEnd = gdb.lookup_symbol("pxEnd")[0].value()
        ucHeap = gdb.lookup_symbol("ucHeap")[0].value()
        self.total_size = ucHeap.dynamic_type.sizeof
        self.address = int(ucHeap.address)
        self.taken_end = gdb.lookup_symbol("xTakenEnd")[0].value()
        self.userstart = gdb.lookup_symbol("userxStart")[0].value()
        self.userfreeEnd = gdb.lookup_symbol("userpxEnd")[0].value()
        userUcHeap = gdb.lookup_symbol("userUcHeap")[0].value()
        self.usertotal_size = userUcHeap.dynamic_type.sizeof
        self.useraddress = int(userUcHeap.address)

    def get_name(self):
        return "HEAP"

    def get_low_address(self):
        return self.address

    def get_high_address(self):
        return int(self.address + self.total_size)

    @staticmethod
    def _get_allocating_task(entry):
        inferiors = gdb.inferiors()
        if len(inferiors) != 1:
            return None
        return PureTask.from_handle(entry["xAllocatingTask"], inferiors[0])

    @staticmethod
    def _make_pod_entry(entry):
        entrySize = int(entry["xBlockSize"]) & 0x7FFFFFFF
        return HeapEntry(
            size=entrySize,
            address=int(entry.address),
            task=Heap._get_allocating_task(entry),
            time=int(entry["xTimeAllocated"]),
        )

    @staticmethod
    def _make_pod_entry_user(entry):
        entrySize = int(entry["xBlockSize"]) & 0x7FFFFFFF
        return UserHeapEntry(size=entrySize, address=int(entry.address))

    def get_stats(self):
        free_bytes = get_int_by_name("xFreeBytesRemaining")
        return HeapStats(
            minimum_free=get_int_by_name("xMinimumEverFreeBytesRemaining"),
            free=free_bytes,
            size=self.total_size,
            used=self.total_size - free_bytes,
            taken=sum([entry.size for entry in self.taken()]),
            free_block_count=len(list(self.free())),
            taken_block_count=len(list(self.taken())),
        )

    def get_userStats(self):
        free_bytes = get_int_by_name("userxFreeBytesRemaining")
        return UserHeapStats(
            minimum_free=get_int_by_name("userxMinimumEverFreeBytesRemaining"),
            free=free_bytes,
            size=self.usertotal_size,
            used=self.usertotal_size - free_bytes,
            free_block_count=len(list(self.userfree())),
        )

    def _check_ptr_invalid(self, pentry):
        return (
            int(pentry) > (self.address + self.total_size) or int(pentry) < self.address
        )

    def _check_user_ptr_invalid(self, pentry):
        return (
            int(pentry) > (self.useraddress + self.usertotal_size - HEAP_STRUCT_SIZE)
            or int(pentry) < self.useraddress
        )

    def free(self):
        if int(self.start["ulMarker"]) != Heap.MARKER_SPECIAL:
            raise HeapError(self.start, "Error in start block")

        pentry = self.start["pxNextFreeBlock"]

        while pentry != self.freeEnd:
            entry = pentry.dereference()
            pentry = entry["pxNextFreeBlock"]
            if self._check_ptr_invalid(pentry):
                raise HeapError(entry, "Invalid next free block")

            if (
                int(entry["ulMarker"]) != Heap.MARKER_UNALLOCATED
                and int(entry["ulMarker"]) != Heap.MARKER_FREED
            ):
                raise HeapError(entry, "Invalid marker")

            yield Heap._make_pod_entry(entry)

    def userfree(self):
        pentry = self.userstart["pxNextFreeBlock"]

        while pentry != self.userfreeEnd:
            entry = pentry.dereference()
            pentry = entry["pxNextFreeBlock"]
            if self._check_user_ptr_invalid(pentry):
                raise UserHeapError(
                    entry, "Invalid next free block - user heap integrity broken! "
                )

            entrySize = int(entry["xBlockSize"]) & 0x7FFFFFFF
            address = int(entry.address)
            # print("userHeap block addr: ", address, "\t\tsize: ", entrySize)

            yield Heap._make_pod_entry_user(entry)

    def taken(self):
        if int(self.start["ulMarker"]) != Heap.MARKER_SPECIAL:
            raise HeapError(self.start, "Error in start block")

        entry = self.start["pxNextTakenBlock"]
        prev = entry

        while entry.address != self.taken_end.address:
            if int(entry["ulMarker"]) != Heap.MARKER_ALLOCATED:
                raise HeapError(entry, "Invalid marker", prev)

            if (
                self._check_ptr_invalid(entry["pxNextTakenBlock"])
                and entry["pxNextTakenBlock"] != self.taken_end.address
            ):
                raise HeapError(entry, "Invalid next taken block", prev)

            yield Heap._make_pod_entry(entry)

            prev = entry
            entry = entry["pxNextTakenBlock"].dereference()

    def taken_per_task(self):
        taken_blocks = self.taken()
        histogram = {}
        for block in taken_blocks:
            if block.task:
                task_name = block.task.get_name()
                histogram[task_name] = histogram.get(task_name, 0) + block.size
        return histogram

    def validate(self):
        try:
            try:
                for _ in self.free():
                    pass

            except HeapError as he:
                print("Error when iterating over heap's free entries")
                raise he

            try:
                for _ in self.taken():
                    pass
            except HeapError as he:
                print("Error when iterating over heap's taken entries")
                raise he

        except HeapError as he:
            print("Reason:", he)
            print("Problematic entry at: ", hex(he.address))
            if he.prev is not None:
                print("Previous entry at: ", hex(he.prev_address))
            return False

        return True


class PureGDB(gdb.Command):
    def __init__(self):
        super(PureGDB, self).__init__("pure", gdb.COMMAND_USER)

        self.heap = Heap()

    def _get_inferior(self):
        infs = gdb.inferiors()
        if len(infs) != 1:
            print("Warning: Multiple inferiors")
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
        """
        Shows memory used for each thread
        see `pure tasks` to show full thread information by thread basic
        """
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
            print("Usage: pure memory [address] ")

        try:
            address = int(args[0], 16)
        except:
            print("Invalid address: ", args[0])
            return False

        if not print_results(self.address_registry.match(address)):
            print("Can't match any of known memory regions to address", args[0])

    def cmd_heapcheck(self, args=None):
        """
        Validates if heap used for stacks is not destroyed block by block
        depends on configSYSTEM_HEAP_STATS define variable
        """
        if self.heap.validate():
            print("Heap check OK")

    def cmd_heapstats(self, args=None):
        stats = self.heap.get_stats()

        maxlen = max([len(desc) for desc in heap_stats_entries.values()])

        for field, desc in heap_stats_entries.iteritems():
            indent = (maxlen - len(desc)) * " "
            print("\t" + desc + indent, ":", getattr(stats, field))

        histogram = self.heap.taken_per_task()
        for task_name, memory_size in histogram.items():
            indent = (maxlen - len(task_name)) * " "
            print("\t" + task_name + indent, ":", str(memory_size))

    def cmd_stackcheck(self, args=None):
        """
        Verifies stacks for each thread with use of each TCB block
        depends on: configSYSTEM_HEAP_INTEGRITY_CHECK define
        """
        blocksize = STACKHEALTH_DEFAULT_BLOCK_SIZE
        if args is not None:
            if len(args) > 1:
                print("Usage: pure stackcheck [BLOCKSIZE]")
                return

            if len(args) == 1:
                try:
                    blocksize = int(args[0])
                except:
                    print("Invalid block size, defaulting to", blocksize)

        valid = True
        for t in self._get_threads():
            try:
                if not t.check_stack(blocksize):
                    print("Stack check failed for:", t.get_name())
                    valid = False
            except StackError as se:
                print(
                    "Error when checking stack of a task at", hex(se.task.get_address())
                )
                print("Reason:", se)
                print("Check TCB blocks!")
                valid = False
            except:
                print("\nFatal error while checking stack!!!")
                return

        if valid:
            print("Stack check OK")

    def cmd_checkhealth(self, args=None):
        """
        Verifies:
            - stack for each thread with stackcheck
            - heap on which stacks are allocated with heapcheck
        """
        self.cmd_stackcheck()
        self.cmd_heapcheck()

    def cmd_stackstats(self, args=None):
        """
        Shows per task stack usage statistics
        """
        if args is None or len(args) == 0:
            stackdepth = STACKHEALTH_DEFAULT_BLOCK_SIZE
        elif len(args) == 1:
            stackdepth = int(args[0])
        else:
            print("Invalid arguments")
            print("Usage: pure stackcheck [stackdepth]")
            return

        threads = self._get_threads()

        data = []
        for t in threads:
            name = t.get_name()
            free = t.get_free_stack_size(stackdepth)
            size = t.get_stack_size()
            pfree = float(free) / float(size) * 100.0
            data.append((name, size, free, pfree))

        print("\tFREE%\tFREE\tSIZE\tTASK")
        for d in sorted(data, key=lambda o: o[3]):
            print("\t", format(d[3], "3.2f"), "\t", d[2], "\t", d[1], "\t", d[0])

    def cmd_help(self, args=None):
        """
        Shows name for each function available as command and it's docstring
        """
        print("Valid commands:")
        for cmd in dir(PureGDB):
            if cmd.startswith("cmd_"):
                docstring = eval("self.{}.__doc__".format(cmd))
                if docstring is None:
                    docstring = "Not documented"
                cmd = cmd.replace("cmd_", "")
                print("\t{}".format(cmd))
                for l in docstring.splitlines():
                    print("\t\t{}".format(l))

    def cmd_userheapstats(self, args=None):
        """
        Shows heap blocks and their size
        """
        print("User heap stats:")
        stats = self.heap.get_userStats()

        maxlen = max([len(desc) for desc in user_heap_stats_entries.values()])

        for field, desc in user_heap_stats_entries.iteritems():
            indent = (maxlen - len(desc)) * " "
            print("\t" + desc + indent, ":", getattr(stats, field))

    def cmd_tasks(self, args=None):
        """
        Shows FreeRTOS tasks data in format:
        |  no |     Handle | Priority | Stack start |  Stack end | Stack size |       Task name      |
        ______________________________________________________________________________________________
        |   1 | 0x20001360 |        3 |  0x20000f40 | 0x20001338 |       1016 |      System_Watchdog |
        |   2 | 0x200039d8 |        0 |  0x200019b8 | 0x200039b0 |       8184 |        SysMgrService |
        """
        tasks = [(int(t.v["uxTCBNumber"]), t) for t in self._get_threads()]
        header = "|  no |     Handle | Priority | Stack start |  Stack end | Stack size |       Task name      |"
        print(header)
        print("{}".format("".join(["_" for v in header])))
        for num, t in sorted(tasks, key=lambda p: p[0]):
            address = t.get_address()
            priority = int(t.v["uxPriority"])
            stack_start = int(t.v["pxStack"])
            stack_end = int(t.v["pxEndOfStack"])
            name = t.get_name()
            print(
                "| {: >3} | 0x{:08x} | {: >8} |  0x{:08x} | 0x{:08x} | {: >10} | {: >20} |".format(
                    num,
                    address,
                    priority,
                    stack_start,
                    stack_end,
                    stack_end - stack_start,
                    name,
                )
            )
        print("{}".format("".join(["_" for v in header])))

    def invoke(self, arg, from_tty):
        if arg == "":
            self.cmd_help()
            return

        cmd = arg.split()[0]
        args = arg.split()[1:]
        try:
            handler = getattr(PureGDB, "cmd_" + cmd)
        except AttributeError:
            print("Unregistered subcommand: " + cmd)
            self.cmd_help()
            return

        try:
            handler(self, args)
        except:
            print(traceback.format_exc())


if __name__ == "__main__":
    print("Registering 'pure' command")
    PureGDB()
