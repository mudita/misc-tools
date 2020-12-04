# PurePhone GDB helper plugin

## Purpose of this plugin

This plugin has been created to help dealing with various of problems
related to corruption of FreeRTOS internal state, such as memory overruns (both stack and system heap).

It is designed to read different values from memory, so if memory
is corrupted and/or not initialised properly it may fail with
memory access exceptions. This plugin is not intended to be failproof.

## Usage

To use this plugin, first you need to load it with:
```
source path_to_plugin/puregdb.py
```
If everything is ok, a message will be shown:
```
Registering 'pure' command
```

Executing `pure` or `pure help` lists available commands:
```
(gdb) pure
Valid commands:
        checkhealth
        heapcheck
        heapstats
        help
        memory
        stackcheck
        stackstats
        tasks
```
### Checking system health (`checkhealth`)

`pure checkhealth` checks health of thread stacks and the heap. Please
refer to `stackcheck` and `heapcheck` commands for more information.

### Checking stack for overruns (`stackcheck`)

`pure stackcheck` checks tasks for stack overruns by reading `0xa5a5aa5a5` pattern at the bottom of a stack. 32 bytes of each stack
is read by default. It is possible to use different check size with
```
pure stackcheck BLOCKSIZE
```
where `BLOCKSIZE` is a non-negative number, e.g. `pure stackcheck 128`.

If there is a pattern mismatch a message will be shown, e.g.:
```
(gdb) pure stackcheck
Stack check failed for: ApplicationManager
```

### Checking heap for overruns (`heapcheck`)

`pure heapcheck` traverse over lists of _free_ and _taken_ heap blocks and checks their integrity by:
 * checking if list addresses are in system heap range,
 * checking value of markers.
If a corrupted block is detected, a message will be printed out:
```
(gdb) pure heapcheck
Error when iterating over heap's taken entries
Reason: Invalid next taken block
Problematic entry at:  0x2002edf8
```
Problematic entry can be printed out with:
```
print *(BlockLink_t*)0x2002edf8
```
You can display heap entry struct size and offsets if you need more
precise watchpoints with:
```
ptype /o BlockLink_t
```

### Matching address

Use `pure memory ADDRESS` to find memory region of `ADDRESS`, e.g.:
```
(gdb) pure memory 0x2000afb4
0x2000afa4 .. 0x2000bfa0 Tmr Svc
(gdb) pure memory 0x2002efb8
0x2000bfa4 .. 0x2005cfa4 HEAP
0x2002eeb8 .. 0x200308b8 ApplicationCall
```
A simple `pure memory` (no arguments) will display known memory regions. Regions can (and should) overlap, e.g. `HEAP` will overlap
stacks of dynamic tasks but won't overlap statically allocated tasks
such as timer service or `IDLE` task.
```
(gdb) pure memory
0x2000ad00 .. 0x2000aef8 IDLE
0x2000afa4 .. 0x2000bfa0 Tmr Svc
0x2000bfa4 .. 0x2005cfa4 HEAP
0x2000c310 .. 0x2000e308 SysMgrService
0x2000e870 .. 0x2000f868 EventManager
0x200103a0 .. 0x20012398 EventManager_w0
0x200125f0 .. 0x200185e8 ServiceDB
0x20018890 .. 0x20019888 Blinky
0x2001a090 .. 0x2001c088 TS0710Worker
0x2001c218 .. 0x20021fd0 ServiceCellular
0x20022228 .. 0x20024220 ServiceAudio
0x200244c8 .. 0x200254c0 ServiceBluetooth
0x20026b98 .. 0x20027b90 tcpip_thread
0x20027c80 .. 0x20028c78 ServiceLwIP
0x20028f20 .. 0x20029f18 ApplicationManager
0x2002a170 .. 0x2002b168 ServiceGUI
0x2002b438 .. 0x2002d430 ServiceGUI_w0
0x2002d6d8 .. 0x2002ead0 ServiceEink
0x2002eeb8 .. 0x200308b8 ApplicationCall
0x20030c50 .. 0x20031c48 AppSpecialInput
0x20031ef0 .. 0x20032ee8 ApplicationDesktop
```


### Displaying tasks' stack usage (`pure stackstats`)

To display tasks' stack usage use `pure stackstats`:
```
(gdb) pure stackstats
        FREE%   FREE    SIZE    TASK
        0.00    0       6656    ApplicationCall
        10.18   416     4088    ApplicationManager
        14.86   1216    8184    SysMgrService
        18.00   736     4088    ApplicationDesktop
        55.71   2848    5112    ServiceEink
        57.93   2368    4088    EventManager
        59.22   14208   23992   ServiceCellular
        62.52   15360   24568   ServiceDB
        66.54   2720    4088    ServiceGUI
        71.23   2912    4088    AppSpecialInput
        77.50   3168    4088    ServiceBluetooth
        79.84   3264    4088    ServiceLwIP
        81.33   6656    8184    TS0710Worker
        81.33   3328    4092    Tmr Svc
        82.54   416     504     IDLE
        85.32   3488    4088    Blinky
        90.71   7424    8184    ServiceGUI_w0
        91.50   7488    8184    EventManager_w0
        92.67   7584    8184    ServiceAudio
        93.15   3808    4088    tcpip_thread
```
List is sorted by usage percentage. If stack has `0` bytes left
on stack most likely its stack is corrupted (stack overflow).
By default blocks of 32 bytes are read so if you need more accurate
data (at cost of execution time) add blocksize argument, i.e.:
```
pure stacksize 4
```
will check every 4 bytes.

### Displaying system heap stats (`pure heapstats`)

Display overall and tasks' heap statistics with `pure heaptstats`:
```
(gdb) pure heapstats
Free blocks count                     : 1
Lowest size of heap                   : 171496
Used size (block + metadata)          : 160280
Free size                             : 171496
Taken blocks count                    : 133
Overall size of blocks (w/o metadata) : 160240
Overall heap size                     : 331776
ServiceBluetooth                      : 1072
ServiceCellular                       : 480
SysMgrService                         : 133760
mtp task                              : 33088
ApplicationManager                    : 34200
EventManager                          : 12176
ServiceDesktop                        : 33088
ServiceGUI                            : 10344
ServiceEink                           : 240
ServiceDB                             : 7920
ServiceTime                           : 80
```

### Displaying list of tasks (`pure tasks`)

Display list of tasks with `pure tasks`:
```
(gdb) pure tasks
#       Prio    Stack start     Stack end       Task
1       0       0x2000c310      0x2000e308      SysMgrService
2       0       0x2000ad00      0x2000aef8      IDLE
3       0       0x2000afa4      0x2000bfa0      Tmr Svc
4       0       0x2000e870      0x2000f868      EventManager
5       0       0x200103a0      0x20012398      EventManager_w0
6       0       0x200125f0      0x200185e8      ServiceDB
7       0       0x20018890      0x20019888      Blinky
8       0       0x2001a090      0x2001c088      TS0710Worker
9       0       0x2001c218      0x20021fd0      ServiceCellular
10      0       0x20022228      0x20024220      ServiceAudio
11      0       0x200244c8      0x200254c0      ServiceBluetooth
12      1       0x20026b98      0x20027b90      tcpip_thread
13      0       0x20027c80      0x20028c78      ServiceLwIP
14      0       0x20028f20      0x20029f18      ApplicationManager
15      0       0x2002a170      0x2002b168      ServiceGUI
16      0       0x2002b438      0x2002d430      ServiceGUI_w0
17      0       0x2002d6d8      0x2002ead0      ServiceEink
18      0       0x2002eeb8      0x200308b8      ApplicationCall
19      0       0x20030c50      0x20031c48      AppSpecialInput
20      0       0x20031ef0      0x20032ee8      ApplicationDesktop
```
First column comes from `uxTCBNumber` field member value.
