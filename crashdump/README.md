# Crash dump script analyzer for BELL and PURE for the regular release.


## Description
**crashdump_backtrace.sh** is a tool for analyse crash dump file created by the Pure and Bell devices in any kind of failures like:

- Hardware failures - Hard Faults
- Abnormal termination - abort()
- Exit with negative error code exit()
- Uncatched exceptions

The script is self contained and for analyse crash dump logs from the released system we don't need to download OS source code, except some tools from the linux package manager. Script is able to automaticaly download all files from regular release required to logs analyse.

## Prerequisites 

Tool is written as a bash script so for proper work we need to install few shell tools: _xz_, _arm-none-eabi-gdb_, _pv_, _wget_, _make_, _gcc_, _git_. 
When you are using ubuntu all required tools can be installed using following command:

```sh
sudo apt install xz-utils gcc-arm-embedded pv wget make git gcc
```

## Howto use the script 

### Retrive stacktrace from the regular release

When the phone crash crashdumps will be stored on the user partition on the user partition in the **/crash_dumps** directory. Latest crash dump has the following path **/crash_dumps/crashdump.hex**. N-1 crashdump is located in the **/crash_dumps/crashdump.hex.1** etc.
When the phone crash stacktrace can be retrived with following steps:

* Mount the pure user partition eg using command `sh sudo mount /dev/<pure_dev3> /mnt `
* Find the tag which from the release was build by checking the following location: [os releases](https://github.com/mudita/MuditaOS/releases)
* Run the script with the following command `crashdump_backtrace.sh --dump /mnt/crash_dumps/crashdump.hex --tag pure_1.0.0-crashdump_fail_test_tag` where the tag is a tag name retrived from the github release page. The crashdump after analyse should print out a backtrace which can be included to the Jira case etc 

Here is an example backtrace from uncatched exception:

```sh
$ ./crashdump_backtrace.sh --dump /media/pure/crash_dumps/crashdump.hex --tag pure_1.0.0-crashdump_fail_test_tag 
/tmp/tmp.xynNfXuDei                                 100%[=================================================================================================================>]   5,34M  10,5MB/s    in 0,5s    
/tmp/tmp.QlwTe0CMfd                                 100%[=================================================================================================================>]  61,08M  37,8MB/s    in 1,6s    
61,1MiB 0:00:04 [14,9MiB/s] [==============================================================================================================================================================>] 100%            
GNU gdb (GNU Arm Embedded Toolchain 10.3-2021.07) 10.2.90.20210621-git
Copyright (C) 2021 Free Software Foundation, Inc.
License GPLv3+: GNU GPL version 3 or later <http://gnu.org/licenses/gpl.html>
This is free software: you are free to change and redistribute it.
There is NO WARRANTY, to the extent permitted by law.
Type "show copying" and "show warranty" for details.
This GDB was configured as "--host=x86_64-linux-gnu --target=arm-none-eabi".
Type "show configuration" for configuration details.
For bug reporting instructions, please see:
<https://www.gnu.org/software/gdb/bugs/>.
Find the GDB manual and other documentation resources online at:
    <http://www.gnu.org/software/gdb/documentation/>.

For help, type "help".
Type "apropos word" to search for commands related to "word"...
Reading symbols from /tmp/tmp.xynNfXuDei...
(No debugging symbols found in /tmp/tmp.xynNfXuDei)
Remote debugging using | "./CrashDebug" --elf "/tmp/tmp.xynNfXuDei" --dump "/media/pure/crash_dumps/crashdump.hex"
0x8002747c in ?? ()
Reading symbols from /tmp/tmp.ChXQDoT9od...
#0  _StackTrace_Dump_And_Abort () at /home/jenkins/workspace/MuditaOS_release_builder_-_signed/MuditaOS/module-os/board/rt1051/include/exit_backtrace.h:49
#1  _exit_backtrace (code=1, bt_dump=<optimized out>) at /home/jenkins/workspace/MuditaOS_release_builder_-_signed/MuditaOS/module-os/board/rt1051/_exit.cpp:72
#2  0x800274bc in _exit (code=<optimized out>) at /home/jenkins/workspace/MuditaOS_release_builder_-_signed/MuditaOS/module-os/board/rt1051/_exit.cpp:80
#3  0x803e8618 in abort ()
#4  0x803aba6c in __gnu_cxx::__verbose_terminate_handler() ()
#5  0x803aae56 in __cxxabiv1::__terminate(void (*)()) ()
#6  0x803aae86 in std::terminate() ()
#7  0x803aafa4 in __cxa_throw () at /usr/local/gcc-arm-none-eabi-10-2020-q4-major/arm-none-eabi/include/c++/10.2.1/bits/stl_map.h:302
#8  0x802a2c0c in BluetoothWorker::handleCommand (this=0x823c8940 <userUcHeap+3967296>, queue=0x20018850 <ucHeap+97760>) at /home/jenkins/workspace/MuditaOS_release_builder_-_signed/MuditaOS/module-bluetooth/Bluetooth/BluetoothWorker.cpp:153
#9  0x802a2d50 in BluetoothWorker::handleMessage (this=<optimized out>, queueID=3) at /home/jenkins/workspace/MuditaOS_release_builder_-_signed/MuditaOS/module-bluetooth/Bluetooth/BluetoothWorker.cpp:196
#10 0x80386e94 in sys::Worker::task (this=0x823c8940 <userUcHeap+3967296>) at /home/jenkins/workspace/MuditaOS_release_builder_-_signed/MuditaOS/module-sys/Service/Worker.cpp:68
#11 0x803e85b4 in ulHighFrequencyTimerTicks () at /home/jenkins/workspace/MuditaOS_release_builder_-_signed/MuditaOS/module-os/board/rt1051/fsl_runtimestat_gpt.c:39
Backtrace stopped: Cannot access memory at address 0xa5a5a5a9

# lucck @ lucck-ThinkPad-T490 in ~/worksrc/MuditaOS/tools/misc/crashdump on git:EGD-7980_script_for_crash_dump_automation x [9:44:19] 
```
### Retrive stacktrace from the developer build

The script is not only to able to retrieve stacktrace from regular release but also it can take a stacktrace from the developer build. The script is located in the OS repository in the following location **tools/misc/crashdump**. 
If we have a build binary we can retrieve the stacktrace using the following command: `sh ./crashdump_backtrace.sh --dir ~/worksrc/MuditaOS/build-PurePhone-rt1051-RelWithDebInfo --dump ~/worksrc/crashdump.sample/crashdump.hex`
Where:

* **--dir** is a path to the OS build directory
* **--dump** is a path to the crash dump for analyse on the phone 

Also, an optional argument can be given for both developer and release builds:
* **--gdb** is a path to a custom GDB executable, e.g. when you need one more recent than the system's default

For more information you can type: `sh crashdump_backtrace.sh --help`
