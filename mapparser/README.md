The script can parse linker map files. By defualt it prints out object
files with sizes (sumarized symbol's sizes not file size) and symbol
list. Both file list and symbol list are sorted, symbol list is sorted
for each object file.

Usage:
```sh
python3 mapparser.py [<mapfile>] [<sourcepath>]
```

If no mapfile is provided the script uses tries to find `linker.map`
file. `sourcepath` argument is used only to format relative paths.

