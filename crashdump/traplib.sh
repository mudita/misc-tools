#!/bin/bash -e

# This is a simple trap library for
# handle resources free when the bash
# function left the current scope.
# Author: Lucjan Bryndza


# Global variable for handle resource free on exit
declare -a _TRAPLIB_ON_EXIT_ITEMS

# Internal function executed by the trap handler
function _traplib_on_exit()
{
    for i in "${_TRAPLIB_ON_EXIT_ITEMS[@]}"
    do
        eval $i
    done
}

# Library function that allows to add
# resource free command when bash function
# left the current scope
# Example usage: traplib_add_on_exit rm file
function traplib_add_on_exit()
{
    local n=${#_TRAPLIB_ON_EXIT_ITEMS[*]}
    _TRAPLIB_ON_EXIT_ITEMS[$n]="$*"
    if [[ $n -eq 0 ]]; then
        trap _traplib_on_exit EXIT
    fi
}

# Global variable for handle resource free on error
declare -a _TRAPLIB_ON_ERROR_ITEMS

# Internal function executed by the trap handler
function _traplib_on_error()
{
    for i in "${_TRAPLIB_ON_ERROR_ITEMS[@]}"
    do
        eval $i
    done
}

# Library functions that allows to add resource
# free command which will be executed on error
# Example usage: traplib_on_error rm file
function traplib_add_on_error()
{
    local n=${#_TRAPLIB_ON_ERROR_ITEMS[*]}
    _TRAPLIB_ON_ERROR_ITEMS[$n]="$*"
    if [[ $n -eq 0 ]]; then
        trap _traplib_on_error ERR
    fi
}

