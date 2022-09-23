#!/bin/bash -e
# Copyright (c) 2017-2021, Mudita Sp. z.o.o. All rights reserved.
# For licensing, see https://github.com/mudita/MuditaOS/LICENSE.md

LIB_DIR="$(dirname "$(readlink -f "$0")")"
source "$LIB_DIR/traplib.sh"

# Print long help
help() 
{
cat<<EOF
Usage:
Analyse crashdump from the regular release and print on the stdout
    $(basename $0) --dump <crashdump-file> --tag <git-tag>
Analyse crashdump from the developer OS build and print on the stdout
    $(basename $0) --dump <crashdump-file> --dir <build-dir>
Display help:
    $(basename $0) --help

Mandatory arguments for regular release:
    crashdump-file:     The crash dump file grabbed from the phone
    git-tag:            Git tag of the OS version for mudita os release
Mandatory arguments for the developer build:
    crashdump-file:     The crash dump file grabbed from the phone
    build-dir:          Build directory with the MuditaOS source
EOF
    exit 0
}

#Exit abnormal check
exit_abnormal() {
cat<<EOF >&2
$(basename $0): $1
Try '$(basename $0) --help' for more information
EOF
    exit 1
}


# Check if all programs needed by scripts are installed
# arg1 .. argn: programs for validate
# On failure terminate the script and set errno
validate_req_cmds() {
    for cmd in $@; do
        if [ ! $(command -v $cmd) ]; then
            echo "Error! $cmd is not installed, please use your package manager to install required tool. E.g. sudo apt install"
            exit 100
        fi
    done
}

# Detect product type in a directory
# Input:  arg1 Base directory
# Output: elf and dbg file
autodetect_product_in_dir() {
    local elf="$(find "$1" -maxdepth 1 -type f -iname '*.elf' -executable -printf '%f' -quit)"
    local dbg="$(find "$1" -maxdepth 1 -type f -iname '*.elf.debug' -executable -printf '%f' -quit)"
    echo "$elf"
    echo "$dbg"
}

# Detect product type by the tag
# Input: arg1 Base directory
# Return elf and dbg file
autodetect_product_with_tag() {
    if [[ "$1" =~ pure_* ]]; then
        local elf="PurePhone.elf"
        local dbg="PurePhone.elf.debug.xz"
    elif [[ "$1" =~ bell_* ]]; then
        local elf="BellHybrid.elf"
        local dbg="BellHybrid.elf.debug.xz"
    else
        local elf="unknown"
        local dbg="unknown"
    fi
    echo "$elf"
    echo "$dbg"
}


# Parse command line arguments
parse_cmdline() {
    local prg_arg_list=(
        "dump:"
        "tag:"
        "dir:"
        "help"
    )
    local args=("$@")
    opts=$(getopt --longoptions "$(printf "%s," "${prg_arg_list[@]}")" \
        --name "$(basename "$0")" --options "" -- "$@"
    ) || exit 2
    eval set --$opts
    while [[ $# -gt 0 ]]; do
        case "$1" in
            --dump)
                DUMP_FILE="$2"
                shift
                ;;
            --help)
                shift
                help
                ;;
            --dir)
                BUILD_DIR="$2"
                shift
                ;;
            --tag)
                BUILD_TAG="$2"
                shift
                ;;
            --)
                shift
                break
                ;;
        esac;
        shift
    done
 # Validate mode
    if [[ -z "$BUILD_DIR" && -z "$BUILD_TAG" ]]; then
        exit_abnormal "Unknown command mode. Use --tag or --dir"
    fi
	if [[ -v BUILD_DIR ]]; then
        # Check if input file exists
        if [ ! -d "$BUILD_DIR" ]; then
            exit_abnormal "Build directory: $BUILD_DIR doesn't exists"
        fi
        {
            read -r ELF_NAME
            read -r DBG_NAME
        } <<< "$(autodetect_product_in_dir "$BUILD_DIR")"
		# Check for the executable elf file
		ELF_FILE="$BUILD_DIR/$ELF_NAME"
        if [ ! -f "$ELF_FILE" ]; then
            exit_abnormal "Executable file: $ELF_FILE doesn't exists"
        fi
		# Check for debug elf file
		DBG_FILE="$BUILD_DIR/$DBG_NAME"
        if [ ! -f "$DBG_FILE" ]; then
            exit_abnormal "Executable file: $DBG_FILE doesn't exists"
		fi
	fi
	# Check for dump file
	if [ ! -f "$DUMP_FILE" ]; then
		exit_abnormal "Crashdump file: $DUMP_FILE doesn't exists"
	fi
}

#Crash debug on local dir
CRASH_DEBUG="./CrashDebug"

# Build crash debug 
build_crash_debug() {
	if [ ! -f "$CRASH_DEBUG" ]; then
        echo "CrashCatcher not found. Compiling ..."
		local crashdbg_url="git@github.com:adamgreen/CrashDebug.git"
		local crashdbg_src="$(mktemp -d)"
		traplib_add_on_exit rm -rf "$crashdbg_src"
		cd "$crashdbg_src"
		git clone --quiet --recursive --depth 1 "$crashdbg_url"
        make -C CrashDebug CrashDebug -j $(nproc) > /dev/null
		local crash_bin="$crashdbg_src/CrashDebug/CrashDebug"
		cd - > /dev/null
		cp "$crash_bin" "$CRASH_DEBUG"
	fi
}

#Download files using release
download_get_backtrace() {
    local tag="$1"
    local elf
    local dbg
    tag="${tag// /_}"
    {
        read -r elf
        read -r dbg
    } <<< "$(autodetect_product_with_tag "$tag")"
    if [ $elf = "unknown" ]; then
        exit_abnormal "Unable to detect product by tag $1"
    fi
    local dump="$2"
    local url_assets="https://api.github.com/repos/mudita/MuditaOS-releases/releases/tags/$tag"
    local gh_token="$(git config user.apitoken)"
    if [ -z "$gh_token" ]; then
        exit_abnormal "No user token defined in git user.apitoken variable"
    fi
    local auth_header="Authorization: token $gh_token"

    echo "Fetching URLs..."
    local assets=$(curl -sH "$auth_header" "$url_assets")
    local url_elf=$(echo "$assets" | jq -r ".assets[] | select(.name==\"$elf\") | .url")
    local url_dbg=$(echo "$assets" | jq -r ".assets[] | select(.name==\"$dbg\") | .url")

    local elf="$(mktemp)"
    local dbgxz="$(mktemp)"
    local dbg="$(mktemp)"
    traplib_add_on_exit rm "$elf"
    traplib_add_on_exit rm "$dbg"
    traplib_add_on_exit rm "$dbgxz"

    echo "Fetching ELF..."
    wget -q --show-progress --header="Accept: application/octet-stream" --header="$auth_header" "$url_elf" -O "$elf"
    echo "Fetching DBG..."
    wget -q --show-progress --header="Accept: application/octet-stream" --header="$auth_header" "$url_dbg" -O "$dbgxz"

    pv "$dbgxz" | xz -d --stdout  > "$dbg"
	  get_backtrace "$elf" "$dbg" "$dump"
}


# Only get and analyse backtrace
get_backtrace() {
	local elf="$1"
	local dbg="$2"
	local dump="$3"
  arm-none-eabi-gdb "$elf" \
        -x "$LIB_DIR/crashdump-gdbinit" \
        -ex "target remote | \"$CRASH_DEBUG\" --elf \"$elf\" --dump \"$dump\"" \
        -ex "symbol-file $dbg" \
        -ex 'backtrace'
}
parse_cmdline "$@"
validate_req_cmds xz arm-none-eabi-gdb pv make gcc git curl wget jq
build_crash_debug
if [[ -v BUILD_DIR ]]; then
	get_backtrace "$ELF_FILE" "$DBG_FILE" "$DUMP_FILE"
elif [[ -v BUILD_TAG ]]; then
    download_get_backtrace "$BUILD_TAG" "$DUMP_FILE"
else
    exit_abnormal "Unrecognized command"
fi
