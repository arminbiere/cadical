#!/bin/sh
cd `dirname $0`/..
set -xe
ccache -C
./configure --time $*
LC_ALL=C
export LC_ALL
make -j1 2>&1 | grep compiling | sort -rg -k 4 | head -10
