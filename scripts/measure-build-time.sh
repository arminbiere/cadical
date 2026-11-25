#!/bin/sh
cd `dirname $0`/..
set -xe
LC_ALL=C
export LC_ALL
CCACHE_DISABLE=1
export CCACHE_DISABLE
./configure --time $*
make -j1 2>&1 | grep compiling | sort -rg -k 4 | head -10
