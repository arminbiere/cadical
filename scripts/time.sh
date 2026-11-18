#!/bin/sh
file=`echo "$*"|awk '{print $NF}'`
exec /usr/bin/time -f "  compiling $file took %e seconds"  $*
