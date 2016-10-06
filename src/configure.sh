#!/bin/sh

# just a proxy to '../build/configure.sh'

cd ../build
exec ./configure.sh $*
