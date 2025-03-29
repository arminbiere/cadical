#!/bin/bash
rm -f build/libcadi*
rm -f build/cadical
emconfigure ./configure --no-contracts --no-tracing
emmake make -j12
cp build/libcadical* $EMINSTALL/lib/
