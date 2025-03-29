#!/bin/bash
export CXX=/usr/lib/emscripten/em++
export CC=/usr/lib/emscripten/emcc
export AR=/usr/lib/emscripten/emar
export CXXFLAGS=-fPIC
./configure_emscripten --no-unlocked --no-flexible
make -j12
