#!/bin/bash
CXX=/usr/lib/emscripten/emcc ./configure_emscripten --no-unlocked --no-flexible
make -j12
