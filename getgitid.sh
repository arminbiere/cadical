#!/bin/sh
git show|awk '{print $2;exit}'
