#!/bin/sh
# print current SHA1 git id which uniquely identifies the source code
git show|awk '{print $2;exit}'
