#!/bin/sh
# print current SHA1 git id which uniquely identifies the source code
git show 2>/dev/null |awk '{print $2;exit}'
