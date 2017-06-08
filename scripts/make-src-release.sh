#!/bin/sh
cd `dirname $0`/..
root=`pwd`
version="`cat VERSION`"
gitid="`./scripts/get-git-id.sh|sed -e 's,^\(.......\).*,\1,'`"
name=cadical-${version}-${gitid}
dir=/tmp/$name
tar=/tmp/$name.tar.xz
rm -rf $dir
mkdir $dir || exit 1
cd $dir || exit 1
git clone $root $dir || exit 1
sed -i \
  -e 's,`./scripts/get-git-id.sh`,'"`./scripts/get-git-id.sh`", \
  $dir/scripts/make-config-header.sh
rm -rf $dir/test
sed -i -e '/rm -f test/d' $dir/makefile.in
cd /tmp
rm -rf /tmp/$name/.git
tar cJf $tar $name
ls -l $tar
