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
rm -rf TODO.md test $dir/scripts
sed -i -e '/rm -f test/d' $dir/makefile.in
sed -i -e '/optionally test it/d' $dir/configure
mkdir $dir/scripts
sed \
  -e 's,`../scripts/get-git-id.sh`,'"`$root/scripts/get-git-id.sh`", \
  $root/scripts/make-config-header.sh > $dir/scripts/make-config-header.sh
chmod 755 $dir/scripts/*.sh
cd /tmp
rm -rf /tmp/$name/.git
tar cJf $tar $name
ls -l $tar
