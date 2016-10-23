#!/bin/sh
cd `dirname $0`/../build
version="`cat ../VERSION`"
gitid="`./get-git-id.sh|sed -e 's,^\(.......\).*,\1,'`"
name=cadical-$version-$gitid
dir=/tmp/$name
tar=/tmp/$name.tar.xz
rm -rf $dir
mkdir $dir
cp -p ../LICENSE ../README.md ../VERSION $dir
mkdir $dir/src
cp -p ../src/*.[ch]pp $dir/src
mkdir $dir/build
cp -p makefile.in configure.sh make-config-header.sh $dir/build
sed -i -e 's,`./get-git-id.sh`,'"`./get-git-id.sh`", $dir/build/make-config-header.sh
sed -i -e '/rm -f test/d' $dir/build/makefile.in
cd /tmp
tar cJf $tar $name
ls -l $tar
