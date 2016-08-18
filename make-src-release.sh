#!/bin/sh
version="`cat VERSION`"
gitid="`./get-git-id.sh|sed -e 's,^\(.......\).*,\1,'`"
name=cadical-$version-$gitid
dir=/tmp/$name
tar=/tmp/$name.tar.bz2
rm -rf $dir
mkdir $dir
cp -p \
cadical.cc \
configure.sh \
LICENSE \
makefile.in \
make-config-header.sh \
README.md \
VERSION \
$dir
sed -i \
-e 's,`./get-git-id.sh`,'"`./get-git-id.sh`", \
$dir/make-config-header.sh
cd /tmp
tar jcf $tar $name
ls -l $tar
