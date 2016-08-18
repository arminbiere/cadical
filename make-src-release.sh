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
make-config-header.sh \
makefile.in \
README.md \
VERSION \
$dir
cd /tmp
tar jcf $tar $name
ls -l $tar
