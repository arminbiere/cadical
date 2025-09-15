#!/bin/sh
set -x
cd `dirname $0`/..
root=`pwd`
tmp=/tmp/prepare-cadical-sc2024-submission.log
VERSION=`cat VERSION`
rm -f $tmp
##########################################################################
cd $root
./scripts/make-src-release.sh >$tmp || exit 1
tar=`awk '{print $2}' $tmp |sed -e "s,',,g"`
##########################################################################
cd $root
base=cadical-${VERSION}-starexec
dir=/tmp/$base
rm -rf $dir
mkdir $dir
mkdir $dir/bin
mkdir $dir/build
mkdir $dir/archives
cp -a $tar $dir/archives
cat <<EOF >$dir/build/build.sh
#!/bin/sh
tar xf ../archives/cadical*
mv cadical* cadical
cd cadical
./configure --competition
make test
install -s build/cadical ../../bin/
EOF
chmod 755 $dir/build/build.sh
cat <<EOF >$dir/starexec_build
#!/bin/sh
cd build
exec ./build.sh
EOF
chmod 755 $dir/starexec_build
cat <<EOF >$dir/bin/starexec_run_default
#!/bin/sh
exec ./cadical \$1 \$2/proof.out
EOF
chmod 755 $dir/bin/starexec_run_default
description=$dir/starexec_description.txt
grep '^CaDiCaL' README.md|head -1 >$description
cat $description
archive=/tmp/$base.zip
rm -f $archive
cd $dir
zip -r $archive .
cd /tmp/
ls -l $archive
rm -f $tmp
rm -rf $dir/
