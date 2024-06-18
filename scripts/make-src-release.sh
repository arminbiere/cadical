#!/bin/sh
die () {
  echo "make-src-release.sh: error: $*" 1>&2
  exit 1
}
cd `dirname $0`/..
[ -d .git ] || \
die "does not seem to be under 'git' control ('.git' not found)"
version="`awk '/define VERSION/{print $3}' src/version.cpp|sed -e 's,",,g'`"
VERSION="`cat VERSION`"
[ "$version" = "$VERSION" ] || \
die "versions '$version' in 'src/version.cpp' and " \
    "'$VERSION' in 'VERSION' do not match (run 'scripts/update-version.sh')"
fullgitid="`./scripts/get-git-id.sh`"
gitid="`echo $fullgitid|sed -e 's,^\(.......\).*,\1,'`"
branch=`git branch|grep '^\*'|head -1|awk '{print $2}'`
[ "$branch" = "" ] && die "could not get branch from 'git'"
name=cadical-${version}-${gitid}
[ "$branch" = "master" ] || name="$name-$branch"
dir=/tmp/$name
tar=/tmp/$name.tar.xz
rm -rf $dir
mkdir $dir || exit 1
git archive $branch | tar -x -C $dir
cat >$dir/scripts/get-git-id.sh <<EOF
#!/bin/sh
echo "$fullgitid"
EOF
sed -i -e "s,IDENTIFIER 0$,IDENTIFIER \"$fullgitid\"," $dir/src/version.cpp
chmod 755 $dir/scripts/*.sh
cd /tmp
rm -rf /tmp/$name/.git
tar cJf $tar $name
bytes="`ls --block-size=1 -s $tar 2>/dev/null |awk '{print $1}'`"
echo "generated '$tar' of $bytes bytes"
rm -rf $dir
