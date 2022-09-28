#!/bin/bash
set -euo pipefail
IFS=$'\n\t'

if command -v gnutar >/dev/null ; then
  # On MacOS, run "sudo port install gnutar" to obtain gnutar.
  TAR=gnutar
else
  TAR=tar
fi

ARCHIVE=slgc

rm -rf $ARCHIVE $ARCHIVE.tar.gz

mkdir $ARCHIVE

make clean

cp -r \
   dune-project \
   README.md \
   src \
   setup.sh \
   Makefile \
   $ARCHIVE

find $ARCHIVE -type f -name '*.v' -exec sed -i 's/\s*(\*.*LATER.* \*)//g' {} \;

$TAR cvfz $ARCHIVE.tar.gz \
  --exclude-ignore-recursive=.gitignore \
  --owner=0 --group=0 \
  $ARCHIVE

rm -rf $ARCHIVE
