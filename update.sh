#!/bin/sh
set -xe
make -C .. html
rm -r docs
mv ../html docs
sh ./cleanup.sh
git add docs
set +x
echo "OK!"
echo "Now do this > git commit -m \"Update\""
