#!/bin/bash
set -e

post_process () {
   sed -f ../sed-commands $1 > $1.mod
}

rm -rf fluid
mkdir fluid
pushd fluid
wget https://raw.githubusercontent.com/explorable-viz/fluid/master/fluid/lib/convolution.fld
post_process convolution.fld
wget https://raw.githubusercontent.com/explorable-viz/fluid/master/fluid/example/slicing/conv-extend.fld
post_process conv-extend.fld
popd
