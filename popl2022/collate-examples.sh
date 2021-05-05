#!/bin/bash
set -e

post_process () {
   sed -f ../sed-commands $1 > $1.mod
}

rm -rf fluid
mkdir fluid
pushd fluid
# wget https://raw.githubusercontent.com/explorable-viz/fluid/master/fluid/lib/convolution.fld
# post_process convolution.fld
# wget https://raw.githubusercontent.com/explorable-viz/fluid/master/fluid/example/slicing/conv-extend.fld
# post_process conv-extend.fld
popd

download_image () {
   ext=png
   folder=~/Downloads
   image=$folder/$1.$2
   echo $image
   mkdir $folder
   chrome --headless --disable-gpu --no-sandbox http://f.luid.org/new/
   until [ -f $image ]
   do
        sleep 1
        ls -la $folder
   done
   echo "Found $1.$2"
   exit
}

download_image image
