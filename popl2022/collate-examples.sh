#!/bin/bash
set -e

post_process () {
   sed -f ../sed-commands $1 > $1.mod
}

rm -rf fluid
mkdir fluid
pushd fluid
wget https://raw.githubusercontent.com/explorable-viz/fluid/develop/fluid/example/linking/bar-chart.fld
post_process bar-chart.fld
wget https://raw.githubusercontent.com/explorable-viz/fluid/develop/fluid/example/linking/line-chart.fld
post_process line-chart.fld
wget https://raw.githubusercontent.com/explorable-viz/fluid/develop/fluid/lib/convolution.fld
post_process convolution.fld
wget https://raw.githubusercontent.com/explorable-viz/fluid/develop/fluid/example/slicing/conv-extend.fld
post_process conv-extend.fld
wget https://raw.githubusercontent.com/explorable-viz/fluid/tree-example/fluid/example/slicing/list-comp.fld
post_process list-comp.fld
popd

# Need ChromeDriver for headless downloads; need to figure that out.
download_image () {
   ext=png
   folder=~/Downloads
   image=$folder/$1.$ext
   echo $image
   chrome --headless --user-data-dir=C:/tmp --disable-gpu --no-sandbox http://f.luid.org/new/
   until [ -f $image ]
   do
        sleep 1
        ls -la $folder
   done
   echo "Found $1.$2"
   exit
}

# download_image image
