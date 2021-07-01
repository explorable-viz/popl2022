#!/bin/bash
set -e

rm -rf fluid
mkdir fluid
wget -P fluid https://raw.githubusercontent.com/explorable-viz/fluid/master/fluid/example/linking/bar-chart.fld
./post-process.sh fluid/bar-chart.fld
wget -P fluid https://raw.githubusercontent.com/explorable-viz/fluid/master/fluid/example/linking/line-chart.fld
./post-process.sh fluid/line-chart.fld
wget -P fluid https://raw.githubusercontent.com/explorable-viz/fluid/master/fluid/lib/convolution.fld
./post-process.sh fluid/convolution.fld
wget -P fluid https://raw.githubusercontent.com/explorable-viz/fluid/master/fluid/example/slicing/conv-emboss.fld
./post-process.sh fluid/conv-emboss.fld

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
