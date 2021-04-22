#!/bin/bash
set -e

post_process () {
   echo sed -i .bak 's/>=/$\\numgeq$/' $1
   sed -i .bak 's/>=/$\\numgeq$/' $1
   sed -i .bak 's/<=/$\\numleq$/' $1
   sed -i .bak 's/<-/$\\leftarrow$/' $1
   sed -i .bak 's/\[|/\$\\langle$/' $1
   sed -i .bak 's/\|]/$\\rangle$/' $1
   rm $1.bak
}

rm -rf fluid
mkdir fluid
pushd fluid
wget https://raw.githubusercontent.com/explorable-viz/fluid/master/fluid/lib/convolution.fld
post_process convolution.fld
wget https://raw.githubusercontent.com/explorable-viz/fluid/master/fluid/example/slicing/conv-extend.fld
post_process conv-extend.fld
popd
