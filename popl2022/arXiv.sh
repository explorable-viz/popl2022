#!/bin/bash
set -e

NAME=arXiv.zip
pushd ..

zip -r $NAME popl2022 tex-common

zip -d $NAME *.pdf
zip -d $NAME *.DS_Store
zip -d $NAME *.git

ls -al $NAME
unzip -l $NAME

popd
