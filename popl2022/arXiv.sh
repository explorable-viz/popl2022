#!/bin/bash
set -e

NAME=arXiv.zip
TARGET=final-full

pdflatex $TARGET
bibtex $TARGET

rm -f $TARGET.aux $TARGET.dvi $TARGET.log $TARGET.blg $TARGET.out $TARGET.pag $TARGET.cb $TARGET.cb2 $TARGET.toc

pushd ..

zip -r $NAME popl2022 tex-common

zip -d $NAME *.pdf
zip -d $NAME *.DS_Store
zip -d $NAME *.git
zip -d $NAME *.gitignore

ls -al $NAME
unzip -l $NAME

popd

rm -f $TARGET.bbl
