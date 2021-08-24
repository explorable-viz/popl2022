#!/bin/bash
set -e

PDFLATEX="pdflatex -file-line-error -halt-on-error"
TARGET=${1:-main}
echo Building target \"$TARGET\".

$PDFLATEX $TARGET
# bibtex $TARGET
# $PDFLATEX $TARGET
$PDFLATEX $TARGET
rm -f $TARGET.aux $TARGET.dvi $TARGET.log $TARGET.bbl $TARGET.blg $TARGET.out $TARGET.pag $TARGET.cb $TARGET.cb2 $TARGET.toc
