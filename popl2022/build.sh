PDFLATEX="pdflatex -file-line-error -halt-on-error"
TARGET=main

$PDFLATEX $TARGET
#	bibtex $TARGET
#	$PDFLATEX $TARGET
$PDFLATEX $TARGET
rm -f $TARGET.aux $TARGET.dvi $TARGET.log $TARGET.bbl $TARGET.blg $TARGET.out $TARGET.pag $TARGET.cb $TARGET.cb2 $TARGET.toc
