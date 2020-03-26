PDFLATEX = pdflatex -file-line-error -halt-on-error

default: main

main:
	$(PDFLATEX) $@
#	bibtex $@
#	$(PDFLATEX) $@
	$(PDFLATEX) $@
	rm -f $@.aux $@.dvi $@.log $@.bbl $@.blg $@.out $@.pag $@.cb $@.cb2 $@.toc
