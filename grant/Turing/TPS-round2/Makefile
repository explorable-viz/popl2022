PDFLATEX = pdflatex -file-line-error -halt-on-error
LATEX = latex

default: proposal

proposal:
	$(PDFLATEX) $@
	bibtex $@
	$(PDFLATEX) $@
	$(PDFLATEX) $@
	rm -f *.aux *.dvi *.log *.bbl *.blg *.out
	evince $@.pdf &
