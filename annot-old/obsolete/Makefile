PDFLATEX = pdflatex -file-line-error -halt-on-error
LATEX = latex

default: main

main:
	$(PDFLATEX) main
	#bibtex main
	#$(PDFLATEX) main
	$(PDFLATEX) main
	rm -f *.aux *.dvi *.log *.bbl *.blg
