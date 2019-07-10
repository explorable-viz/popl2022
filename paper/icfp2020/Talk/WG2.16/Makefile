PDFLATEX = pdflatex -file-line-error -halt-on-error
LATEX = latex

default: main

pdfs:
	rm -f fig/*.pdf
	epstopdf fig/UI-example-1.eps
	epstopdf fig/UI-example-2.eps
	epstopdf fig/UI-example-3.eps
	epstopdf fig/UI-example-4.eps

main:
	rm -f *.aux *.dvi *.log *.bbl *.blg *.vrb *.toc *.nav *.snm *.out
	rm -f *.pdf
	$(PDFLATEX) main
	gnome-open main.pdf &
	rm -f *.aux *.dvi *.log *.bbl *.blg *.vrb *.toc *.nav *.snm *.out
