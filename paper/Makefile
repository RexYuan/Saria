all: poset.tex poset.bib
	pdflatex poset
	bibtex poset
	pdflatex poset
	pdflatex poset

clean:
	rm -f *.aux *.bbl *.blg *.log *.out *.toc poset.pdf *.cut _minted

.PHONY: all clean
