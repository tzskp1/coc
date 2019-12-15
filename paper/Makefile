all: 321701183.pdf

.PHONY: edit

edit:
	latexmk -pvc

321701183.pdf: main.pdf
	cp $^ $@ 

%.pdf: %.tex bib.bib
	lualatex $*
	pbibtex $*
	lualatex $*
	lualatex $*
