all: 321701183.pdf

321701183.pdf: main.pdf
	cp $^ $@ 

%.pdf: %.tex bib.bib
	lualatex $<
	pbibtex $<
	lualatex $<
	lualatex $<
