
#
# REQUIRED TOOLS
#
# * latexmk: http://www.phys.psu.edu/~collins/software/latexmk/
#

.PHONY : thesis.pdf thesis.tex default thesis

thesis : 
	lhs2TeX --poly thesis.lhs > thesis.tex
	latexmk -pdf thesis.tex

TARGET := thesis

default : $(TARGET).pdf

$(TARGET).pdf : $(TARGET).bib

#-------------------------------------------------------------------------------

clean :
	rm -rf $(TARGET).tex $(TARGET).pdf
	rm -rf *.log *.aux *.thm *.toc *.fdb_latexmk *.ptb *.out *.bbl *.blg *.nav *.snm
	rm -rf *.pdfsync *.synctex.gz

#-------------------------------------------------------------------------------

%.pdf : %.tex
	latexmk -pdf $<

%.tex : %.lhs
	lhs2TeX --poly $< > $@

.SECONDARY : $(TARGET).tex
