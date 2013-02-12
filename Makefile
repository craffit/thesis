
#
# REQUIRED TOOLS
#
# * latexmk: http://www.phys.psu.edu/~collins/software/latexmk/
#

.PHONY : thesis.pdf thesis.tex default thesis presentation presentation.pdf presentation.tex

all : thesis presentation

thesis : 
	lhs2TeX --agda thesis.lhs > thesis.tex
	latexmk -pdf thesis.tex
	
presentation:
	lhs2TeX --agda presentation.lhs -o presentation.latex
	latexmk -pdf presentation.latex

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
