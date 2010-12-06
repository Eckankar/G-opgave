BASENAME=root
OUTDIR=$(CURDIR)/output

default: compile
compile:
	@mkdir -p $(CURDIR)/output
	#pdflatex -output-directory=output/ $(BASENAME).tex
	#cd $(CURDIR)/output
	#bibtex $(CURDIR)/output/rapport.aux
	#cd $(CURDIR)
	pdflatex -output-directory=output/ $(BASENAME).tex && pdflatex -output-directory=output/ $(BASENAME).tex


view: compile
	evince $(CURDIR)/output/$(BASENAME).pdf

print:
	cat $(BASENAME).pdf | ssh ask.diku.dk lpr -P s2a

clean:
	rm -r $(OUTDIR)

