BASENAME=root
OUTDIR=$(CURDIR)/output

default: compile
compile:
	@mkdir -p $(OUTDIR)
	pdflatex -output-directory="$(OUTDIR)" $(BASENAME).tex
	-cd $(OUTDIR) && bibtex $(BASENAME)
	pdflatex -output-directory="$(OUTDIR)" $(BASENAME).tex
	pdflatex -output-directory="$(OUTDIR)" $(BASENAME).tex


view: compile
	evince $(OUTDIR)/$(BASENAME).pdf

print:
	cat $(BASENAME).pdf | ssh ask.diku.dk lpr -P s2a

clean:
	rm -r $(OUTDIR)
