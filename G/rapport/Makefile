BASENAME=root
STARTDIR=$(CURDIR)
OUTDIR=$(CURDIR)/output
PRINTER=s2a

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
	cat $(BASENAME).pdf | ssh ask lpr -P $(PRINTER)

clean:
	rm -r $(OUTDIR)
