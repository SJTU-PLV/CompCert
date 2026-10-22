LATEX ?= xelatex
TARGET := clight2rust_beamer

.PHONY: all tectonic clean

all:
	$(LATEX) -interaction=nonstopmode $(TARGET).tex
	$(LATEX) -interaction=nonstopmode $(TARGET).tex

tectonic:
	tectonic $(TARGET).tex

clean:
	rm -f $(TARGET).aux $(TARGET).log $(TARGET).nav $(TARGET).out $(TARGET).snm $(TARGET).toc $(TARGET).vrb $(TARGET).pdf
