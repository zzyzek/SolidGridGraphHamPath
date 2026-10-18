# SPDX-License-Identifier: CC0-1.0
#
# Build build/hpst.pdf.  Uses latexmk when it is installed, otherwise
# pdflatex + bibtex.  `make figures` regenerates the TikZ figures.

MAIN    := hpst
BUILD   := build
LATEXMK := $(shell command -v latexmk 2>/dev/null)
PDFLATEX := pdflatex -interaction=nonstopmode -halt-on-error -output-directory=$(BUILD)
FIGS    := $(wildcard figures/fig_*.tex)

.PHONY: all figures clean

all: $(BUILD)/$(MAIN).pdf

$(BUILD)/$(MAIN).pdf: $(MAIN).tex references.bib $(FIGS) | $(BUILD)
ifneq ($(LATEXMK),)
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=$(BUILD) $(MAIN).tex
else
	$(PDFLATEX) $(MAIN).tex
	cd $(BUILD) && BIBINPUTS=..: bibtex $(MAIN)
	$(PDFLATEX) $(MAIN).tex
	$(PDFLATEX) $(MAIN).tex
endif

$(BUILD):
	mkdir -p $(BUILD)

figures:
	cd figures && python3 gen.py

clean:
	rm -rf $(BUILD)
