# Build the paper. paper.md is the single source; paper.tex is generated from
# it with pandoc, then compiled with pdflatex. Requires pandoc (>= 3) and a
# TeX distribution with pdflatex (TeX Live / MacTeX).

SRC      := paper.md
BUILD    := build
TEX      := $(BUILD)/paper.tex
PDF      := $(BUILD)/paper.pdf
HTML     := $(BUILD)/paper.html
PANDOC   := pandoc
LATEX    := pdflatex
LATEXOPT := -interaction=nonstopmode -halt-on-error \
	-output-directory=$(BUILD)
PANDOC_TEX_OPTS := -s -f markdown -t latex \
	-V geometry:margin=2.5cm -V colorlinks=true -V fontsize=11pt \
	-V header-includes='\usepackage{amsmath,amssymb}' \
	-V header-includes='\usepackage{url}' \
	--lua-filter=latex-paths.lua

.PHONY: help
help: ## Ask for help!
	@grep -E '^[a-zA-Z0-9_-]+:.*?## .*$$' $(MAKEFILE_LIST) | sort | \
		awk 'BEGIN {FS = ":.*?## "}; \
		{printf "\033[36m%-30s\033[0m %s\n", $$1, $$2}'

.PHONY: all
all: pdf html ## Build the PDF and the HTML version

.PHONY: tex
tex: $(TEX) ## Generate the LaTeX source build/paper.tex from paper.md

.PHONY: pdf
pdf: $(PDF) ## Compile build/paper.pdf (via LaTeX)

.PHONY: html
html: $(HTML) ## Standalone HTML with MathML math (renders offline, phones)

$(BUILD):
	mkdir -p $(BUILD)

$(TEX): $(SRC) latex-paths.lua | $(BUILD)
	$(PANDOC) $(SRC) $(PANDOC_TEX_OPTS) -o $@

# Two passes so cross-references and hyperlinks settle.
$(PDF): $(TEX)
	$(LATEX) $(LATEXOPT) $(TEX) > $(BUILD)/latex.log 2>&1 || \
		{ grep -n -A3 '^!' $(BUILD)/latex.log; exit 1; }
	$(LATEX) $(LATEXOPT) $(TEX) > $(BUILD)/latex.log 2>&1 || \
		{ grep -n -A3 '^!' $(BUILD)/latex.log; exit 1; }
	@echo "built $@"

$(HTML): $(SRC) | $(BUILD)
	$(PANDOC) $(SRC) -s -f markdown -t html5 --math-method=mathml \
		--metadata title-prefix="" -o $@
	@echo "built $@"

.PHONY: check
check: pdf ## Build the PDF and fail on undefined references or overfull math
	@! grep -n 'Undefined control sequence\|undefined references' \
		$(BUILD)/latex.log

.PHONY: clean
clean: ## Remove build artifacts
	rm -rf $(BUILD)
