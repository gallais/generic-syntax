SED=sed
PAPER=icfp18
SLIDES=icfp18-slides

all: latex/$(PAPER).pdf

AGDA_FILES:=\
  Stdlib.lagda \
  Data/Environment.lagda \
  Generic/Bisimilar.lagda \
  Generic/Cofinite.lagda \
  Generic/Examples/Colist.lagda \
  Generic/Syntax/LetBinder.lagda \
  Generic/Semantics/NbyE.lagda \
  Generic/Examples/NbyE.lagda \
  Generic/Syntax/STLC.lagda \
  Generic/Semantics/TypeChecking.lagda \
  Generic/Syntax/UTLC.lagda \
  Generic/Fusion.lagda \
  Generic/Fusion/Syntactic.lagda \
  Generic/Semantics.lagda \
  Generic/Semantics/Syntactic.lagda \
  Generic/Semantics/Elaboration/LetBinder.lagda \
  Generic/Simulation.lagda \
  Generic/Simulation/Syntactic.lagda \
  Generic/Syntax.lagda \
  Generic/Relator.lagda \
  StateOfTheArt/ACMM.lagda \
  StateOfTheArt/CDMM.lagda \
  Data/Var/Varlike.lagda \
  Data/Var.lagda

AGDA_OUTPUT:=$(patsubst %.lagda,latex/%.tex,$(AGDA_FILES))

.SECONDARY: $(AGDA_OUTPUT)

PAPER_DEPENDENCIES:=\
  common\
  latex/$(PAPER).tex\
  latex/syntax.tex \
  latex/acmart.cls \
  latex/commands.tex \
  latex/unicode.tex \
  latex/agda.sty \
  latex/main.bib \
  latex/ACM-Reference-Format.bst \

SLIDES_DEPENDENCIES:=\
  latex/$(SLIDES).tex\
  $(PAPER_DEPENDENCIES)

common:
	make -C ../common

latex/$(SLIDES).pdf: $(SLIDES_DEPENDENCIES)
	cd latex; latexmk -pdf $(SLIDES).tex

latex/$(PAPER).pdf: $(PAPER_DEPENDENCIES)
	cd latex; latexmk -pdf -bibtex $(PAPER).tex

latex/main.bib: main.bib
	@mkdir -p $(dir $@)
	cp $< $@

latex/agda.sty: $(AGDA_OUTPUT)
	@mkdir -p $(dir $@)
	cp ../common/latex/agda.sty latex/

latex/unicode.tex: unicode.tex
	@mkdir -p $(dir $@)
	cp $< $@

latex/commands.tex: commands.tex
	@mkdir -p $(dir $@)
	cp $< $@

latex/ACM-Reference-Format.bst: ACM-Reference-Format.bst
	@mkdir -p $(dir $@)
	cp $< $@

latex/acmart.cls: acmart.cls
	@mkdir -p $(dir $@)
	cp $< $@

latex/$(PAPER).tex: $(PAPER).tex rules.sed
	@mkdir -p $(dir $@)
	cp $< $@

latex/$(SLIDES).tex: $(SLIDES).tex rules.sed
	@mkdir -p $(dir $@)
	cp $< $@

latex/syntax.tex: syntax.tex rules.sed
	@mkdir -p $(dir $@)
	cp $< $@

latex/%.tex: ../common/latex/%.tex common
	@mkdir -p $(dir $@)
	cp $< $@

clean:
	make clean -C ../common
	rm -rf latex
