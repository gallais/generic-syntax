PAPER=jfp19

all: latex/$(PAPER).pdf

AGDA_FILES:=\
  Stdlib.lagda \
  Data/Environment.lagda \
  Generic/Scopecheck.lagda \
  Generic/Bisimilar.lagda \
  Generic/Cofinite.lagda \
  Generic/Examples/Colist.lagda \
  Generic/Syntax/LetBinder.lagda \
  Generic/Syntax/LetCounter.lagda \
  Generic/Semantics/NbyE.lagda \
  Generic/Examples/NbyE.lagda \
  Generic/Syntax/STLC.lagda \
  Generic/Syntax/Bidirectional.lagda \
  Generic/Semantics/TypeChecking.lagda \
  Generic/Syntax/UTLC.lagda \
  Generic/Fusion.lagda \
  Generic/Fusion/Syntactic.lagda \
  Generic/Semantics.lagda \
  Generic/Semantics/Syntactic.lagda \
  Generic/Semantics/Printing.lagda \
  Generic/Examples/Printing.lagda \
  Generic/Semantics/Elaboration/LetBinder.lagda \
  Generic/Semantics/Elaboration/LetCounter.lagda \
  Generic/Semantics/Elaboration/Typed.lagda \
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
  latex/catalogue/desugaring.tex\
  latex/catalogue/elaborating.tex\
  latex/catalogue/inlining.tex\
  latex/catalogue/normalising.tex\
  latex/catalogue/printing.tex\
  latex/catalogue/scopechecking.tex\
  latex/catalogue/typechecking.tex\
  latex/jfp1.cls \
  latex/jfp.bst \
  latex/commands.tex \
  latex/unicode.tex \
  latex/agda.sty \
  latex/main.bib \

SLIDES_DEPENDENCIES:=\
  latex/$(SLIDES).tex\
  $(PAPER_DEPENDENCIES)

common:
	$(MAKE) -C ../common

latex/catalogue/%.tex: catalogue/%.tex
	mkdir -p $(dir $@)
	cp $< $@

latex/$(SLIDES).pdf: $(SLIDES_DEPENDENCIES)
	cd latex; latexmk -pdf $(SLIDES).tex

latex/$(PAPER).pdf: $(PAPER_DEPENDENCIES)
	cd latex; latexmk -pdf -bibtex $(PAPER).tex

latex/main.bib: ../common/main.bib
	@mkdir -p $(dir $@)
	cp $< $@

latex/agda.sty: $(AGDA_OUTPUT)
	@mkdir -p $(dir $@)
	cp ../common/latex/agda.sty latex/

latex/unicode.tex: ../common/unicode.tex
	@mkdir -p $(dir $@)
	cp $< $@

latex/commands.tex: ../common/commands.tex
	@mkdir -p $(dir $@)
	cp $< $@

latex/%.cls: %.cls
	@mkdir -p $(dir $@)
	cp $< $@

latex/%.bst: %.bst
	@mkdir -p $(dir $@)
	cp $< $@

latex/$(PAPER).tex: $(PAPER).tex
	@mkdir -p $(dir $@)
	cp $< $@

latex/$(SLIDES).tex: $(SLIDES).tex
	@mkdir -p $(dir $@)
	cp $< $@

latex/syntax.tex: syntax.tex
	@mkdir -p $(dir $@)
	cp $< $@

latex/%.tex: ../common/latex/%.tex common
	@mkdir -p $(dir $@)
	cp $< $@

clean:
	make clean -C ../common
	rm -rf latex
