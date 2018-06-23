SED=sed
PAPER=icfp18
AGDA=agda

all: latex/$(PAPER).pdf

AGDA_FILES:=\
  environment.lagda \
  Generic/Bisimilar.lagda \
  Generic/Cofinite.lagda \
  Generic/Data.lagda \
  Generic/Examples/Colist.lagda \
  Generic/Examples/ElaborationLet.lagda \
  Generic/Examples/NbyE.lagda \
  Generic/Examples/STLC.lagda \
  Generic/Examples/TypeChecking.lagda \
  Generic/Examples/UntypedLC.lagda \
  Generic/Fusion.lagda \
  Generic/Semantics.lagda \
  Generic/Simulation.lagda \
  Generic/Syntax.lagda \
  Generic/Zip.lagda \
  indexed.lagda \
  motivation.lagda \
  varlike.lagda \
  var.lagda

AGDA_OUTPUT:=$(patsubst %.lagda,latex-agda-output/%.tex,$(AGDA_FILES))
AGDA_OUTPUT_PROCESSED:=$(patsubst %.lagda,latex/%.tex,$(AGDA_FILES))

.SECONDARY: $(AGDA_OUTPUT)

PAPER_DEPENDENCIES:=\
  latex/$(PAPER).tex\
  latex/syntax.tex \
  latex/acmart.cls \
  latex/commands.tex \
  latex/agda.sty \
  latex/main.bib \
  latex/ACM-Reference-Format.bst \
  $(AGDA_OUTPUT_PROCESSED)

latex/$(PAPER).pdf: $(PAPER_DEPENDENCIES)
	cd latex; latexmk -pdf -bibtex $(PAPER).tex

latex/main.bib: main.bib
	@mkdir -p $(dir $@)
	cp $< $@

latex/agda.sty: $(AGDA_OUTPUT)
	@mkdir -p $(dir $@)
	cp latex-agda-output/agda.sty $@

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
	${SED} -f rules.sed $< > $@

latex/syntax.tex: syntax.tex rules.sed
	@mkdir -p $(dir $@)
	${SED} -f rules.sed $< > $@

latex/%.tex: latex-agda-output/%.tex rules.sed
	@mkdir -p $(dir $@)
	${SED} -f rules.sed $< > $@
	${SED} -f rules.sed -i $@
	${SED} -f rules.sed -i $@

latex-agda-output/%.tex: %.lagda
	@mkdir -p $(dir $@)
	${AGDA} -i . --allow-unsolved-metas --latex $< --latex-dir=latex-agda-output > $(basename $@).log

clean:
	find . -name '*.agdai' | xargs rm
	rm -rf latex
	rm -rf latex-agda-output
