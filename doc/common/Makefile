AGDA ?= agda-2.6.1.3 +RTS -M2G -H2G -A128M -RTS

AGDA_FILES:=$(shell find . -name "*.lagda" -type f | sed 's|\./||g' | sort)
AGDA_OUTPUT:=$(patsubst %.lagda,latex/%.tex,$(AGDA_FILES))

all: $(AGDA_OUTPUT)

latex/%.tex: %.lagda
	@mkdir -p $(dir $@)
	${AGDA} -i . --latex $< --latex-dir=latex > $(basename $@).log

clean:
	find . -name '*.agdai' | xargs rm
	rm -rf latex
