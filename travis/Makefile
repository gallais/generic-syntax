AGDA=agda

AGDA_FILES:=$(shell find . -name "*.agda" -type f | sed 's|\./||g' | sort)
AGDA_OUTPUT:=$(patsubst %.agda,%.agdai,$(AGDA_FILES))

all: $(AGDA_OUTPUT)

%.agdai: %.agda
	${AGDA} -i . $< > $(basename $@).log

clean:
	find . -name '*.agdai' | xargs rm
	find . -name '*.log'   | xargs rm
