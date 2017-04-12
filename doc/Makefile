STDLIB=~/languages/agda/libs/agda-stdlib-dev/src/
SED=sed
PAPER=fscd17

all: finish

prepare:
	mkdir -p latex/
	cp cc-by.pdf lipics-logo-bw.pdf *.sty *.tex *.cls *.bib *.bst *.sed latex/

paper-lagda:    
	./lagda2tex indexed.lagda
	./lagda2tex var.lagda
	./lagda2tex motivation.lagda
	./lagda2tex environment.lagda
	./lagda2tex generic-data.lagda
	./lagda2tex generic-syntax.lagda
	./lagda2tex generic-cofinite.lagda
	./lagda2tex generic-simulation.lagda
	./lagda2tex generic-bisimilar.lagda

paper: prepare paper-lagda
	cd latex \
	&& ${SED} -f rules.sed -i ${PAPER}.tex \
	&& ${SED} -f rules.sed -i syntax.tex \
	&& ${SED} -f rules.sed -i indexed.tex \
	&& ${SED} -f rules.sed -i motivation.tex \
        && ${SED} -f rules.sed -i environment.tex \
        && ${SED} -f rules.sed -i generic-data.tex \
        && ${SED} -f rules.sed -i generic-syntax.tex \
        && ${SED} -f rules.sed -i generic-cofinite.tex \
        && ${SED} -f rules.sed -i generic-simulation.tex \
        && ${SED} -f rules.sed -i generic-bisimilar.tex \
        && \
	latexmk -bibtex -xelatex -pdf -e '$$pdflatex=q/xelatex %O %S/' $(PAPER).tex && cd ..

finish: paper
	ln -sf latex/${PAPER}.pdf .
	xdotool search --class mupdf key --window %@ r > /dev/null 2>&1

clean:
	rm latex/${PAPER}.pdf

fullclean:
	rm -f *.agdai
	rm -rf latex/
