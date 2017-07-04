SED=sed
PAPER=popl18

all: finish

prepare:
	mkdir -p latex/
	cp cc-by.pdf lipics-logo-bw.pdf *.sty *.tex *.cls *.bib *.bst *.sed latex/

paper-lagda:    
	./build-lagda.sh

paper: prepare paper-lagda
	cd latex \
	&& ${SED} -f rules.sed -i ${PAPER}.tex \
	&& ${SED} -f rules.sed -i syntax.tex \
        && latexmk -bibtex -xelatex -pdf -e '$$pdflatex=q/xelatex %O %S/' $(PAPER).tex \
        && cd ..

finish: paper
	ln -sf latex/${PAPER}.pdf .
	xdotool search --class mupdf key --window %@ r > /dev/null 2>&1

clean:
	rm latex/${PAPER}.pdf

fullclean:
	rm -f *.agdai *.log *.hash *~ ${PAPER}.pdf
	rm -rf latex/
