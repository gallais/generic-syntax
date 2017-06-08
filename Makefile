TARGETS=`git ls-tree -r --name-only HEAD doc/*.lagda | basename -s .lagda`

.PHONY: src

src:
	mkdir -p src/
	./tools/build-src.sh

clean:
	./tools/clean-src.sh
	rm -f lit2raw tools/*.o tools/*.hi
