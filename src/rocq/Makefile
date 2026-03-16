.PHONY: build extract

build: lib/*.v extract/*.v lib/dune extract/dune dune-project
	dune build --root .

extraction: build
	rm -f ../lib/extraction/*.ml
	rm -f ../lib/extraction/*.mli
	cp _build/default/extract/*.mli ../lib/extraction/
	cp _build/default/extract/*.ml ../lib/extraction/
