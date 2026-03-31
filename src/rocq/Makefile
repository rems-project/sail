.PHONY: build extract
.SILENT: extraction

build:
	dune build --root .

MODS := $(shell cat extract/gen/modules.txt)

extraction: build
	echo "Copying extracted source"
	rm -f ../lib/extraction/*.ml
	rm -f ../lib/extraction/*.mli
	cp $(addprefix _build/default/extract/prelude/, $(addsuffix .ml, $(MODS))) ../lib/extraction/
	cp $(addprefix _build/default/extract/prelude/, $(addsuffix .mli, $(MODS))) ../lib/extraction/

COQDOCJS := vendor/coqdocjs/extra

doc: build
	rm -rf doc && mkdir doc
	rocq doc -R _build/default/lib Sail \
		--html --utf8 \
		--interpolate \
		--parse-comments \
		--index indexpage \
		--toc --toc-depth 2 \
		--no-lib-name \
		--with-header $(COQDOCJS)/header.html \
		--with-footer $(COQDOCJS)/header.html \
		--directory doc \
		_build/default/lib/*.v \
		_build/default/lib/Domain/*.v
	cp -r $(COQDOCJS)/resources doc/resources
