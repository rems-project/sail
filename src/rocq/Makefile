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
