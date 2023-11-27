SAIL_PLUGIN ?= asciidoctor-sail

SAIL_DOCS = sail_doc/riscv_duopod.json
SAIL_DOCS += sail_doc/pattern_matching.json
SAIL_DOCS += sail_doc/my_replicate_bits.json
SAIL_DOCS += sail_doc/bitfield.json
SAIL_DOCS += sail_doc/exn.json
SAIL_DOCS += sail_doc/mapping.json
SAIL_DOCS += sail_doc/scattered.json
SAIL_DOCS += sail_doc/tuples.json
SAIL_DOCS += sail_doc/string.json
SAIL_DOCS += module_sail_doc/simple_mod.json
SAIL_DOCS += module_sail_doc/simple_mod_err.error
SAIL_DOCS += module_sail_doc/cond.rigging
SAIL_DOCS += custom_sail_doc/cannot_wildcard.json
SAIL_DOCS += lib_sail_doc/concurrency_interface/read_write.json

TIKZ_FIGURES = ordering-tikz.png

EXTRAS = ../examples/simple_mod.rigging

default: manual.pdf

sail_doc/%.json: ../examples/%.sail
	mkdir -p sail_doc
	sail -doc -doc_file $< -doc_embed plain -doc_bundle $(notdir $@) $<

lib_sail_doc/%.json: ../../lib/%.sail
	mkdir -p lib_sail_doc
	mkdir -p lib_sail_doc/concurrency_interface
	sail -doc -doc_file $< -doc_embed plain -doc_bundle $(patsubst lib_sail_doc/%,%,$@) -o lib_sail_doc $<

.SECONDEXPANSION:

module_sail_doc/%.json: ../examples/%.rigging $$(shell sail ../examples/%.rigging -list_files)
	mkdir -p module_sail_doc
	sail -doc $(addprefix -doc_file ,$(shell sail $< -list_files)) -doc_embed plain -doc_bundle $(notdir $@) -o module_sail_doc $<

module_sail_doc/%.error: ../examples/%.rigging $$(shell sail ../examples/%.rigging -list_files)
	mkdir -p module_sail_doc
	-sail -no_color $< 2> $@

module_sail_doc/%.rigging: ../examples/%.rigging
	mkdir -p module_sail_doc
	sail $< -list_files
	cp $< $@

custom_sail_doc/cannot_wildcard.json: ../examples/cannot_wildcard.sail
	mkdir -p custom_sail_doc
	sail -no_color -doc -doc_file $< -doc_embed plain -doc_bundle $(notdir $@) -o custom_sail_doc 2> custom_sail_doc/cannot_wildcard_warning $<

ordering-tikz.pdf: latex/ordering.tex
	pdflatex --jobname=ordering-tikz $<

%.png: %.pdf
	pdftoppm -r 300 -png $< > $@

parser.txt: ../../src/lib/parser.mly parser.sed
	obelisk -i $< | tr '\n' '+' | sed 's/+[ ][ ]*\([^| ]\)/ \1/g' | tr '+' '\n' > $@
	sed -i.bak -f parser.sed $@

manual.pdf: *.adoc $(SAIL_DOCS) $(EXTRAS) $(TIKZ_FIGURES) parser.txt
	asciidoctor-pdf manual.adoc -r $(SAIL_PLUGIN) -r asciidoctor-bibtex

manual.html: *.adoc $(SAIL_DOCS) $(EXTRAS) $(TIKZ_FIGURES) parser.txt manual.css
	asciidoctor manual.adoc -r $(SAIL_PLUGIN) -r asciidoctor-bibtex

.PHONY: clean
clean:
	-rm *.pdf
	-rm *.png
	-rm *.log
	-rm *.aux
	-rm parser.txt
	-rm manual.html
