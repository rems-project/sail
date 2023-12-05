SAIL_LOGO_PATH ?= ../../etc/logo/sail_logo_square.png

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
SAIL_DOCS += sail_doc/function_pat.json
SAIL_DOCS += sail_doc/let_var.json
SAIL_DOCS += sail_doc/list.json
SAIL_DOCS += module_sail_doc/simple_mod.json
SAIL_DOCS += module_sail_doc/simple_mod_err.error
SAIL_DOCS += module_sail_doc/cond.sail_project
SAIL_DOCS += sail_doc/cannot_wildcard.json
SAIL_DOCS += lib_sail_doc/concurrency_interface/read_write.json

TIKZ_FIGURES = ordering-tikz.png

INCS = module_sail_doc/simple_mod.sail_project

all: manual.html manual.pdf

sail_doc/%.json: ../examples/%.sail
	mkdir -p sail_doc
	sail -no_color -doc -doc_file $< -doc_embed plain -doc_bundle $(notdir $@) $< 2> $(basename $@).warning

lib_sail_doc/%.json: ../../lib/%.sail
	mkdir -p lib_sail_doc
	mkdir -p lib_sail_doc/concurrency_interface
	sail -doc -doc_file $< -doc_embed plain -doc_bundle $(patsubst lib_sail_doc/%,%,$@) -o lib_sail_doc $<

.SECONDEXPANSION:

module_sail_doc/%.json: ../examples/%.sail_project $$(shell sail ../examples/%.sail_project -list_files)
	mkdir -p module_sail_doc
	sail -doc $(addprefix -doc_file ,$(shell sail $< -list_files)) -doc_embed plain -doc_bundle $(notdir $@) -o module_sail_doc $<

module_sail_doc/%.error: ../examples/%.sail_project $$(shell sail ../examples/%.sail_project -list_files)
	mkdir -p module_sail_doc
	-sail -no_color $< 2> $@

module_sail_doc/%.sail_project: ../examples/%.sail_project
	mkdir -p module_sail_doc
	sail $< -list_files 1>/dev/null
	cp $< $@

ordering-tikz.pdf: latex_figures/ordering.tex
	pdflatex --jobname=ordering-tikz $<

sail_logo_square.png: ../../etc/logo/sail_logo_square.png
	cp $< $@

%.png: %.pdf
	pdftoppm -r 300 -png $< > $@

parser.txt: ../../src/lib/parser.mly parser.sed
	obelisk -i $< | tr '\n' '+' | sed 's/+[ ][ ]*\([^| ]\)/ \1/g' | tr '+' '\n' > $@
	sed -i.bak -f parser.sed $@

manual.pdf: *.adoc $(SAIL_DOCS) $(INCS) $(TIKZ_FIGURES) manual.bib parser.txt
	asciidoctor-pdf manual.adoc -r $(SAIL_PLUGIN) -r asciidoctor-bibtex

docinfo.html: docinfo.template
	sed 's/SAIL_LOGO_PATH/$(shell echo $(SAIL_LOGO_PATH) | sed 's/\//\\\//g')/' $< > $@

manual.html: *.adoc $(SAIL_DOCS) $(INCS) $(TIKZ_FIGURES) manual.bib parser.txt manual.css docinfo.html
	asciidoctor manual.adoc -r $(SAIL_PLUGIN) -r asciidoctor-bibtex

.PHONY: clean
clean:
	-rm -rf sail_doc/
	-rm -rf lib_sail_doc/
	-rm -rf module_sail_doc/
	-rm *.pdf
	-rm *.png
	-rm *.log
	-rm *.aux
	-rm parser.txt
	-rm docinfo.html
	-rm manual.html
