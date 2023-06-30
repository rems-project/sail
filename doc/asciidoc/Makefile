SAIL_PLUGIN ?= asciidoctor-sail

SAIL_DOCS = sail_doc/riscv_duopod.json
SAIL_DOCS += sail_doc/pattern_matching.json
SAIL_DOCS += sail_doc/my_replicate_bits.json
SAIL_DOCS += sail_doc/exn.json

CUSTOM_SAIL_DOCS = custom_sail_doc/cannot_wildcard.json

LIB_SAIL_DOCS = lib_sail_doc/concurrency_interface/read_write.json

default: manual.pdf

sail_doc/%.json: ../examples/%.sail
	mkdir -p sail_doc
	sail -doc $< -doc_file $< -doc_embed plain -doc_bundle $(notdir $@)

lib_sail_doc/%.json: ../../lib/%.sail
	mkdir -p lib_sail_doc
	mkdir -p lib_sail_doc/concurrency_interface
	sail -doc $< -doc_file $< -doc_embed plain -doc_bundle $(patsubst lib_sail_doc/%,%,$@) -o lib_sail_doc

custom_sail_doc/cannot_wildcard.json: ../examples/cannot_wildcard.sail
	mkdir -p custom_sail_doc
	sail -no_color -doc $< -doc_file $< -doc_embed plain -doc_bundle $(notdir $@) -o custom_sail_doc 2> custom_sail_doc/cannot_wildcard_warning

manual.pdf: *.adoc $(SAIL_DOCS) $(LIB_SAIL_DOCS) $(CUSTOM_SAIL_DOCS)
	asciidoctor-pdf manual.adoc -r $(SAIL_PLUGIN) -r asciidoctor-bibtex

manual.html: *.adoc $(SAIL_DOCS) $(LIB_SAIL_DOCS) $(CUSTOM_SAIL_DOCS)
	asciidoctor manual.adoc -r $(SAIL_PLUGIN) -r asciidoctor-bibtex

clean:
	-rm manual.pdf
	-rm manual.html
