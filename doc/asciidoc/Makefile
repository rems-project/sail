SAIL_PLUGIN ?= asciidoctor-sail

SAIL_DOCS = sail_doc/riscv_duopod.json
SAIL_DOCS += sail_doc/pattern_matching.json
SAIL_DOCS += sail_doc/my_replicate_bits.json
SAIL_DOCS += sail_doc/exn.json

CUSTOM_SAIL_DOCS = custom_sail_doc/cannot_wildcard.json

default: manual.pdf

sail_doc/%.json: ../examples/%.sail
	sail -doc $< -doc_file $< -doc_embed plain -doc_bundle $(notdir $@)

custom_sail_doc/cannot_wildcard.json: ../examples/cannot_wildcard.sail
	mkdir -p custom_sail_doc
	sail -no_color -doc $< -doc_file $< -doc_embed plain -doc_bundle $(notdir $@) -o custom_sail_doc 2> custom_sail_doc/cannot_wildcard_warning

manual.pdf: *.adoc $(SAIL_DOCS) $(CUSTOM_SAIL_DOCS)
	asciidoctor-pdf manual.adoc -r $(SAIL_PLUGIN) -r asciidoctor-bibtex

manual.html: *.adoc $(SAIL_DOCS) $(CUSTOM_SAIL_DOCS)
	asciidoctor manual.adoc -r $(SAIL_PLUGIN) -r asciidoctor-bibtex

clean:
	-rm manual.pdf
	-rm manual.html
