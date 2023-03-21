
SAIL_PLUGIN ?= ../../../sail-asciidoc/sail.rb

SAIL_DOCS = sail_doc/riscv_duopod.json

default: manual.pdf

sail_doc/%.json: ../examples/%.sail
	sail -doc $< -doc_file $< -doc_embed plain -doc_bundle $(notdir $@)

manual.pdf: *.adoc $(SAIL_DOCS)
	asciidoctor-pdf manual.adoc -r $(SAIL_PLUGIN) -r asciidoctor-bibtex

manual.html: *.adoc $(SAIL_DOCS)
	asciidoctor manual.adoc -r $(SAIL_PLUGIN) -r asciidoctor-bibtex

clean:
	-rm manual.pdf
	-rm manual.html
