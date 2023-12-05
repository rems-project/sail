
FIGURES = ordering-tikz.png

default: manual.html

.PHONY: asciidoc

asciidoc:
	$(MAKE) SAIL_LOGO_PATH=../etc/logo/sail_logo_square.png -C asciidoc manual.html

%.png: asciidoc/%.png asciidoc
	mkdir -p built
	cp $< $@

manual.html: $(FIGURES) asciidoc
	cp asciidoc/manual.html $@
