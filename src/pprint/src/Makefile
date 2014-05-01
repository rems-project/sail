.PHONY: all install clean doc test

OCAMLBUILD := ocamlbuild -use-ocamlfind -cflags "-g" -lflags "-g" -classic-display
OCAMLFIND  := ocamlfind
DOCDIR     := doc
MAIN       := PPrintTest
TO_BUILD   := PPrintLib.cma PPrintLib.cmxa

all:
	$(OCAMLBUILD) $(TO_BUILD)

install: all
	$(OCAMLFIND) install pprint META \
		$(patsubst %,_build/%,$(TO_BUILD)) \
		_build/PPrintLib.a _build/*.cmx _build/*.cmi

clean:
	rm -f *~
	rm -rf doc
	$(OCAMLBUILD) -clean

doc: all
	@rm -rf $(DOCDIR)
	@mkdir $(DOCDIR)
	ocamlfind ocamldoc \
	  -html \
	  -I _build \
	  -d $(DOCDIR) \
	  -charset utf8 \
	  PPrintRenderer.ml PPrintEngine.mli PPrintCombinators.mli PPrintOCaml.mli PPrint.ml

test: all
	$(OCAMLBUILD) $(MAIN).native
	./$(MAIN).native

