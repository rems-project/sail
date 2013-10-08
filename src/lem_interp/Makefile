.PHONY: all clean

LEMDIR=$(abspath ../../../lem)
OCAMLPATH:=$(LEMDIR)/ocaml-lib:$(OCAMLPATH)

all: interp.native

.PHONY: interp.native
interp.native:
	OCAMLPATH=$(OCAMLPATH) ocamlbuild -use-ocamlfind -pkg lem interp.native

clean:
	-ocamlbuild -clean
	-rm -rf _build
