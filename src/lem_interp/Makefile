.PHONY: all clean

LEMDIR=$(abspath ../../../lem)
OCAMLPATH:=$(LEMDIR)/ocaml-lib:$(OCAMLPATH)

all: interp.native

ast.ml interp.ml: ast.lem interp.lem
	$(LEMDIR)/lem -ocaml $^

interp.native: ast.ml interp.ml
	OCAMLPATH=$(OCAMLPATH) ocamlbuild -use-ocamlfind -pkg lem interp.native

clean:
	-ocamlbuild -clean
	-rm -rf _build *.ml
