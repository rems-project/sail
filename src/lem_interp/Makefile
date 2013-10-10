.PHONY: all clean

LEMDIR=$(abspath ../../../lem)
OCAMLPATH:=$(LEMDIR)/ocaml-lib:$(OCAMLPATH)

all: interp.cma interp.cmxa

interp_ast.ml interp.ml: interp_ast.lem interp.lem
	$(LEMDIR)/lem -ocaml $^

interp.cma interp.cmxa: interp_ast.ml interp.ml
	OCAMLPATH=$(OCAMLPATH) ocamlbuild -use-ocamlfind -pkg lem $@

clean:
	-ocamlbuild -clean
	-rm -rf _build *.ml
