.PHONY: all test clean update_lem_lib

all:
	ocamlbuild -classic-display main.native test/run_tests.native

test: all
	./run_tests.native

clean:
	-ocamlbuild -clean
	-rm -rf _build
	-rm -rf html-doc
	-rm -rf tex-doc
	-rm -rf lem lib
