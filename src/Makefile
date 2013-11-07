.PHONY: all test clean update_lem_lib

all:
	ocamlbuild -classic-display main.native test/run_tests.native

test: all
	./run_tests.native

update_lem_lib:
	mkdir -p lem_lib
	../../lem/lem -ocaml -only_changed_output -outdir lem_lib ../../lem/library-new/*.lem
	rm -f lem_lib/basic_classes.ml

clean:
	-ocamlbuild -clean
	-rm -rf _build
	-rm -rf html-doc
	-rm -rf tex-doc
	-rm -rf lem lib
