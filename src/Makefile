.PHONY: all test clean doc lib test_power test_idempotence

all: lib doc
	ocamlbuild -classic-display sail.native test/run_tests.native

test: all
	./run_tests.native

test_power:
	#../../../rsem/idl/power/binary/run.sh
	ocamlbuild -classic-display sail.native test/run_power.native
	./run_power.native --file ../../../rsem/idl/power/binary/main.bin

test_idempotence:
	@cd test; for file in *.sail; do \
		./idempotence.sh $$file; echo ;\
	done

clean:
	-ocamlbuild -clean
	-rm -rf _build
	-rm -rf html-doc
	-rm -rf tex-doc
	-rm -rf lem lib
	-rm -rf sail.docdir

doc:
	ocamlbuild sail.docdir/index.html

lib:
	ocamlbuild pretty_print.cmxa pretty_print.cma
