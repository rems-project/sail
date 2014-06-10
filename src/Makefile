.PHONY: all sail test clean doc lib power test_power test_idempotence

all: sail lib power doc test

sail:
	ocamlbuild sail.native

test: sail
	ocamlbuild test/run_tests.native
	./run_tests.native

power: sail
	ocamlbuild test/run_power.native

test_power: power
	#../../../rsem/idl/power/binary/run.sh
	./run_power.native --file ../../../rsem/idl/power/binary/main.bin

test_idempotence: sail
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
