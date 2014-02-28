.PHONY: all test clean update_lem_lib power_test

all:
	ocamlbuild -classic-display main.native test/run_tests.native test/run_power.native

test: all
	./run_tests.native

test_power: all
	#../../../rsem/idl/power/binary/run.sh
	./run_power.native --file ../../../rsem/idl/power/binary/main.bin

clean:
	-ocamlbuild -clean
	-rm -rf _build
	-rm -rf html-doc
	-rm -rf tex-doc
	-rm -rf lem lib
