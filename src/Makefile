.PHONY: all test clean update_lem_lib test_power

all:
	ocamlbuild -classic-display main.native test/run_tests.native

test: all
	./run_tests.native

test_power:
	#../../../rsem/idl/power/binary/run.sh
	SAIL_OPTS=-skip_constraints ocamlbuild -classic-display main.native test/run_power.native
	./run_power.native --file ../../../rsem/idl/power/binary/main.bin

clean:
	-ocamlbuild -clean
	-rm -rf _build
	-rm -rf html-doc
	-rm -rf tex-doc
	-rm -rf lem lib
