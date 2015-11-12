.PHONY: all sail test clean doc lib power test_power test_idempotence

all: sail lib doc

full: sail lib power doc test

sail:
	ocamlbuild sail.native sail_lib.cma sail_lib.cmxa

interpreter: 
	ocamlbuild lem_interp/extract.cmxa
	ocamlbuild lem_interp/extract.cma

elf:
	ocamlbuild -use-ocamlfind -pkgs batteries,uint,unix,zarith src_elf/main_elf.native

test: sail interpreter
	ocamlbuild test/run_tests.native
	./run_tests.native

LEM = ~/bitbucket/lem/lem
LEMLIBOCAML = ~/bitbucket/lem/ocaml-lib/

install_elf:
	cp -p ../../system-v-abi/src/*.lem elf_model/
	cp -p ../../system-v-abi/src/*.ml elf_model/
	cp -p -r ../../system-v-abi/src/libraries elf_model/libraries


power: sail interpreter elf
	mkdir -p _build/test
	cp -p test/* _build/test/
	cd _build/test ;\
	../../sail.native -lem_ast power.sail ;\
	$(LEM) -ocaml -only_changed_output -lib ../lem_interp/ power.lem;\
	env OCAMLRUNPARAM=l=100M ocamlfind ocamlopt -package num -package bitstring -package batteries -package uint -I $(LEMLIBOCAML) -I ../lem_interp/ -I ../elf_model/ -linkpkg $(LEMLIBOCAML)extract.cmxa ../pprint/src/PPrintLib.cmxa ../lem_interp/extract.cmxa elf_extract.cmxa power.ml run_power.ml -o run_power.native
	ln -fs _build/test/run_power.native run_power.native

test_power: power
	./run_power.native --file ../../../rsem/idl/power/binary/main.bin

test_power_interactive: power
	./run_power.native --interactive --file ../../../rsem/idl/power/binary/main.bin

test_power_interactive_srcs:
	ebig ~/rsem/idl/power/generated/power.sail ../../../rsem/idl/power/binary/hello.c  ../../../rsem/idl/power/binary/hello.s 

# or test/power.sail for cut-down one


test_idempotence: sail
	@cd test; for file in *.sail; do \
		./idempotence.sh $$file; echo ;\
	done

clean:
	-ocamlbuild -clean
	-rm -rf _build *.native
	-rm -rf html-doc
	-rm -rf tex-doc
	-rm -rf lem lib
	-rm -rf sail.docdir

doc:
	ocamlbuild sail.docdir/index.html

lib:
	ocamlbuild pretty_print.cmxa pretty_print.cma
