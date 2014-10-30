.PHONY: all sail test clean doc lib power test_power test_idempotence

all: sail lib doc

full: sail lib power doc test

sail:
	ocamlbuild sail.native sail_lib.cma sail_lib.cmxa

interpreter: 
	ocamlbuild lem_interp/extract.cmxa
	ocamlbuild lem_interp/extract.cma

test: sail interpreter
	ocamlbuild test/run_tests.native
	./run_tests.native

LEM = ~/bitbucket/lem/lem
LEMLIB = ~/bitbucket/lem/ocaml-lib/_build/

install_elf:
	cp -p ../../system-v-abi/src/*.lem elf_model/
	cp -p ../../system-v-abi/src/*.ml elf_model/
	cp -p -r ../../system-v-abi/src/libraries elf_model/libraries

elf:
	$(MAKE) -C elf_model ocaml_native
	mkdir -p _build/elf_model
	cp -p elf_model/*.cmi _build/elf_model/
	cp -p elf_model/*.cmx _build/elf_model/
	cp -p elf_model/*.o _build/elf_model/
	cd _build/elf_model ;\
	ocamlfind ocamlopt -package batteries -package uint -package bitstring -I $(LEMLIB) -a -o elf_extract.cmxa missing_pervasives.cmx \
show.cmx endianness.cmx error.cmx ml_bindings.cmx default_printing.cmx bitstring_local.cmx elf_types.cmx elf_header.cmx elf_file1.cmx elf_program_header_table.cmx elf_executable_file2.cmx string_table.cmx elf_section_header_table.cmx elf_interpreted_segment.cmx elf_symbol_table.cmx elf_executable_file3.cmx elf_linking_file2.cmx elf_linking_file3.cmx elf_relocation.cmx sail_interface.cmx


power: sail interpreter elf
	mkdir -p _build/test
	cp -p test/* _build/test/
	cd _build/test ;\
	../../sail.native -lem_ast power.sail ;\
	$(LEM) -ocaml -only_changed_output -lib ../lem_interp/ power.lem;\
	env OCAMLRUNPARAM=l=100M ocamlfind ocamlopt -package num -package bitstring -package batteries -package uint -I $(LEMLIB) -I ../lem_interp/ -I ../elf_model/ -linkpkg $(LEMLIB)extract.cmxa ../pprint/src/PPrintLib.cmxa ../lem_interp/extract.cmxa elf_extract.cmxa power.ml run_power.ml -o run_power.native
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
