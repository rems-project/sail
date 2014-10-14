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

power: sail interpreter
	mkdir -p _build/test
	mkdir -p _build/elf_model
	cp -p test/* _build/test/
	cp -p elf_model/* _build/elf_model
	cd _build/elf_model ;\
	$(LEM) -ocaml -only_changed_output missing_pervasives.lem show.lem endianness.lem bitstring.lem elf_types.lem elf_interpreted_segment.lem elf_header.lem elf_file1.lem elf_program_header_table.lem elf_executable_file2.lem elf_section_header_table.lem elf_executable_file3.lem string_table.lem elf_executable_file4.lem elf_executable_file5.lem sail_interface.lem main.lem ;\
	ocamlfind ocamlopt -package bitstring.syntax -package batteries -package uint -package bitstring -syntax camlp4o -I $(LEMLIB) nat_num.cmx lem.cmx lem_function.cmx lem_list.cmx -linkpkg missing_pervasives.ml show.ml endianness.ml error.ml ml_bindings.ml bitstring_local.ml elf_types.ml elf_header.ml elf_file1.ml elf_program_header_table.ml elf_executable_file2.ml string_table.ml elf_section_header_table.ml elf_executable_file3.ml elf_executable_file4.ml elf_interpreted_segment.ml elf_executable_file5.ml sail_interface.ml main.ml ;\
	ocamlfind ocamlopt -package batteries -package uint -package bitstring -I $(LEMLIB) -a -o elf_extract.cmxa missing_pervasives.cmx show.cmx endianness.cmx error.cmx ml_bindings.cmx bitstring_local.cmx elf_types.cmx elf_header.cmx elf_file1.cmx elf_program_header_table.cmx elf_executable_file2.cmx string_table.cmx elf_section_header_table.cmx elf_executable_file3.cmx elf_executable_file4.cmx elf_interpreted_segment.cmx elf_executable_file5.cmx sail_interface.cmx
	cd _build/test ;\
	../../sail.native -lem_ast power.sail ;\
	$(LEM) -ocaml -only_changed_output -lib ../lem_interp/ power.lem;\
	env OCAMLRUNPARAM=l=10M ocamlfind ocamlopt -package num -package bitstring -package batteries -package uint -I $(LEMLIB) -I ../lem_interp/ -I ../elf_model/ -linkpkg $(LEMLIB)extract.cmxa ../pprint/src/PPrintLib.cmxa ../lem_interp/extract.cmxa elf_extract.cmxa power.ml run_power.ml -o run_power.native
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
