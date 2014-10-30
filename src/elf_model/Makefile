dummy: all

lem-model:
	../../lem/lem -ocaml -only_changed_output missing_pervasives.lem show.lem endianness.lem default_printing.lem bitstring.lem elf_types.lem elf_interpreted_segment.lem elf_symbol_table.lem elf_header.lem elf_file1.lem elf_program_header_table.lem elf_executable_file2.lem elf_section_header_table.lem elf_executable_file3.lem string_table.lem elf_linking_file2.lem elf_linking_file3.lem elf_relocation.lem sail_interface.lem main.lem

clean:
	rm -rf missing_pervasives.ml show.ml endianness.ml bitstring_local.ml default_printing.ml elf_types.ml elf_header.ml elf_file1.ml elf_program_header_table.ml elf_executable_file2.ml elf_section_header_table.ml elf_executable_file3.ml string_table.ml elf_interpreted_segment.ml elf_symbol_table.ml elf_executable_file5.ml elf_linking_file2.ml elf_linking_file3.ml elf_relocation.ml elf_symbol_table.ml sail_interface.ml main.ml
	make -C libraries clean
	rm -rf elf_section_header.ml elf_symbol_table.ml
	rm -rf *~
	rm -rf *.cmi *.cmo

camlp4:
	camlp4 '-I' '/home/dpm/.opam/4.01.0/lib/ocaml/camlp4' '-I' '/home/dpm/.opam/4.01.0/lib/bitstring' '-parser' 'o' '-parser' 'op' '-printer' 'p' 'unix.cma' 'bitstring.cma' 'bitstring_persistent.cma' 'pa_bitstring.cmo' pa_o.cmo pr_o.cmo -oml_bindings.ml 'ml_bindings_camlp4_sugared.ml'



ocaml:
	ocamlfind ocamlc \
-I libraries/batteries/_build/src \
-I libraries/bitstring \
-I libraries/uint/_build/lib  \
-I ../../lem/ocaml-lib/_build/ \
unix.cma nums.cma  batteries.cma uint.cma bitstring.cma nat_num.cmo \
lem.cmo lem_function.cmo lem_list.cmo \
missing_pervasives.ml \
show.ml endianness.ml error.ml ml_bindings.ml default_printing.ml bitstring_local.ml elf_types.ml elf_header.ml elf_file1.ml elf_program_header_table.ml elf_executable_file2.ml string_table.ml elf_section_header_table.ml elf_interpreted_segment.ml elf_symbol_table.ml elf_executable_file3.ml elf_linking_file2.ml elf_linking_file3.ml elf_relocation.ml sail_interface.ml main.ml \
-dllpath libraries/uint/_build/lib -dllpath libraries/bitstring -package bitstring -package uint -package batteries

ocaml_native:
	ocamlfind ocamlopt \
-I ../../../lem/ocaml-lib/_build/ \
-package bitstring -package uint -package batteries \
nums.cmxa unix.cmxa batteries.cmxa uint.cmxa bitstring.cmxa ../../../lem/ocaml-lib/_build/extract.cmxa \
missing_pervasives.ml \
show.ml endianness.ml error.ml ml_bindings.ml default_printing.ml bitstring_local.ml elf_types.ml elf_header.ml elf_file1.ml elf_program_header_table.ml elf_executable_file2.ml string_table.ml elf_section_header_table.ml elf_interpreted_segment.ml elf_symbol_table.ml elf_executable_file3.ml elf_linking_file2.ml elf_linking_file3.ml elf_relocation.ml sail_interface.ml main.ml 


ocaml_with_ocamlbuild:
	ocamlbuild -classic-display \
  -X libraries -X ocaml-obsolete \
  -cflag -g \
  -cflags -I,libraries/batteries/_build_src   \
  -cflags -I,../libraries/bitstring \
  -cflags -I,libraries/uint/_build/lib \
  -cflags -dllpath,libraries/uint/_build/lib \
  -cflags -dllpath,libraries/bitstring \
  main.byte 

ocaml_with_ocamlbuild_native:
	ocamlbuild -classic-display \
  -X libraries -X ocaml-obsolete \
  -cflag -g \
  -cflags -I,../../../../lem/ocaml-lib/_build/ \
  -cflags -I,libraries/batteries/_build_src   \
  -cflags -I,libraries/bitstring \
  -cflags -I,libraries/uint/_build/lib \
  -cflags -dllpath,libraries/uint/_build/lib \
  -cflags -dllpath,libraries/bitstring \
  main.native


clean_with_ocamlbuild:
	ocamlbuild -classic-display -clean


stacktrace:
	export OCAMLRUNPARAM=b
	ocamlfind ocamlc -package bitstring -package batteries -I ../../lem/ocaml-lib/_build/ unix.cma bitstring.cma nums.cma nat_num.cmo lem.cmo lem_function.cmo lem_list.cmo -linkpkg -g missing_pervasives.ml show.ml endianness.ml error.ml ml_bindings.ml default_printing.ml bitstring_local.ml elf_types.ml elf_header.ml elf_file1.ml elf_program_header_table.ml elf_executable_file2.ml string_table.ml elf_section_header_table.ml elf_interpreted_segment.ml elf_symbol_table.ml elf_executable_file3.ml elf_executable_file5.ml elf_linking_file2.ml elf_linking_file3.ml elf_relocation.ml sail_interface.ml main.ml

oldall: lem-model camlp4 ocaml

all: ocaml

execute:
	./a.out

go: all execute

go-debug: lem-model stacktrace execute
