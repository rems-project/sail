dummy: all

lem-model:
	../../lem/lem -ocaml -only_changed_output missing_pervasives.lem show.lem endianness.lem bitstring.lem elf_types.lem elf_interpreted_segment.lem elf_header.lem elf_file1.lem elf_program_header_table.lem elf_executable_file2.lem elf_section_header_table.lem elf_executable_file3.lem string_table.lem elf_executable_file4.lem elf_executable_file5.lem sail_interface.lem main.lem

clean:
	rm missing_pervasives.ml show.ml endianness.ml bitstring_local.ml elf_types.ml elf_header.ml elf_file1.ml elf_program_header_table.ml elf_executable_file2.ml elf_section_header_table.ml elf_executable_file3.ml string_table.ml elf_executable_file4.ml elf_interpreted_segment.ml elf_executable_file5.ml sail_interface.ml main.ml

ocaml:
	ocamlfind ocamlc -package bitstring.syntax -package batteries -package uint -syntax camlp4o -I ../../lem/ocaml-lib/_build/ unix.cma bitstring.cma nums.cma nat_num.cmo lem.cmo lem_function.cmo lem_list.cmo -linkpkg missing_pervasives.ml show.ml endianness.ml error.ml ml_bindings.ml bitstring_local.ml elf_types.ml elf_header.ml elf_file1.ml elf_program_header_table.ml elf_executable_file2.ml string_table.ml elf_section_header_table.ml elf_executable_file3.ml elf_executable_file4.ml elf_interpreted_segment.ml elf_executable_file5.ml sail_interface.ml main.ml

stacktrace:
	export OCAMLRUNPARAM=b
	ocamlfind ocamlc -package bitstring.syntax -package batteries -syntax camlp4o -I ../../lem/ocaml-lib/_build/ unix.cma bitstring.cma nums.cma nat_num.cmo lem.cmo lem_function.cmo lem_list.cmo -linkpkg -g missing_pervasives.ml show.ml endianness.ml error.ml ml_bindings.ml bitstring_local.ml elf_types.ml elf_header.ml elf_file1.ml elf_program_header_table.ml elf_executable_file2.ml string_table.ml elf_section_header_table.ml elf_executable_file3.ml elf_executable_file4.ml elf_interpreted_segment.ml elf_executable_file5.ml sail_interface.ml main.ml

all: lem-model ocaml

execute:
	./a.out

go: all execute

go-debug: lem-model stacktrace execute
	
