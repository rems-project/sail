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
	ocamlbuild -use-ocamlfind -pkgs batteries,uint,unix,zarith src_elf/abis/power64/abi_power64.cmxa
	ocamlbuild -use-ocamlfind -pkgs batteries,uint,unix,zarith src_elf/abis/power64/abi_power64.cma
	ocamlbuild -use-ocamlfind -pkgs batteries,uint,unix,zarith src_elf/abis/aarch64/abi_aarch64_le.cmxa
	ocamlbuild -use-ocamlfind -pkgs batteries,uint,unix,zarith src_elf/abis/aarch64/abi_aarch64_le.cma

test: sail interpreter
	ocamlbuild test/run_tests.native
	./run_tests.native

LEM = ~/bitbucket/lem/lem
LEMLIBOCAML = ~/bitbucket/lem/ocaml-lib/

ELFDIR= ../../../bitbucket/linksem

get_elf:
	-chmod u+w src_elf/*.ml*
	-chmod u+w src_elf/abis/*.ml*	
	-chmod u+w src_elf/abis/amd64/*.ml*
	-chmod u+w src_elf/abis/power64/*.ml*
	-chmod u+w src_elf/abis/aarch64/*.ml*
	-chmod u+w src_elf/adaptors/*.ml*
	-chmod u+w src_elf/gnu_extensions/*.ml*
	rm -rf src_elf/*.ml*
	rm -rf src_elf/abis/*.ml*
	rm -rf src_elf/abis/amd64/*.ml*
	rm -rf src_elf/abis/power64/*.ml*
	rm -rf src_elf/abis/aarch64/*.ml*
	rm -rf src_elf/adaptors/*.ml*
	rm -rf src_elf/gnu_extensions/*.ml*
	$(MAKE) -C $(ELFDIR)/src clean
	$(MAKE) -C $(ELFDIR)/src lem-all-ocaml
	cp -a $(ELFDIR)/src/*.ml src_elf
	cp -a $(ELFDIR)/src/abis/*.ml src_elf/abis
	cp -a $(ELFDIR)/src/abis/amd64/*.ml src_elf/abis/amd64
	cp -a $(ELFDIR)/src/abis/power64/*.ml src_elf/abis/power64
	cp -a $(ELFDIR)/src/abis/aarch64/*.ml src_elf/abis/aarch64
	cp -a $(ELFDIR)/src/adaptors/*.ml src_elf/adaptors
	cp -a $(ELFDIR)/src/gnu_extensions/*.ml*
	chmod ugo-w src_elf/*.ml*
	chmod ugo-w src_elf/abis/*.ml*
	chmod ugo-w src_elf/abis/amd64/*.ml*
	chmod ugo-w src_elf/abis/power64/*.ml*
	chmod ugo-w src_elf/abis/aarch64/*.ml*
	chmod ugo-w src_elf/adaptors/*.ml*
	chmod ugo-w src_elf/gnu_extensions/*.ml*


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
