.PHONY: all sail test clean doc lib power test_power test_idempotence

all: sail lib doc

full: sail lib power doc test

sail:
	ocamlbuild sail.native sail_lib.cma sail_lib.cmxa

sail.native: sail

interpreter: 
	ocamlbuild lem_interp/extract.cmxa
	ocamlbuild lem_interp/extract.cma

test: sail interpreter
	ocamlbuild test/run_tests.native
	./run_tests.native

THIS_MAKEFILE := $(realpath $(lastword $(MAKEFILE_LIST)))
BITBUCKET_ROOT=$(realpath $(dir $(THIS_MAKEFILE))../..)

LEM = $(BITBUCKET_ROOT)/lem/lem
LEMLIBOCAML = $(BITBUCKET_ROOT)/lem/ocaml-lib
ELFDIR= $(BITBUCKET_ROOT)/linksem

MIPS_SAIL_DIR:=$(BITBUCKET_ROOT)/l2/mips
MIPS_SAILS:=$(MIPS_SAIL_DIR)/mips_prelude.sail $(MIPS_SAIL_DIR)/mips_insts.sail $(MIPS_SAIL_DIR)/mips_epilogue.sail
CHERI_SAIL_DIR:=$(BITBUCKET_ROOT)/l2/cheri
CHERI_SAILS:=$(MIPS_SAIL_DIR)/mips_prelude.sail $(CHERI_SAIL_DIR)/cheri_prelude.sail $(MIPS_SAIL_DIR)/mips_insts.sail $(CHERI_SAIL_DIR)/cheri_insts.sail $(MIPS_SAIL_DIR)/mips_epilogue.sail

elf:
	make -C $(ELFDIR)

_build/mips_extras.lem: ../mips/mips_extras.lem
	mkdir -p _build
	cp $< $@

_build/run_with_elf.ml: lem_interp/run_with_elf.ml
	mkdir -p _build
	cp $< $@
_build/run_with_elf_cheri.ml: lem_interp/run_with_elf_cheri.ml
	mkdir -p _build
	cp $< $@

_build/mips.lem: $(MIPS_SAILS) ./sail.native
	mkdir -p _build
	cd _build ;\
	../sail.native -lem_ast -o mips $(MIPS_SAILS)

_build/cheri.lem: $(CHERI_SAILS) ./sail.native
	mkdir -p _build
	cd _build ;\
	../sail.native -lem_ast -o cheri $(CHERI_SAILS)

%.ml: %.lem
	$(LEM) -only_changed_output -ocaml -lib lem_interp/ $<

run_mips.native: _build/mips.ml _build/mips_extras.ml _build/run_with_elf.ml interpreter
	env OCAMLRUNPARAM=l=100M ocamlfind ocamlopt -g -package num -package str -package unix -I $(ELFDIR)/contrib/ocaml-uint/_build/lib -I $(LEMLIBOCAML) -I $(LEMLIBOCAML)/dependencies/zarith -I _build/lem_interp/ -I $(ELFDIR)/src  -I $(ELFDIR)/src/adaptors -I $(ELFDIR)/src/abis/mips64 -I _build -linkpkg $(LEMLIBOCAML)/dependencies/zarith/zarith.cmxa $(LEMLIBOCAML)/extract.cmxa $(ELFDIR)/contrib/ocaml-uint/_build/lib/uint.cmxa $(ELFDIR)/src/linksem.cmxa  _build/pprint/src/PPrintLib.cmxa _build/lem_interp/extract.cmxa _build/mips.ml _build/mips_extras.ml _build/run_with_elf.ml  -o run_mips.native

run_cheri.native:  _build/cheri.ml _build/mips_extras.ml _build/run_with_elf_cheri.ml interpreter
	env OCAMLRUNPARAM=l=100M ocamlfind ocamlopt -g -package num -package str -package unix -I $(ELFDIR)/contrib/ocaml-uint/_build/lib -I $(LEMLIBOCAML) -I $(LEMLIBOCAML)/dependencies/zarith -I _build/lem_interp/ -I $(ELFDIR)/src  -I $(ELFDIR)/src/adaptors -I $(ELFDIR)/src/abis/mips64 -I _build -linkpkg $(LEMLIBOCAML)/dependencies/zarith/zarith.cmxa $(LEMLIBOCAML)/extract.cmxa $(ELFDIR)/contrib/ocaml-uint/_build/lib/uint.cmxa $(ELFDIR)/src/linksem.cmxa  _build/pprint/src/PPrintLib.cmxa _build/lem_interp/extract.cmxa _build/cheri.ml _build/mips_extras.ml _build/run_with_elf_cheri.ml  -o run_cheri.native

mips: elf run_mips.native

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
