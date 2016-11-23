.PHONY: all sail test clean doc lib power test_power test_idempotence

all: sail lib doc

full: sail lib power doc test

sail:
	ocamlbuild sail.native sail_lib.cma sail_lib.cmxa

sail.native: sail

sail.byte: 
	ocamlbuild -cflag -g sail.byte

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

MIPS_SAIL_DIR:=$(BITBUCKET_ROOT)/sail/mips

MIPS_SAILS_PRE:=$(MIPS_SAIL_DIR)/mips_prelude.sail $(MIPS_SAIL_DIR)/mips_tlb.sail $(MIPS_SAIL_DIR)/mips_wrappers.sail $(MIPS_SAIL_DIR)/mips_insts.sail $(MIPS_SAIL_DIR)/mips_ri.sail $(MIPS_SAIL_DIR)/mips_epilogue.sail

MIPS_SAILS:=$(MIPS_SAILS_PRE) $(BITBUCKET_ROOT)/sail/etc/regfp.sail $(MIPS_SAIL_DIR)/mips_regfp.sail

MIPS_NOTLB_SAILS_PRE:=$(MIPS_SAIL_DIR)/mips_prelude.sail $(MIPS_SAIL_DIR)/mips_tlb_stub.sail $(MIPS_SAIL_DIR)/mips_wrappers.sail $(MIPS_SAIL_DIR)/mips_insts.sail $(MIPS_SAIL_DIR)/mips_epilogue.sail

MIPS_NOTLB_SAILS:=$(MIPS_NOTLB_SAILS_PRE) $(BITBUCKET_ROOT)/sail/etc/regfp.sail $(MIPS_SAIL_DIR)/mips_regfp.sail

CHERI_SAIL_DIR:=$(BITBUCKET_ROOT)/sail/cheri

CHERI_SAILS:=$(MIPS_SAIL_DIR)/mips_prelude.sail $(MIPS_SAIL_DIR)/mips_tlb.sail $(CHERI_SAIL_DIR)/cheri_prelude.sail $(MIPS_SAIL_DIR)/mips_insts.sail $(CHERI_SAIL_DIR)/cheri_insts.sail $(MIPS_SAIL_DIR)/mips_ri.sail $(MIPS_SAIL_DIR)/mips_epilogue.sail

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

_build/mips_embedded.lem: $(MIPS_SAILS) ./sail.native
	mkdir -p _build
	cd _build ;\
	../sail.native -lem_lib "Mips_extras_embed" -lem -o mips $(MIPS_NOTLB_SAILS)

_build/mips_sequential_embedded.lem: $(MIPS_SAILS) ./sail.native
	mkdir -p _build
	cd _build ;\
	../sail.native -lem_lib "Mips_extras_sequential_embed" -lem_sequential -o mips $(MIPS_NOTLB_SAILS)

_build/mips_notlb.lem: $(MIPS_NOTLB_SAILS) ./sail.native
	mkdir -p _build
	cd _build ; \
	../sail.native -lem_ast -o mips_notlb $(MIPS_NOTLB_SAILS)

_build/cheri.lem: $(CHERI_SAILS) ./sail.native
	mkdir -p _build
	cd _build ;\
	../sail.native -lem_ast -o cheri $(CHERI_SAILS)

_build/mips_all.sail: $(MIPS_SAILS)
	cat $(MIPS_SAILS) > $@

_build/cheri_all.sail: $(CHERI_SAILS)
	cat $(CHERI_SAILS) > $@

_build/%_trimmed.sail: _build/%_all.sail
	grep -v -e '^\s*$$' $< > $@

count: _build/cheri_trimmed.sail _build/mips_trimmed.sail
	wc -l $^

%.ml: %.lem
	$(LEM) -only_changed_output -ocaml -lib lem_interp/ $<

run_mips.native: _build/mips.ml _build/mips_extras.ml _build/run_with_elf.ml interpreter
	env OCAMLRUNPARAM=l=100M ocamlfind ocamlopt -g -package num -package str -package unix -I $(ELFDIR)/contrib/ocaml-uint/_build/lib -I $(LEMLIBOCAML) -I $(LEMLIBOCAML)/dependencies/zarith -I _build/lem_interp/ -I $(ELFDIR)/src  -I $(ELFDIR)/src/adaptors -I $(ELFDIR)/src/abis/mips64 -I _build -linkpkg $(LEMLIBOCAML)/dependencies/zarith/zarith.cmxa $(LEMLIBOCAML)/extract.cmxa $(ELFDIR)/contrib/ocaml-uint/_build/lib/uint.cmxa $(ELFDIR)/src/linksem.cmxa  _build/pprint/src/PPrintLib.cmxa _build/lem_interp/extract.cmxa _build/mips.ml _build/mips_extras.ml _build/run_with_elf.ml  -o run_mips.native

run_cheri.native:  _build/cheri.ml _build/mips_extras.ml _build/run_with_elf_cheri.ml interpreter
	env OCAMLRUNPARAM=l=100M ocamlfind ocamlopt -g -package num -package str -package unix -I $(ELFDIR)/contrib/ocaml-uint/_build/lib -I $(LEMLIBOCAML) -I $(LEMLIBOCAML)/dependencies/zarith -I _build/lem_interp/ -I $(ELFDIR)/src  -I $(ELFDIR)/src/adaptors -I $(ELFDIR)/src/abis/mips64 -I _build -linkpkg $(LEMLIBOCAML)/dependencies/zarith/zarith.cmxa $(LEMLIBOCAML)/extract.cmxa $(ELFDIR)/contrib/ocaml-uint/_build/lib/uint.cmxa $(ELFDIR)/src/linksem.cmxa  _build/pprint/src/PPrintLib.cmxa _build/lem_interp/extract.cmxa _build/cheri.ml _build/mips_extras.ml _build/run_with_elf_cheri.ml  -o run_cheri.native

mips_notlb: _build/mips_notlb.ml  _build/mips_embedded.lem _build/mips_sequential_embedded.lem _build/mips_extras.ml
	true

mips: elf run_mips.native

cheri: elf run_cheri.native

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
