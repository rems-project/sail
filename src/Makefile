##########################################################################
#     Sail                                                               #
#                                                                        #
#  Copyright (c) 2013-2017                                               #
#    Kathyrn Gray                                                        #
#    Shaked Flur                                                         #
#    Stephen Kell                                                        #
#    Gabriel Kerneis                                                     #
#    Robert Norton-Wright                                                #
#    Christopher Pulte                                                   #
#    Peter Sewell                                                        #
#    Alasdair Armstrong                                                  #
#    Brian Campbell                                                      #
#    Thomas Bauereiss                                                    #
#    Anthony Fox                                                         #
#    Jon French                                                          #
#    Dominic Mulligan                                                    #
#    Stephen Kell                                                        #
#    Mark Wassell                                                        #
#                                                                        #
#  All rights reserved.                                                  #
#                                                                        #
#  This software was developed by the University of Cambridge Computer   #
#  Laboratory as part of the Rigorous Engineering of Mainstream Systems  #
#  (REMS) project, funded by EPSRC grant EP/K008528/1.                   #
#                                                                        #
#  Redistribution and use in source and binary forms, with or without    #
#  modification, are permitted provided that the following conditions    #
#  are met:                                                              #
#  1. Redistributions of source code must retain the above copyright     #
#     notice, this list of conditions and the following disclaimer.      #
#  2. Redistributions in binary form must reproduce the above copyright  #
#     notice, this list of conditions and the following disclaimer in    #
#     the documentation and/or other materials provided with the         #
#     distribution.                                                      #
#                                                                        #
#  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    #
#  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     #
#  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       #
#  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   #
#  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          #
#  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      #
#  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      #
#  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   #
#  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    #
#  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    #
#  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    #
#  SUCH DAMAGE.                                                          #
##########################################################################

$(warning MAKECMDGOALS is $(MAKECMDGOALS))
ifneq ($(MAKECMDGOALS),clean)
# Lem optionally vendors the zarith dependency, but currently
# we don't use that -- just assume the host system has zarith.
ifeq ($(shell ocamlfind query zarith),)
$(error No zarith installed [anywhere ocamlfind can find it]; install it (opam install zarith || apt-get install libzarith-ocaml{,-dev} || yum install ocaml-zarith), or use make install_dependencies in lem/ocaml-lib.)
endif
# assume the host system has lem
ifeq ($(shell ocamlfind query lem),)
$(error No lem installed [anywhere ocamlfind can find it]; please install it ('make install' from lem/ocaml-lib || 'make local-install' from lem/ocaml-lib and add lem/ocaml-lib/local to OCAMLPATH))
endif
endif


.PHONY: all sail sail.native sail.byte test clean doc lib power test_power test_idempotence

# set to -p on command line to enable gprof profiling
OCAML_OPTS?=

all: sail lib doc

full: sail lib power doc test

ast.lem: ../language/l2.ott
	ott -sort false -generate_aux_rules true -o ast.lem -picky_multiple_parses true ../language/l2.ott

bytecode.lem: ../language/bytecode.ott ast.lem
	ott -sort false -generate_aux_rules true -o bytecode.lem -picky_multiple_parses true ../language/bytecode.ott

ast.ml: ast.lem
	lem -ocaml ast.lem
	sed -i -f ast.sed ast.ml

bytecode.ml: bytecode.lem
	lem -ocaml bytecode.lem
	sed -i -f ast.sed bytecode.ml

lem_interp/interp_ast.lem: ../language/l2.ott
	ott -sort false -generate_aux_rules true -o lem_interp/interp_ast.lem -picky_multiple_parses true ../language/l2.ott

sail: ast.ml bytecode.ml
	ocamlbuild -use-ocamlfind sail.native sail_lib.cma sail_lib.cmxa

isail: ast.ml bytecode.ml
	ocamlbuild -use-ocamlfind isail.native

sail.native: sail

sail.byte:
	ocamlbuild -use-ocamlfind -cflag -g sail.byte

interpreter: lem_interp/interp_ast.lem
	ocamlbuild -use-ocamlfind lem_interp/extract.cmxa
	ocamlbuild -use-ocamlfind lem_interp/extract.cma

test: sail interpreter
	ocamlbuild -use-ocamlfind test/run_tests.native
	./run_tests.native

THIS_MAKEFILE := $(realpath $(lastword $(MAKEFILE_LIST)))
SAIL_DIR:=$(realpath $(dir $(THIS_MAKEFILE))..)
PROJECT_ROOT=$(realpath $(dir $(THIS_MAKEFILE))../..)

LEM = $(PROJECT_ROOT)/lem/lem
ELFDIR= $(PROJECT_ROOT)/linksem

SAIL_LIB_DIR:=$(SAIL_DIR)/lib
MIPS_SAIL_DIR:=$(SAIL_DIR)/mips_new_tc

MIPS_SAILS_PRE:=$(SAIL_LIB_DIR)/flow.sail $(MIPS_SAIL_DIR)/prelude.sail $(MIPS_SAIL_DIR)/mips_prelude.sail $(MIPS_SAIL_DIR)/mips_tlb.sail $(MIPS_SAIL_DIR)/mips_wrappers.sail $(MIPS_SAIL_DIR)/mips_ast_decl.sail $(MIPS_SAIL_DIR)/mips_insts.sail $(MIPS_SAIL_DIR)/mips_ri.sail $(MIPS_SAIL_DIR)/mips_epilogue.sail

MIPS_SAILS:=$(MIPS_SAILS_PRE)

MIPS_NOTLB_SAILS_PRE:=$(SAIL_LIB_DIR)/flow.sail $(MIPS_SAIL_DIR)/prelude.sail $(MIPS_SAIL_DIR)/mips_prelude.sail $(MIPS_SAIL_DIR)/mips_tlb_stub.sail $(MIPS_SAIL_DIR)/mips_wrappers.sail $(MIPS_SAIL_DIR)/mips_ast_decl.sail $(MIPS_SAIL_DIR)/mips_insts.sail $(MIPS_SAIL_DIR)/mips_epilogue.sail

MIPS_NOTLB_SAILS:=$(MIPS_NOTLB_SAILS_PRE) $(SAIL_DIR)/etc/regfp.sail $(MIPS_SAIL_DIR)/mips_regfp.sail

CHERI_SAIL_DIR:=$(SAIL_DIR)/cheri

CHERI_NOTLB_SAILS:=$(SAIL_LIB_DIR)/prelude.sail $(SAIL_LIB_DIR)/prelude_wrappers.sail $(MIPS_SAIL_DIR)/mips_prelude.sail $(MIPS_SAIL_DIR)/mips_tlb_stub.sail $(CHERI_SAIL_DIR)/cheri_types.sail $(CHERI_SAIL_DIR)/cheri_prelude_256.sail $(CHERI_SAIL_DIR)/cheri_prelude_common.sail $(MIPS_SAIL_DIR)/mips_insts.sail $(CHERI_SAIL_DIR)/cheri_insts.sail $(MIPS_SAIL_DIR)/mips_ri.sail $(MIPS_SAIL_DIR)/mips_epilogue.sail

CHERI_SAILS:=$(SAIL_LIB_DIR)/prelude.sail $(SAIL_LIB_DIR)/prelude_wrappers.sail $(MIPS_SAIL_DIR)/mips_prelude.sail $(MIPS_SAIL_DIR)/mips_tlb.sail $(CHERI_SAIL_DIR)/cheri_types.sail $(CHERI_SAIL_DIR)/cheri_prelude_256.sail $(CHERI_SAIL_DIR)/cheri_prelude_common.sail $(MIPS_SAIL_DIR)/mips_insts.sail $(CHERI_SAIL_DIR)/cheri_insts.sail $(MIPS_SAIL_DIR)/mips_ri.sail $(MIPS_SAIL_DIR)/mips_epilogue.sail

CHERI128_SAILS:=$(SAIL_LIB_DIR)/prelude.sail $(SAIL_LIB_DIR)/prelude_wrappers.sail $(MIPS_SAIL_DIR)/mips_prelude.sail $(MIPS_SAIL_DIR)/mips_tlb.sail $(CHERI_SAIL_DIR)/cheri_types.sail  $(CHERI_SAIL_DIR)/cheri_prelude_128.sail $(CHERI_SAIL_DIR)/cheri_prelude_common.sail $(MIPS_SAIL_DIR)/mips_insts.sail $(CHERI_SAIL_DIR)/cheri_insts.sail $(MIPS_SAIL_DIR)/mips_ri.sail $(MIPS_SAIL_DIR)/mips_epilogue.sail

elf:
	make -C $(ELFDIR)

CP_TO_BUILD=mkdir -p _build; cp $< $@

_build/mips_extras.lem: ../mips/mips_extras.lem
	$(CP_TO_BUILD)

_build/mips_extras_ml.ml: ../mips/mips_extras_ml.ml
	$(CP_TO_BUILD)

_build/sail_values.ml: gen_lib/sail_values.ml
	$(CP_TO_BUILD)

_build/run_with_elf.ml: lem_interp/run_with_elf.ml
	$(CP_TO_BUILD)

_build/run_with_elf_cheri.ml: lem_interp/run_with_elf_cheri.ml
	$(CP_TO_BUILD)

_build/run_with_elf_cheri128.ml: lem_interp/run_with_elf_cheri128.ml
	$(CP_TO_BUILD)

_build/run_embed.ml: ../mips/run_embed.ml
	$(CP_TO_BUILD)

_build/mips.lem: $(MIPS_SAILS) ./sail.native
	mkdir -p _build
	cd _build ;\
	../sail.native -lem_ast -o mips $(MIPS_SAILS)

_build/mips_types.lem: $(MIPS_NOTLB_SAILS) ./sail.native
	mkdir -p _build
	cd _build ;\
	../sail.native -lem_lib "Mips_extras" -lem -lem_mwords -o mips $(MIPS_NOTLB_SAILS)

_build/Mips.thy: _build/mips_types.lem
	cd _build ;\
	lem -isa -outdir . -lib ../lem_interp -lib ../gen_lib $(MIPS_SAIL_DIR)/mips_extras.lem mips_types.lem mips.lem

_build/mips_notlb.lem: $(MIPS_NOTLB_SAILS) ./sail.native
	mkdir -p _build
	cd _build ; \
	../sail.native -lem_ast -o mips_notlb $(MIPS_NOTLB_SAILS_PRE)

_build/mips_notlb.ml: $(MIPS_NOTLB_SAILS_PRE) ./sail.native
	mkdir -p _build
	cd _build ; \
	../sail.native -ocaml -lem -lem_ast -ocaml_lib Mips_extras_ml -o mips_notlb $(MIPS_NOTLB_SAILS_PRE)

_build/mips.ml: $(MIPS_SAILS_PRE) ./sail.native
	mkdir -p _build
	cd _build ; \
	../sail.native -ocaml -lem -lem_ast -ocaml_lib Mips_extras_ml -o mips $(MIPS_SAILS_PRE)

_build/cheri.ml: $(CHERI_SAILS) ./sail.native
	mkdir -p _build
	cd _build ; \
	../sail.native -ocaml -lem -lem_ast -ocaml_lib Mips_extras_ml -o cheri $(CHERI_SAILS)

_build/cheri128.ml: $(CHERI128_SAILS) ./sail.native
	mkdir -p _build
	cd _build ; \
	../sail.native -ocaml -lem -lem_ast -ocaml_lib Mips_extras_ml -o cheri128 $(CHERI128_SAILS)

_build/cheri.lem: $(CHERI_SAILS) ./sail.native
	mkdir -p _build
	cd _build ;\
	../sail.native -lem_ast -o cheri $(CHERI_SAILS)

_build/cheri128.lem: $(CHERI128_SAILS) ./sail.native
	mkdir -p _build
	cd _build ;\
	../sail.native -lem_ast -o cheri128 $(CHERI128_SAILS)

_build/cheri_notlb.lem: $(CHERI_NOTLB_SAILS) ./sail.native
	mkdir -p _build
	cd _build ;\
	../sail.native -lem_ast -o cheri_notlb $(CHERI_NOTLB_SAILS)

_build/cheri_types.lem: $(CHERI_SAILS) ./sail.native
	mkdir -p _build
	cd _build ;\
	../sail.native -lem_lib "Mips_extras" -lem -lem_mwords -o cheri $(CHERI_SAILS)

_build/Cheri.thy: _build/cheri_types.lem
	cd _build ;\
	lem -isa -outdir . -lib ../lem_interp -lib ../gen_lib $(MIPS_SAIL_DIR)/mips_extras.lem cheri_types.lem cheri.lem

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

#run_mips.native: _build/mips.ml _build/mips_extras.ml _build/run_with_elf.ml interpreter
#	env OCAMLRUNPARAM=l=100M ocamlfind ocamlopt $(OCAML_OPTS) -g -package num -package str -package unix -I $(ELFDIR)/contrib/ocaml-uint/_build/lib -I $(LEMLIBOCAML) -I $(ZARITH_DIR) -I _build/lem_interp/ -I $(ELFDIR)/src  -I $(ELFDIR)/src/adaptors -I $(ELFDIR)/src/abis/mips64 -I _build -linkpkg $(ZARITH_LIB) $(LEMLIBOCAML)/extract.cmxa $(ELFDIR)/contrib/ocaml-uint/_build/lib/uint.cmxa $(ELFDIR)/src/linksem.cmxa  _build/pprint/src/PPrintLib.cmxa _build/lem_interp/extract.cmxa _build/mips.ml _build/mips_extras.ml _build/run_with_elf.ml  -o run_mips.native

run_mips.native: _build/mips.ml _build/mips_extras.ml _build/run_with_elf.ml interpreter
	env OCAMLRUNPARAM=l=100M ocamlfind ocamlopt $(OCAML_OPTS) -g -package num -package str -package unix -package zarith -package lem -package linksem -linkpkg -I _build/lem_interp/ -I _build _build/pprint/src/PPrintLib.cmxa _build/lem_interp/extract.cmxa _build/mips.ml _build/mips_extras.ml _build/run_with_elf.ml -o run_mips.native

run_cheri.native:  _build/cheri.ml _build/mips_extras.ml _build/run_with_elf_cheri.ml interpreter
	env OCAMLRUNPARAM=l=100M ocamlfind ocamlopt $(OCAML_OPTS) -g -package num -package str -package unix -package zarith -package lem -package linksem -linkpkg -I _build/lem_interp/ -I _build _build/pprint/src/PPrintLib.cmxa _build/lem_interp/extract.cmxa _build/cheri.ml _build/mips_extras.ml _build/run_with_elf_cheri.ml  -o run_cheri.native

run_cheri128.native:  _build/cheri128.ml _build/mips_extras.ml _build/run_with_elf_cheri128.ml interpreter
	env OCAMLRUNPARAM=l=100M ocamlfind ocamlopt $(OCAML_OPTS) -g -package num -package str -package unix -package zarith -package lem -package linksem -linkpkg -I _build/lem_interp/ -I _build _build/pprint/src/PPrintLib.cmxa _build/lem_interp/extract.cmxa _build/cheri128.ml _build/mips_extras.ml _build/run_with_elf_cheri128.ml  -o run_cheri128.native

run_embed.native: _build/sail_values.ml _build/mips_extras_ml.ml _build/mips.ml _build/cheri.ml _build/cheri128.ml _build/run_embed.ml
	env OCAMLRUNPARAM=l=100M ocamlfind ocamlopt $(OCAML_OPTS) -g -package zarith -package unix -I _build -linkpkg $^ -o $@

_build/power.ml: $(SAIL_DIR)/src/test/power.sail sail.native
	cd _build; \
	./sail.native -lem_ast -ocaml $< -o $(basename $(@))

_build/power.native: _build/sail_values.ml _build/power.ml
	env OCAMLRUNPARAM=l=100M ocamlfind ocamlopt $(OCAML_OPTS) -g -package zarith -package unix -I _build -linkpkg $^ -o $@

_build/armv8_embed.ml: sail.native
	make -C ../arm ocaml
	cp ../arm/build/armv8_embed.ml $@

_build/arm.native: _build/sail_values.ml _build/armv8_embed.ml
	env OCAMLRUNPARAM=l=100M ocamlfind ocamlopt $(OCAML_OPTS) -g -package zarith -package unix -I _build -linkpkg $^ -o $@

mips_notlb: _build/mips_notlb.ml  _build/mips_types.lem _build/mips_extras.ml
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
	-rm -f ast.ml
	-rm -f ast.lem
	-rm -f bytecode.ml
	-rm -f bytecode.lem

doc:
	ocamlbuild -use-ocamlfind sail.docdir/index.html

lib:
	ocamlbuild -use-ocamlfind pretty_print.cmxa pretty_print.cma
