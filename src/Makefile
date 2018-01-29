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

.PHONY: all sail sail.native sail.byte test clean doc lib power test_power test_idempotence

# set to -p on command line to enable gprof profiling
OCAML_OPTS?=

all: sail lib doc

full: sail lib power doc test

ast.lem: ../language/l2.ott
	ott -sort false -generate_aux_rules true -o ast.lem -picky_multiple_parses true ../language/l2.ott

ast.ml: ast.lem
	lem -ocaml ast.lem
	sed -i -f ast.sed ast.ml

lem_interp/interp_ast.lem: ../language/l2.ott
	ott -sort false -generate_aux_rules true -o lem_interp/interp_ast.lem -picky_multiple_parses true ../language/l2.ott

sail: ast.ml
	ocamlbuild -use-ocamlfind sail.native

isail: ast.ml
	ocamlbuild -use-ocamlfind isail.native

sail.native: sail

sail.byte:
	ocamlbuild -use-ocamlfind -cflag -g sail.byte

interpreter: lem_interp/interp_ast.lem
	ocamlbuild lem_interp/extract.cmxa
	ocamlbuild lem_interp/extract.cma

test: sail interpreter
	ocamlbuild test/run_tests.native
	./run_tests.native

THIS_MAKEFILE := $(realpath $(lastword $(MAKEFILE_LIST)))
SAIL_DIR:=$(realpath $(dir $(THIS_MAKEFILE))..)
BITBUCKET_ROOT=$(realpath $(dir $(THIS_MAKEFILE))../..)

LEM = $(BITBUCKET_ROOT)/lem/lem
LEMLIBOCAML = $(BITBUCKET_ROOT)/lem/ocaml-lib/_build_zarith
ELFDIR= $(BITBUCKET_ROOT)/linksem
ZARITH_DIR=$(LEMLIBOCAML)/dependencies/zarith
ZARITH_LIB=$(ZARITH_DIR)/zarith.cma
# ZARITH_LIB=$(ZARITH_DIR)/zarith.cmxa

SAIL_LIB_DIR:=$(SAIL_DIR)/lib
MIPS_SAIL_DIR:=$(SAIL_DIR)/mips_new_tc

MIPS_SAILS_PRE:=$(SAIL_LIB_DIR)/prelude.sail $(SAIL_LIB_DIR)/prelude_wrappers.sail $(MIPS_SAIL_DIR)/mips_prelude.sail $(MIPS_SAIL_DIR)/mips_tlb.sail $(MIPS_SAIL_DIR)/mips_wrappers.sail $(MIPS_SAIL_DIR)/mips_ast_decl.sail $(MIPS_SAIL_DIR)/mips_insts.sail $(MIPS_SAIL_DIR)/mips_ri.sail $(MIPS_SAIL_DIR)/mips_epilogue.sail

MIPS_SAILS:=$(MIPS_SAILS_PRE) $(SAIL_DIR)/etc/regfp.sail $(MIPS_SAIL_DIR)/mips_regfp.sail

MIPS_NOTLB_SAILS_PRE:=$(SAIL_LIB_DIR)/prelude.sail $(SAIL_LIB_DIR)/prelude_wrappers.sail $(MIPS_SAIL_DIR)/mips_prelude.sail $(MIPS_SAIL_DIR)/mips_tlb_stub.sail $(MIPS_SAIL_DIR)/mips_wrappers.sail $(MIPS_SAIL_DIR)/mips_ast_decl.sail $(MIPS_SAIL_DIR)/mips_insts.sail $(MIPS_SAIL_DIR)/mips_epilogue.sail

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

_build/mips_embed_types.lem: $(MIPS_NOTLB_SAILS) ./sail.native
	mkdir -p _build
	cd _build ;\
	../sail.native -lem_lib "Mips_extras_embed" -lem -lem_mwords -o mips $(MIPS_NOTLB_SAILS)

_build/Mips_embed.thy: _build/mips_embed_types.lem
	cd _build ;\
	lem -isa -outdir . -lib ../lem_interp -lib ../gen_lib $(MIPS_SAIL_DIR)/mips_extras_embed.lem mips_embed_types.lem mips_embed.lem

_build/mips_notlb.lem: $(MIPS_NOTLB_SAILS) ./sail.native
	mkdir -p _build
	cd _build ; \
	../sail.native -lem_ast -o mips_notlb $(MIPS_NOTLB_SAILS)

_build/mips_notlb_embed.ml: $(MIPS_NOTLB_SAILS_PRE) ./sail.native
	mkdir -p _build
	cd _build ; \
	../sail.native -ocaml -lem -lem_ast -ocaml_lib Mips_extras_ml -o mips_notlb_embed $(MIPS_NOTLB_SAILS_PRE)

_build/mips_embed.ml: $(MIPS_SAILS_PRE) ./sail.native
	mkdir -p _build
	cd _build ; \
	../sail.native -ocaml -lem -lem_ast -ocaml_lib Mips_extras_ml -o mips_embed $(MIPS_SAILS_PRE)

_build/cheri_embed.ml: $(CHERI_SAILS) ./sail.native
	mkdir -p _build
	cd _build ; \
	../sail.native -ocaml -lem -lem_ast -ocaml_lib Mips_extras_ml -o cheri_embed $(CHERI_SAILS)

_build/cheri128_embed.ml: $(CHERI128_SAILS) ./sail.native
	mkdir -p _build
	cd _build ; \
	../sail.native -ocaml -lem -lem_ast -ocaml_lib Mips_extras_ml -o cheri128_embed $(CHERI128_SAILS)

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

_build/cheri_embed_types_sequential.lem: $(CHERI_SAILS) ./sail.native
	mkdir -p _build
	cd _build ;\
	../sail.native -lem_lib "Mips_extras_embed" -lem -lem_sequential -lem_mwords -o cheri $(CHERI_SAILS)

_build/Cheri_embed_sequential.thy: _build/cheri_embed_types_sequential.lem
	cd _build ;\
	lem -isa -outdir . -lib ../lem_interp -lib ../gen_lib $(MIPS_SAIL_DIR)/mips_extras_embed_sequential.lem cheri_embed_types_sequential.lem cheri_embed_sequential.lem

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
	env OCAMLRUNPARAM=l=100M ocamlfind ocamlc $(OCAML_OPTS) -g -package num -package str -package unix -I $(ELFDIR)/contrib/ocaml-uint/_build/lib -I $(LEMLIBOCAML) -I $(ZARITH_DIR) -I _build/lem_interp/ -I $(ELFDIR)/src  -I $(ELFDIR)/src/adaptors -I $(ELFDIR)/src/abis/mips64 -I _build -linkpkg $(ZARITH_LIB) $(LEMLIBOCAML)/extract.cma $(ELFDIR)/contrib/ocaml-uint/_build/lib/uint.cma $(ELFDIR)/src/linksem.cma  _build/pprint/src/PPrintLib.cma _build/lem_interp/extract.cma _build/mips.ml _build/mips_extras.ml _build/run_with_elf.ml  -o run_mips.native

run_cheri.native:  _build/cheri.ml _build/mips_extras.ml _build/run_with_elf_cheri.ml interpreter
	env OCAMLRUNPARAM=l=100M ocamlfind ocamlopt $(OCAML_OPTS) -g -package num -package str -package unix -I $(ELFDIR)/contrib/ocaml-uint/_build/lib -I $(LEMLIBOCAML) -I $(ZARITH_DIR) -I _build/lem_interp/ -I $(ELFDIR)/src  -I $(ELFDIR)/src/adaptors -I $(ELFDIR)/src/abis/mips64 -I _build -linkpkg $(ZARITH_LIB) $(LEMLIBOCAML)/extract.cmxa $(ELFDIR)/contrib/ocaml-uint/_build/lib/uint.cmxa $(ELFDIR)/src/linksem.cmxa  _build/pprint/src/PPrintLib.cmxa _build/lem_interp/extract.cmxa _build/cheri.ml _build/mips_extras.ml _build/run_with_elf_cheri.ml  -o run_cheri.native

run_cheri128.native:  _build/cheri128.ml _build/mips_extras.ml _build/run_with_elf_cheri128.ml interpreter
	env OCAMLRUNPARAM=l=100M ocamlfind ocamlopt $(OCAML_OPTS) -g -package num -package str -package unix -I $(ELFDIR)/contrib/ocaml-uint/_build/lib -I $(LEMLIBOCAML) -I $(ZARITH_DIR) -I _build/lem_interp/ -I $(ELFDIR)/src  -I $(ELFDIR)/src/adaptors -I $(ELFDIR)/src/abis/mips64 -I _build -linkpkg $(ZARITH_LIB) $(LEMLIBOCAML)/extract.cmxa $(ELFDIR)/contrib/ocaml-uint/_build/lib/uint.cmxa $(ELFDIR)/src/linksem.cmxa  _build/pprint/src/PPrintLib.cmxa _build/lem_interp/extract.cmxa _build/cheri128.ml _build/mips_extras.ml _build/run_with_elf_cheri128.ml  -o run_cheri128.native

run_embed.native: _build/sail_values.ml _build/mips_extras_ml.ml _build/mips_embed.ml _build/cheri_embed.ml _build/cheri128_embed.ml _build/run_embed.ml
	env OCAMLRUNPARAM=l=100M ocamlfind ocamlopt $(OCAML_OPTS) -g -package unix -I $(ZARITH_DIR) -I _build -linkpkg $(ZARITH_LIB) $^ -o $@

_build/power.ml: $(SAIL_DIR)/src/test/power.sail sail.native
	cd _build; \
	./sail.native -lem_ast -ocaml $< -o $(basename $(@))

_build/power.native: _build/sail_values.ml _build/power.ml
	env OCAMLRUNPARAM=l=100M ocamlfind ocamlopt $(OCAML_OPTS) -g -package unix -I $(ZARITH_DIR) -I _build -linkpkg $(ZARITH_LIB) $^ -o $@

_build/armv8_embed.ml: sail.native
	make -C ../arm ocaml
	cp ../arm/build/armv8_embed.ml $@

_build/arm.native: _build/sail_values.ml _build/armv8_embed.ml
	env OCAMLRUNPARAM=l=100M ocamlfind ocamlopt $(OCAML_OPTS) -g -package unix -I $(ZARITH_DIR) -I _build -linkpkg $(ZARITH_LIB) $^ -o $@

mips_notlb: _build/mips_notlb.ml  _build/mips_embed_types.lem _build/mips_extras.ml
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

doc:
	ocamlbuild -use-ocamlfind sail.docdir/index.html

lib:
	ocamlbuild -use-ocamlfind pretty_print.cmxa pretty_print.cma
