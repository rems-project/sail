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

SHARE_DIR?=$(realpath ..)

all: sail lib doc

full: sail lib power doc test

ast.lem: ../language/sail.ott
	ott -sort false -generate_aux_rules true -o ast.lem -picky_multiple_parses true ../language/sail.ott

bytecode.lem: ../language/bytecode.ott ast.lem
	ott -sort false -generate_aux_rules true -o bytecode.lem -picky_multiple_parses true ../language/bytecode.ott

ast.ml: ast.lem
	lem -ocaml ast.lem
	sed -i.bak -f ast.sed ast.ml

bytecode.ml: bytecode.lem
	lem -ocaml bytecode.lem -lib . -lib gen_lib/
	sed -i.bak -f ast.sed bytecode.ml

lem_interp/interp_ast.lem: ../language/l2.ott
	ott -sort false -generate_aux_rules true -o lem_interp/interp_ast.lem -picky_multiple_parses true ../language/l2.ott

share_directory.ml:
	echo "(* Generated file -- do not edit. *)" > share_directory.ml
	echo let d=\"$(SHARE_DIR)\" >> share_directory.ml

sail: ast.ml bytecode.ml share_directory.ml
	ocamlbuild -use-ocamlfind sail.native sail_lib.cma sail_lib.cmxa

isail: ast.ml bytecode.ml share_directory.ml
	ocamlbuild -use-ocamlfind isail.native

sail.native: sail

sail.byte: ast.ml bytecode.ml share_directory.ml
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

_build/sail_values.ml: gen_lib/sail_values.ml
	$(CP_TO_BUILD)

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

clean:
	-ocamlbuild -clean
	-rm -rf _build *.native
	-rm -rf html-doc
	-rm -rf tex-doc
	-rm -rf lem lib
	-rm -rf sail.docdir
	-rm -f gen_lib/*.ml
	-rm -f ast.ml
	-rm -f ast.lem
	-rm -f ast.ml.bak
	-rm -f bytecode.ml
	-rm -f bytecode.lem
	-rm -f bytecode.ml.bak
	-rm -f share_directory.ml

doc:
	ocamlbuild -use-ocamlfind sail.docdir/index.html

lib:
	ocamlbuild -use-ocamlfind pretty_print.cmxa pretty_print.cma
