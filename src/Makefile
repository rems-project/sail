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


.PHONY: all sail isail coverage sail.native sail.byte manifest.ml clean doc lib

# set to -p on command line to enable gprof profiling
OCAML_OPTS?=

all: sail lib doc

full: sail lib doc

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

manifest.ml:
	echo "(* Generated file -- do not edit. *)" > manifest.ml
ifndef SHARE_DIR
	echo let dir=\"$(realpath ..)\" >> manifest.ml
	echo let commit=\"$(shell git rev-parse HEAD)\" >> manifest.ml
	echo let branch=\"$(shell  git rev-parse --abbrev-ref HEAD)\" >> manifest.ml
	echo let version=\"$(shell git describe)\" >> manifest.ml
else
	echo let dir=\"$(SHARE_DIR)\" >> manifest.ml
	echo let commit=\"opam\" >> manifest.ml
	echo let branch=\"sail2\" >> manifest.ml
	echo let version=\"$(shell grep '^version:' ../opam | grep -o -E '"[^"]+"')\" >> manifest.ml
endif

sail: ast.ml bytecode.ml manifest.ml
	ocamlbuild -use-ocamlfind sail.native sail_lib.cma sail_lib.cmxa

isail: ast.ml bytecode.ml manifest.ml
	ocamlbuild -use-ocamlfind isail.native

coverage: ast.ml bytecode.ml manifest.ml
	BISECT_COVERAGE=YES ocamlbuild -use-ocamlfind -plugin-tag 'package(bisect_ppx-ocamlbuild)' isail.native

sail.native: sail

sail.byte: ast.ml bytecode.ml manifest.ml
	ocamlbuild -use-ocamlfind -cflag -g sail.byte

isail.byte: ast.ml bytecode.ml share_directory.ml
	ocamlbuild -use-ocamlfind isail.byte

interpreter: lem_interp/interp_ast.lem
	ocamlbuild -use-ocamlfind lem_interp/extract.cmxa
	ocamlbuild -use-ocamlfind lem_interp/extract.cma

THIS_MAKEFILE := $(realpath $(lastword $(MAKEFILE_LIST)))
SAIL_DIR:=$(realpath $(dir $(THIS_MAKEFILE))..)
PROJECT_ROOT=$(realpath $(dir $(THIS_MAKEFILE))../..)

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
	-rm -f manifest.ml

doc:
	ocamlbuild -use-ocamlfind sail.docdir/index.html

lib:
	ocamlbuild -use-ocamlfind pretty_print.cmxa pretty_print.cma
