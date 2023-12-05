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

ifeq ($(shell which sail),)
$(error Cannot find sail executable, make sure it is in PATH)
endif

SAIL_RISCV=../../sail-riscv

all: manual.pdf

.PHONY: clean

code_riscv.tex: examples/riscv_duopod.sail
	sail -o code_riscv -latex -latex_full_valspecs $^
	cp code_riscv/commands.tex code_riscv.tex

code_myreplicatebits.tex: examples/my_replicate_bits.sail
	sail -o code_myreplicatebits -latex -latex_full_valspecs -latex_prefix mrb examples/my_replicate_bits.sail
	cp code_myreplicatebits/commands.tex code_myreplicatebits.tex

grammar.tex: ../language/sail.ott
	ott -pp_grammar -tex_wrap false -tex_suppress_category I -tex_suppress_category D -tex_suppress_ntr terminals -tex_suppress_ntr formula -tex_suppress_ntr judgement -tex_suppress_ntr user_syntax -tex_suppress_ntr dec_comm -sort false -generate_aux_rules false  -picky_multiple_parses true -i ../language/sail.ott -o grammar.tex

lexer_syntax.sed: ../src/lib/lexer.mll
	sed -n -e 's/^ *("\([A-Za-z0-9]*\)",[ \t]*(fun . -> \(.*\)));$//s\/{\2}\/{\\\\lstinline{\1}}\//p' \
	  -e '/ *| "~"/d' \
	  -e 's/~/\\\\~/g' \
	  -e 's/^ *| "\([^"{}&]\+\)"[ \t]*{ (\?\([A-Za-z]\+\)\((.*)\)\?)\? }$//s\/{\2}\/{\\\\lstinline"\1"}\//p' \
	  < ../src/lib/lexer.mll > lexer_syntax.sed

# The first sed removes a couple of rules that are only used for
# partially rewritten programs, and non-terminals that are used for
# interactive mode. Ideally I'd like to replace it by adding a
# filtering option to obelisk.
parser_grammar.tex parser_package.sty: ../src/lib/parser.mly lexer_syntax.sed extra_lexer_syntax.sed
	sed -e '/[Ii]nternal_\?\([Pp][Ll]et\|[Rr]eturn\)/d' -e '/_eof:/,/^ *$$/d' ../src/lib/parser.mly > parser.mly
	obelisk latex -i -o parser_grammar.tex -prefix sail -package parser_package parser.mly
	sed -i.bak -f lexer_syntax.sed -f extra_lexer_syntax.sed parser_package.sty

internals.tex: internals.md
	pandoc $< -f markdown -t latex --listings -o $@
	sed -i.bak -f pandocfix.sed $@

LATEXARG=manual.tex
manual.pdf: grammar.tex introduction.tex usage.tex types.tex code_riscv.tex riscv.tex manual.tex manual.bib tutorial.tex internals.tex code_myreplicatebits.tex parser_grammar.tex parser_package.sty grammar_section.tex
	pdflatex ${LATEXARG}
	bibtex manual
	pdflatex ${LATEXARG}
	pdflatex ${LATEXARG}

manual.pdf: examples/bitfield.sail

anon_man: LATEXARG='\def\ANON{}\input{manual.tex}'
anon_man: manual.pdf

clean:
	-rm manual.pdf
	-rm -rf code_riscv/
	-rm -f code_riscv.tex
	-rm -f internals.tex
	-rm -rf code_myreplicatebits/
	-rm -f code_myreplicatebits.tex
	-rm -f lexer_syntax.sed parser_grammar.tex parser_package.sty parser.mly
	-rm -f *.aux
	-rm -f *.log
