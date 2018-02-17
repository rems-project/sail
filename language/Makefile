#OTT=../../../rsem/ott/bin/ott
# this is the binary that gets rebuilt by make in ott/src:
OTT=../../ott/src/ott
OTTLIB=$(dir $(shell which ott))../hol

.PHONY: all
all: l2.ml l2_parse.ml l2.lem l2_parse2.ml l2_parse2_parser.mly

docs: l2.pdf l2_parse.pdf 

%.pdf: %.tex
	pdflatex $<

%Theory.uo: %Script.sml
	Holmake --qof -I $(OTTLIB) $@

type_system.pdf: doc_in.tex type_system.tex
	pdflatex type_system.tex
	pdflatex type_system.tex

l2.tex: l2.ott  l2_rules.ott # l2_terminals_non_tt.ott  l2_typ.ott l2_rules.ott
	$(OTT) -sort false -generate_aux_rules false -o $@ -picky_multiple_parses true $^

doc_in.tex: l2.ott primitive_doc.ott l2_terminals_tt.ott l2_typ.ott l2_rules.ott
	$(OTT) -sort false -generate_aux_rules false -tex_wrap false -o $@ -picky_multiple_parses true $^

%.tex: %.ott
	$(OTT) -sort false -generate_aux_rules false -o $@ -picky_multiple_parses true $^

%.ml: %.ott
	$(OTT) -sort false -generate_aux_rules true -o $@ -picky_multiple_parses true $^

%Script.sml: %.ott
	$(OTT) -sort false -generate_aux_rules true -o $@ -picky_multiple_parses true $^

l2.lem: l2.ott
	$(OTT) -sort false -generate_aux_rules true -o $@ -picky_multiple_parses true $^

ROOT=l2_parse2
# generate the ocaml AST type, ocamllex lexer, menhir parser, and ocaml pretty printers for the AST, all from the Ott soruce
$(ROOT)_ast.ml  $(ROOT)_lexer.mll $(ROOT)_parser.mly $(ROOT)_parser_pp.ml $(ROOT)_ast.tex : $(ROOT).ott Makefile
	$(OTT) -quotient_rules false -generate_aux_rules false -i $(ROOT).ott  -o $(ROOT)_parser.mly -o $(ROOT)_lexer.mll -o $(ROOT)_ast.ml -o $(ROOT).tex


clean:
	rm -rf *~
	rm -rf *.uo *.ui *.sig *.sml .HOLMK
	rm -f *.aux *.log *.dvi *.ps *.pdf *.toc
	rm -rf l2.pdf l2_parse.pdf 
	rm -rf l2.tex doc_in.tex

realclean:
	$(MAKE) clean
	rm -rf l2.ml l2_parse.ml l2.lem
