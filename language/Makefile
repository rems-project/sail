OTTLIB=$(dir $(shell which ott))../hol

all: l2.pdf l2_parse.pdf parse_ast.ml

l2.pdf: l2.tex
	pdflatex l2.tex

l2_parse.pdf: l2_parse.tex
	pdflatex l2_parse.tex

l2Theory.uo: l2Script.sml
	Holmake --qof -I $(OTTLIB) l2Theory.uo

l2.tex ../src/ast.ml ../src/ast.lem l2Script.sml: l2.ott 
	ott -sort false -generate_aux_rules false -o l2.tex  -picky_multiple_parses true l2.ott
	ott -sort false -generate_aux_rules false -o ../src/ast.lem -o l2Script.sml -picky_multiple_parses true l2.ott
	ott -sort false -generate_aux_rules true -o ../src/ast.ml -picky_multiple_parses true l2.ott
# the above is working around what is probably a bug in -generate_aux_rules true: when we try to generate Lem code with that turned on, we get some surprising-looking parse failures in a few rules.  Likely we're not doing the proper transform for rules generated from inductive relation syntax. 

l2_parse.tex parse_ast.ml ../src/parse_ast.ml: l2_parse.ott
	ott -sort false -generate_aux_rules false -o l2_parse.tex  -picky_multiple_parses true l2_parse.ott
	ott -sort false -generate_aux_rules true -o ../src/parse_ast.ml -picky_multiple_parses true l2_parse.ott
  

#	rm -f ../src/ast.ml
#	chmod a-w ../src/ast.ml

l2.lem: l2.ott
	ott -o l2.lem -picky_multiple_parses true l2.ott


clean:
	rm -rf *~
	-rm -rf *.uo *.ui l2Theory.sig l2Theory.sml l2.tex l2Script.sml l2.aux l2.log l2.dvi l2.ps l2_unwrapped.tex .HOLMK  l2.ml
#l2.sys l2 library/lib_cache

