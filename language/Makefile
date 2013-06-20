#OTTLIB=/Users/sowens/ott/hol
OTTLIB=$(dir $(shell which ott))../hol

all: l2.pdf

l2.pdf: l2.tex
	pdflatex l2.tex

l2Theory.uo: l2Script.sml
	Holmake --qof -I $(OTTLIB) l2Theory.uo

l2.tex ../src/ast.ml l2Script.sml: l2.ott
	ott -ocaml_include_terminals true -o l2.tex -o l2.ml -o l2Script.sml -picky_multiple_parses true l2.ott

	#rm -f ../src/ast.ml
#	chmod a-w ../src/ast.ml

l2.lem: l2.ott
	ott -o l2.lem -picky_multiple_parses true l2.ott


clean:
	rm -rf *~
	-rm -rf *.uo *.ui l2Theory.sig l2Theory.sml l2.tex l2Script.sml l2.aux l2.log l2.dvi l2.ps l2_unwrapped.tex .HOLMK 
#l2.sys l2 library/lib_cache

