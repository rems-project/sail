OTTLIB=$(dir $(shell which ott))../hol

.PHONY: all
all: l2.pdf l2_parse.pdf l2.ml l2_parse.ml l2.lem

%.pdf: %.tex
	pdflatex $<

%Theory.uo: %Script.sml
	Holmake --qof -I $(OTTLIB) $@

l2.tex: l2.ott l2_typ.ott l2_rules.ott
	ott -sort false -generate_aux_rules false -o $@ -picky_multiple_parses true $^

%.tex: %.ott
	ott -sort false -generate_aux_rules false -o $@ -picky_multiple_parses true $^

%.ml: %.ott
	ott -sort false -generate_aux_rules true -o $@ -picky_multiple_parses true $^

%Script.sml: %.ott
	ott -sort false -generate_aux_rules true -o $@ -picky_multiple_parses true $^

l2.lem: l2.ott l2_typ.ott
	ott -sort false -generate_aux_rules true -o $@ -picky_multiple_parses true $^

clean:
	rm -rf *~
	-rm -rf *.uo *.ui *.sig *.sml .HOLMK
	-rm -f *.tex *.aux *.log *.dvi *.ps *.pdf
