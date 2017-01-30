#OTT=../../../rsem/ott/bin/ott
# this is the binary that gets rebuilt by make in ott/src:
OTT=../../../rsem/ott/src/ott
OTTLIB=$(dir $(shell which ott))../hol

.PHONY: all
all: l2.pdf l2_parse.pdf l2.ml l2_parse.ml l2.lem

%.pdf: %.tex
	pdflatex $<

%Theory.uo: %Script.sml
	Holmake --qof -I $(OTTLIB) $@

manual.pdf: doc_in.tex manual.tex
	pdflatex manual.tex
	pdflatex manual.tex

l2.tex: l2.ott l2_typ.ott l2_rules.ott
	$(OTT) -sort false -generate_aux_rules false -o $@ -picky_multiple_parses true $^

doc_in.tex: l2.ott primitive_doc.ott l2_typ.ott l2_rules.ott
	$(OTT) -sort false -generate_aux_rules false -tex_wrap false -o $@ -picky_multiple_parses true $^

%.tex: %.ott
	$(OTT) -sort false -generate_aux_rules false -o $@ -picky_multiple_parses true $^

%.ml: %.ott
	$(OTT) -sort false -generate_aux_rules true -o $@ -picky_multiple_parses true $^

%Script.sml: %.ott
	$(OTT) -sort false -generate_aux_rules true -o $@ -picky_multiple_parses true $^

l2.lem: l2.ott l2_typ.ott
	$(OTT) -sort false -generate_aux_rules true -o $@ -picky_multiple_parses true $^

clean:
	rm -rf *~
	-rm -rf *.uo *.ui *.sig *.sml .HOLMK
	-rm -f *.aux *.log *.dvi *.ps *.pdf
	rm -rf l2.pdf l2_parse.pdf l2.ml l2_parse.ml l2.lem
	rm -rf l2.tex doc_in.tex