##
## Makefile to generate PDF and Coq for MiniSailPlus and PDF for MiniSail
##
## Ott definition for MiniSail+ is split so that we can get the embeddings to be put into the right place
## in the resulting theorem prover code.
##
## Coq prover files require the Ott Coq support library via OPAM. This can be install using 'opam install coq-ott'.
## It has been tested with Coq 8.5 through 8.10.0. Ancient versions like 8.4 are not supported.
##


# We are going to use
OTT=ott -signal_parse_errors true -coq_expand_list_types false

%.vo: %.v
	   coqc $<

%.pdf : %.tex
	pdflatex $<

all: Typing.vo 

minisailplus.tex :  common.ott minisailplus_ast_vct.ott minisailplus_ast_ped.ott minisailplus_rules.ott
	$(OTT) -sort false -generate_aux_rules false -merge true -o $@ -picky_multiple_parses true $^

minisail_anf.tex: minisail_anf.ott
	$(OTT) -sort false -generate_aux_rules false -merge true -o $@ -picky_multiple_parses true $^

Typing.v SyntaxVCT.v SyntaxPED.v : common.ott minisailplus_ast_vct.ott minisailplus_ast_ped.ott minisailplus_rules.ott
	$(OTT)  -sort false -generate_aux_rules false -aux_style_rules false -picky_multiple_parses true  \
	-i common.ott -i minisailplus_ast_vct.ott -o SyntaxVCT.v \
	-i minisailplus_ast_ped.ott -o SyntaxPED.v \
        -i minisailplus_rules.ott -o Typing.v

Typing.vo : SyntaxVCT.vo SyntaxPED.vo


minisailplus.vo: SyntaxVCT.v SyntaxPED.v Typing.v
	coqc $^

clean:
	rm -f *.vo
	rm -f *.v
	rm -f *.glob
