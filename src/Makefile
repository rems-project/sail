.PHONY: all doc doc-pdf doc-dot clean

all:
	ocamlbuild main.native
	$(MAKE) -C lem_interp

doc:
	mkdir -p html-doc
	ocamldoc -I _build/ *.mli ulib/*.mli -sort -html -d html-doc

doc-pdf:
	mkdir -p tex-doc
	ocamldoc -I _build/ *.mli -latex -sort -d tex-doc -o tex-doc/lem-doc.tex; true
	cd tex-doc; pdflatex lem-doc.tex

doc-dot:
	ocamldoc -I _build/ *.ml *.mli ulib/*.ml -dot -sort -d tex-doc -dot-reduce -o dep.dot; true
	dot -Tpdf -o dep.pdf dep.dot

clean:
	-ocamlbuild -clean
	-rm -rf _build
	-rm -rf html-doc
	-rm -rf tex-doc
