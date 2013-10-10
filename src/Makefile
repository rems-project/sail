.PHONY: all test clean

all: main.native test

.PHONY: main.native
main.native:
	ocamlbuild main.native

TESTS=test/test1.native

test:
	ocamlbuild $(TESTS)

clean:
	-ocamlbuild -clean
	-rm -rf _build
	-rm -rf html-doc
	-rm -rf tex-doc
