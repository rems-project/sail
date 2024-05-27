.PHONY: all isail sail install coverage clean asciidoc docker test core-tests c-tests

all: sail

isail: sail

sail:
	dune build --release

install: sail
	dune install


# Build binary tarball. The lib directory is very large and not needed
# for running the compiler. TARBALL_EXTRA_BIN can be used to bundle z3.
tarball: sail
	dune install --relocatable --prefix=_build/tarball/sail
	rm -rf _build/tarball/sail/lib
ifdef TARBALL_EXTRA_BIN
	cp $(TARBALL_EXTRA_BIN) _build/tarball/sail/bin/
endif
	tar czvf _build/sail.tar.gz -C _build/tarball sail

coverage:
	dune build --release --instrument-with bisect_ppx

clean:
	dune clean

asciidoc:
	$(MAKE) -C doc/asciidoc
	cp doc/asciidoc/manual.html manual.html

docker:
	docker build --tag sail:0.1 .
	@echo 'for example: docker run --volume `PWD`:/data/ sail:0.1 --help'

test:
	SAIL_DIR=`pwd` SAIL=`pwd`/sail test/run_tests.sh

core-tests:
	SAIL_DIR=`pwd` SAIL=`pwd`/sail test/run_core_tests.sh

c-tests:
	SAIL_DIR=`pwd` SAIL=`pwd`/sail test/c/run_tests.py
