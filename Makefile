.PHONY: all isail sail install coverage clean asciidoc docker test core-tests c-tests

all: sail

isail: sail

sail:
	dune build --release

install: sail
	dune install

libsail_coverage:
	$(MAKE) -C lib/coverage

# Build binary tarball. The lib directory is very large and not needed
# for running the compiler. TARBALL_EXTRA_BIN can be used to bundle z3.
tarball: sail libsail_coverage
	dune install --relocatable --prefix=_build/tarball/sail
	rm -rf _build/tarball/sail/lib
	cp LICENSE _build/tarball/sail
	cp THIRD_PARTY_FILES.md _build/tarball/sail
	cp -a etc/tarball_extra/. _build/tarball/sail
ifdef TARBALL_EXTRA_BIN
	cp $(TARBALL_EXTRA_BIN) _build/tarball/sail/bin/
endif
	cp lib/coverage/libsail_coverage.a _build/tarball/sail/share/sail/lib/coverage/
	tar czvf _build/sail-$(shell uname -s)-$(shell uname -m).tar.gz -C _build/tarball sail

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
