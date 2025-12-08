.PHONY: all isail sail install coverage clean asciidoc docker test core-tests c-tests extraction

all: sail

isail: sail

sail:
	dune build --release

install: sail
	dune install

libsail_coverage:
	$(MAKE) -C lib/coverage

# TODO: Make this work on Windows.
extraction:
	$(MAKE) -C src/lib/rocq
	mv src/lib/rocq/*.mli src/lib/extraction
	mv src/lib/rocq/*.ml src/lib/extraction

# Build binary tarball. The lib directory is very large and not needed
# for running the compiler. Z3_EXE can be used to bundle a z3 binary.
# GMP_DLL can be used to bundle a libgmp DLL (this is only used on Windows currently).
tarball: sail libsail_coverage
	dune install --relocatable --prefix=_build/tarball/sail
	dune exec -- sail_maker tarball --prefix=_build/tarball/sail --z3=$(Z3_EXE) --gmp=$(GMP_DLL)
ifeq ($(OS),Windows_NT)
	powershell Compress-Archive -Path "_build/tarball/sail" -DestinationPath "_build/sail-Windows-$(PROCESSOR_ARCHITECTURE).zip" -Force
else
	tar czvf _build/sail-$(shell uname -s)-$(shell uname -m).tar.gz -C _build/tarball sail
endif

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
