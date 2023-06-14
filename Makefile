.PHONY: all isail sail install coverage clean docker test core-tests c-tests

all: sail

isail: sail

sail:
	dune build --release

install: sail
	dune install

coverage:
	dune build --release --instrument-with bisect_ppx

clean:
	dune clean

docker:
	docker build --tag sail:0.1 .
	@echo 'for example: docker run --volume `PWD`:/data/ sail:0.1 --help'

test:
	SAIL_DIR=`pwd` SAIL=`pwd`/sail test/run_tests.sh

core-tests:
	SAIL_DIR=`pwd` SAIL=`pwd`/sail test/run_core_tests.sh

c-tests:
	SAIL_DIR=`pwd` SAIL=`pwd`/sail test/c/run_tests.py
