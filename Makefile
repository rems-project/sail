.PHONY: all isail sail install clean docker

all: sail

isail: sail

sail:
	dune build --release

install: sail
	dune install

clean:
	dune clean
	rm -f sail

docker:
	docker build --tag sail:0.1 .
	@echo 'for example: docker run --volume `PWD`:/data/ sail:0.1 --help'
