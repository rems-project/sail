.PHONY: all sail language clean power test

all: sail

sail:
	$(MAKE) -C src
	ln -f -s src/sail.native sail

language:
	$(MAKE) -C language

interpreter: 
	$(MAKE) -C src interpreter

clean:
	$(MAKE) -C src clean
	rm sail
