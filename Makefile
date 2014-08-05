.PHONY: all src language clean power test

all: src language

src: language
	$(MAKE) -C $@

language:
	$(MAKE) -C $@

test: 
	$(MAKE) -C src test

power: 
	$(MAKE) -C src power

clean:
	$(MAKE) -C src clean
