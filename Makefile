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

test_power_interactive:
	$(MAKE) -C src test_power_interactive

clean:
	$(MAKE) -C src clean
