.PHONY: all sail language clean power test

all: sail interpreter language

sail: language
	$(MAKE) -C src

language:
	$(MAKE) -C language

interpreter: 
	$(MAKE) -C src interpreter

test: 
	$(MAKE) -C src test

power: 
	$(MAKE) -C src power

test_power_interactive:
	$(MAKE) -C src test_power_interactive

clean:
	$(MAKE) -C src clean
