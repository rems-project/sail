.PHONY: all src language

all: src language

src: language
	$(MAKE) -C $@

language:
	$(MAKE) -C $@
