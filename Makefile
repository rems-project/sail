.PHONY: all src language

all: src language

src:
	$(MAKE) -C $@

language:
	$(MAKE) -C $@
