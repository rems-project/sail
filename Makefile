.PHONY: all src language

all: src language

src: language
	$(MAKE) -C $@ update_lem_lib all

language:
	$(MAKE) -C $@
