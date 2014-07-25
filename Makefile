.PHONY: all src language clean

all: src language

src: language
	$(MAKE) -C $@

language:
	$(MAKE) -C $@

clean:
	$(MAKE) -C src clean
