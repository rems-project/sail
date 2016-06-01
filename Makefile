.PHONY: all sail language clean power test

all: sail

apply_header:
	headache -c etc/headache_config -h etc/mips_header `ls mips/*.sail`
	headache -c etc/headache_config -h etc/mips_header `ls cheri/*.sail`

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
