.PHONY: all sail language clean archs

all: sail

apply_header:
	headache -c etc/headache_config -h etc/mips_header `ls mips/*.sail`
	headache -c etc/headache_config -h etc/mips_header `ls cheri/*.sail`
	$(MAKE) -C arm apply_header

sail:
	$(MAKE) -C src
	ln -f -s src/sail.native sail

language:
	$(MAKE) -C language

interpreter: 
	$(MAKE) -C src interpreter

clean:
	for subdir in src arm ; do\
	  $(MAKE) -C "$$subdir" clean;\
	done
	rm sail

archs:
	for arch in arm mips cheri; do\
	  $(MAKE) -C "$$arch" || exit;\
	done
