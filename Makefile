.PHONY: all sail language clean archs

all: sail interpreter

apply_header:
	$(MAKE) clean
	headache -c etc/headache_config -h etc/mips_header `ls mips/*.sail`
	headache -c etc/headache_config -h etc/mips_header `ls cheri/*.sail`
	headache -c etc/headache_config -h src/LICENCE `ls src/*.{ml,mli,nll,mly}`
	headache -c etc/headache_config -h src/LICENCE `ls src/lem_interp*.{ml,mli,lem}`
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
