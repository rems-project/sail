.PHONY: all sail language clean archs apply_header

all: sail interpreter

sail:
	$(MAKE) -C src
	ln -f -s src/sail.native sail

language:
	$(MAKE) -C language

interpreter: 
	$(MAKE) -C src interpreter

archs:
	for arch in arm mips cheri; do\
	  $(MAKE) -C "$$arch" || exit;\
	done

apply_header:
	$(MAKE) clean
	headache -c etc/headache_config -h etc/mips_header `ls mips/*.sail`
	headache -c etc/headache_config -h etc/mips_header `ls cheri/*.sail`
	headache -c etc/headache_config -h src/LICENCE `ls src/Makefile*`
	headache -c etc/headache_config -h src/LICENCE `ls src/*.ml*`
	headache -c etc/headache_config -h src/LICENCE `ls src/lem_interp/*.ml`
	headache -c etc/headache_config -h src/LICENCE `ls src/lem_interp/*.lem`
	$(MAKE) -C arm apply_header

clean:
	for subdir in src arm ; do\
	  $(MAKE) -C "$$subdir" clean;\
	done
	-rm sail

