.PHONY: all sail language clean archs isabelle-lib apply_header

INSTALL_DIR ?= .
SHARE_DIR ?= $(INSTALL_DIR)

all: sail

sail:
	$(MAKE) -C src sail
	ln -f -s src/sail.native sail

isail:
	$(MAKE) -C src isail
	ln -f -s src/isail.native sail

install:
	mkdir -p $(INSTALL_DIR)/bin
	cp src/isail.native $(INSTALL_DIR)/bin/sail
	mkdir -p $(SHARE_DIR)
	cp -r lib $(SHARE_DIR)
	mkdir -p $(SHARE_DIR)/src
	cp src/elf_loader.ml $(SHARE_DIR)/src
	cp src/sail_lib.ml $(SHARE_DIR)/src

uninstall:
	rm -f $(INSTALL_DIR)/bin/sail
	rm -rf $(SHARE_DIR)

language:
	$(MAKE) -C language

interpreter:
	$(MAKE) -C src interpreter

archs:
	for arch in arm mips cheri; do\
	  $(MAKE) -C "$$arch" || exit;\
	done

isabelle-lib:
	$(MAKE) -C isabelle-lib

apply_header:
	$(MAKE) clean
	headache -c etc/headache_config -h etc/mips_header `ls mips/*.sail`
	headache -c etc/headache_config -h etc/mips_header `ls cheri/*.sail`
	headache -c etc/headache_config -h LICENCE `ls src/Makefile*`
	headache -c etc/headache_config -h LICENCE `ls src/*.ml*`
	headache -c etc/headache_config -h LICENCE `ls src/lem_interp/*.ml`
	headache -c etc/headache_config -h LICENCE `ls src/lem_interp/*.lem`
	$(MAKE) -C arm apply_header

clean:
	for subdir in src arm ; do\
	  $(MAKE) -C "$$subdir" clean;\
	done
	-rm sail
