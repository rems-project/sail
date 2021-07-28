.PHONY: all sail language clean archs isabelle-lib apply_header docker

INSTALL_DIR ?= .

all: sail

sail:
	$(MAKE) -C src sail
	ln -f -s src/sail.native sail

isail:
	$(MAKE) -C src isail
	ln -f -s src/isail.native sail

coverage:
	$(MAKE) -C src coverage
	ln -f -s src/isail.native sail

install:
	if [ -z "$(SHARE_DIR)" ]; then echo SHARE_DIR is unset; false; fi
	mkdir -p $(INSTALL_DIR)/bin
	cp src/isail.native $(INSTALL_DIR)/bin/sail
	mkdir -p $(SHARE_DIR)
	make -C lib/isabelle all
	make -C lib/hol all-scripts
	cp -r lib $(SHARE_DIR)
	mkdir -p $(SHARE_DIR)/src
	cp src/elf_loader.ml $(SHARE_DIR)/src
	cp src/sail_lib.ml $(SHARE_DIR)/src
	cp src/util.ml $(SHARE_DIR)/src
	cp -r src/gen_lib $(SHARE_DIR)/src
	cp -r src/lem_interp $(SHARE_DIR)/src
	$(MAKE) install_libsail

install_libsail:
	-$(MAKE) uninstall_libsail
	ocamlfind install sail src/META src/_build/libsail.* $$(find src/_build \( -name '*.mli' -or -name '*.cmi' -or -name '*.cmx' \) -and -not -name 'myocamlbuild.*')

uninstall:
	if [ -z "$(SHARE_DIR)" ]; then echo SHARE_DIR is unset; false; else rm -rf $(SHARE_DIR); fi
	rm -f $(INSTALL_DIR)/bin/sail
	$(MAKE) uninstall_libsail

uninstall_libsail:
	ocamlfind remove sail

language:
	$(MAKE) -C language

interpreter:
	$(MAKE) -C src interpreter

apply_header:
	$(MAKE) clean
	headache -c etc/headache_config -h LICENCE `ls src/Makefile*`
	headache -c etc/headache_config -h LICENCE `ls src/*.ml` `ls src/*.mli`
	headache -c etc/headache_config -h LICENCE `ls src/*.mly` `ls src/*.mll`
	headache -c etc/headache_config -h LICENCE `ls src/*.lem`
	headache -c etc/headache_config -h LICENCE `ls src/lem_interp/*.ml`
	headache -c etc/headache_config -h LICENCE `ls src/lem_interp/*.lem`
	headache -c etc/headache_config -h LICENCE `ls src/jib/*.ml`
	headache -c etc/headache_config -h LICENCE `ls src/jib/*.mli`
	headache -c etc/headache_config -h LICENCE `ls lib/*.c` `ls lib/*.h`
	headache -c etc/headache_config -h LICENCE `ls lib/*.ml`
	headache -c etc/headache_config -h LICENCE `ls lib/*.sail`
	headache -c etc/headache_config -h LICENCE `ls lib/coq/*.v`

# If you want to use this you probably need to update the files it is applied to...
#anon_dist:
#	headache -c etc/headache_config -h etc/anon_header `ls lib/*.ml`
#	headache -c etc/headache_config -h etc/anon_header `ls lib/coq/*.v`
#	headache -c etc/headache_config -h etc/anon_header `ls src/Makefile*`
#	headache -c etc/headache_config -h etc/anon_header `ls src/*.ml*`
#	headache -c etc/headache_config -h etc/anon_header `ls src/*.lem`
#	headache -c etc/headache_config -h etc/anon_header `ls src/lem_interp/*.ml`
#	headache -c etc/headache_config -h etc/anon_header `ls src/lem_interp/*.lem`
#	headache -c etc/headache_config -h etc/anon_header `ls snapshots/isabelle/lib/sail/*.thy`
#	headache -c etc/headache_config -h etc/anon_header `ls snapshots/isabelle/lib/lem/*.thy`
#	headache -c etc/headache_config -h etc/anon_header `ls snapshots/hol4/lem/hol-lib/*.sml`

clean:
	for subdir in src ; do\
	  $(MAKE) -C "$$subdir" clean;\
	done
	rm -f sail

docker:
	docker build --tag sail:0.1 .
	@echo 'for example: docker run --volume `PWD`:/data/ sail:0.1 --help'
