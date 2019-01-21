LEM_ISA_LIB?=$(shell opam config var lem:share)/isabelle-lib
ifeq ($(wildcard $(LEM_ISA_LIB)/ROOT),)
$(error isabelle-lib directory of Lem not found. Please set the LEM_ISA_LIB environment variable)
endif

SAIL_ISA_LIB = ../../lib/isabelle
CHERI_DIR ?= ../../../sail-cheri-mips/cheri
AARCH64_DIR ?= ../../aarch64
TGTS = run_cheri.native run_aarch64.native
SESSION_DIRS = -d $(LEM_ISA_LIB) -d $(SAIL_ISA_LIB) -d $(CHERI_DIR) -d $(AARCH64_DIR) -d .

.PHONY: all clean

all: $(TGTS)

%.native: %.ml elf_loader.ml
	ocamlbuild -use-ocamlfind -pkg lem -pkg linksem -pkg num -pkg unix $@

run_cheri.native: cheri_export.ml
run_aarch64.native: aarch64_export.ml

cheri_export.ml: Cheri_code.thy
	make -C $(CHERI_DIR) Cheri.thy
	isabelle build -c $(SESSION_DIRS) Sail-CHERI-Code

aarch64_export.ml: Aarch64_code.thy
	make -C $(AARCH64_DIR) Aarch64.thy
	isabelle build -c $(SESSION_DIRS) Sail-AArch64-Code

clean:
	-ocamlbuild -clean
	-rm -f cheri_export.ml
	-rm -f aarch64_export.ml
