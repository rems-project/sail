HAVE_OPAM_BBV=$(shell if opam config var coq-bbv:share >/dev/null 2>/dev/null; then echo yes; else echo no; fi)

ifeq ($(HAVE_OPAM_BBV),no)
BBV_DIR?=../../../bbv/src/bbv
endif

CORESRC=Prompt_monad.v  Prompt.v  Impl_base.v  Instr_kinds.v  Operators_bitlists.v  Operators_mwords.v  Operators.v  Values.v  State_monad.v  State.v  State_lifting.v  String.v  Real.v  Base.v
PROOFSRC=Values_lemmas.v State_monad_lemmas.v State_lemmas.v Hoare.v
SRC=$(CORESRC) $(PROOFSRC)

ifdef BBV_DIR
COQ_LIBS = -Q . Sail -Q "$(BBV_DIR)" bbv
else
COQ_LIBS = -Q . Sail
endif

TARGETS=$(SRC:.v=.vo)

.PHONY: all clean install

all: $(TARGETS)
clean:
	rm -f -- $(TARGETS) $(TARGETS:.vo=.glob) $(TARGETS:%.vo=.%.aux) deps

$(TARGETS): %.vo: %.v
	coqc $(COQ_LIBS) $<

deps: $(SRC)
	coqdep $(COQ_LIBS) $(SRC) > deps

-include deps

COQLIB = $(shell coqc -where)
DESTDIR ?=
INSTALLDIR = $(DESTDIR)/$(COQLIB)/user-contrib/Sail

install: $(TARGETS)
	test -d "$(DESTDIR)/$(COQLIB)/user-contrib" || echo Coq library directory "$(DESTDIR)/$(COQLIB)/user-contrib" not present
	install -d -- "$(INSTALLDIR)"
	install -m 644 -- $(SRC) $(TARGETS) $(TARGETS:.vo=.glob) "$(INSTALLDIR)"
