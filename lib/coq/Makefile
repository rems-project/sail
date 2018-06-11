BBV_DIR=../../../bbv

SRC=Prompt_monad.v  Prompt.v  Sail_impl_base.v  Sail_instr_kinds.v  Sail_operators_bitlists.v  Sail_operators_mwords.v  Sail_operators.v  Sail_values.v  State_monad.v  State.v

COQ_LIBS = -R . Sail -R "$(BBV_DIR)" bbv

TARGETS=$(SRC:.v=.vo)

.PHONY: all clean *.ide

all: $(TARGETS)
clean:
	rm -f -- $(TARGETS) $(TARGETS:.vo=.glob) $(TARGETS:%.vo=.%.aux) deps

%.vo: %.v
	coqc $(COQ_LIBS) $<

%.ide: %.v
	coqide $(COQ_LIBS) $<

deps: $(SRC)
	coqdep $(COQ_LIBS) $(SRC) > deps

-include deps
