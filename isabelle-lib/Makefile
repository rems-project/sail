THYS = Sail_impl_base.thy Sail_values.thy State.thy Prompt.thy
LEMS = sail_impl_base.lem sail_values.lem state.lem prompt.lem

.PHONY: all heap-img clean

all: heap-img

heap-img: $(THYS)
	@echo '*** To build a heap image with the Sail library, please'
	@echo '*** add the ROOT file in this directory to your ROOTS file'
	@echo '*** (e.g. $$HOME/.isabelle/Isabelle<version>/ROOTS)'
	@echo '*** and add the isabelle binary to your PATH.'
	isabelle build -b Sail

Sail_impl_base.thy: sail_impl_base.lem
	lem -isa $<

Sail_values.thy: sail_values.lem Sail_impl_base.thy
	lem -isa $<

State.thy: state.lem Sail_values.thy
	lem -isa $<

Prompt.thy: prompt.lem Sail_values.thy
	lem -isa $<

sail_impl_base.lem: ../src/lem_interp/sail_impl_base.lem
	cp $< .

sail_values.lem: ../src/gen_lib/sail_values.lem
	cp $< .
	
state.lem: ../src/gen_lib/state.lem
	cp $< .

prompt.lem: ../src/gen_lib/prompt.lem
	cp $< .

clean:
	rm $(THYS) $(LEMS)
	rm *Auxiliary.thy
