SAIL:=../src/sail.native
LEM:=../../lem/lem

SOURCES:=power.sail ../lib/regfp.sail power_regfp.sail


all: power.lem power.ml power_embed.lem

power.lem: $(SOURCES)
	$(SAIL) -lem_ast -o power $(SOURCES)

power.ml: power.lem ../src/lem_interp/interp_ast.lem
	$(LEM) -ocaml -lib ../src/lem_interp/ $<


power_embed.lem: $(SOURCES)
# also generates power_embed_sequential.lem, power_embed_types.lem, power_toFromInterp.lem
	$(SAIL) -lem -lem_lib Power_extras_embed -o power $(SOURCES)

clean:
	rm -f power.lem power.ml
	rm -f power_embed*.lem power_toFromInterp.lem

######################################################################
ETCDIR=../etc

apply_header:
	headache -c $(ETCDIR)/headache_config -h $(ETCDIR)/power_header *.sail
.PHONY: apply_header

######################################################################
IDLPOWER=../../../rsem/idl/power

pull_from_idl:
	cp -a $(IDLPOWER)/generated/power.sail ./
# 	cp -a $(IDLPOWER)/generated/*.lem ./
# 	cp -a $(IDLPOWER)/generated/power.ml ./
# 	cp -a $(IDLPOWER)/generated/*.txt ./
	cp -a $(IDLPOWER)/extras/*.sail ./
	cp -a $(IDLPOWER)/extras/*.lem ./
	mkdir -p gen
	cp -a $(IDLPOWER)/generated/*.gen gen/
	cp -a $(IDLPOWER)/*.hgen gen/
	$(MAKE) apply_header
.PHONY: pull_from_idl
