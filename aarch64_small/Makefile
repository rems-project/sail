SAIL:=../src/sail.native
LEM:=../../lem/lem

default: armV8_embed.lem

# the order of the files is important
SOURCES=prelude.sail\
  armV8.h.sail\
  armV8_A64_sys_regs.sail\
  armV8_A64_special_purpose_regs.sail\
  armV8_A32_sys_regs.sail\
  armV8_pstate.sail\
  armV8_lib.h.sail\
  armV8_common_lib.sail\
  armV8_A64_lib.sail\
  armV8.sail

all: armV8.lem armV8.ml armV8_embed.lem

armV8.lem: $(SOURCES)
	$(SAIL) -lem_ast -o armV8 $(SOURCES)

armV8.ml: armV8.lem ../src/lem_interp/interp_ast.lem
	$(LEM) -ocaml -lib ../src/lem_interp/ $<


armV8_embed.lem: $(SOURCES) ../etc/regfp2.sail aarch64_regfp.sail
# also generates armV8_embed_sequential.lem, armV8_embed_types.lem, armV8_toFromInterp.lem
	$(SAIL) -lem -lem_lib ArmV8_extras_embed -o armV8 $^

clean:
	rm -f armV8.lem armV8.ml
	rm -f armV8_embed*.lem armV8_toFromInterp.lem

######################################################################
ETCDIR=../etc

apply_header:
	headache -c $(ETCDIR)/headache_config -h $(ETCDIR)/arm_header *.sail

.PHONY: apply_header

######################################################################
IDLARM=../../rsem/idlarm

pull_from_idlarm:
	$(MAKE) -C $(IDLARM) clean
	$(MAKE) -C $(IDLARM) san_sail
	rm -f *.sail
	cp -a $(IDLARM)/build/*.sail ./
	cp -a $(IDLARM)/armV8_extras_embed.lem ./
	cp -a $(IDLARM)/armV8_extras_embed_sequential.lem ./
	cp -a $(IDLARM)/armV8_extras.lem ./
	mkdir -p gen
	cp -a $(IDLARM)/*.hgen gen/
	$(MAKE) apply_header
