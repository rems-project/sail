SAIL:=../sail -Ofast_undefined
LEM:=../../lem/lem

default: all

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
  armV8.sail\
  ../lib/regfp.sail\
  aarch64_regfp.sail

all: armV8.lem for-rmem/armV8.lem for-rmem/armV8_toFromInterp2.ml for-rmem/armV8.defs

armV8.lem: $(SOURCES)
# also generates armV8_embed_sequential.lem, armV8_embed_types.lem, armV8_toFromInterp.lem
	$(SAIL) $(SAILFLAGS) -lem -lem_lib ArmV8_extras_embed -o armV8 $^

armV8.axiomatic_model: $(SOURCES)
	$(SAIL) $(SAILFLAGS) -axiomatic -o armV8 $^

for-rmem/armV8.lem: $(SOURCES)
	mkdir -p $(dir $@)
#	We do not need the isabelle .thy files, but sail always generates them
	$(SAIL) -lem -lem_lib ArmV8_extras_embed -lem_output_dir $(dir $@) -isa_output_dir $(dir $@) -o $(notdir $(basename $@)) $^

for-rmem/armV8_toFromInterp2.ml: $(SOURCES)
	mkdir -p $(dir $@)
	$(SAIL) -tofrominterp -tofrominterp_lem  -tofrominterp_output_dir $(dir $@) -o armV8 $^

for-rmem/armV8.defs: $(SOURCES)
	mkdir -p $(dir $@)
	$(SAIL) -marshal -o $(basename $@) $^

clean:
	rm -f armV8.lem armV8.ml
	rm -f armV8_embed*.lem armV8_toFromInterp.lem
	rm -f for-rmem/*

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
