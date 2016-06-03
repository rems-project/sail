BUILDDIR=./build

SAIL=../sail
ifeq ("$(wildcard $(SAIL))","")
  $(warning can not find Sail)
endif

LEM=../../lem/lem
ifeq ("$(wildcard $(LEM))","")
  $(warning can not find Lem)
endif

LEMINTERPDIR=../src/lem_interp/

# the order of the files is important
SOURCES=armv8.h.sail\
  armv8_A64_sys_regs.sail\
  armv8_A64_special_purpose_regs.sail\
  armv8_A32_sys_regs.sail\
  armv8_pstate.sail\
  armv8_lib.h.sail\
  armv8_common_lib.sail\
  armv8_A64_lib.sail\
  armv8.sail

all: $(BUILDDIR)/armv8.ml

clean:
	rm -rf $(BUILDDIR)

.PHONY: all clean

$(BUILDDIR):
	mkdir -p $@

$(BUILDDIR)/armv8.lem: $(SOURCES) | $(BUILDDIR)
	$(SAIL) -lem_ast $(SOURCES) -o $(basename $@)
#	sail generates the .lem file in pwd
	mv $(notdir $@) $@

$(BUILDDIR)/armv8.ml: $(BUILDDIR)/armv8.lem
	$(LEM) -ocaml -lib $(LEMINTERPDIR) $<

######################################################################
ETCDIR=../etc
SAIL_FILES=$(wildcard *.sail)

apply_header:
	headache -c $(ETCDIR)/headache_config -h $(ETCDIR)/arm_header $(SAIL_FILES)

.PHONY: apply_header
