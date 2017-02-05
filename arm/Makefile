BUILDDIR=./build

SAIL=../sail -verbose
ifeq ("$(wildcard $(SAIL))","")
  $(warning can not find Sail)
endif

LEM=../../lem/lem
ifeq ("$(wildcard $(LEM))","")
  $(warning can not find Lem)
endif

LEMINTERPDIR=../src/lem_interp/

# the order of the files is important
SOURCES=armV8.h.sail\
  armV8_A64_sys_regs.sail\
  armV8_A64_special_purpose_regs.sail\
  armV8_A32_sys_regs.sail\
  armV8_pstate.sail\
  armV8_lib.h.sail\
  armV8_common_lib.sail\
  armV8_A64_lib.sail\
  armV8.sail

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

apply_header:
	-chmod u+w *.sail
	headache -c $(ETCDIR)/headache_config -h $(ETCDIR)/arm_header *.sail
	chmod a-w *.sail

.PHONY: apply_header

######################################################################
IDLARM=../../../rsem/idlarm

pull_from_idlarm:
	svn up $(IDLARM)
	$(MAKE) -C $(IDLARM)
	-chmod u+w *.sail
	rm -f *.sail
	cp -a $(IDLARM)/build/*.sail ./
	chmod a-w *.sail
	$(MAKE) apply_header
