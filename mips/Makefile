BITBUCKETDIR= ~/bitbucket
SAILDIR=$(BITBUCKETDIR)/l2/
SAIL=$(SAILDIR)/src/_build/sail.native
BUILDDIR=./build/
LEMDIR=$(BITBUCKETDIR)/lem/
LEM=$(LEMDIR)/lem

# we need bash to use PIPESTATUS for the error parsing
# (if bash is not found the build will still work)
ifneq ("$(wildcard /bin/bash)","")
SHELL=/bin/bash
endif


# the order of the files is important
MIPSSOURCES= mips.sail

all: $(BUILDDIR)mips.ml $(BUILDDIR)mips_extras.ml

lem: $(BUILDDIR)mips.lem

# this will force build everything, including the tools
full:
	$(MAKE) -B

test: $(BUILDDIR)/test.lem

### tools: these will run only if the tools don't already exist or with 'make full'

$(SAIL):
	$(MAKE) -C $(SAILDIR)

$(LEM):
	$(MAKE) -C $(LEMDIR)

### tools end

$(BUILDDIR):
	mkdir -p $@

$(BUILDDIR)mips.lem: $(MIPSSOURCES) $(SAIL) | $(BUILDDIR)
# if bash is detected we can print nicer errors
ifeq ($(SHELL),/bin/bash)
# 	the test at the end is so we return the exit code of sail and not parse_sail.sh
	$(SAIL) -lem_ast $(MIPSSOURCES) 2>&1 | ./parse_sail.sh; test "$${PIPESTATUS[0]}" -eq 0
else
	$(SAIL) -lem_ast $(MIPSSOURCES)
endif
#       sail uses the name of the first file on the list
	@mv $(<:.sail=.lem) $(BUILDDIR)mips.lem

$(BUILDDIR)mips.ml: $(BUILDDIR)mips.lem $(LEM)
	$(LEM) -ocaml -only_changed_output -lib $(SAILDIR)/src/lem_interp/ $<
# 	FIXME: lem bug, does not change modification time
	touch $@

$(BUILDDIR)mips_extras.ml: 
	cp mips_extras.lem $@
	$(LEM) -ocaml -only_changed_output -lib $(SAILDIR)/src/lem_interp/ $<
	touch $@

$(BUILDDIR)/test.lem: test.sail $(SAIL) | $(BUILDDIR)
# if bash is detected we can print nicer errors
ifeq ($(SHELL),/bin/bash)
# 	the test at the end is so we return the exit code of sail and not parse_sail.sh
	$(SAIL) -lem_ast test.sail 2>&1 | ./parse_sail.sh; test "$${PIPESTATUS[0]}" -eq 0
else
	$(SAIL) -lem_ast test.sail
endif

clean:
	rm -rf $(BUILDDIR)

.PHONY: all full clean test
