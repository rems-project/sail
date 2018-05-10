TEMPDIR:=sloc_tmp
loc: $(LOC_FILES)
	@rm -rf $(TEMPDIR)
	@mkdir -p $(TEMPDIR)
	@cp $^ $(TEMPDIR)
	@for f in $(TEMPDIR)/*.sail; do mv "$$f" "$${f%.sail}.c"; done
	@sloccount --details $(TEMPDIR) | grep ansic
	@sloccount $(TEMPDIR) | grep ansic
	rm -rf $(TEMPDIR)

cloc: $(LOC_FILES)
	cloc --by-file --force-lang C,sail $^

