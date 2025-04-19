SYNTAX_FILE=theories/Autosubst2/syntax.v theories/Autosubst2/core.v theories/Autosubst2/unscoped.v
COQMAKEFILE=CoqMakefile

theories: $(COQMAKEFILE) FORCE
	$(MAKE) -f $(COQMAKEFILE)

$(COQMAKEFILE) : $(SYNTAX_FILE)
	$(COQBIN)coq_makefile -f _CoqProject -o $(COQMAKEFILE)

install: $(COQMAKEFILE)
	$(MAKE) -f $^ install

uninstall: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) uninstall

$(SYNTAX_FILE) : syntax.sig
	autosubst -f -v ge813 -s ucoq -o theories/Autosubst2/syntax.v syntax.sig

.PHONY: clean FORCE
clean:
	test ! -f $(COQMAKEFILE) || ( $(MAKE) -f $(COQMAKEFILE) clean && rm $(COQMAKEFILE) )
	rm -f $(SYNTAX_FILE)

FORCE:
