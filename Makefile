SYNTAX_FILE=theories/Autosubst2/syntax.v
COQMAKEFILE=CoqMakefile

coq: $(COQMAKEFILE) $(SYNTAX_FILE)
	$(MAKE) -f $(COQMAKEFILE)

$(COQMAKEFILE) :
	$(COQBIN)coq_makefile -f _CoqProject -o $(COQMAKEFILE)

install: $(COQMAKEFILE) $(SYNTAX_FILE)
	$(MAKE) -f $(COQMAKEFILE) install

uninstall: $(COQMAKEFILE) $(SYNTAX_FILE)
	$(MAKE) -f $(COQMAKEFILE) uninstall

$(SYNTAX_FILE) : syntax.sig
	as2-exe -i syntax.sig -p UCoq > $(SYNTAX_FILE)
	perl -i -pe 's/^(Hint|Instance)/#[export]$1/' $(SYNTAX_FILE)

.PHONY: clean
clean:
	rm -f $(SYNTAX_FILE)
	test ! -f CoqSrc.mk || ( $(MAKE) -f $(COQMAKEFILE) clean && rm $(COQMAKEFILE) )
