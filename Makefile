SYNTAX_FILE=theories/Autosubst2/syntax.v
COQMAKEFILE=CoqMakefile

theories: $(COQMAKEFILE)
	$(MAKE) -f $^

$(COQMAKEFILE) : $(SYNTAX_FILE)
	$(COQBIN)coq_makefile -f _CoqProject -o $(COQMAKEFILE)

install: $(COQMAKEFILE)
	$(MAKE) -f $^ install

uninstall: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) uninstall

$(SYNTAX_FILE) : syntax.sig
	as2-exe -i syntax.sig -p UCoq > $(SYNTAX_FILE)
	perl -i -pe 's/^(Hint|Instance)/#[export]$1/' $(SYNTAX_FILE)

.PHONY: clean
clean:
	test ! -f $(COQMAKEFILE) || ( $(MAKE) -f $(COQMAKEFILE) clean && rm $(COQMAKEFILE) )
	rm -f $(SYNTAX_FILE)
