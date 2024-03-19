SYNTAX_FILE=theories/Autosubst2/syntax.v

coq: CoqMakefile $(SYNTAX_FILE)
	$(MAKE) -f CoqMakefile

$(SYNTAX_FILE) : syntax.sig
	as2-exe -i syntax.sig -p UCoq > $(SYNTAX_FILE)
	perl -i -pe 's/^(Hint|Instance)/#[export]$1/' $(SYNTAX_FILE)

.PHONY: clean
clean: CoqMakefile
	rm -f $(SYNTAX_FILE)
	$(MAKE) -f CoqMakefile clean
