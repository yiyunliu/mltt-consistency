LIBNAME=WR

coq: CoqSrc.mk $(VFILES)
	$(MAKE) -f CoqSrc.mk

%.vo: %.v CoqSrc.mk
	$(MAKE) -f CoqSrc.mk $*.vo

vos:  CoqSrc.mk
	@$(MAKE) -f CoqSrc.mk vos

%.vos:  %.v CoqSrc.mk
	@$(MAKE) -f CoqSrc.mk $*.vos

syntax.v : syntax.sig gen_syntax.pl
	as2-exe -i syntax.sig -p UCoq > syntax.v
	perl gen_syntax.pl


_CoqProject : syntax.v *.v
	{ echo "-R . $(LIBNAME) " ; ls *.v ; } > _CoqProject

CoqSrc.mk: _CoqProject
	 coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module' -f _CoqProject -o CoqSrc.mk

.PHONY: clean
clean:
	rm -f syntax.v
	$(MAKE) -f CoqSrc.mk clean
