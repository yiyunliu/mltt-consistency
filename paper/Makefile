PDFLATEX = pdflatex -shell-escape
BIBTEX = bibtex
OTT = ott
OTT_FLAGS := -tex_wrap false -tex_show_meta false -picky_multiple_parses false -merge true

# all : paper-output.pdf

# paper-output.tex: Qualitative.ott Auxiliary.ott paper.tex Makefile Qualitative-rules.tex
#	$(OTT) $(OTT_FLAGS) -tex_filter paper.tex paper-output.tex
#	perl -i -ne 'print unless m/^%/' paper-output.tex

# paper-output.pdf : $(MAIN)-output.tex $(MAKEDEPS) $(LATEXDEPS)
#	$(PDFLATEX) $(MAIN)-output.tex
#	$(BIBTEX) $(MAIN)-output
#	$(PDFLATEX) $(MAIN)-output.tex
#	$(PDFLATEX) $(MAIN)-output.tex

spec-out.pdf : spec-out.tex
	pdflatex -interaction nonstopmode spec-out.tex

spec-out.tex : rules.tex spec.tex
	$(OTT) $(OTT_FLAGS) -i spec.ott -tex_filter spec.tex spec-out.tex

rules.tex : spec.ott
	$(OTT) $(OTT_FLAGS) -i spec.ott -o rules.tex

.POHNY: clean
clean:
	rm -if *.log *.aux *.out *~ *.bbl *.blg *.fdb_latexmk *.fls *.tex.tmp *.synctex.gz *.pdf rules.tex
