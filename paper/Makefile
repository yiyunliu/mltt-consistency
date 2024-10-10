PDFLATEX = xelatex -shell-escape
LATEXRUN = ./latexrun --latex-cmd lualatex --latex-args="-jobname=paper -shell-escape" -o paper.pdf
BIBTEX = bibtex
OTT = ott
OTT_FLAGS := -tex_wrap false -tex_show_meta false -picky_multiple_parses false -merge true

all : paper-output.pdf

paper-output.tex: paper.tex rules.tex
	$(OTT) $(OTT_FLAGS) -i spec.ott -tex_filter paper.tex paper-output.tex
	perl -i -ne 'print unless m/^%/' paper-output.tex

paper-output.pdf : paper-output.tex refs.bib
	$(LATEXRUN) paper-output.tex

spec-out.pdf : spec-out.tex
	$(PDFLATEX) -interaction nonstopmode spec-out.tex

spec-out.tex : rules.tex spec.tex
	$(OTT) $(OTT_FLAGS) -i spec.ott -tex_filter spec.tex spec-out.tex

rules.tex : spec.ott
	$(OTT) $(OTT_FLAGS) -i spec.ott -o rules.tex

.POHNY: clean
clean:
	rm -if *.log *.aux *.out *~ *.bbl *.blg *.fdb_latexmk *.fls *.tex.tmp *.synctex.gz *.pdf rules.tex
