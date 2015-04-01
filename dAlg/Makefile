#-----------------------------------------------------------------------------
# Programs
#-----------------------------------------------------------------------------
LHS2TEX     := lhs2TeX
PDFLATEX    := pdflatex
LATEX       := latex
BIBTEX      := bibtex
GHCI        := ghci


#-----------------------------------------------------------------------------
# Directories and source files
#-----------------------------------------------------------------------------
MAIN        := mrm
MAINTECH    := mrm_techmemo
SRCDIR      := sections
LHSFILES    := $(wildcard $(SRCDIR)/*.lhs)
TEXFILES    := $(wildcard $(SRCDIR)/*.tex)

#-----------------------------------------------------------------------------
# Flags
#-----------------------------------------------------------------------------
GHCFLAGS      := -Wall -O
LHS2TEX_FLAGS := --poly
SPELL         := ispell -d british -t -l -p

all: $(MAIN).pdf
supplement: $(SRCDIR)/Supplement.pdf

# $(MAINTECH).pdf

#-----------------------------------------------------------------------------
# Pattern rules
#-----------------------------------------------------------------------------

$(MAINTECH).pdf: $(MAINTECH).tex lhs $(TEXFILES) force
	$(PDFLATEX) $<
	if grep -s '^LaTeX Warning: Citation' $(<:.tex=.log); \
	then $(BIBTEX) $(<:.tex=); $(PDFLATEX) $(<); \
	fi
	while grep -s "Warning.*Rerun" $(<:.tex=.log); \
	  do $(PDFLATEX) $<; done;

%.tex : %.lhs force
	[ $(<) ] && ($(LHS2TEX) $(LHS2TEX_FLAGS) $< > $@ || rm -f $@)

#-----------------------------------------------------------------------------
# Rules
#-----------------------------------------------------------------------------

$(MAIN).pdf: $(MAIN).tex lhs $(TEXFILES) force
	$(PDFLATEX) $(<)
	if grep -s '^LaTeX Warning: Citation' $(<:.tex=.log); \
	then $(BIBTEX) $(<:.tex=); $(LATEX) $(<); \
	fi
	while grep -s "Warning.*Rerun" $(<:.tex=.log); \
	  do $(PDFLATEX) $<; done;

$(SRCDIR)/Supplement.pdf: $(SRCDIR)/Supplement.tex lhs $(TEXFILES) 
	$(PDFLATEX) $(<)
	if grep -s '^LaTeX Warning: Citation' $(<:.tex=.log); \
	then $(BIBTEX) $(<:.tex=); $(LATEX) $(<); \
	fi
	while grep -s "Warning.*Rerun" $(<:.tex=.log); \
	  do $(PDFLATEX) $<; done;

lhs: $(LHSFILES:.lhs=.tex)

ghci: $(file).lhs
	ghci $(file).lhs

spell: $(file).tex
	egrep -v '$\%' $(file).tex | $(spell) $(file).spell | sort | uniq

force:

clean:
	rm -vf $(LHSFILES:.lhs=.tex)
	rm -vf *.pdf
	rm -vf *.dvi
	rm -vf *.aux *.log *.bbl *.blg *.ptb
	rm -rfv auto _region_.tex

.PHONY: ghci spell force clean

