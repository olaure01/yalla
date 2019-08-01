
COQ = coqc -R $(OLLIBSDIR) "" -R $(YALLADIR) ""
COQDOC = coqdoc -g

VFILES = $(wildcard *.v)

%.vo: %.v
	$(COQ) $<

%.glob: %.vo
	@true

%.html: %.v %.vo
	$(COQDOC) $<


doc: $(VFILES:.v=.glob)
	$(COQDOC) -toc $(VFILES)

clean :
	rm -f $(VFILES:.v=.vo)
	rm -f .*.aux
	rm -f *.crashcoqide
	rm -f *.glob
	rm -f *.html
	rm -f coqdoc.css
	rm -f lia.cache
	rm -f .lia.cache

.PHONY: clean
.PRECIOUS: %.vo %.glob



OLLIBSDIR = ../ollibs
YALLADIR  = ../yalla

.DEFAULT_GOAL := microyalla

all: microyalla doc

microyalla: $(VFILES:.v=.vo)

nano_macro_ll.vo: nano_macro_ll.v $(OLLIBSDIR)/Permutation_Type.vo $(YALLADIR)/ll_def.vo nanoll.vo

nano_macro_ill.vo: nano_macro_ill.v $(OLLIBSDIR)/Permutation_Type.vo $(YALLADIR)/ill_def.vo nanoill.vo

micro_macro_ll.vo: micro_macro_ll.v $(OLLIBSDIR)/Permutation_Type.vo $(YALLADIR)/ll_def.vo microll.vo

micro_macro_ill.vo: micro_macro_ill.v $(OLLIBSDIR)/Permutation_Type.vo $(YALLADIR)/ill_def.vo microill.vo

transp_perm.vo : transp_perm.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/Permutation_Type.vo
