
COQ = coqc -R $(MYLIBSDIR) ''
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

clean:
	rm -f $(VFILES:.v=.vo)
	rm -f *.glob
	rm -f *.html
	rm -f coqdoc.css
	rm -f lia.cache

.PHONY: clean
.PRECIOUS: %.vo %.glob


MYLIBSDIR = ../mylibs

.DEFAULT_GOAL := all

all: cutelim

mylibs:
	cd $(MYLIBSDIR) && $(MAKE)

cutelim: mylibs $(VFILES:.v=.vo)

include $(MYLIBSDIR)/mylibs.mk

basic_tactics.vo: basic_tactics.v $(MYLIBSDIR)/genperm.vo
flat_map_lemmas.vo : flat_map_lemmas.v $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/Permutation_more.vo $(MYLIBSDIR)/CyclicPerm.vo $(MYLIBSDIR)/Permutation_solve.vo $(MYLIBSDIR)/CPermutation_solve.vo $(MYLIBSDIR)/genperm.vo basic_tactics.vo

bbb.vo: bbb.v $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/Permutation_more.vo $(MYLIBSDIR)/Permutation_solve.vo $(MYLIBSDIR)/genperm.vo ll.vo ll_fragments.vo
formulas.vo: formulas.v $(MYLIBSDIR)/Injective.vo
fmformulas.vo: fmformulas.v $(MYLIBSDIR)/Injective.vo $(MYLIBSDIR)/nattree.vo $(MYLIBSDIR)/fmsetlist.vo formulas.vo
ll_fragments.vo: ll_fragments.v $(MYLIBSDIR)/Permutation_more.vo $(MYLIBSDIR)/genperm.vo ll.vo subs.vo
ll.vo: ll.v $(MYLIBSDIR)/Injective.vo $(MYLIBSDIR)/Bool_more.vo $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/Permutation_more.vo $(MYLIBSDIR)/CyclicPerm.vo $(MYLIBSDIR)/Permutation_solve.vo $(MYLIBSDIR)/CPermutation_solve.vo $(MYLIBSDIR)/genperm.vo basic_tactics.vo flat_map_lemmas.vo formulas.vo
iformulas.vo: iformulas.v $(MYLIBSDIR)/Bool_more.vo
fmiformulas.vo: fmformulas.v $(MYLIBSDIR)/Injective.vo $(MYLIBSDIR)/nattree.vo $(MYLIBSDIR)/fmsetlist.vo iformulas.vo
ill.vo: ill.v $(MYLIBSDIR)/Injective.vo $(MYLIBSDIR)/Bool_more.vo $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/Permutation_more.vo $(MYLIBSDIR)/CyclicPerm.vo $(MYLIBSDIR)/Permutation_solve.vo $(MYLIBSDIR)/CPermutation_solve.vo $(MYLIBSDIR)/genperm.vo ll.vo iformulas.vo
nn.vo: nn.v $(MYLIBSDIR)/Injective.vo $(MYLIBSDIR)/Bool_more.vo $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/Permutation_more.vo $(MYLIBSDIR)/genperm.vo ll.vo subs.vo ll_fragments.vo ill.vo bbb.vo
subs.vo: subs.v $(MYLIBSDIR)/genperm.vo ll.vo

mell2.vo: mell2.v $(MYLIBSDIR)/Injective.vo $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/Permutation_more.vo $(MYLIBSDIR)/Permutation_solve.vo ll.vo
lambek.vo: lambek.v $(MYLIBSDIR)/Injective.vo $(MYLIBSDIR)/List_more.vo ill.vo
mell_mset.vo : mell_mset.v $(MYLIBSDIR)/Injective.vo $(MYLIBSDIR)/nattree.vo $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/Permutation_more.vo $(MYLIBSDIR)/fmsetlist.vo ll.vo fmformulas.vo
mell_msetoid.vo : mell_msetoid.v $(MYLIBSDIR)/Injective.vo $(MYLIBSDIR)/Permutation_more.vo $(MYLIBSDIR)/fmsetoidlist.vo ll.vo
llpol.vo: llpol.v $(MYLIBSDIR)/Injective.vo $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/Permutation_more.vo $(MYLIBSDIR)/Permutation_solve.vo ll.vo

