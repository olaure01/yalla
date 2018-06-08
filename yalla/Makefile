
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
	rm -f .*.aux
	rm -f *.crashcoqide
	rm -f *.glob
	rm -f *.html
	rm -f coqdoc.css
	rm -f lia.cache
	rm -f .lia.cache

.PHONY: clean
.PRECIOUS: %.vo %.glob


MYLIBSDIR = ../mylibs

.DEFAULT_GOAL := all

all: cutelim

mylibs:
	cd $(MYLIBSDIR) && $(MAKE)

cutelim: mylibs $(VFILES:.v=.vo)

include $(MYLIBSDIR)/mylibs.mk

basic_tactics.vo: basic_tactics.v $(MYLIBSDIR)/Permutation_Type_solve.vo $(MYLIBSDIR)/genperm_Type.vo
flat_map_lemmas.vo : flat_map_lemmas.v $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/Permutation_more.vo $(MYLIBSDIR)/CyclicPerm.vo $(MYLIBSDIR)/Permutation_solve.vo $(MYLIBSDIR)/CPermutation_solve.vo $(MYLIBSDIR)/genperm.vo basic_tactics.vo

formulas.vo: formulas.v $(MYLIBSDIR)/Injective.vo $(MYLIBSDIR)/Bool_more.vo yalla_ax.vo
fmformulas.vo: fmformulas.v $(MYLIBSDIR)/Injective.vo $(MYLIBSDIR)/nattree.vo $(MYLIBSDIR)/fmsetlist.vo formulas.vo
ll_fragments.vo: ll_fragments.v $(MYLIBSDIR)/Permutation_more.vo $(MYLIBSDIR)/genperm_Type.vo ll.vo subs.vo
ll.vo: ll.v $(MYLIBSDIR)/Injective.vo $(MYLIBSDIR)/Bool_more.vo $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/List_Type_more.vo $(MYLIBSDIR)/Permutation_Type_more.vo $(MYLIBSDIR)/CyclicPerm_Type.vo $(MYLIBSDIR)/Permutation_Type_solve.vo $(MYLIBSDIR)/CPermutation_Type_solve.vo $(MYLIBSDIR)/genperm_Type.vo basic_tactics.vo formulas.vo # flat_map_lemmas.vo 
iformulas.vo: iformulas.v yalla_ax.vo
fmiformulas.vo: fmiformulas.v $(MYLIBSDIR)/Injective.vo $(MYLIBSDIR)/nattree.vo $(MYLIBSDIR)/fmsetlist.vo iformulas.vo
ill.vo: ill.v $(MYLIBSDIR)/Injective.vo $(MYLIBSDIR)/Bool_more.vo $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/Permutation_more.vo $(MYLIBSDIR)/CyclicPerm.vo $(MYLIBSDIR)/Permutation_solve.vo $(MYLIBSDIR)/CPermutation_solve.vo $(MYLIBSDIR)/genperm.vo ll.vo iformulas.vo ll_fragments.vo
subs.vo: subs.v $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/genperm.vo ll.vo
isubs.vo: isubs.v $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/genperm.vo basic_tactics.vo ill.vo

mell2.vo: mell2.v $(MYLIBSDIR)/Injective.vo $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/Permutation_more.vo $(MYLIBSDIR)/Permutation_solve.vo ll.vo ll_fragments.vo
mell_prop.vo: mell_prop.v $(MYLIBSDIR)/Injective.vo $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/Permutation_more.vo $(MYLIBSDIR)/Permutation_solve.vo ll.vo ll_fragments.vo
lambek.vo: lambek.v $(MYLIBSDIR)/Injective.vo $(MYLIBSDIR)/List_more.vo ill.vo
mell_mset.vo : mell_mset.v $(MYLIBSDIR)/Injective.vo $(MYLIBSDIR)/nattree.vo $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/Permutation_more.vo $(MYLIBSDIR)/fmsetlist.vo ll.vo ll_fragments.vo fmformulas.vo
mell_msetoid.vo : mell_msetoid.v $(MYLIBSDIR)/Injective.vo $(MYLIBSDIR)/fmsetoidlist.vo $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/Permutation_more.vo ll.vo
llpol.vo: llpol.v $(MYLIBSDIR)/Injective.vo $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/List_Type_more.vo $(MYLIBSDIR)/Permutation_Type.vo $(MYLIBSDIR)/Permutation_Type_more.vo $(MYLIBSDIR)/Permutation_Type_solve.vo ll.vo
llfoc.vo: llfoc.v $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/Permutation_more.vo $(MYLIBSDIR)/genperm.vo ll_fragments.vo
tl.vo: tl.v $(MYLIBSDIR)/Injective.vo $(MYLIBSDIR)/Bool_more.vo $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/genperm.vo ill.vo ll.vo

yalla_ax.vo: $(MYLIBSDIR)/Injective.vo yalla_ax.v

bbb.vo: bbb.v $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/Permutation_more.vo $(MYLIBSDIR)/Permutation_solve.vo $(MYLIBSDIR)/genperm.vo ll.vo ll_fragments.vo
nn.vo: nn.v $(MYLIBSDIR)/Injective.vo $(MYLIBSDIR)/Bool_more.vo $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/Permutation_more.vo $(MYLIBSDIR)/Permutation_solve.vo $(MYLIBSDIR)/genperm.vo subs.vo isubs.vo ll_fragments.vo bbb.vo
nnfoc.vo: nnfoc.v $(MYLIBSDIR)/Injective.vo $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/Permutation_more.vo $(MYLIBSDIR)/Permutation_solve.vo $(MYLIBSDIR)/genperm.vo basic_tactics.vo ll_fragments.vo ill.vo llfoc.vo tl.vo nn.vo


