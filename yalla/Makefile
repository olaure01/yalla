
COQ = coqc -R $(OLLIBSDIR) "" -R $(MICROYALLADIR) ""
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


OLLIBSDIR = ../ollibs

MICROYALLADIR = ../microyalla

.DEFAULT_GOAL := all

all: microyalla cutelim

ollibs:
	cd $(OLLIBSDIR) && $(MAKE)

microyalla:
	cd $(MICROYALLADIR) && $(MAKE)

cutelim: ollibs $(VFILES:.v=.vo)

include $(OLLIBSDIR)/ollibs.mk

basic_tactics.vo: basic_tactics.v $(OLLIBSDIR)/Permutation_Type_solve.vo $(OLLIBSDIR)/genperm_Type.vo

formulas.vo: formulas.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/Bool_more.vo yalla_ax.vo
fmformulas.vo: fmformulas.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/nattree.vo $(OLLIBSDIR)/fmsetlist_Type.vo formulas.vo
ll_mix.vo: ll_mix.v $(OLLIBSDIR)/Bool_more.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/Permutation_Type_solve.vo $(OLLIBSDIR)/genperm_Type.vo ll_def.vo ll_prop.vo
ll_fragments.vo: ll_fragments.v $(OLLIBSDIR)/Permutation_more.vo $(OLLIBSDIR)/genperm_Type.vo ll_prop.vo ll_mix.vo subs.vo
ll_def.vo: ll_def.v $(OLLIBSDIR)/Bool_more.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/CyclicPerm_Type.vo $(OLLIBSDIR)/Permutation_Type_solve.vo $(OLLIBSDIR)/CPermutation_Type_solve.vo $(OLLIBSDIR)/genperm_Type.vo basic_tactics.vo formulas.vo
ll_cut.vo: ll_cut.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/genperm_Type.vo $(OLLIBSDIR)/flat_map_Type_more.vo $(OLLIBSDIR)/wf_nat_more.vo ll_def.vo
ll_prop.vo: ll_prop.v $(OLLIBSDIR)/Bool_more.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/CyclicPerm_Type.vo $(OLLIBSDIR)/genperm_Type.vo ll_def.vo ll_cut.vo
iformulas.vo: iformulas.v $(OLLIBSDIR)/Bool_more.vo yalla_ax.vo
fmiformulas.vo: fmiformulas.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/nattree.vo $(OLLIBSDIR)/fmsetlist_Type.vo iformulas.vo
ill_def.vo: ill_def.v $(OLLIBSDIR)/Bool_more.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/genperm_Type.vo ll_def.vo iformulas.vo
ill_cut.vo: ill_cut.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/genperm_Type.vo $(OLLIBSDIR)/flat_map_Type_more.vo $(OLLIBSDIR)/wf_nat_more.vo basic_tactics.vo ill_def.vo
ill_prop.vo: ill_prop.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/Bool_more.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/Permutation_Type_solve.vo $(OLLIBSDIR)/CPermutation_Type_solve.vo $(OLLIBSDIR)/genperm_Type.vo ll_fragments.vo ill_cut.vo
subs.vo: subs.v $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/genperm.vo ll_def.vo
isubs.vo: isubs.v $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/genperm.vo basic_tactics.vo ill_def.vo

ll_smp.vo: ll_smp.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/Permutation_Type_solve.vo ll_fragments.vo $(MICROYALLADIR)/ll.vo
ill_smp.vo: ill_smp.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/Permutation_Type_solve.vo ill_cut.vo $(MICROYALLADIR)/ill.vo
mell2.vo: mell2.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/Permutation_Type_solve.vo ll_prop.vo
mell_Prop.vo: mell_Prop.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/Permutation_more.vo $(OLLIBSDIR)/Permutation_solve.vo ll_prop.vo
lambek.vo: lambek.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo ill_cut.vo
mell_mset.vo : mell_mset.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/nattree.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/Permutation_more.vo $(OLLIBSDIR)/fmsetlist.vo ll_prop.vo fmformulas.vo
mell_msetoid.vo : mell_msetoid.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/fmsetoidlist.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/Permutation_more.vo ll_prop.vo
llpol.vo: llpol.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/Permutation_Type_solve.vo ll_prop.vo
llfoc.vo: llfoc.v $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/Permutation_more.vo $(OLLIBSDIR)/genperm.vo ll_fragments.vo
tl.vo: tl.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/Bool_more.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/genperm.vo ill_prop.vo ll_def.vo

yalla_ax.vo: $(OLLIBSDIR)/Injective.vo yalla_ax.v

bbb.vo: bbb.v $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/Permutation_Type_solve.vo $(OLLIBSDIR)/genperm_Type.vo ll_mix.vo ll_fragments.vo
nn_def.vo: nn_def.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/Permutation_Type.vo $(OLLIBSDIR)/genperm_Type.vo subs.vo isubs.vo
nn_prop.vo: nn_prop.v $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type.vo $(OLLIBSDIR)/genperm_Type.vo subs.vo ll_fragments.vo ill_prop.vo nn_def.vo bbb.vo
nn_foc.vo: nn_foc.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/Permutation_Type_solve.vo $(OLLIBSDIR)/genperm_Type.vo basic_tactics.vo ll_fragments.vo ill_prop.vo llfoc.vo tl.vo nn_prop.vo


