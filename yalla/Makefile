
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

basic_misc.vo: basic_misc.v $(OLLIBSDIR)/Permutation_Type_solve.vo $(OLLIBSDIR)/genperm_Type.vo
yalla_ax.vo: yalla_ax.v $(OLLIBSDIR)/Injective.vo

formulas.vo: formulas.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/Bool_more.vo yalla_ax.vo
fmformulas.vo: fmformulas.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/nattree.vo $(OLLIBSDIR)/fmsetlist_Type.vo formulas.vo
ll_def.vo: ll_def.v $(OLLIBSDIR)/Bool_more.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/CyclicPerm_Type.vo $(OLLIBSDIR)/Permutation_Type_solve.vo $(OLLIBSDIR)/CPermutation_Type_solve.vo $(OLLIBSDIR)/genperm_Type.vo basic_misc.vo formulas.vo
subs.vo: subs.v $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/Permutation_Type.vo $(OLLIBSDIR)/genperm_Type.vo ll_def.vo
ll_cut.vo: ll_cut.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/genperm_Type.vo $(OLLIBSDIR)/flat_map_Type_more.vo $(OLLIBSDIR)/wf_nat_more.vo ll_def.vo
ll_prop.vo: ll_prop.v $(OLLIBSDIR)/Bool_more.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/CyclicPerm_Type.vo $(OLLIBSDIR)/genperm_Type.vo ll_cut.vo
ll_fragments.vo: ll_fragments.v $(OLLIBSDIR)/Bool_more.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/Permutation_Type_solve.vo $(OLLIBSDIR)/genperm_Type.vo ll_prop.vo subs.vo

iformulas.vo: iformulas.v $(OLLIBSDIR)/Bool_more.vo yalla_ax.vo
fmiformulas.vo: fmiformulas.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/nattree.vo $(OLLIBSDIR)/fmsetlist_Type.vo iformulas.vo
ill_def.vo: ill_def.v $(OLLIBSDIR)/Bool_more.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/genperm_Type.vo basic_misc.vo iformulas.vo
isubs.vo: isubs.v $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/Permutation_Type.vo $(OLLIBSDIR)/genperm_Type.vo ill_def.vo
ill_cut.vo: ill_cut.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/genperm_Type.vo $(OLLIBSDIR)/flat_map_Type_more.vo $(OLLIBSDIR)/wf_nat_more.vo ill_def.vo
ill_prop.vo: ill_prop.v $(OLLIBSDIR)/Bool_more.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/genperm_Type.vo ill_cut.vo
ill_vs_ll.vo: ill_vs_ll.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/Permutation_Type_solve.vo $(OLLIBSDIR)/genperm_Type.vo ll_fragments.vo ill_prop.vo

llfoc.vo: llfoc.v $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/Permutation_Type_solve.vo $(OLLIBSDIR)/genperm_Type.vo ll_fragments.vo
bbb.vo: bbb.v $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/Permutation_Type_solve.vo $(OLLIBSDIR)/genperm_Type.vo ll_fragments.vo
tl.vo: tl.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/Bool_more.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/genperm_Type.vo ill_vs_ll.vo ll_def.vo
nn_def.vo: nn_def.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/Permutation_Type.vo $(OLLIBSDIR)/genperm_Type.vo subs.vo isubs.vo ill_vs_ll.vo
nn_prop.vo: nn_prop.v $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type.vo $(OLLIBSDIR)/genperm_Type.vo subs.vo ll_fragments.vo nn_def.vo bbb.vo
nn_foc.vo: nn_foc.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/Permutation_Type_solve.vo $(OLLIBSDIR)/genperm_Type.vo ll_fragments.vo llfoc.vo tl.vo nn_prop.vo

ll_smp.vo: ll_smp.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/Permutation_Type_solve.vo ll_fragments.vo $(MICROYALLADIR)/ll.vo
ill_smp.vo: ill_smp.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/Permutation_Type_solve.vo ill_cut.vo $(MICROYALLADIR)/ill.vo
mell2.vo: mell2.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/Permutation_Type_solve.vo ll_cut.vo
mell_Prop.vo: mell_Prop.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/Permutation_more.vo $(OLLIBSDIR)/Permutation_solve.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/Permutation_Type_solve.vo ll_cut.vo
mell_mset.vo : mell_mset.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/nattree.vo $(OLLIBSDIR)/fmsetlist_Type.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo ll_cut.vo fmformulas.vo
mell_msetoid.vo : mell_msetoid.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/fmsetoidlist_Type.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo ll_cut.vo
llpol.vo: llpol.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/Permutation_Type_solve.vo ll_cut.vo
lambek.vo: lambek.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo ill_cut.vo
lj.vo: lj.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo  $(OLLIBSDIR)/Permutation_Type_solve.vo ill_prop.vo

Forall_Type_more2.vo: Forall_Type_more2.v $(OLLIBSDIR)/List_Type_more.vo
Dependent_Forall_Type.vo : Dependent_Forall_Type.v $(OLLIBSDIR)/List_Type_more.vo Forall_Type_more2.vo
concat_Type_more.vo : concat_Type_more.v Dependent_Forall_Type.vo basic_misc.vo $(OLLIBSDIR)/List_Type_more.vo
flat_map_Type_more_new.vo : flat_map_Type_more_new.v $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/CyclicPerm_Type.vo $(OLLIBSDIR)/Injective.vo



