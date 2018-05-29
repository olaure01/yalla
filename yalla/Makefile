
COQ = coqc
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
	rm -f *.glob
	rm -f *.html
	rm -f coqdoc.css
	rm -f lia.cache
	rm -f .lia.cache

.PHONY: clean
.PRECIOUS: %.vo %.glob


.DEFAULT_GOAL := all

all: $(VFILES:.v=.vo)

Bool_more.vo: Bool_more.v
CPermutation_solve.vo: CPermutation_solve.v List_more.vo CyclicPerm.vo
CyclicPerm.vo: CyclicPerm.v List_more.vo Permutation_more.vo
genperm.vo: genperm.v Permutation_more.vo Permutation_solve.vo CyclicPerm.vo CPermutation_solve.vo Injective.vo
Injective.vo: Injective.v List_more.vo Permutation_more.vo
List_more.vo: List_more.v
Permutation_more.vo: Permutation_more.v List_more.vo
Permutation_solve.vo: Permutation_solve.v List_more.vo Permutation_more.vo

basic_tactics.vo: basic_tactics.v Permutation_solve.vo genperm.vo
flat_map_lemmas.vo : flat_map_lemmas.v List_more.vo Permutation_more.vo CyclicPerm.vo Permutation_solve.vo CPermutation_solve.vo genperm.vo basic_tactics.vo

formulas.vo: formulas.v Injective.vo yalla_ax.vo
ll_fragments.vo: ll_fragments.v Permutation_more.vo genperm.vo ll.vo subs.vo
ll.vo: ll.v Injective.vo Bool_more.vo List_more.vo Permutation_more.vo CyclicPerm.vo Permutation_solve.vo CPermutation_solve.vo genperm.vo basic_tactics.vo flat_map_lemmas.vo formulas.vo
iformulas.vo: iformulas.v yalla_ax.vo
ill.vo: ill.v Injective.vo Bool_more.vo List_more.vo Permutation_more.vo CyclicPerm.vo Permutation_solve.vo CPermutation_solve.vo genperm.vo ll.vo iformulas.vo ll_fragments.vo
subs.vo: subs.v List_more.vo genperm.vo ll.vo
isubs.vo: isubs.v List_more.vo genperm.vo basic_tactics.vo ill.vo

llfoc.vo: llfoc.v List_more.vo Permutation_more.vo genperm.vo ll_fragments.vo
tl.vo: tl.v Injective.vo Bool_more.vo List_more.vo genperm.vo ill.vo ll.vo

yalla_ax.vo: Injective.vo yalla_ax.v

bbb.vo: bbb.v List_more.vo Permutation_more.vo Permutation_solve.vo genperm.vo ll.vo ll_fragments.vo
nn.vo: nn.v Injective.vo Bool_more.vo List_more.vo Permutation_more.vo Permutation_solve.vo genperm.vo subs.vo isubs.vo ll_fragments.vo bbb.vo
nnfoc.vo: nnfoc.v Injective.vo List_more.vo Permutation_more.vo Permutation_solve.vo genperm.vo basic_tactics.vo ll_fragments.vo ill.vo llfoc.vo tl.vo nn.vo


