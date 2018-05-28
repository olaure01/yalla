$(MYLIBSDIR)/AFC.vo: $(MYLIBSDIR)/AFC.v
$(MYLIBSDIR)/Bool_more.vo: $(MYLIBSDIR)/Bool_more.v
$(MYLIBSDIR)/CPermutation_solve.vo: $(MYLIBSDIR)/CPermutation_solve.v $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/CyclicPerm.vo
$(MYLIBSDIR)/CyclicPerm.vo: $(MYLIBSDIR)/CyclicPerm.v $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/Permutation_more.vo
$(MYLIBSDIR)/fmsetlist.vo : $(MYLIBSDIR)/fmsetlist.v $(MYLIBSDIR)/Bool_more.vo $(MYLIBSDIR)/Injective.vo
$(MYLIBSDIR)/fmsetoidlist.vo : $(MYLIBSDIR)/fmsetlist.v
$(MYLIBSDIR)/genperm.vo: $(MYLIBSDIR)/genperm.v $(MYLIBSDIR)/Permutation_more.vo $(MYLIBSDIR)/Permutation_solve.vo $(MYLIBSDIR)/CyclicPerm.vo $(MYLIBSDIR)/CPermutation_solve.vo $(MYLIBSDIR)/Injective.vo
$(MYLIBSDIR)/Injective.vo: $(MYLIBSDIR)/Injective.v $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/Permutation_more.vo
$(MYLIBSDIR)/Surjective.vo: $(MYLIBSDIR)/Surjective.v
$(MYLIBSDIR)/List_more.vo: $(MYLIBSDIR)/List_more.v
$(MYLIBSDIR)/Permutation_more.vo: $(MYLIBSDIR)/Permutation_more.v $(MYLIBSDIR)/List_more.vo
$(MYLIBSDIR)/Permutation_solve.vo: $(MYLIBSDIR)/Permutation_solve.v $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/Permutation_more.vo
$(MYLIBSDIR)/nattree.vo : $(MYLIBSDIR)/nattree.v $(MYLIBSDIR)/Injective.vo $(MYLIBSDIR)/Surjective.vo
$(MYLIBSDIR)/wf_prod.vo: $(MYLIBSDIR)/wf_prod.v
