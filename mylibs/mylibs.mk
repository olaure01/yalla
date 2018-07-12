$(MYLIBSDIR)/AFC.vo: $(MYLIBSDIR)/AFC.v
$(MYLIBSDIR)/Bool_more.vo: $(MYLIBSDIR)/Bool_more.v $(MYLIBSDIR)/List_Type.vo
$(MYLIBSDIR)/CPermutation_solve.vo: $(MYLIBSDIR)/CPermutation_solve.v $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/CyclicPerm.vo
$(MYLIBSDIR)/CyclicPerm.vo: $(MYLIBSDIR)/CyclicPerm.v $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/Permutation_more.vo
$(MYLIBSDIR)/fmsetlist.vo : $(MYLIBSDIR)/fmsetlist.v $(MYLIBSDIR)/Bool_more.vo $(MYLIBSDIR)/Injective.vo
$(MYLIBSDIR)/fmsetoidlist.vo : $(MYLIBSDIR)/fmsetoidlist.v
$(MYLIBSDIR)/genperm.vo: $(MYLIBSDIR)/genperm.v $(MYLIBSDIR)/Permutation_more.vo $(MYLIBSDIR)/Permutation_solve.vo $(MYLIBSDIR)/CyclicPerm.vo $(MYLIBSDIR)/CPermutation_solve.vo $(MYLIBSDIR)/Injective.vo
$(MYLIBSDIR)/Injective.vo: $(MYLIBSDIR)/Injective.v $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/Permutation_more.vo
$(MYLIBSDIR)/Surjective.vo: $(MYLIBSDIR)/Surjective.v
$(MYLIBSDIR)/List_more.vo: $(MYLIBSDIR)/List_more.v
$(MYLIBSDIR)/Permutation_more.vo: $(MYLIBSDIR)/Permutation_more.v $(MYLIBSDIR)/List_more.vo
$(MYLIBSDIR)/Permutation_solve.vo: $(MYLIBSDIR)/Permutation_solve.v $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/Permutation_more.vo
$(MYLIBSDIR)/nattree.vo : $(MYLIBSDIR)/nattree.v $(MYLIBSDIR)/Injective.vo $(MYLIBSDIR)/Surjective.vo
$(MYLIBSDIR)/wf_prod.vo: $(MYLIBSDIR)/wf_prod.v

$(MYLIBSDIR)/List_Type.vo: $(MYLIBSDIR)/List_Type.v
$(MYLIBSDIR)/List_Type_more.vo: $(MYLIBSDIR)/List_Type_more.v $(MYLIBSDIR)/List_Type.vo 
$(MYLIBSDIR)/CyclicPerm_Type.vo: $(MYLIBSDIR)/CyclicPerm_Type.v $(MYLIBSDIR)/List_Type.vo $(MYLIBSDIR)/List_Type_more.vo $(MYLIBSDIR)/Permutation_Type_more.vo
$(MYLIBSDIR)/genperm_Type.vo: $(MYLIBSDIR)/genperm_Type.v $(MYLIBSDIR)/Permutation_Type_more.vo $(MYLIBSDIR)/CyclicPerm_Type.vo $(MYLIBSDIR)/Permutation_Type_solve.vo $(MYLIBSDIR)/CPermutation_Type_solve.vo $(MYLIBSDIR)/Injective.vo
$(MYLIBSDIR)/Permutation_Type.vo: $(MYLIBSDIR)/Permutation_Type_more.v $(MYLIBSDIR)/List_Type.vo
$(MYLIBSDIR)/Permutation_Type_more.vo: $(MYLIBSDIR)/Permutation_Type_more.v $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/List_Type.vo $(MYLIBSDIR)/List_Type_more.vo $(MYLIBSDIR)/Permutation_more.vo $(MYLIBSDIR)/Permutation_Type.vo
$(MYLIBSDIR)/Permutation_Type_solve.vo: $(MYLIBSDIR)/Permutation_Type_solve.v $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/Permutation_Type.vo $(MYLIBSDIR)/Permutation_Type_more.vo
$(MYLIBSDIR)/CPermutation_Type_solve.vo: $(MYLIBSDIR)/CPermutation_Type_solve.v $(MYLIBSDIR)/List_more.vo $(MYLIBSDIR)/CyclicPerm_Type.vo
$(MYLIBSDIR)/fmsetlist_Type.vo : $(MYLIBSDIR)/fmsetlist_Type.v $(MYLIBSDIR)/Bool_more.vo $(MYLIBSDIR)/Injective.vo $(MYLIBSDIR)/Permutation_Type.vo $(MYLIBSDIR)/COrders.vo
$(MYLIBSDIR)/fmsetoidlist_Type.vo : $(MYLIBSDIR)/fmsetoidlist_Type.v $(MYLIBSDIR)/Permutation_Type.vo
$(MYLIBSDIR)/CEqualities.vo : $(MYLIBSDIR)/CEqualities.v
$(MYLIBSDIR)/COrders.vo : $(MYLIBSDIR)/COrders.v $(MYLIBSDIR)/CEqualities.vo

