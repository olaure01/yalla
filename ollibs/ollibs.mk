$(OLLIBSDIR)/AFC.vo: $(OLLIBSDIR)/Vector_more.vo $(OLLIBSDIR)/AFC.v
$(OLLIBSDIR)/Bool_more.vo: $(OLLIBSDIR)/Bool_more.v $(OLLIBSDIR)/List_Type.vo
$(OLLIBSDIR)/CPermutation_solve.vo: $(OLLIBSDIR)/CPermutation_solve.v $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/CyclicPerm.vo
$(OLLIBSDIR)/CyclicPerm.vo: $(OLLIBSDIR)/CyclicPerm.v $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/Permutation_more.vo
$(OLLIBSDIR)/fmsetlist.vo : $(OLLIBSDIR)/fmsetlist.v $(OLLIBSDIR)/Bool_more.vo $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/Permutation_more.vo
$(OLLIBSDIR)/fmsetoidlist.vo : $(OLLIBSDIR)/fmsetoidlist.v
$(OLLIBSDIR)/genperm.vo: $(OLLIBSDIR)/genperm.v $(OLLIBSDIR)/Permutation_more.vo $(OLLIBSDIR)/Permutation_solve.vo $(OLLIBSDIR)/CyclicPerm.vo $(OLLIBSDIR)/CPermutation_solve.vo $(OLLIBSDIR)/Injective.vo
$(OLLIBSDIR)/Injective.vo: $(OLLIBSDIR)/Injective.v $(OLLIBSDIR)/List_more.vo
$(OLLIBSDIR)/Surjective.vo: $(OLLIBSDIR)/Surjective.v
$(OLLIBSDIR)/List_more.vo: $(OLLIBSDIR)/List_more.v
$(OLLIBSDIR)/Permutation_more.vo: $(OLLIBSDIR)/Permutation_more.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/List_more.vo
$(OLLIBSDIR)/Permutation_solve.vo: $(OLLIBSDIR)/Permutation_solve.v $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/Permutation_more.vo
$(OLLIBSDIR)/nattree.vo : $(OLLIBSDIR)/nattree.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/Surjective.vo
$(OLLIBSDIR)/Vector_more.vo: $(OLLIBSDIR)/Vector_more.v
$(OLLIBSDIR)/wf_nat_more.vo: $(OLLIBSDIR)/wf_nat_more.v
$(OLLIBSDIR)/wf_prod.vo: $(OLLIBSDIR)/wf_prod.v

$(OLLIBSDIR)/List_Type.vo: $(OLLIBSDIR)/List_Type.v
$(OLLIBSDIR)/List_Type_more.vo: $(OLLIBSDIR)/List_Type_more.v $(OLLIBSDIR)/List_Type.vo 
$(OLLIBSDIR)/CyclicPerm_Type.vo: $(OLLIBSDIR)/CyclicPerm_Type.v $(OLLIBSDIR)/List_Type.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo
$(OLLIBSDIR)/flat_map_Type_more.vo: $(OLLIBSDIR)/flat_map_Type_more.v $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/CyclicPerm_Type.vo
$(OLLIBSDIR)/genperm_Type.vo: $(OLLIBSDIR)/genperm_Type.v $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/CyclicPerm_Type.vo $(OLLIBSDIR)/Permutation_Type_solve.vo $(OLLIBSDIR)/CPermutation_Type_solve.vo $(OLLIBSDIR)/Injective.vo
$(OLLIBSDIR)/Permutation_Type.vo: $(OLLIBSDIR)/Permutation_Type_more.v $(OLLIBSDIR)/List_Type.vo
$(OLLIBSDIR)/Permutation_Type_more.vo: $(OLLIBSDIR)/Permutation_Type_more.v $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/List_Type.vo $(OLLIBSDIR)/List_Type_more.vo $(OLLIBSDIR)/Permutation_more.vo $(OLLIBSDIR)/Permutation_Type.vo
$(OLLIBSDIR)/Permutation_Type_solve.vo: $(OLLIBSDIR)/Permutation_Type_solve.v $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/Permutation_Type.vo $(OLLIBSDIR)/Permutation_Type_more.vo
$(OLLIBSDIR)/CPermutation_Type_solve.vo: $(OLLIBSDIR)/CPermutation_Type_solve.v $(OLLIBSDIR)/List_more.vo $(OLLIBSDIR)/CyclicPerm_Type.vo
$(OLLIBSDIR)/fmsetlist_Type.vo : $(OLLIBSDIR)/fmsetlist_Type.v $(OLLIBSDIR)/Bool_more.vo $(OLLIBSDIR)/Injective.vo $(OLLIBSDIR)/Permutation_Type_more.vo $(OLLIBSDIR)/COrders.vo
$(OLLIBSDIR)/fmsetoidlist_Type.vo : $(OLLIBSDIR)/fmsetoidlist_Type.v $(OLLIBSDIR)/Permutation_Type.vo
$(OLLIBSDIR)/CEqualities.vo : $(OLLIBSDIR)/CEqualities.v
$(OLLIBSDIR)/COrders.vo : $(OLLIBSDIR)/COrders.v $(OLLIBSDIR)/CEqualities.vo
$(OLLIBSDIR)/Dependent_Forall_Type.vo : $(OLLIBSDIR)/Dependent_Forall_Type.v $(OLLIBSDIR)/List_Type_more.vo

