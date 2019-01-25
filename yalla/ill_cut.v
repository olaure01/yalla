(* ill library for yalla *)


(** * Intuitionistic Linear Logic *)
(* Cut admissibility, see ill_prop.v for other properties *)

Require Import Arith_base.
Require Import List.

Require Import Injective.
Require Import List_more.
Require Import List_Type_more.
Require Import Permutation_Type_more.
Require Import genperm_Type.
Require Import flat_map_Type_more.
Require Import wf_nat_more.

Require Export ill_def.


Section Cut_Elim_Proof.

Context {P : ipfrag}.

Hypothesis P_gax_noN_l : forall a, In N (fst (projT2 (ipgax P) a)) -> False.
Hypothesis P_gax_at_l : forall a, Forall iatomic (fst (projT2 (ipgax P) a)).
Hypothesis P_gax_at_r : forall a, iatomic (snd (projT2 (ipgax P) a)).
Hypothesis P_gax_cut : forall a b l1 l2,
                            fst (projT2 (ipgax P) b) = l1 ++ snd (projT2 (ipgax P) a) :: l2 -> 
                          { c | l1 ++ fst (projT2 (ipgax P) a) ++ l2 = fst (projT2 (ipgax P) c)
                                /\ snd (projT2 (ipgax P) b) = snd (projT2 (ipgax P) c) }.

Lemma cut_oc_comm_left : ipcut P = false -> forall n A C l1 l2, ill P (l1 ++ ioc A :: l2) C -> 
  (forall lw (pi0 : ill P (map ioc lw) A), ipsize pi0 < n -> ill P (l1 ++ map ioc lw ++ l2) C) ->
  forall l0 (pi1 : ill P l0 (ioc A)), ipsize pi1 <= n -> ill P (l1 ++ l0 ++ l2) C.
Proof with myeasy_perm_Type.
intros P_cutfree n A C l1 l2 pi2 ; induction n ; intros IH l0 pi1 Hs ;
  remember (ioc A) as B ; destruct_ill pi1 f X l Hl Hr HP a ;
  try (exfalso ; simpl in Hs ; clear -Hs ; myeasy ; fail) ; try inversion HeqB.
- apply (ex_ir _ (l1 ++ l ++ l2)).
  + simpl in Hs.
    refine (IHn _ _ Hl _)...
    intros ; refine (IH _ pi0 _)...
  + apply PEperm_Type_app_head ; apply PEperm_Type_app_tail...
- list_simpl ; rewrite app_assoc ; eapply ex_oc_ir...
  list_simpl ; rewrite (app_assoc l) ; rewrite (app_assoc _ l0) ; rewrite <- (app_assoc l).
  simpl in Hs ; refine (IHn _ _ Hl _)...
  intros ; refine (IH _ pi0 _)...
- list_simpl ; rewrite app_assoc ; apply one_ilr.
  list_simpl ; rewrite (app_assoc l0).
  simpl in Hs ; refine (IHn _ _ Hl _)...
  intros ; refine (IH _ pi0 _)...
- list_simpl ; rewrite app_assoc ; apply tens_ilr.
  list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l0).
  simpl in Hs ; refine (IHn _ _ Hl _)...
  intros ; refine (IH _ pi0 _)...
- list_simpl ; rewrite app_assoc ; apply lpam_ilr...
  list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l3).
  simpl in Hs ; refine (IHn _ _ Hr _)...
  intros ; refine (IH _ pi0 _)...
- list_simpl ; rewrite app_assoc ; apply lmap_ilr...
  list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l3).
  simpl in Hs ; refine (IHn _ _ Hr _)...
  intros ; refine (IH _ pi0 _)...
- list_simpl ; rewrite app_assoc ; apply with_ilr1.
  list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l0).
  simpl in Hs ; refine (IHn _ _ Hl _)...
  intros ; refine (IH _ pi0 _)...
- list_simpl ; rewrite app_assoc ; apply with_ilr2.
  list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l0).
  simpl in Hs ; refine (IHn _ _ Hl _)...
  intros ; refine (IH _ pi0 _)...
- list_simpl ; rewrite app_assoc ; apply zero_ilr.
- list_simpl ; rewrite app_assoc ; apply plus_ilr.
  + list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l0).
    simpl in Hs ; refine (IHn _ _ Hl _)...
    intros ; refine (IH _ pi0 _)...
  + list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l0).
    simpl in Hs ; refine (IHn _ _ Hr _)...
    intros ; refine (IH _ pi0 _)...
- subst ; apply (IH _ Hl)...
- list_simpl ; rewrite app_assoc ; apply de_ilr.
  list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l0).
  simpl in Hs ; refine (IHn _ _ Hl _)...
  intros ; refine (IH _ pi0 _)...
- list_simpl ; rewrite app_assoc ; apply wk_ilr.
  list_simpl ; rewrite (app_assoc l0).
  simpl in Hs ; refine (IHn _ _ Hl _)...
  intros ; refine (IH _ pi0 _)...
- list_simpl ; rewrite app_assoc ; apply co_ilr.
  list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l0).
  simpl in Hs ; refine (IHn _ _ Hl _)...
  intros ; refine (IH _ pi0 _)...
- rewrite f in P_cutfree ; inversion P_cutfree.
- exfalso ; assert (Hiq := P_gax_at_r a) ; rewrite H0 in Hiq ; inversion Hiq.
Qed.

Lemma substitution_ioc : ipcut P = false -> forall A,
  (forall l0 l1 l2 C, ill P l0 A -> ill P (l1 ++ A :: l2) C -> ill P (l1 ++ l0 ++ l2) C) ->
  forall lw l C, ill P (map ioc lw) A -> ill P l C -> forall l' L,
  l = l' ++ flat_map (cons (ioc A)) L -> ill P (l' ++ flat_map (app (map ioc lw)) L) C.
Proof with myeasy_perm_Type.
intros P_cutfree A IHcut lw l C pi1 pi2.
induction pi2 ; intros l' L Heq.
- destruct l' ; inversion Heq.
  + destruct L ; inversion Heq.
  + symmetry in H1 ; apply app_eq_nil in H1 ; destruct H1 ; subst.
    destruct L ; inversion H1.
    apply ax_ir.
- case_eq (ipperm P) ; intros Hperm ; rewrite Hperm in p ; simpl in p ; subst.
  + destruct (perm_Type_app_flat_map _ (map ioc lw) _ _ _ p) as [[L' l''] (Hnil' & HeqL' & HPL')] ;
      simpl in Hnil' ; simpl in HeqL' ; simpl in HPL' ; subst.
    eapply ex_ir ; [ | rewrite Hperm ; simpl ; apply HPL' ].
    refine (IHpi2 _ _ _)...
  + refine (IHpi2 _ _ _)...
- assert (injective ioc) as Hinj by (intros x y Hxy ; inversion Hxy ; reflexivity).
  destruct (perm_flat_map_cons_flat_map_app  _ ioc Hinj lw _ _ _ _ _ _ p Heq)
    as [(((lw1',lw2'),(l1',l2')),(l'',L')) HH] ; simpl in HH ; destruct HH as (H1 & H2 & H3 & H4).
  rewrite <- H4 ; apply (ex_oc_ir _ _ lw1')...
  rewrite H3 ; apply IHpi2...
- symmetry in Heq ; apply app_eq_nil in Heq ; destruct Heq as [H Heq] ; subst.
  destruct L ; inversion Heq.
  apply one_irr.
- elt_vs_app_flat_map_inv Heq.
  + list_simpl ; apply one_ilr.
    rewrite app_assoc ; refine (IHpi2 _ _ _) ; list_simpl...
  + rewrite flat_map_app.
    list_simpl ; rewrite 3 app_assoc ; apply one_ilr.
    rewrite <- 3 app_assoc.
    replace (map ioc lw ++ l ++ l0 ++ flat_map (app (map ioc lw)) L1)
       with (flat_map (app (map ioc lw)) ((l ++ l0) :: L1)) by (list_simpl ; reflexivity).
    rewrite <- flat_map_app ; refine (IHpi2 _ _ _)...
    rewrite ? flat_map_app ; list_simpl...
- app_vs_app_flat_map_inv Heq.
  + list_simpl ; apply tens_irr...
    refine (IHpi2_2 _ _ _)...
  + rewrite flat_map_app ; list_simpl.
    rewrite 3 app_assoc ; apply tens_irr...
    * list_simpl.
      replace (flat_map (app (map ioc lw)) L0 ++ map ioc lw ++ l)
         with (flat_map (app (map ioc lw)) (L0 ++ l :: nil))
        by (rewrite flat_map_app ; list_simpl ; reflexivity).
      refine (IHpi2_1 _ _ _)...
    * refine (IHpi2_2 _ _ _)...
  + rewrite flat_map_app ; list_simpl.
    rewrite app_assoc ; apply tens_irr...
    * refine (IHpi2_1 _ _ _)...
    * rewrite <- (app_nil_l _) ; refine (IHpi2_2 _ _ _)...
- elt_vs_app_flat_map_inv Heq.
  + list_simpl ; apply tens_ilr.
    rewrite 2 app_comm_cons ; rewrite app_assoc ; refine (IHpi2 _ _ _) ; list_simpl...
  + rewrite flat_map_app.
    list_simpl ; rewrite 3 app_assoc ; apply tens_ilr.
    rewrite <- 3 app_assoc.
    replace (map ioc lw ++ l ++ A0 :: B :: l0 ++ flat_map (app (map ioc lw)) L1)
      with (flat_map (app (map ioc lw)) ((l ++ A0 :: B :: l0) :: L1)) by (list_simpl ; reflexivity).
    rewrite <- flat_map_app ; refine (IHpi2 _ _ _)...
    rewrite ? flat_map_app ; list_simpl...
- apply lpam_irr.
  induction L using rev_ind_Type ; list_simpl.
  + change nil with (nil ++ flat_map (app (map ioc lw)) nil).
    rewrite app_comm_cons ; rewrite app_assoc ; refine (IHpi2 _ _ _) ; subst ; list_simpl...
  + replace (flat_map (app (map ioc lw)) (L ++ x :: nil) ++ A0 :: nil)
       with (flat_map (app (map ioc lw)) (L ++ (x ++ (A0 :: nil)) :: nil))
      by (rewrite ? flat_map_app ; list_simpl ; reflexivity).
    refine (IHpi2 _ _ _) ; subst ; list_simpl...
    rewrite ? flat_map_app ; list_simpl...
- elt_vs_app_flat_map_inv Heq.
  + app_vs_app_flat_map_inv Heq1.
    * list_simpl ; apply lpam_ilr...
      rewrite app_comm_cons ; rewrite app_assoc ; refine (IHpi2_2 _ _ _) ; list_simpl...
    * list_simpl ; rewrite ? flat_map_app ; list_simpl.
      rewrite (app_assoc l) ; rewrite (app_assoc _ (map ioc lw)) ; rewrite (app_assoc _ l3).
      replace (((l ++ flat_map (app (map ioc lw)) L0) ++ map ioc lw) ++ l3)
         with (l ++ flat_map (app (map ioc lw)) (L0 ++ l3 :: nil))
        by (rewrite flat_map_app ; list_simpl ; reflexivity).
      apply lpam_ilr...
      -- refine (IHpi2_1 _ _ _)...
      -- rewrite app_comm_cons ; rewrite app_assoc ; refine (IHpi2_2 _ _ _) ; list_simpl...
    * list_simpl ; rewrite flat_map_app.
      rewrite (app_assoc l) ; apply lpam_ilr.
      -- refine (IHpi2_1 _ _ _)...
      -- rewrite <- (app_nil_l (flat_map _ _)).
         rewrite app_comm_cons ; rewrite app_assoc ; refine (IHpi2_2 _ _ _) ; list_simpl...
  + app_vs_app_flat_map_inv Heq2.
    * list_simpl ; rewrite ? flat_map_app ; list_simpl.
      rewrite (app_assoc l') ; rewrite (app_assoc _ (map ioc lw)) ; rewrite (app_assoc _ l).
      replace (((l' ++ flat_map (app (map ioc lw)) L0) ++ map ioc lw) ++ l)
         with (l' ++ flat_map (app (map ioc lw)) (L0 ++ l :: nil))
        by (rewrite flat_map_app ; list_simpl ; reflexivity).
      apply lpam_ilr...
      list_simpl.
      replace (flat_map (app (map ioc lw)) (L0 ++ l :: nil) ++ B :: l1 ++ flat_map (app (map ioc lw)) L1)
         with (flat_map (app (map ioc lw)) (L0 ++ (l ++ B :: l1) :: L1))
        by (rewrite ? flat_map_app ; list_simpl ; reflexivity).
      refine (IHpi2_2 _ _ _) ; rewrite ? flat_map_app ; list_simpl...
    * list_simpl ; rewrite ? flat_map_app ; list_simpl ; rewrite ? flat_map_app ; list_simpl.
      rewrite (app_assoc l3) ; rewrite (app_assoc _ _ (l1 ++ _)) ; rewrite (app_assoc _ l1).
      replace (((l3 ++ flat_map (app (map ioc lw)) L) ++ map ioc lw) ++ l1)
         with (l3 ++ flat_map (app (map ioc lw)) (L ++ l1 :: nil))
        by (rewrite flat_map_app ; list_simpl ; reflexivity).
      rewrite 3 app_assoc ; apply lpam_ilr...
      -- refine (IHpi2_1 _ _ _)...
      -- list_simpl.
         replace (flat_map (app (map ioc lw)) L0 ++ map ioc lw ++ l ++ B :: l4
                                                 ++ flat_map (app (map ioc lw)) L2)
            with (flat_map (app (map ioc lw)) (L0 ++ (l ++ B :: l4) :: L2))
           by (rewrite ? flat_map_app ; list_simpl ; reflexivity).
         refine (IHpi2_2 _ _ _) ; rewrite ? flat_map_app ; list_simpl...
    * list_simpl ; rewrite ? flat_map_app ; list_simpl ; rewrite ? flat_map_app ; list_simpl.
      rewrite (app_assoc l3) ; rewrite 3 app_assoc ; apply lpam_ilr...
      -- refine (IHpi2_1 _ _ _)...
      -- list_simpl.
         replace (flat_map (app (map ioc lw)) L0 ++ map ioc lw ++ l
                                                 ++ B :: flat_map (app (map ioc lw)) L2)
            with (flat_map (app (map ioc lw)) (L0 ++ (l ++ B :: nil) :: L2))
           by (rewrite ? flat_map_app ; list_simpl ; reflexivity).
         refine (IHpi2_2 _ _ _) ; rewrite ? flat_map_app ; list_simpl...
- apply gen_irr.
  induction L using rev_ind_Type ; list_simpl.
  + change nil with (nil ++ flat_map (app (map ioc lw)) nil).
    rewrite app_comm_cons ; rewrite app_assoc ; refine (IHpi2 _ _ _) ; subst ; list_simpl...
  + replace (flat_map (app (map ioc lw)) (L ++ x :: nil) ++ A0 :: nil)
       with (flat_map (app (map ioc lw)) (L ++ (x ++ (A0 :: nil)) :: nil))
      by (rewrite ? flat_map_app ; list_simpl ; reflexivity).
    refine (IHpi2 _ _ _) ; subst ; list_simpl...
    rewrite ? flat_map_app ; list_simpl...
- destruct l' ; inversion Heq ; subst.
  + destruct L ; inversion H0.
  + list_simpl.
    apply gen_ilr.
    apply IHpi2...
- apply lmap_irr.
  rewrite app_comm_cons ; refine (IHpi2 _ _ _) ; subst ; list_simpl...
- rewrite app_assoc in Heq ; elt_vs_app_flat_map_inv Heq.
  + list_simpl ; apply lmap_ilr...
    rewrite app_comm_cons ; rewrite app_assoc ; refine (IHpi2_2 _ _ _) ; list_simpl...
  + replace (flat_map (cons (ioc A)) L0 ++ ioc A :: l)
       with (flat_map (cons (ioc A)) (L0 ++ l :: nil))
      in Heq1 by (rewrite flat_map_app ; list_simpl ; reflexivity).
    app_vs_app_flat_map_inv Heq1.
    * list_simpl ; rewrite ? flat_map_app ; list_simpl.
      rewrite (app_assoc l2) ; rewrite (app_assoc _ (map ioc lw)) ; rewrite (app_assoc _ l).
      replace (((l2 ++ flat_map (app (map ioc lw)) L0) ++ map ioc lw) ++ l)
         with (l2 ++ flat_map (app (map ioc lw)) (L0 ++ l :: nil))
        by (rewrite flat_map_app ; list_simpl ; reflexivity).
      apply lmap_ilr...
      -- refine (IHpi2_1 _ _ _)...
      -- rewrite app_comm_cons ; rewrite app_assoc ; refine (IHpi2_2 _ _ _) ; list_simpl...
    * induction L2 using rev_ind_Type ; [ | clear IHL2 ].
      -- assert (L0 = L /\ l = l2 ++ l4) as [Heq1 Heq2] ; subst.
         { apply (f_equal (@rev _)) in Heq0.
           rewrite ? rev_app_distr in Heq0.
           inversion Heq0 ; subst.
           apply (f_equal (@rev _)) in H1.
           rewrite ? rev_involutive in H1 ; subst.
           split... }
         list_simpl ; rewrite ? flat_map_app ; list_simpl ; rewrite ? flat_map_app ; list_simpl.
         list_simpl in pi2_1.
         rewrite 3 app_assoc ; apply lmap_ilr...
         list_simpl ; rewrite <- app_assoc in IHpi2_2.
         replace (flat_map (cons (ioc A)) (L ++ l2 :: nil) ++ B :: l3 ++ flat_map (cons (ioc A)) L1)
            with (flat_map (cons (ioc A)) (L ++ (l2 ++ B :: l3) :: L1)) in IHpi2_2
           by (rewrite ? flat_map_app ; list_simpl ; reflexivity).
         assert (pi2' := IHpi2_2 _ _ eq_refl).
         rewrite ? flat_map_app in pi2' ; list_simpl in pi2'...
      -- assert (L0 = L ++ (l2 ++ l4) :: L2 /\ l = x) as [Heq1 Heq2] ; subst.
         { apply (f_equal (@rev _)) in Heq0.
           rewrite ? rev_app_distr in Heq0 ; list_simpl in Heq0.
           inversion Heq0 ; subst.
           apply (f_equal (@rev _)) in H1.
           rewrite ? rev_involutive in H1 ; subst.
           rewrite ? rev_app_distr ; list_simpl ; split... }
         list_simpl ; rewrite ? flat_map_app ; list_simpl ; rewrite ? flat_map_app ; list_simpl.
         rewrite 3 app_assoc ; rewrite (app_assoc l4) ; rewrite (app_assoc (l4 ++ _)) ; rewrite (app_assoc _ x).
         apply lmap_ilr...
         ++ list_simpl.
            replace (flat_map (app (map ioc lw)) L2 ++ map ioc lw ++ x)
               with (flat_map (app (map ioc lw)) (L2 ++ x :: nil))
              by (rewrite flat_map_app ; list_simpl ; reflexivity).
            refine (IHpi2_1 _ _ _)...
         ++ list_simpl ; rewrite <- app_assoc in IHpi2_2.
            replace (flat_map (cons (ioc A)) (L ++ l2 :: nil) ++ B :: l3 ++ flat_map (cons (ioc A)) L1)
               with (flat_map (cons (ioc A)) (L ++ (l2 ++ B :: l3) :: L1)) in IHpi2_2
              by (rewrite ? flat_map_app ; list_simpl ; reflexivity).
            assert (pi2' := IHpi2_2 _ _ eq_refl).
            rewrite ? flat_map_app in pi2' ; list_simpl in pi2'...
    * induction L2 using rev_ind_Type ; [ | clear IHL2 ].
      -- list_simpl in Heq0 ; subst.
         list_simpl ; rewrite ? flat_map_app ; list_simpl ; rewrite ? flat_map_app ; list_simpl.
         list_simpl in pi2_1.
         rewrite <- (app_nil_l (ilmap _ _ :: _)) ; rewrite 3 app_assoc ; apply lmap_ilr...
         list_simpl ; rewrite <- app_assoc in IHpi2_2.
         replace (flat_map (cons (ioc A)) (L0 ++ l :: nil) ++ B :: l3 ++ flat_map (cons (ioc A)) L1)
            with (flat_map (cons (ioc A)) (L0 ++ (l ++ B :: l3) :: L1)) in IHpi2_2
           by (rewrite ? flat_map_app ; list_simpl ; reflexivity).
         assert (pi2' := IHpi2_2 _ _ eq_refl).
         rewrite ? flat_map_app in pi2' ; list_simpl in pi2'...
      -- assert (L0 = L ++ L2 /\ l = x) as [Heq1 Heq2] ; subst.
         { apply (f_equal (@rev _)) in Heq0.
           rewrite ? rev_app_distr in Heq0 ; list_simpl in Heq0.
           inversion Heq0 ; subst.
           apply (f_equal (@rev _)) in H1.
           rewrite rev_involutive in H1 ; subst.
           rewrite rev_app_distr ; list_simpl ; split... }
         list_simpl ; rewrite ? flat_map_app ; list_simpl ; rewrite ? flat_map_app ; list_simpl.
         rewrite app_assoc ; rewrite (app_assoc _ (map ioc lw)) ; rewrite (app_assoc _ x) ; apply lmap_ilr...
         ++ list_simpl.
            replace (flat_map (app (map ioc lw)) L2 ++ map ioc lw ++ x)
               with (flat_map (app (map ioc lw)) (L2 ++ x :: nil))
              by (rewrite flat_map_app ; list_simpl ; reflexivity).
            rewrite <- (app_nil_l _).
            refine (IHpi2_1 _ _ _)...
         ++ induction L using rev_ind_Type ; [ | clear IHL ].
            ** list_simpl in IHpi2_2 ; list_simpl.
               rewrite app_comm_cons ; rewrite app_assoc ; refine (IHpi2_2 _ _ _) ; list_simpl...
            ** list_simpl ; rewrite <- app_assoc in IHpi2_2.
               replace (flat_map (cons (ioc A)) (L ++ x0 :: nil) ++ B :: l3 ++ flat_map (cons (ioc A)) L1)
                  with (flat_map (cons (ioc A)) (L ++ (x0 ++ B :: l3) :: L1)) in IHpi2_2
                 by (rewrite ? flat_map_app ; list_simpl ; reflexivity).
               assert (pi2' := IHpi2_2 _ _ eq_refl).
               rewrite ? flat_map_app in pi2' ; list_simpl in pi2'.
               rewrite ? flat_map_app ; list_simpl...
- apply neg_irr.
  rewrite app_comm_cons ; refine (IHpi2 _ _ _) ; subst ; list_simpl...
- elt_vs_app_flat_map_inv Heq.
  + symmetry in Heq1 ; apply app_eq_nil in Heq1 ; destruct Heq1 as [Heq Heq1] ; subst.
    destruct L ; inversion Heq1.
    list_simpl ; apply neg_ilr...
  + symmetry in Heq2 ; apply app_eq_nil in Heq2 ; destruct Heq2 as [Heq Heq2] ; subst.
    destruct L1 ; inversion Heq2.
    rewrite flat_map_app.
    list_simpl ; rewrite 3 app_assoc ; apply neg_ilr.
    rewrite <- 2 app_assoc.
    replace (map ioc lw ++ l0)
      with (flat_map (app (map ioc lw)) (l0 :: nil)) by (list_simpl ; reflexivity).
    rewrite <- flat_map_app ; refine (IHpi2 _ _ _)...
    rewrite ? flat_map_app ; list_simpl...
- apply top_irr.
- apply with_irr.
  + refine (IHpi2_1 _ _ _) ; list_simpl...
  + refine (IHpi2_2 _ _ _) ; list_simpl...
- elt_vs_app_flat_map_inv Heq.
  + list_simpl ; apply with_ilr1.
    rewrite app_comm_cons ; rewrite app_assoc ; refine (IHpi2 _ _ _) ; list_simpl...
  + rewrite flat_map_app.
    list_simpl ; rewrite 3 app_assoc ; apply with_ilr1.
    rewrite <- 3 app_assoc.
    replace (map ioc lw ++ l ++ A0 :: l0 ++ flat_map (app (map ioc lw)) L1)
      with (flat_map (app (map ioc lw)) ((l ++ A0 :: l0) :: L1)) by (list_simpl ; reflexivity).
    rewrite <- flat_map_app ; refine (IHpi2 _ _ _)...
    rewrite ? flat_map_app ; list_simpl...
- elt_vs_app_flat_map_inv Heq.
  + list_simpl ; apply with_ilr2.
    rewrite app_comm_cons ; rewrite app_assoc ; refine (IHpi2 _ _ _) ; list_simpl...
  + rewrite flat_map_app.
    list_simpl ; rewrite 3 app_assoc ; apply with_ilr2.
    rewrite <- 3 app_assoc.
    replace (map ioc lw ++ l ++ A0 :: l0 ++ flat_map (app (map ioc lw)) L1)
      with (flat_map (app (map ioc lw)) ((l ++ A0 :: l0) :: L1)) by (list_simpl ; reflexivity).
    rewrite <- flat_map_app ; refine (IHpi2 _ _ _)...
    rewrite ? flat_map_app ; list_simpl...
- elt_vs_app_flat_map_inv Heq.
  + list_simpl ; apply zero_ilr.
  + rewrite flat_map_app.
    list_simpl ; rewrite 3 app_assoc ; apply zero_ilr.
- apply plus_irr1.
  refine (IHpi2 _ _ _) ; subst ; list_simpl...
- apply plus_irr2.
  refine (IHpi2 _ _ _) ; subst ; list_simpl...
- elt_vs_app_flat_map_inv Heq.
  + list_simpl ; apply plus_ilr.
    * rewrite app_comm_cons ; rewrite app_assoc ; refine (IHpi2_1 _ _ _) ; list_simpl...
    * rewrite app_comm_cons ; rewrite app_assoc ; refine (IHpi2_2 _ _ _) ; list_simpl...
  + rewrite flat_map_app.
    list_simpl ; rewrite 3 app_assoc ; apply plus_ilr ; rewrite <- 3 app_assoc.
    * replace (map ioc lw ++ l ++ A0 :: l0 ++ flat_map (app (map ioc lw)) L1)
        with (flat_map (app (map ioc lw)) ((l ++ A0 :: l0) :: L1)) by (list_simpl ; reflexivity).
      rewrite <- flat_map_app ; refine (IHpi2_1 _ _ _)...
      rewrite ? flat_map_app ; list_simpl...
    * replace (map ioc lw ++ l ++ B :: l0 ++ flat_map (app (map ioc lw)) L1)
        with (flat_map (app (map ioc lw)) ((l ++ B :: l0) :: L1)) by (list_simpl ; reflexivity).
      rewrite <- flat_map_app ; refine (IHpi2_2 _ _ _)...
      rewrite ? flat_map_app ; list_simpl...
- symmetry in Heq ; decomp_map_Type Heq ; subst ; simpl in Heq2 ; simpl.
  assert ({ Lw | flat_map (app (map ioc lw)) L = map ioc Lw }) as [Lw HeqLw].
  { clear pi2 IHpi2 ; revert l2 Heq2 ; clear ; induction L ; intros l2 Heq2.
    - exists nil...
    - simpl in Heq2.
      decomp_map_Type Heq2 ; subst.
      inversion Heq1 ; subst ; simpl.
      simpl in Heq4 ; apply IHL in Heq4.
      destruct Heq4 as [Lw Heq4].
      exists (lw ++ l1 ++ Lw) ; list_simpl ; rewrite <- Heq4... }
  rewrite HeqLw ; rewrite <- map_app ; apply oc_irr.
  list_simpl ; rewrite <- HeqLw ; refine (IHpi2 _ _ _).
  rewrite Heq2 ; list_simpl...
- elt_vs_app_flat_map_inv Heq.
  + list_simpl ; apply de_ilr.
    rewrite app_comm_cons ; rewrite app_assoc ; refine (IHpi2 _ _ _) ; list_simpl...
  + rewrite flat_map_app.
    list_simpl ; rewrite 3 app_assoc ; apply de_ilr.
    rewrite <- 3 app_assoc.
    replace (map ioc lw ++ l ++ A0 :: l0 ++ flat_map (app (map ioc lw)) L1)
      with (flat_map (app (map ioc lw)) ((l ++ A0 :: l0) :: L1)) by (list_simpl ; reflexivity).
    rewrite <- flat_map_app ; refine (IHpi2 _ _ _)...
    rewrite ? flat_map_app ; list_simpl...
  + inversion HeqA ; subst.
    induction L0 using rev_ind_Type ; [ | clear IHL0 ].
    * list_simpl ; list_simpl in IHpi2.
      rewrite app_comm_cons in IHpi2 ; rewrite app_assoc in IHpi2.
      assert (pi2' := IHpi2 _ _ eq_refl).
      list_simpl in pi2' ; apply (IHcut _ _ _ _ pi1) in pi2'...
    * rewrite <- ? app_assoc in IHpi2.
      replace (flat_map (cons (ioc A)) (L0 ++ x :: nil) ++ A :: l ++ flat_map (cons (ioc A)) L1)
         with (flat_map (cons (ioc A)) (L0 ++ (x ++ A :: l) :: L1)) in IHpi2
        by (rewrite ? flat_map_app ; list_simpl ; reflexivity).
      assert (pi2' := IHpi2 _ _ eq_refl).
      rewrite flat_map_app in pi2' ; list_simpl in pi2'.
      rewrite 3 app_assoc in pi2' ; apply (IHcut _ _ _ _ pi1) in pi2'...
      list_simpl in pi2' ; rewrite ? flat_map_app ; list_simpl...
- elt_vs_app_flat_map_inv Heq.
  + list_simpl ; apply wk_ilr.
    rewrite app_assoc ; refine (IHpi2 _ _ _) ; list_simpl...
  + rewrite flat_map_app.
    list_simpl ; rewrite 3 app_assoc ; apply wk_ilr.
    rewrite <- 3 app_assoc.
    replace (map ioc lw ++ l ++ l0 ++ flat_map (app (map ioc lw)) L1)
      with (flat_map (app (map ioc lw)) ((l ++ l0) :: L1)) by (list_simpl ; reflexivity).
    rewrite <- flat_map_app ; refine (IHpi2 _ _ _)...
    rewrite ? flat_map_app ; list_simpl...
  + inversion HeqA ; subst.
    induction L0 using rev_ind_Type ; [ | clear IHL0 ].
    * list_simpl ; apply wk_list_ilr.
      list_simpl in IHpi2 ; rewrite app_assoc in IHpi2.
      rewrite app_assoc ; refine (IHpi2 _ _ _)...
    * rewrite <- ? app_assoc in IHpi2.
      replace (flat_map (cons (ioc A)) (L0 ++ x :: nil) ++ l ++ flat_map (cons (ioc A)) L1)
         with (flat_map (cons (ioc A)) (L0 ++ (x ++ l) :: L1)) in IHpi2
        by (rewrite ? flat_map_app ; list_simpl ; reflexivity).
      assert (pi2' := IHpi2 _ _ eq_refl).
      rewrite flat_map_app in pi2' ; list_simpl in pi2'.
      list_simpl ; rewrite flat_map_app ; list_simpl.
      rewrite 3 app_assoc ; apply wk_list_ilr ; list_simpl...
- elt_vs_app_flat_map_inv Heq.
  + list_simpl ; apply co_ilr.
    rewrite 2 app_comm_cons ; rewrite app_assoc ; refine (IHpi2 _ _ _) ; list_simpl...
  + rewrite flat_map_app.
    list_simpl ; rewrite 3 app_assoc ; apply co_ilr.
    rewrite <- 3 app_assoc.
    replace (map ioc lw ++ l ++ ioc A0 :: ioc A0 :: l0 ++ flat_map (app (map ioc lw)) L1)
      with (flat_map (app (map ioc lw)) ((l ++ ioc A0 :: ioc A0 :: l0) :: L1)) by (list_simpl ; reflexivity).
    rewrite <- flat_map_app ; refine (IHpi2 _ _ _)...
    rewrite ? flat_map_app ; list_simpl...
  + inversion HeqA ; subst.
    induction L0 using rev_ind_Type ; [ | clear IHL0 ].
    * list_simpl ; apply co_list_ilr.
      list_simpl in IHpi2.
      replace (ioc A :: ioc A :: l ++ flat_map (cons (ioc A)) L1)
         with (flat_map (cons (ioc A)) (nil :: l :: L1)) in IHpi2
        by (list_simpl ; reflexivity).
      replace (map ioc lw ++ map ioc lw ++ l ++ flat_map (app (map ioc lw)) L1)
         with (flat_map (app (map ioc lw)) (nil :: l :: L1))
        by (list_simpl ; reflexivity).
      refine (IHpi2 _ _ _)...
    * rewrite <- ? app_assoc in IHpi2.
      replace (flat_map (cons (ioc A)) (L0 ++ x :: nil) ++ ioc A :: ioc A :: l ++ flat_map (cons (ioc A)) L1)
         with (flat_map (cons (ioc A)) (L0 ++ x :: nil :: l :: L1)) in IHpi2
        by (rewrite ? flat_map_app ; list_simpl ; reflexivity).
      assert (pi2' := IHpi2 _ _ eq_refl).
      rewrite flat_map_app in pi2' ; list_simpl in pi2'.
      list_simpl ; rewrite flat_map_app ; list_simpl.
      rewrite 3 app_assoc ; apply co_list_ilr ; list_simpl...
- rewrite f in P_cutfree ; inversion P_cutfree.
- assert (L = nil) as Hnil ; subst.
  { specialize P_gax_at_l with a.
    rewrite Heq in P_gax_at_l.
    apply Forall_app_inv in P_gax_at_l ; destruct P_gax_at_l as [_ Hat].
    destruct L ; inversion Hat...
    inversion H1. }
  list_simpl in Heq ; list_simpl ; subst ; apply gax_ir.
Qed.

Theorem cut_ir_gaxat : forall A l0 l1 l2 C,
  ill P l0 A -> ill P (l1 ++ A :: l2) C -> ill P (l1 ++ l0 ++ l2) C.
Proof with myeasy_perm_Type.
case_eq (ipcut P) ; intros P_cutfree.
{ intros A l0 l1 l2 C pi1 pi2 ; eapply cut_ir... }
enough (forall c s A l0 l1 l2 C (pi1 : ill P l0 A) (pi2 : ill P (l1 ++ A :: l2) C),
          s = ipsize pi1 + ipsize pi2 -> ifsize A <= c -> ill P (l1 ++ l0 ++ l2) C) as IH
by (intros A l0 l1 l2 C pi1 pi2 ; refine (IH _ _ A _ _ _ _ pi1 pi2 _ _) ; myeasy_perm_Type).
induction c as [c IHcut0] using lt_wf_rect.
assert (forall A, ifsize A < c -> forall l0 l1 l2 C,
          ill P l0 A -> ill P (l1 ++ A :: l2) C -> ill P (l1 ++ l0 ++ l2) C) as IHcut
  by (intros A Hs l0 l1 l2 C pi1 pi2 ; refine (IHcut0 _ _ _ _ _ _ _ _ pi1 pi2 _ _) ; myeasy_perm_Type) ;
  clear IHcut0.
induction s as [s IHsize0] using lt_wf_rect.
assert (forall A l0 l1 l2 C (pi1 : ill P l0 A) (pi2 : ill P (l1 ++ A :: l2) C),
          ipsize pi1 + ipsize pi2 < s -> ifsize A <= c -> ill P (l1 ++ l0 ++ l2) C)
  as IHsize by (intros ; eapply IHsize0 ; myeasy_perm_Type) ; clear IHsize0.
intros A l0 l1 l2 C pi1 pi2 Heqs Hc.
rewrite_all Heqs ; clear s Heqs.
remember (l1 ++ A :: l2) as l ; destruct_ill pi2 f X l Hl Hr HP a.
- (* ax_ir *)
  unit_vs_elt_inv Heql ; list_simpl...
- (* ex_ir *)
  simpl in IHsize.
  case_eq (ipperm P) ; intros Hperm ; rewrite_all Hperm ; simpl in HP.
  + assert (HP' := HP).
    apply Permutation_Type_vs_elt_inv in HP' ; destruct HP' as [(l1',l2') Heq] ;
      simpl in Heq ; subst.
    apply Permutation_Type_app_inv in HP.
    eapply (ex_ir _ (l1' ++ l0 ++ l2')) ; [ | rewrite Hperm ; apply Permutation_Type_app_middle ]...
    refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
  + subst.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
- (* ex_oc_ir *)
  simpl in IHsize.
  dichot_Type_elt_app_exec Heql ; subst.
  + rewrite 2 app_assoc.
    eapply ex_oc_ir...
    revert Hl IHsize ; list_simpl ; intros Hl IHsize.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
  + dichot_Type_elt_app_exec Heql1 ; subst.
    * decomp_map_Type Heql0 ; subst ; simpl in HP ; simpl in pi1.
      assert (HP' := HP).
      apply Permutation_Type_vs_elt_inv in HP' ; destruct HP' as [(l1',l2') Heq] ;
        simpl in Heq ; subst.
      apply Permutation_Type_app_inv in HP.
      revert Hl IHsize ; list_simpl ; rewrite app_assoc ; intros Hl IHsize.
      rewrite app_assoc ; eapply (cut_oc_comm_left _ (ipsize pi1))...
      -- list_simpl ; rewrite app_comm_cons ; change (ioc x :: map ioc l7) with (map ioc (x :: l7)) ;
           rewrite (app_assoc (map ioc l4)) ; rewrite <- map_app.
         apply (ex_oc_ir _ _ (l1' ++ x :: l2'))...
         revert Hl IHsize ; list_simpl ; rewrite app_assoc ; intros Hl IHsize...
      -- intros lw pi0 Hs'.
         list_simpl ; rewrite (app_assoc (map ioc l4)) ; rewrite (app_assoc _ (map ioc l7)) ;
           rewrite <- (app_assoc (map ioc l4)) ; rewrite <- 2 map_app ;
           apply (ex_oc_ir _ _ (l1' ++ lw ++ l2'))...
         list_simpl ; rewrite app_assoc.
         refine (IHsize _ _ _ _ _ (oc_irr _ _ _ pi0) Hl _ _) ; simpl...
    * rewrite <- 2 app_assoc.
      eapply ex_oc_ir...
      revert Hl IHsize ; simpl ; rewrite 2 app_assoc ; intros Hl IHsize.
      rewrite 2 app_assoc ; refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
- (* one_irr *)
  destruct l1 ; inversion Heql.
- (* one_ilr *)
  trichot_Type_elt_elt_exec Heql.
  + list_simpl.
    apply one_ilr.
    revert Hl IHsize ; simpl ; rewrite app_assoc ; intros Hl IHsize.
    rewrite app_assoc ; refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
  + remember (one_ilr _ _ _ _ Hl) as Hone ; clear HeqHone.
    remember (ione) as C ; destruct_ill pi1 f X l Hl2 Hr2 HP a ; try inversion HeqC.
    * apply (ex_ir _ (l3 ++ l ++ l4)).
      -- simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hone _ _)...
      -- apply PEperm_Type_app_head ; apply PEperm_Type_app_tail...
    * list_simpl ; rewrite app_assoc ; eapply ex_oc_ir...
      list_simpl ; rewrite (app_assoc l) ; rewrite (app_assoc _ l2) ; rewrite <- (app_assoc l).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hone _ _)...
    * list_simpl...
    * list_simpl ; rewrite app_assoc ; apply one_ilr.
      list_simpl ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hone _ _)...
    * list_simpl ; rewrite app_assoc ; apply tens_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hone _ _)...
    * list_simpl ; rewrite app_assoc ; apply lpam_ilr...
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hone _ _)...
    * list_simpl ; rewrite app_assoc ; apply lmap_ilr...
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hone _ _)...
    * list_simpl ; rewrite app_assoc ; apply with_ilr1.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hone _ _)...
    * list_simpl ; rewrite app_assoc ; apply with_ilr2.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hone _ _)...
    * list_simpl ; rewrite app_assoc ; apply zero_ilr.
    * list_simpl ; rewrite app_assoc ; apply plus_ilr.
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hone _ _)...
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         simpl in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hone _ _)...
    * list_simpl ; rewrite app_assoc ; apply de_ilr.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hone _ _)...
    * list_simpl ; rewrite app_assoc ; apply wk_ilr.
      list_simpl ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hone _ _)...
    * list_simpl ; rewrite app_assoc ; apply co_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hone _ _)...
    * rewrite f in P_cutfree ; inversion P_cutfree.
    * exfalso ; assert (Hiq := P_gax_at_r a) ; rewrite H0 in Hiq ; inversion Hiq.
  + rewrite 2 app_assoc.
    apply one_ilr.
    revert Hl IHsize ; list_simpl ; intros Hl IHsize.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
- (* tens_irr *)
  dichot_Type_elt_app_exec Heql ; subst.
  + rewrite 2 app_assoc ; apply tens_irr...
    revert Hl IHsize ; list_simpl ; intros Hl IHsize.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
  + rewrite <- app_assoc ; apply tens_irr...
    revert Hl IHsize ; list_simpl ; intros Hl IHsize.
    refine (IHsize _ _ _ _ _ pi1 Hr _ _)...
- (* tens_ilr *)
  trichot_Type_elt_elt_exec Heql.
  + list_simpl.
    apply tens_ilr.
    revert Hl IHsize ; simpl ; rewrite 2 app_comm_cons ; rewrite app_assoc ; intros Hl IHsize.
    rewrite 2 app_comm_cons ; rewrite app_assoc.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
  + remember (tens_ilr _ _ _ _ _ _ Hl) as Htens ; clear HeqHtens.
    remember (itens A0 B) as D ; destruct_ill pi1 f X l Hl2 Hr2 HP a ; try inversion HeqD.
    * apply (ex_ir _ (l3 ++ l ++ l4)).
      -- simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Htens _ _)...
      -- apply PEperm_Type_app_head ; apply PEperm_Type_app_tail...
    * list_simpl ; rewrite app_assoc ; eapply ex_oc_ir...
      list_simpl ; rewrite (app_assoc l) ; rewrite (app_assoc _ l2) ; rewrite <- (app_assoc l).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Htens _ _)...
    * list_simpl ; rewrite app_assoc ; apply one_ilr.
      list_simpl ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Htens _ _)...
    * rewrite <- app_assoc ; rewrite app_assoc.
      simpl in Hc ; subst ; refine (IHcut _ _ _ _ _ _ Hr2 _)...
      list_simpl ; refine (IHcut _ _ _ _ _ _ Hl2 Hl)...
    * list_simpl ; rewrite app_assoc ; apply tens_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Htens _ _)...
    * list_simpl ; rewrite app_assoc ; apply lpam_ilr...
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Htens _ _)...
    * list_simpl ; rewrite app_assoc ; apply lmap_ilr...
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Htens _ _)...
    * list_simpl ; rewrite app_assoc ; apply with_ilr1.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Htens _ _)...
    * list_simpl ; rewrite app_assoc ; apply with_ilr2.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Htens _ _)...
    * list_simpl ; rewrite app_assoc ; apply zero_ilr.
    * list_simpl ; rewrite app_assoc ; apply plus_ilr.
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Htens _ _)...
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         simpl in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Htens _ _)...
    * list_simpl ; rewrite app_assoc ; apply de_ilr.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Htens _ _)...
    * list_simpl ; rewrite app_assoc ; apply wk_ilr.
      list_simpl ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Htens _ _)...
    * list_simpl ; rewrite app_assoc ; apply co_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Htens _ _)...
    * rewrite f in P_cutfree ; inversion P_cutfree.
    * exfalso ; assert (Hiq := P_gax_at_r a) ; rewrite H0 in Hiq ; inversion Hiq.
  + rewrite 2 app_assoc.
    apply tens_ilr.
    revert Hl IHsize ; list_simpl ; intros Hl IHsize.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
- (* lpam_irr *)
  revert Hl IHsize ; list_simpl ; intros Hl IHsize.
  apply lpam_irr.
  list_simpl ; refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
- (* lpam_ilr *)
  simpl in IHsize ; trichot_Type_elt_elt_exec Heql.
  + dichot_Type_elt_app_exec Heql1 ; subst.
    * list_simpl ; rewrite 2 app_assoc.
      apply lpam_ilr...
      list_simpl ; refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
    * list_simpl ; apply lpam_ilr...
      revert Hr IHsize ; rewrite app_comm_cons ; rewrite app_assoc ; intros Hr IHsize.
      rewrite app_comm_cons ; rewrite app_assoc.
      refine (IHsize _ _ _ _ _ pi1 Hr _ _)...
  + change (S (ipsize Hl + ipsize Hr)) with (ipsize (lpam_ilr _ _ _ _ _ _ _ Hl Hr)) in IHsize.
    remember (lpam_ilr _ _ _ _ _ _ _ Hl Hr) as Hlpam ; clear HeqHlpam.
    remember (ilpam A0 B) as D ; destruct_ill pi1 f X l Hl2 Hr2 HP a ; try inversion HeqD.
    * apply (ex_ir _ (l4 ++ l ++ l3 ++ l5)).
      -- simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlpam _ _)...
      -- apply PEperm_Type_app_head ; apply PEperm_Type_app_tail...
    * list_simpl ; rewrite app_assoc ; eapply ex_oc_ir...
      list_simpl ; rewrite (app_assoc l) ; rewrite (app_assoc _ l2) ; rewrite <- (app_assoc l).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlpam _ _)...
    * list_simpl ; rewrite app_assoc ; apply one_ilr.
      list_simpl ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlpam _ _)...
    * list_simpl ; rewrite app_assoc ; apply tens_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlpam _ _)...
    * rewrite app_assoc.
      simpl in Hc ; subst ; refine (IHcut _ _ _ _ _ _ Hl _)...
      list_simpl ; change (A0 :: l5) with ((A0 :: nil) ++ l5) ; rewrite (app_assoc l).
      refine (IHcut _ _ _ _ _ _ Hl2 Hr)...
    * list_simpl ; rewrite app_assoc ; apply lpam_ilr...
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hlpam _ _)...
    * list_simpl ; rewrite app_assoc ; apply lmap_ilr...
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hlpam _ _)...
    * list_simpl ; rewrite app_assoc ; apply with_ilr1.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlpam _ _)...
    * list_simpl ; rewrite app_assoc ; apply with_ilr2.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlpam _ _)...
    * list_simpl ; rewrite app_assoc ; apply zero_ilr.
    * list_simpl ; rewrite app_assoc ; apply plus_ilr.
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlpam _ _)...
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         simpl in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hlpam _ _)...
    * list_simpl ; rewrite app_assoc ; apply de_ilr.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlpam _ _)...
    * list_simpl ; rewrite app_assoc ; apply wk_ilr.
      list_simpl ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlpam _ _)...
    * list_simpl ; rewrite app_assoc ; apply co_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlpam _ _)...
    * rewrite f in P_cutfree ; inversion P_cutfree.
    * exfalso ; assert (Hiq := P_gax_at_r a) ; rewrite H0 in Hiq ; inversion Hiq.
  + rewrite 2 app_assoc ; apply lpam_ilr...
    revert Hr IHsize ; list_simpl ; intros Hr IHsize.
    refine (IHsize _ _ _ _ _ pi1 Hr _ _)...
- (* gen_irr *)
  simpl in IHsize.
  apply gen_irr.
  revert Hl IHsize ; list_simpl ; intros Hl IHsize.
  refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
- (* gen_ilr *)
  destruct l1 ; inversion Heql ; subst.
  + remember (gen_ilr _ _ _ Hl) as Hgen ; clear HeqHgen.
    remember (igen A0) as D ; destruct_ill pi1 f X l' Hl2 Hr2 HP a ; try inversion HeqD.
    * apply (ex_ir _ (nil ++ l' ++ l2)).
      -- revert Hgen IHsize ; rewrite <- (app_nil_l _) ; intros Hgen IHsize.
         refine (IHsize _ _ _ _ _ Hl2 Hgen _ _) ; simpl...
      -- apply PEperm_Type_app_head ; apply PEperm_Type_app_tail...
    * rewrite <- ? app_assoc ; rewrite app_assoc ; eapply ex_oc_ir...
      rewrite <- app_assoc ; rewrite (app_assoc l') ; rewrite (app_assoc _ l0) ; rewrite <- (app_assoc l').
      revert Hgen IHsize ; rewrite <- (app_nil_l _) ; intros Hgen IHsize.
      refine (IHsize _ _ _ _ _ Hl2 Hgen _ _) ; simpl...
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply one_ilr.
      list_simpl ; rewrite (app_assoc l1).
      revert Hgen IHsize ; rewrite <- (app_nil_l _) ; intros Hgen IHsize.
      refine (IHsize _ _ _ _ _ Hl2 Hgen _ _) ; simpl...
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply tens_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      revert Hgen IHsize ; rewrite <- (app_nil_l _) ; intros Hgen IHsize.
      refine (IHsize _ _ _ _ _ Hl2 Hgen _ _) ; simpl...
    * rewrite <- ? app_assoc ; rewrite <- app_comm_cons ; rewrite <- app_assoc ; rewrite app_assoc.
      apply lpam_ilr...
      rewrite <- app_assoc ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      revert Hgen IHsize ; rewrite <- (app_nil_l _) ; intros Hgen IHsize.
      refine (IHsize _ _ _ _ _ Hr2 Hgen  _ _) ; simpl...
    * subst ; list_simpl ; rewrite <- (app_nil_r _) ; rewrite <- app_assoc.
      refine (IHcut _ _ _ _ _ _ Hl Hl2) ; simpl...
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply lmap_ilr...
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      revert Hgen IHsize ; rewrite <- (app_nil_l _) ; intros Hgen IHsize.
      refine (IHsize _ _ _ _ _ Hr2 Hgen _ _) ; simpl...
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply with_ilr1.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      revert Hgen IHsize ; rewrite <- (app_nil_l _) ; intros Hgen IHsize.
      refine (IHsize _ _ _ _ _ Hl2 Hgen _ _) ; simpl...
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply with_ilr2.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      revert Hgen IHsize ; rewrite <- (app_nil_l _) ; intros Hgen IHsize.
      refine (IHsize _ _ _ _ _ Hl2 Hgen _ _) ; simpl...
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply zero_ilr.
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply plus_ilr.
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         revert Hgen IHsize ; rewrite <- (app_nil_l _) ; intros Hgen IHsize.
         refine (IHsize _ _ _ _ _ Hl2 Hgen _ _) ; simpl...
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         revert Hgen IHsize ; rewrite <- (app_nil_l _) ; intros Hgen IHsize.
         refine (IHsize _ _ _ _ _ Hr2 Hgen _ _) ; simpl...
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply de_ilr.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      revert Hgen IHsize ; rewrite <- (app_nil_l _) ; intros Hgen IHsize.
      refine (IHsize _ _ _ _ _ Hl2 Hgen _ _) ; simpl...
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply wk_ilr.
      list_simpl ; rewrite (app_assoc l1).
      revert Hgen IHsize ; rewrite <- (app_nil_l _) ; intros Hgen IHsize.
      refine (IHsize _ _ _ _ _ Hl2 Hgen _ _) ; simpl...
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply co_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      revert Hgen IHsize ; rewrite <- (app_nil_l _) ; intros Hgen IHsize.
      refine (IHsize _ _ _ _ _ Hl2 Hgen _ _) ; simpl...
    * rewrite f in P_cutfree ; inversion P_cutfree.
    * exfalso ; assert (Hiq := P_gax_at_r a) ; rewrite H0 in Hiq ; inversion Hiq.
  + list_simpl ; apply gen_ilr.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _) ; simpl...
- (* lmap_irr *)
  simpl in IHsize.
  apply lmap_irr.
  revert Hl IHsize ; rewrite app_comm_cons ; intros Hl IHsize.
  rewrite app_comm_cons ; refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
- (* lmap_ilr *)
  simpl in IHsize ; rewrite app_assoc in Heql ; trichot_Type_elt_elt_exec Heql.
  + list_simpl ; apply lmap_ilr...
    revert Hr IHsize ; rewrite app_comm_cons ; rewrite app_assoc ; intros Hr IHsize.
    rewrite app_comm_cons ; rewrite app_assoc.
    refine (IHsize _ _ _ _ _ pi1 Hr _ _)...
  + change (S (ipsize Hl + ipsize Hr)) with (ipsize (lmap_ilr _ _ _ _ _ _ _ Hl Hr)) in IHsize.
    remember (lmap_ilr _ _ _ _ _ _ _ Hl Hr) as Hlmap  ; clear HeqHlmap.
    revert Hlmap IHsize ; rewrite app_assoc ; intros Hlmap IHsize.
    remember (ilmap A0 B) as D ; destruct_ill pi1 f X l Hl2 Hr2 HP a ; try inversion HeqD.
    * apply (ex_ir _ ((l4 ++ l3) ++ l ++ l5)).
      -- simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlmap _ _)...
      -- apply PEperm_Type_app_head ; apply PEperm_Type_app_tail...
    * list_simpl ; rewrite 2 app_assoc ; eapply ex_oc_ir...
      list_simpl ; rewrite (app_assoc l) ; rewrite (app_assoc _ l2) ;
        rewrite <- (app_assoc l) ; rewrite app_assoc ; simpl in IHsize.
      refine (IHsize _ _ _ _ _ Hl2 Hlmap _ _)...
    * list_simpl ; rewrite 2 app_assoc ; apply one_ilr.
      list_simpl ; rewrite (app_assoc l1) ; rewrite app_assoc.
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlmap _ _)...
    * list_simpl ; rewrite 2 app_assoc ; apply tens_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1) ; rewrite app_assoc.
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlmap _ _)...
    * list_simpl ; rewrite 2 app_assoc ; apply lpam_ilr...
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1) ; rewrite app_assoc.
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hlmap _ _)...
    * list_simpl ; simpl in Hc ; subst ; refine (IHcut _ _ _ _ _ _ Hl _)...
      rewrite app_comm_cons ; refine (IHcut _ _ _ _ _ _ Hl2 Hr)...
    * list_simpl ; rewrite 2 app_assoc ; apply lmap_ilr...
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1) ; rewrite app_assoc.
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hlmap _ _)...
    * list_simpl ; rewrite 2 app_assoc ; apply with_ilr1.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1) ; rewrite app_assoc.
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlmap _ _)...
    * list_simpl ; rewrite 2 app_assoc ; apply with_ilr2.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1) ; rewrite app_assoc.
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlmap _ _)...
    * list_simpl ; rewrite 2 app_assoc ; apply zero_ilr.
    * list_simpl ; rewrite 2 app_assoc ; apply plus_ilr.
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1) ; rewrite app_assoc.
         simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlmap _ _)...
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1) ; rewrite app_assoc.
         simpl in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hlmap _ _)...
    * list_simpl ; rewrite 2 app_assoc ; apply de_ilr.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1) ; rewrite app_assoc.
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlmap _ _)...
    * list_simpl ; rewrite 2 app_assoc ; apply wk_ilr.
      list_simpl ; rewrite (app_assoc l1) ; rewrite app_assoc.
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlmap _ _)...
    * list_simpl ; rewrite 2 app_assoc ; apply co_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1) ; rewrite app_assoc.
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlmap _ _)...
    * rewrite f in P_cutfree ; inversion P_cutfree.
    * exfalso ; assert (Hiq := P_gax_at_r a) ; rewrite H0 in Hiq ; inversion Hiq.
  + dichot_Type_elt_app_exec Heql0 ; subst.
    * list_simpl ; rewrite 2 app_assoc.
      apply lmap_ilr...
      revert Hr IHsize ; list_simpl ; intros Hr IHsize.
      refine (IHsize _ _ _ _ _ pi1 Hr _ _)...
    * list_simpl ; rewrite (app_assoc l6) ; rewrite (app_assoc _ l) ; apply lmap_ilr...
      list_simpl ; refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
- (* neg_irr *)
  simpl in IHsize.
  apply neg_irr.
  revert Hl IHsize ; rewrite app_comm_cons ; intros Hl IHsize.
  rewrite app_comm_cons ; refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
- (* neg_ilr *)
  trichot_Type_elt_elt_exec Heql.
  + destruct l3 ; inversion Heql1.
  + remember (neg_ilr _ _ _ Hl) as Hneg ; clear HeqHneg.
    remember (ineg A0) as D ; destruct_ill pi1 f X l' Hl2 Hr2 HP a ; try inversion HeqD.
    * apply (ex_ir _ (l ++ l' ++ nil)).
      -- simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hneg _ _)...
      -- apply PEperm_Type_app_head ; apply PEperm_Type_app_tail...
    * rewrite <- ? app_assoc ; rewrite app_assoc ; eapply ex_oc_ir...
      rewrite <- app_assoc ; rewrite (app_assoc l') ; rewrite (app_assoc _ l2) ; rewrite <- (app_assoc l').
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hneg _ _)...
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply one_ilr.
      list_simpl ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hneg _ _)...
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply tens_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hneg _ _)...
    * rewrite <- ? app_assoc ; rewrite <- app_comm_cons ; rewrite <- app_assoc ; rewrite app_assoc.
      apply lpam_ilr...
      rewrite <- app_assoc ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hneg _ _)...
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply lmap_ilr...
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hneg _ _)...
    * clear IHsize ; rewrite <- (app_nil_l (A :: l0)) in Hl2.
      list_simpl ; simpl in Hc ; subst ; refine (IHcut _ _ _ _ _ _ Hl Hl2)...
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply with_ilr1.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hneg _ _)...
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply with_ilr2.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hneg _ _)...
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply zero_ilr.
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply plus_ilr.
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hneg _ _)...
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         simpl in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hneg _ _)...
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply de_ilr.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hneg _ _)...
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply wk_ilr.
      list_simpl ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hneg _ _)...
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply co_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hneg _ _)...
    * rewrite f in P_cutfree ; inversion P_cutfree.
    * exfalso ; assert (Hiq := P_gax_at_r a) ; rewrite H0 in Hiq ; inversion Hiq.
  + rewrite 2 app_assoc.
    apply neg_ilr...
    revert Hl IHsize ; list_simpl ; intros Hl IHsize.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
- (* top_irr *)
  apply top_irr.
- (* with_irr *)
  simpl in IHsize.
  apply with_irr.
  + refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
  + refine (IHsize _ _ _ _ _ pi1 Hr _ _)...
- (* with_ilr1 *)
  trichot_Type_elt_elt_exec Heql.
  + list_simpl.
    apply with_ilr1.
    revert Hl IHsize ; simpl ; rewrite app_comm_cons ; rewrite app_assoc ; intros Hl IHsize.
    rewrite app_comm_cons ; rewrite app_assoc.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
  + remember (with_ilr1 _ _ _ _ _ _ Hl) as Hwith ; clear HeqHwith.
    remember (iwith A0 B) as D ; destruct_ill pi1 f X l Hl2 Hr2 HP a ; try inversion HeqD.
    * apply (ex_ir _ (l3 ++ l ++ l4)).
      -- simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _)...
      -- apply PEperm_Type_app_head ; apply PEperm_Type_app_tail...
    * list_simpl ; rewrite app_assoc ; eapply ex_oc_ir...
      list_simpl ; rewrite (app_assoc l) ; rewrite (app_assoc _ l2) ; rewrite <- (app_assoc l).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _)...
    * list_simpl ; rewrite app_assoc ; apply one_ilr.
      list_simpl ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _)...
    * list_simpl ; rewrite app_assoc ; apply tens_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _)...
    * list_simpl ; rewrite app_assoc ; apply lpam_ilr...
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hwith _ _)...
    * list_simpl ; rewrite app_assoc ; apply lmap_ilr...
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hwith _ _)...
    * simpl in Hc ; subst ; refine (IHcut _ _ _ _ _ _ Hl2 Hl)...
    * list_simpl ; rewrite app_assoc ; apply with_ilr1.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _)...
    * list_simpl ; rewrite app_assoc ; apply with_ilr2.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _)...
    * list_simpl ; rewrite app_assoc ; apply zero_ilr.
    * list_simpl ; rewrite app_assoc ; apply plus_ilr.
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _)...
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         simpl in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hwith _ _)...
    * list_simpl ; rewrite app_assoc ; apply de_ilr.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _)...
    * list_simpl ; rewrite app_assoc ; apply wk_ilr.
      list_simpl ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _)...
    * list_simpl ; rewrite app_assoc ; apply co_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _)...
    * rewrite f in P_cutfree ; inversion P_cutfree.
    * exfalso ; assert (Hiq := P_gax_at_r a) ; rewrite H0 in Hiq ; inversion Hiq.
  + rewrite 2 app_assoc.
    apply with_ilr1.
    revert Hl IHsize ; list_simpl ; intros Hl IHsize.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
- (* with_ilr2 *)
  trichot_Type_elt_elt_exec Heql.
  + list_simpl.
    apply with_ilr2.
    revert Hl IHsize ; simpl ; rewrite app_comm_cons ; rewrite app_assoc ; intros Hl IHsize.
    rewrite app_comm_cons ; rewrite app_assoc.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
  + remember (with_ilr2 _ _ _ _ _ _ Hl) as Hwith ; clear HeqHwith.
    remember (iwith B A0) as D ; destruct_ill pi1 f X l Hl2 Hr2 HP a ; try inversion HeqD.
    * apply (ex_ir _ (l3 ++ l ++ l4)).
      -- simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _)...
      -- apply PEperm_Type_app_head ; apply PEperm_Type_app_tail...
    * list_simpl ; rewrite app_assoc ; eapply ex_oc_ir...
      list_simpl ; rewrite (app_assoc l) ; rewrite (app_assoc _ l2) ; rewrite <- (app_assoc l).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _)...
    * list_simpl ; rewrite app_assoc ; apply one_ilr.
      list_simpl ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _)...
    * list_simpl ; rewrite app_assoc ; apply tens_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _)...
    * list_simpl ; rewrite app_assoc ; apply lpam_ilr...
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hwith _ _)...
    * list_simpl ; rewrite app_assoc ; apply lmap_ilr...
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hwith _ _)...
    * simpl in Hc ; subst ; refine (IHcut _ _ _ _ _ _ Hr2 Hl)...
    * list_simpl ; rewrite app_assoc ; apply with_ilr1.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _)...
    * list_simpl ; rewrite app_assoc ; apply with_ilr2.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _)...
    * list_simpl ; rewrite app_assoc ; apply zero_ilr.
    * list_simpl ; rewrite app_assoc ; apply plus_ilr.
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _)...
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         simpl in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hwith _ _)...
    * list_simpl ; rewrite app_assoc ; apply de_ilr.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _)...
    * list_simpl ; rewrite app_assoc ; apply wk_ilr.
      list_simpl ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _)...
    * list_simpl ; rewrite app_assoc ; apply co_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _)...
    * rewrite f in P_cutfree ; inversion P_cutfree.
    * exfalso ; assert (Hiq := P_gax_at_r a) ; rewrite H0 in Hiq ; inversion Hiq.
  + rewrite 2 app_assoc.
    apply with_ilr2.
    revert Hl IHsize ; list_simpl ; intros Hl IHsize.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
- (* zero_ilr *)
  trichot_Type_elt_elt_exec Heql.
  + list_simpl.
    apply zero_ilr.
  + remember (zero_ilr _ l3 l4 C) as Hzero ; clear HeqHzero.
    remember izero as D ; destruct_ill pi1 f X l Hl2 Hr2 HP a ; try inversion HeqD.
    * apply (ex_ir _ (l3 ++ l ++ l4)).
      -- simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hzero _ _)...
      -- apply PEperm_Type_app_head ; apply PEperm_Type_app_tail...
    * list_simpl ; rewrite app_assoc ; eapply ex_oc_ir...
      list_simpl ; rewrite (app_assoc l) ; rewrite (app_assoc _ l2) ; rewrite <- (app_assoc l).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hzero _ _)...
    * list_simpl ; rewrite app_assoc ; apply one_ilr.
      list_simpl ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hzero _ _)...
    * list_simpl ; rewrite app_assoc ; apply tens_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hzero _ _)...
    * list_simpl ; rewrite app_assoc ; apply lpam_ilr...
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hzero _ _)...
    * list_simpl ; rewrite app_assoc ; apply lmap_ilr...
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hzero _ _)...
    * list_simpl ; rewrite app_assoc ; apply with_ilr1.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hzero _ _)...
    * list_simpl ; rewrite app_assoc ; apply with_ilr2.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hzero _ _)...
    * list_simpl ; rewrite app_assoc ; apply zero_ilr.
    * list_simpl ; rewrite app_assoc ; apply plus_ilr.
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hzero _ _)...
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         simpl in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hzero _ _)...
    * list_simpl ; rewrite app_assoc ; apply de_ilr.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hzero _ _)...
    * list_simpl ; rewrite app_assoc ; apply wk_ilr.
      list_simpl ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hzero _ _)...
    * list_simpl ; rewrite app_assoc ; apply co_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hzero _ _)...
    * rewrite f in P_cutfree ; inversion P_cutfree.
    * exfalso ; assert (Hiq := P_gax_at_r a) ; rewrite H0 in Hiq ; inversion Hiq.
  + rewrite 2 app_assoc.
    apply zero_ilr.
- (* plus_irr1 *)
  simpl in IHsize.
  apply plus_irr1.
  refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
- (* plus_irr2 *)
  simpl in IHsize.
  apply plus_irr2.
  refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
- (* plus_ilr *)
  trichot_Type_elt_elt_exec Heql.
  + list_simpl.
    apply plus_ilr.
    * revert Hl IHsize ; simpl ; rewrite app_comm_cons ; rewrite app_assoc ; intros Hl IHsize.
      rewrite app_comm_cons ; rewrite app_assoc.
      refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
    * revert Hr IHsize ; simpl ; rewrite app_comm_cons ; rewrite app_assoc ; intros Hr IHsize.
      rewrite app_comm_cons ; rewrite app_assoc.
      refine (IHsize _ _ _ _ _ pi1 Hr _ _)...
  + remember (plus_ilr _ _ _ _ _ _ Hl Hr) as Hplus ; clear HeqHplus.
    remember (iplus A0 B) as D ; destruct_ill pi1 f X l Hl2 Hr2 HP a ; try inversion HeqD.
    * apply (ex_ir _ (l3 ++ l ++ l4)).
      -- simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hplus _ _)...
      -- apply PEperm_Type_app_head ; apply PEperm_Type_app_tail...
    * list_simpl ; rewrite app_assoc ; eapply ex_oc_ir...
      list_simpl ; rewrite (app_assoc l) ; rewrite (app_assoc _ l2) ; rewrite <- (app_assoc l).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hplus _ _)...
    * list_simpl ; rewrite app_assoc ; apply one_ilr.
      list_simpl ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hplus _ _)...
    * list_simpl ; rewrite app_assoc ; apply tens_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hplus _ _)...
    * list_simpl ; rewrite app_assoc ; apply lpam_ilr...
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hplus _ _)...
    * list_simpl ; rewrite app_assoc ; apply lmap_ilr...
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hplus _ _)...
    * list_simpl ; rewrite app_assoc ; apply with_ilr1.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hplus _ _)...
    * list_simpl ; rewrite app_assoc ; apply with_ilr2.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hplus _ _)...
    * list_simpl ; rewrite app_assoc ; apply zero_ilr.
    * simpl in Hc ; subst ; refine (IHcut _ _ _ _ _ _ Hl2 Hl)...
    * simpl in Hc ; subst ; refine (IHcut _ _ _ _ _ _ Hl2 Hr)...
    * list_simpl ; rewrite app_assoc ; apply plus_ilr.
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hplus _ _)...
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         simpl in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hplus _ _)...
    * list_simpl ; rewrite app_assoc ; apply de_ilr.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hplus _ _)...
    * list_simpl ; rewrite app_assoc ; apply wk_ilr.
      list_simpl ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hplus _ _)...
    * list_simpl ; rewrite app_assoc ; apply co_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hplus _ _)...
    * rewrite f in P_cutfree ; inversion P_cutfree.
    * exfalso ; assert (Hiq := P_gax_at_r a) ; rewrite H0 in Hiq ; inversion Hiq.
  + rewrite 2 app_assoc.
    apply plus_ilr.
    * revert Hl IHsize ; list_simpl ; intros Hl IHsize.
      list_simpl ; refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
    * revert Hr IHsize ; list_simpl ; intros Hr IHsize.
      list_simpl ; refine (IHsize _ _ _ _ _ pi1 Hr _ _)...
- (* oc_irr *)
  remember (oc_irr _ _ _ Hl) as Hloc ; rewrite HeqHloc in IHsize ; clear HeqHloc.
  symmetry in Heql ; decomp_map_Type Heql ; subst ; simpl in pi1.
  simpl in IHsize ; simpl in Hl ; list_simpl.
  eapply (cut_oc_comm_left _ (ipsize pi1))...
  + change (ioc x :: map ioc l6) with (map ioc (x :: l6)) ; rewrite <- map_app ; apply oc_irr...
  + intros lw Hs' pi.
    rewrite <- 2 map_app ; apply oc_irr.
    revert Hl IHsize ; list_simpl ; intros Hl IHsize.
    refine (IHsize _ _ _ _ _ (oc_irr _ _ _ Hs') Hl _ _) ; simpl...
- (* de_ilr *)
  trichot_Type_elt_elt_exec Heql.
  + list_simpl.
    apply de_ilr.
    revert Hl IHsize ; simpl ; rewrite app_comm_cons ; rewrite app_assoc ; intros Hl IHsize.
    rewrite app_comm_cons ; rewrite app_assoc.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
  + eapply (cut_oc_comm_left _ (ipsize pi1))...
    * apply de_ilr...
    * intros lw Hs pi.
      simpl in Hc ; refine (IHsize _ _ _ _ _ Hs Hl _ _) ; simpl...
  + rewrite 2 app_assoc.
    apply de_ilr.
    revert Hl IHsize ; list_simpl ; intros Hl IHsize.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
- (* wk_ilr *)
  trichot_Type_elt_elt_exec Heql.
  + list_simpl.
    apply wk_ilr.
    revert Hl IHsize ; simpl ; rewrite app_assoc ; intros Hl IHsize.
    rewrite app_assoc.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
  + eapply (cut_oc_comm_left _ (ipsize pi1))...
    * apply wk_ilr...
    * intros lw Hs pi.
      apply wk_list_ilr...
  + rewrite 2 app_assoc.
    apply wk_ilr.
    revert Hl IHsize ; list_simpl ; intros Hl IHsize.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
- (* co_ilr *)
  trichot_Type_elt_elt_exec Heql.
  + list_simpl.
    apply co_ilr.
    revert Hl IHsize ; simpl ; rewrite 2 app_comm_cons ; rewrite app_assoc ; intros Hl IHsize.
    rewrite 2 app_comm_cons ; rewrite app_assoc.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
  + eapply (cut_oc_comm_left _ (ipsize pi1))...
    * apply co_ilr...
    * intros lw Hs _.
      replace (ioc A0 :: ioc A0 :: l4)
         with (flat_map (cons (ioc A0)) (nil :: l4 :: nil)) in Hl  by (list_simpl ; reflexivity).
      apply co_list_ilr.
      replace (map ioc lw ++ map ioc lw ++ l4)
         with (flat_map (app (map ioc lw)) (nil :: l4 :: nil)) by (list_simpl ; reflexivity).
      refine (substitution_ioc _ _ _ _ _ _ _ _ _ _ _) ; list_simpl...
      apply IHcut...
  + rewrite 2 app_assoc.
    apply co_ilr.
    revert Hl IHsize ; list_simpl ; intros Hl IHsize.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _)...
- (* cut_ir *)
  rewrite f in P_cutfree ; inversion P_cutfree.
- (* gax_ir *)
  assert (Hiq := P_gax_at_l a) ; rewrite Heql in Hiq.
  apply Forall_elt in Hiq.
  simpl in IHsize.
  remember (gax_ir _ a) as Hgax ; apply (f_equal ipsize) in HeqHgax ; simpl in HeqHgax.
  destruct_ill pi1 f X l Hl2 Hr2 HP b ; try (exfalso ; inversion Hiq ; fail).
  + list_simpl ; rewrite <- Heql ; apply (gax_ir _ a).
  + apply (ex_ir _ (l1 ++ l ++ l2)).
    * revert Hgax HeqHgax ; rewrite Heql ; intros Hgax HeqHgax.
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hgax _ _)...
    * apply PEperm_Type_app_head ; apply PEperm_Type_app_tail...
  + list_simpl ; rewrite app_assoc ; eapply ex_oc_ir...
      list_simpl ; rewrite (app_assoc l) ; rewrite (app_assoc _ l0) ; rewrite <- (app_assoc l).
      revert Hgax HeqHgax ; rewrite Heql ; intros Hgax HeqHgax.
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hgax _ _)...
  + list_simpl ; rewrite app_assoc ; apply one_ilr.
    list_simpl ; rewrite (app_assoc l1).
    revert Hgax HeqHgax ; rewrite Heql ; list_simpl ; rewrite (app_assoc l0) ; intros Hgax HeqHgax.
    simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hgax _ _)...
  + list_simpl ; rewrite app_assoc ; apply tens_ilr.
    list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
    revert Hgax HeqHgax ; rewrite Heql ; list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l0) ;
      intros Hgax HeqHgax.
    simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hgax _ _)...
  + list_simpl ; rewrite app_assoc ; apply lpam_ilr...
    list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
    revert Hgax HeqHgax ; rewrite Heql ; list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l3) ;
      intros Hgax HeqHgax.
    simpl in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hgax _ _)...
  + exfalso.
    apply (P_gax_noN_l a).
    rewrite Heql.
    apply in_elt.
  + list_simpl ; rewrite app_assoc ; apply lmap_ilr...
    list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
    revert Hgax HeqHgax ; rewrite Heql ; list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l3) ;
      intros Hgax HeqHgax.
    simpl in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hgax _ _)...
  + exfalso.
    apply (P_gax_noN_l a).
    rewrite Heql.
    apply in_elt.
  + list_simpl ; rewrite app_assoc ; apply with_ilr1.
    list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
    revert Hgax HeqHgax ; rewrite Heql ; list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l0) ;
      intros Hgax HeqHgax.
    simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hgax _ _)...
  + list_simpl ; rewrite app_assoc ; apply with_ilr2.
    list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
    revert Hgax HeqHgax ; rewrite Heql ; list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l0) ;
      intros Hgax HeqHgax.
    simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hgax _ _)...
  + list_simpl ; rewrite app_assoc ; apply zero_ilr.
  + list_simpl ; rewrite app_assoc ; apply plus_ilr.
    * list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      revert Hgax HeqHgax ; rewrite Heql ; list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l0) ;
        intros Hgax HeqHgax.
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hgax _ _)...
    * list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      revert Hgax HeqHgax ; rewrite Heql ; list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l0) ;
        intros Hgax HeqHgax.
      simpl in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hgax _ _)...
  + list_simpl ; rewrite app_assoc ; apply de_ilr.
    list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
    revert Hgax HeqHgax ; rewrite Heql ; list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l0) ;
      intros Hgax HeqHgax.
    simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hgax _ _)...
  + list_simpl ; rewrite app_assoc ; apply wk_ilr.
    list_simpl ; rewrite (app_assoc l1).
    revert Hgax HeqHgax ; rewrite Heql ; list_simpl ; rewrite (app_assoc l0) ; intros Hgax HeqHgax.
    simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hgax _ _)...
  + list_simpl ; rewrite app_assoc ; apply co_ilr.
    list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
    revert Hgax HeqHgax ; rewrite Heql ; list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l0) ;
      intros Hgax HeqHgax.
    simpl in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hgax _ _)...
  + rewrite f in P_cutfree ; inversion P_cutfree.
  + destruct (P_gax_cut b a _ _ Heql) as [x [Hx1 Hx2]].
    rewrite Hx1 ; rewrite Hx2.
    apply (gax_ir _ x).
Unshelve. all : assumption.
Qed.

End Cut_Elim_Proof.

(** ** Variants on cut admissibility *)

(** If axioms are atomic and closed under cut, then the cut rule is admissible:
provability is preserved if we remove the cut rule. *)
Lemma cut_admissible_ill {P} :
  (forall a, In N (fst (projT2 (ipgax P) a)) -> False) ->
  (forall a, Forall iatomic (fst (projT2 (ipgax P) a))) ->
  (forall a, iatomic (snd (projT2 (ipgax P) a))) ->
  (forall a b l1 l2, fst (projT2 (ipgax P) b) = l1 ++ snd (projT2 (ipgax P) a) :: l2 -> 
                  { c | l1 ++ fst (projT2 (ipgax P) a) ++ l2 = fst (projT2 (ipgax P) c)
                        /\ snd (projT2 (ipgax P) b) = snd (projT2 (ipgax P) c) }) ->
  forall l C, ill P l C -> ill (cutrm_ipfrag P) l C.
Proof with myeeasy.
intros HatNl Hatl Hatr Hcut l C pi.
induction pi ; try (econstructor ; myeeasy ; fail).
- eapply cut_ir_gaxat...
- assert (ipgax P = ipgax (cutrm_ipfrag P)) as Hgax by reflexivity.
  revert a ; rewrite Hgax ; apply gax_ir.
Qed.

(** If there are no axioms (except the identity rule), then the cut rule is valid. *)
Lemma cut_ir_axfree {P} : (projT1 (ipgax P) -> False) -> forall A l0 l1 l2 C, 
  ill P l0 A -> ill P (l1 ++ A :: l2) C -> ill P (l1 ++ l0 ++ l2) C.
Proof.
intros P_axfree A l0 l1 l2 C pi1 pi2.
eapply cut_ir_gaxat ; try eassumption.
all: intros a ; exfalso ; apply (P_axfree a).
Qed.

(** If there are no axioms (except the identity rule), then the cut rule is admissible:
provability is preserved if we remove the cut rule. *)
Lemma cut_admissible_ill_axfree {P} : (projT1 (ipgax P) -> False) -> forall l C,
  ill P l C -> ill (cutrm_ipfrag P) l C.
Proof.
intros P_axfree l C pi.
eapply cut_admissible_ill ; try eassumption.
all: intros a ; exfalso ; apply (P_axfree a).
Qed.


(** ** Standard intuitionistic linear logic: [ill_ll] (no axiom, commutative) *)

(** cut / axioms / permutation *)
Definition ipfrag_ill := mk_ipfrag false NoIAxioms true.
(*                                 cut   axioms    perm  *)
Definition ill_ll := ill ipfrag_ill.

Lemma cut_ll_ir : forall A l0 l1 l2 C, 
  ill_ll l0 A -> ill_ll (l1 ++ A :: l2) C -> ill_ll (l1 ++ l0 ++ l2) C.
Proof with myeeasy.
intros A l1 l2 pi1 pi2.
eapply cut_ir_axfree...
intros a ; destruct a.
Qed.

Lemma cut_ll_admissible :
  forall l C, ill (cutupd_ipfrag ipfrag_ill true) l C -> ill_ll l C.
Proof with myeeasy.
intros l C pi.
induction pi ; try (now econstructor).
- eapply ex_ir...
- eapply ex_oc_ir...
- eapply cut_ll_ir...
Qed.


