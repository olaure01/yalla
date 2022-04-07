(* ill library for yalla *)

(** * Intuitionistic Linear Logic *)
(* Cut admissibility, see ill_prop.v for other properties *)

From Coq Require Import PeanoNat Wf_nat List Lia.
From OLlibs Require Import funtheory dectype List_more flat_map_more
                           Permutation_Type_more GPermutation_Type.
From Yalla Require Export ill_cut_at.

Set Implicit Arguments.


Section Atoms.

Context { preiatom : DecType }.

Section Cut_Elim_Proof.

Context { P : @ipfrag preiatom }.
Hypothesis P_gax_noN_l : forall a, notT (In_inf N (fst (projT2 (ipgax P) a))).
Hypothesis P_gax_at_l : forall a, Forall_inf iatomic (fst (projT2 (ipgax P) a)).
Hypothesis P_gax_at_r : forall a, iatomic (snd (projT2 (ipgax P) a)).
Hypothesis P_gax_cut : forall a b l1 l2,
                            fst (projT2 (ipgax P) b) = l1 ++ snd (projT2 (ipgax P) a) :: l2 -> 
                          { c | l1 ++ fst (projT2 (ipgax P) a) ++ l2 = fst (projT2 (ipgax P) c)
                              & snd (projT2 (ipgax P) b) = snd (projT2 (ipgax P) c) }.

Lemma cut_oc_comm_left (P_cutfree : ipcut P = false) n A C l1 l2 : ill P (l1 ++ ioc A :: l2) C ->
  (forall lw (pi0 : ill P (map ioc lw) A), ipsize pi0 < n -> ill P (l1 ++ map ioc lw ++ l2) C) ->
  forall l0 (pi1 : ill P l0 (ioc A)), ipsize pi1 <= n -> ill P (l1 ++ l0 ++ l2) C.
Proof.
intros pi2; induction n; intros IH l0 pi1 Hs;
  remember (ioc A) as B; destruct_ill pi1 f X l Hl Hr HP a;
  try (now exfalso); try inversion HeqB.
- apply (ex_ir (l1 ++ l ++ l2)).
  + cbn in Hs.
    refine (IHn _ _ Hl _); [ | lia ].
    intros; refine (IH _ pi0 _); lia.
  + apply PEPermutation_Type_app_head, PEPermutation_Type_app_tail; assumption.
- list_simpl; rewrite app_assoc; eapply ex_oc_ir; [ | eassumption ].
  list_simpl; rewrite (app_assoc l), (app_assoc _ l0), <- (app_assoc l).
  cbn in Hs; refine (IHn _ _ Hl _); [ | lia ].
  intros; refine (IH _ pi0 _); lia.
- list_simpl; rewrite app_assoc ; apply one_ilr.
  list_simpl; rewrite (app_assoc l0).
  cbn in Hs; refine (IHn _ _ Hl _); [ | lia ].
  intros; refine (IH _ pi0 _); lia.
- list_simpl; rewrite app_assoc ; apply tens_ilr.
  list_simpl; rewrite 2 app_comm_cons ; rewrite (app_assoc l0).
  cbn in Hs; refine (IHn _ _ Hl _); [ | lia ].
  intros; refine (IH _ pi0 _); lia.
- list_simpl; rewrite app_assoc ; apply lpam_ilr; [ assumption | ].
  list_simpl; rewrite app_comm_cons ; rewrite (app_assoc l3).
  cbn in Hs; refine (IHn _ _ Hr _); [ | lia ].
  intros; refine (IH _ pi0 _); lia.
- list_simpl; rewrite app_assoc ; apply lmap_ilr; [ assumption | ].
  list_simpl; rewrite app_comm_cons ; rewrite (app_assoc l3).
  cbn in Hs; refine (IHn _ _ Hr _); [ | lia ].
  intros; refine (IH _ pi0 _); lia.
- list_simpl; rewrite app_assoc ; apply with_ilr1.
  list_simpl; rewrite app_comm_cons ; rewrite (app_assoc l0).
  cbn in Hs; refine (IHn _ _ Hl _); [ | lia ].
  intros; refine (IH _ pi0 _); lia.
- list_simpl; rewrite app_assoc ; apply with_ilr2.
  list_simpl; rewrite app_comm_cons ; rewrite (app_assoc l0).
  cbn in Hs; refine (IHn _ _ Hl _); [ | lia ].
  intros; refine (IH _ pi0 _); lia.
- list_simpl; rewrite app_assoc ; apply zero_ilr.
- list_simpl; rewrite app_assoc ; apply plus_ilr.
  + list_simpl; rewrite app_comm_cons ; rewrite (app_assoc l0).
    cbn in Hs; refine (IHn _ _ Hl _); [ | lia ].
    intros; refine (IH _ pi0 _); lia.
  + list_simpl; rewrite app_comm_cons ; rewrite (app_assoc l0).
    cbn in Hs; refine (IHn _ _ Hr _); [ | lia ].
    intros; refine (IH _ pi0 _); lia.
- subst; apply (IH _ Hl); cbn in Hs; lia.
- list_simpl; rewrite app_assoc ; apply de_ilr.
  list_simpl; rewrite app_comm_cons ; rewrite (app_assoc l0).
  cbn in Hs; refine (IHn _ _ Hl _); [ | lia ].
  intros; refine (IH _ pi0 _); lia.
- list_simpl; rewrite app_assoc ; apply wk_ilr.
  list_simpl; rewrite (app_assoc l0).
  cbn in Hs; refine (IHn _ _ Hl _); [ | lia ].
  intros; refine (IH _ pi0 _); lia.
- list_simpl; rewrite app_assoc ; apply co_ilr.
  list_simpl; rewrite 2 app_comm_cons ; rewrite (app_assoc l0).
  cbn in Hs; refine (IHn _ _ Hl _); [ | lia ].
  intros; refine (IH _ pi0 _); lia.
- rewrite f in P_cutfree; inversion P_cutfree.
- exfalso; assert (Hiq := P_gax_at_r a); rewrite H0 in Hiq; inversion Hiq.
Qed.

Lemma substitution_ioc : ipcut P = false -> forall A,
  (forall l0 l1 l2 C, ill P l0 A -> ill P (l1 ++ A :: l2) C -> ill P (l1 ++ l0 ++ l2) C) ->
  forall lw l C, ill P (map ioc lw) A -> ill P l C -> forall l' L,
  l = l' ++ flat_map (cons (ioc A)) L -> ill P (l' ++ flat_map (app (map ioc lw)) L) C.
Proof.
intros P_cutfree A IHcut lw l C pi1 pi2.
induction pi2 ; intros l' L Heq.
- destruct l' ; inversion Heq.
  + destruct L ; inversion Heq.
  + symmetry in H1 ; apply app_eq_nil in H1 ; destruct H1 ; subst.
    destruct L ; inversion H1.
    apply ax_ir.
- case_eq (ipperm P) ; intros Hperm ; rewrite Hperm in p ; cbn in p ; subst.
  + destruct (Permutation_Type_app_flat_map_cst _ (map ioc lw) _ _ p)
      as [[L' l''] (Hnil' & HeqL' & HPL')];
      cbn in Hnil' ; cbn in HeqL' ; cbn in HPL' ; subst.
    eapply ex_ir ; [ | rewrite Hperm ; cbn ; apply HPL' ].
    refine (IHpi2 _ _ _); reflexivity.
  + refine (IHpi2 _ _ _); reflexivity.
- assert (injective (@ioc preiatom)) as Hinj by (intros x y Hxy ; inversion Hxy ; reflexivity).
  destruct (Permutation_Type_flat_map_cons_flat_map_app_cst _ Hinj lw _ _ _ _ p Heq)
    as [(((((lw1',lw2'),l1'),l2'),l''),L') HH] ; cbn in HH ; destruct HH as (H1 & H2 & H3 & H4).
  rewrite <- H4 ; apply (ex_oc_ir _ lw1'); [ | assumption ].
  rewrite H3 ; apply IHpi2; assumption.
- symmetry in Heq ; apply app_eq_nil in Heq ; destruct Heq as [H Heq] ; subst.
  destruct L ; inversion Heq.
  apply one_irr.
- elt_vs_app_flat_map_cst_inv Heq.
  + list_simpl ; apply one_ilr.
    rewrite app_assoc ; refine (IHpi2 _ _ _) ; list_simpl; reflexivity.
  + rewrite flat_map_app.
    list_simpl ; rewrite 3 app_assoc ; apply one_ilr.
    rewrite <- 3 app_assoc.
    replace (map ioc lw ++ l ++ l0 ++ flat_map (app (map ioc lw)) L1)
       with (flat_map (app (map ioc lw)) ((l ++ l0) :: L1)) by (list_simpl ; reflexivity).
    rewrite <- flat_map_app ; refine (IHpi2 _ _ _).
    rewrite ? flat_map_app ; list_simpl; reflexivity.
- app_vs_app_flat_map_cst_inv Heq.
  + list_simpl ; apply tens_irr; [ assumption | ].
    refine (IHpi2_2 _ _ _); reflexivity.
  + rewrite flat_map_app ; list_simpl.
    rewrite 3 app_assoc ; apply tens_irr.
    * list_simpl.
      replace (flat_map (app (map ioc lw)) L0 ++ map ioc lw ++ l)
         with (flat_map (app (map ioc lw)) (L0 ++ l :: nil))
        by (rewrite flat_map_app ; list_simpl ; reflexivity).
      refine (IHpi2_1 _ _ _); reflexivity.
    * refine (IHpi2_2 _ _ _); reflexivity.
  + rewrite flat_map_app ; list_simpl.
    rewrite app_assoc ; apply tens_irr.
    * refine (IHpi2_1 _ _ _); reflexivity.
    * rewrite <- (app_nil_l _) ; refine (IHpi2_2 _ _ _); reflexivity.
- elt_vs_app_flat_map_cst_inv Heq.
  + list_simpl ; apply tens_ilr.
    rewrite 2 app_comm_cons ; rewrite app_assoc ; refine (IHpi2 _ _ _) ; list_simpl; reflexivity.
  + rewrite flat_map_app.
    list_simpl ; rewrite 3 app_assoc ; apply tens_ilr.
    rewrite <- 3 app_assoc.
    replace (map ioc lw ++ l ++ A0 :: B :: l0 ++ flat_map (app (map ioc lw)) L1)
      with (flat_map (app (map ioc lw)) ((l ++ A0 :: B :: l0) :: L1)) by (list_simpl ; reflexivity).
    rewrite <- flat_map_app ; refine (IHpi2 _ _ _).
    rewrite ? flat_map_app ; list_simpl; reflexivity.
- apply lpam_irr.
  induction L using rev_rect ; list_simpl.
  + change nil with (nil ++ flat_map (app (map ioc lw)) nil).
    rewrite app_comm_cons, app_assoc; refine (IHpi2 _ _ _); subst; list_simpl; reflexivity.
  + replace (flat_map (app (map ioc lw)) L ++ map ioc lw ++ x ++ A0 :: nil)
       with (flat_map (app (map ioc lw)) (L ++ (x ++ (A0 :: nil)) :: nil))
      by now list_simpl.
    refine (IHpi2 _ _ _) ; subst ; list_simpl; reflexivity.
- elt_vs_app_flat_map_cst_inv Heq.
  + app_vs_app_flat_map_cst_inv Heq1.
    * list_simpl ; apply lpam_ilr; [ assumption | ].
      rewrite app_comm_cons, app_assoc; refine (IHpi2_2 _ _ _); list_simpl; reflexivity.
    * list_simpl ; rewrite ? flat_map_app ; list_simpl.
      rewrite (app_assoc l) ; rewrite (app_assoc _ (map ioc lw)) ; rewrite (app_assoc _ l3).
      replace (((l ++ flat_map (app (map ioc lw)) L0) ++ map ioc lw) ++ l3)
         with (l ++ flat_map (app (map ioc lw)) (L0 ++ l3 :: nil))
        by (rewrite flat_map_app ; list_simpl ; reflexivity).
      apply lpam_ilr.
      -- refine (IHpi2_1 _ _ _); reflexivity.
      -- rewrite app_comm_cons, app_assoc; refine (IHpi2_2 _ _ _); list_simpl; reflexivity.
    * list_simpl; rewrite (app_assoc l) ; apply lpam_ilr.
      -- refine (IHpi2_1 _ _ _); reflexivity.
      -- rewrite <- (app_nil_l (flat_map _ _)), app_comm_cons, app_assoc;
           refine (IHpi2_2 _ _ _); list_simpl; reflexivity.
  + app_vs_app_flat_map_cst_inv Heq2.
    * list_simpl ; rewrite ? flat_map_app ; list_simpl.
      rewrite (app_assoc l') ; rewrite (app_assoc _ (map ioc lw)) ; rewrite (app_assoc _ l).
      replace (((l' ++ flat_map (app (map ioc lw)) L0) ++ map ioc lw) ++ l)
         with (l' ++ flat_map (app (map ioc lw)) (L0 ++ l :: nil))
        by (rewrite flat_map_app ; list_simpl ; reflexivity).
      apply lpam_ilr; [ assumption | ].
      list_simpl.
      replace (flat_map (app (map ioc lw)) L0 ++ map ioc lw ++ l ++
                 B :: l1 ++ flat_map (app (map ioc lw)) L1)
         with (flat_map (app (map ioc lw)) (L0 ++ (l ++ B :: l1) :: L1))
        by now list_simpl.
      refine (IHpi2_2 _ _ _); list_simpl; reflexivity.
    * list_simpl; rewrite (app_assoc l3), (app_assoc _ _ (l1 ++ _)), (app_assoc _ l1).
      replace (((l3 ++ flat_map (app (map ioc lw)) L) ++ map ioc lw) ++ l1)
         with (l3 ++ flat_map (app (map ioc lw)) (L ++ l1 :: nil))
        by (rewrite flat_map_app ; list_simpl ; reflexivity).
      rewrite 3 app_assoc ; apply lpam_ilr.
      -- refine (IHpi2_1 _ _ _); reflexivity.
      -- list_simpl.
         replace (flat_map (app (map ioc lw)) L0 ++ map ioc lw ++ l ++ B :: l4
                                                 ++ flat_map (app (map ioc lw)) L2)
            with (flat_map (app (map ioc lw)) (L0 ++ (l ++ B :: l4) :: L2))
           by (rewrite ? flat_map_app ; list_simpl ; reflexivity).
         refine (IHpi2_2 _ _ _) ; rewrite ? flat_map_app ; list_simpl; reflexivity.
    * list_simpl ; rewrite ? flat_map_app ; list_simpl ; rewrite ? flat_map_app ; list_simpl.
      rewrite (app_assoc l3) ; rewrite 3 app_assoc ; apply lpam_ilr.
      -- refine (IHpi2_1 _ _ _); reflexivity.
      -- list_simpl.
         replace (flat_map (app (map ioc lw)) L0 ++ map ioc lw ++ l
                                                 ++ B :: flat_map (app (map ioc lw)) L2)
            with (flat_map (app (map ioc lw)) (L0 ++ (l ++ B :: nil) :: L2))
           by (rewrite ? flat_map_app ; list_simpl ; reflexivity).
         refine (IHpi2_2 _ _ _) ; rewrite ? flat_map_app ; list_simpl; reflexivity.
- apply gen_irr.
  induction L using rev_rect ; list_simpl.
  + change nil with (nil ++ flat_map (app (map ioc lw)) nil).
    rewrite app_comm_cons, app_assoc; refine (IHpi2 _ _ _); subst; list_simpl; reflexivity.
  + replace (flat_map (app (map ioc lw)) L ++ map ioc lw ++ x ++ A0 :: nil)
       with (flat_map (app (map ioc lw)) (L ++ (x ++ (A0 :: nil)) :: nil))
      by now list_simpl.
    refine (IHpi2 _ _ _) ; subst ; list_simpl; reflexivity.
- destruct l' ; inversion Heq ; subst.
  + destruct L ; inversion H0.
  + list_simpl.
    apply gen_ilr.
    apply IHpi2; reflexivity.
- apply lmap_irr.
  rewrite app_comm_cons ; refine (IHpi2 _ _ _) ; subst ; list_simpl; reflexivity.
- rewrite app_assoc in Heq; elt_vs_app_flat_map_cst_inv Heq.
  + list_simpl ; apply lmap_ilr; [ assumption | ].
    rewrite app_comm_cons, app_assoc; refine (IHpi2_2 _ _ _); list_simpl; reflexivity.
  + replace (flat_map (cons (ioc A)) L0 ++ ioc A :: l)
       with (flat_map (cons (ioc A)) (L0 ++ l :: nil))
      in Heq1 by (rewrite flat_map_app ; list_simpl ; reflexivity).
    app_vs_app_flat_map_cst_inv Heq1.
    * list_simpl ; rewrite ? flat_map_app ; list_simpl.
      rewrite (app_assoc l2) ; rewrite (app_assoc _ (map ioc lw)) ; rewrite (app_assoc _ l).
      replace (((l2 ++ flat_map (app (map ioc lw)) L0) ++ map ioc lw) ++ l)
         with (l2 ++ flat_map (app (map ioc lw)) (L0 ++ l :: nil))
        by (rewrite flat_map_app ; list_simpl ; reflexivity).
      apply lmap_ilr.
      -- refine (IHpi2_1 _ _ _); reflexivity.
      -- rewrite app_comm_cons, app_assoc; refine (IHpi2_2 _ _ _); list_simpl; reflexivity.
    * induction L2 using rev_rect ; [ | clear IHL2 ].
      -- assert (L0 = L /\ l = l2 ++ l4) as [Heq1 Heq2] ; subst.
         { apply (f_equal (@rev _)) in Heq0.
           rewrite ? rev_app_distr in Heq0.
           inversion Heq0 ; subst.
           apply (f_equal (@rev _)) in H1.
           rewrite ? rev_involutive in H1 ; subst.
           split; reflexivity. }
         list_simpl ; rewrite ? flat_map_app ; list_simpl ; rewrite ? flat_map_app ; list_simpl.
         list_simpl in pi2_1.
         rewrite 3 app_assoc ; apply lmap_ilr; [ assumption | ].
         list_simpl ; rewrite <- app_assoc in IHpi2_2.
         replace (flat_map (cons (ioc A)) (L ++ l2 :: nil) ++ B :: l3 ++ flat_map (cons (ioc A)) L1)
            with (flat_map (cons (ioc A)) (L ++ (l2 ++ B :: l3) :: L1)) in IHpi2_2
           by (rewrite ? flat_map_app ; list_simpl ; reflexivity).
         assert (pi2' := IHpi2_2 _ _ eq_refl).
         rewrite ? flat_map_app in pi2' ; list_simpl in pi2'; assumption.
      -- assert (L0 = L ++ (l2 ++ l4) :: L2 /\ l = x) as [Heq1 Heq2] ; subst.
         { apply (f_equal (@rev _)) in Heq0.
           rewrite ? rev_app_distr in Heq0 ; list_simpl in Heq0.
           inversion Heq0 ; subst.
           apply (f_equal (@rev _)) in H1.
           rewrite ? rev_involutive in H1 ; subst.
           rewrite ? rev_app_distr ; list_simpl ; split; reflexivity. }
         list_simpl ; rewrite ? flat_map_app ; list_simpl ; rewrite ? flat_map_app ; list_simpl.
         rewrite 3 app_assoc, (app_assoc l4), (app_assoc (l4 ++ _)), (app_assoc _ x).
         apply lmap_ilr.
         ++ list_simpl.
            replace (flat_map (app (map ioc lw)) L2 ++ map ioc lw ++ x)
               with (flat_map (app (map ioc lw)) (L2 ++ x :: nil))
              by (rewrite flat_map_app ; list_simpl ; reflexivity).
            refine (IHpi2_1 _ _ _); reflexivity.
         ++ list_simpl ; rewrite <- app_assoc in IHpi2_2.
            replace (flat_map (cons (ioc A)) (L ++ l2 :: nil) ++
                       B :: l3 ++ flat_map (cons (ioc A)) L1)
               with (flat_map (cons (ioc A)) (L ++ (l2 ++ B :: l3) :: L1)) in IHpi2_2
              by (rewrite ? flat_map_app ; list_simpl ; reflexivity).
            assert (pi2' := IHpi2_2 _ _ eq_refl).
            rewrite ? flat_map_app in pi2' ; list_simpl in pi2'; assumption.
    * induction L2 using rev_rect ; [ | clear IHL2 ].
      -- list_simpl in Heq0 ; subst.
         list_simpl ; rewrite ? flat_map_app ; list_simpl ; rewrite ? flat_map_app ; list_simpl.
         list_simpl in pi2_1.
         rewrite <- (app_nil_l (ilmap _ _ :: _)), 3 app_assoc; apply lmap_ilr; [ assumption | ].
         list_simpl ; rewrite <- app_assoc in IHpi2_2.
         replace (flat_map (cons (ioc A)) (L0 ++ l :: nil) ++ B :: l3 ++ flat_map (cons (ioc A)) L1)
            with (flat_map (cons (ioc A)) (L0 ++ (l ++ B :: l3) :: L1)) in IHpi2_2
           by (rewrite ? flat_map_app ; list_simpl ; reflexivity).
         assert (pi2' := IHpi2_2 _ _ eq_refl).
         rewrite ? flat_map_app in pi2' ; list_simpl in pi2'; assumption.
      -- assert (L0 = L ++ L2 /\ l = x) as [Heq1 Heq2] ; subst.
         { apply (f_equal (@rev _)) in Heq0.
           rewrite ? rev_app_distr in Heq0 ; list_simpl in Heq0.
           inversion Heq0 ; subst.
           apply (f_equal (@rev _)) in H1.
           rewrite rev_involutive in H1 ; subst.
           rewrite rev_app_distr ; list_simpl ; split; reflexivity. }
         list_simpl ; rewrite ? flat_map_app ; list_simpl ; rewrite ? flat_map_app ; list_simpl.
         rewrite app_assoc, (app_assoc _ (map ioc lw)), (app_assoc _ x); apply lmap_ilr.
         ++ list_simpl.
            replace (flat_map (app (map ioc lw)) L2 ++ map ioc lw ++ x)
               with (flat_map (app (map ioc lw)) (L2 ++ x :: nil))
              by (rewrite flat_map_app ; list_simpl ; reflexivity).
            rewrite <- (app_nil_l _).
            refine (IHpi2_1 _ _ _); reflexivity.
         ++ induction L using rev_rect ; [ | clear IHL ].
            ** list_simpl in IHpi2_2 ; list_simpl.
               rewrite app_comm_cons, app_assoc; refine (IHpi2_2 _ _ _); list_simpl; reflexivity.
            ** list_simpl ; rewrite <- app_assoc in IHpi2_2.
               replace (flat_map (cons (ioc A)) (L ++ x0 :: nil) ++
                          B :: l3 ++ flat_map (cons (ioc A)) L1)
                  with (flat_map (cons (ioc A)) (L ++ (x0 ++ B :: l3) :: L1)) in IHpi2_2
                 by (rewrite ? flat_map_app ; list_simpl ; reflexivity).
               assert (pi2' := IHpi2_2 _ _ eq_refl).
               rewrite ? flat_map_app in pi2' ; list_simpl in pi2'.
               rewrite ? flat_map_app ; list_simpl; assumption.
- apply neg_irr.
  rewrite app_comm_cons ; refine (IHpi2 _ _ _) ; subst ; list_simpl; reflexivity.
- elt_vs_app_flat_map_cst_inv Heq.
  + symmetry in Heq1 ; apply app_eq_nil in Heq1 ; destruct Heq1 as [Heq Heq1] ; subst.
    destruct L ; inversion Heq1.
    list_simpl ; apply neg_ilr; assumption.
  + symmetry in Heq2 ; apply app_eq_nil in Heq2 ; destruct Heq2 as [Heq Heq2] ; subst.
    destruct L1 ; inversion Heq2.
    rewrite flat_map_app.
    list_simpl ; rewrite 3 app_assoc ; apply neg_ilr.
    rewrite <- 2 app_assoc.
    replace (map ioc lw ++ l0)
      with (flat_map (app (map ioc lw)) (l0 :: nil)) by (list_simpl ; reflexivity).
    rewrite <- flat_map_app ; refine (IHpi2 _ _ _).
    rewrite ? flat_map_app ; list_simpl; reflexivity.
- apply top_irr.
- apply with_irr.
  + refine (IHpi2_1 _ _ _) ; list_simpl; assumption.
  + refine (IHpi2_2 _ _ _) ; list_simpl; assumption.
- elt_vs_app_flat_map_cst_inv Heq.
  + list_simpl ; apply with_ilr1.
    rewrite app_comm_cons, app_assoc; refine (IHpi2 _ _ _); list_simpl; reflexivity.
  + rewrite flat_map_app.
    list_simpl ; rewrite 3 app_assoc ; apply with_ilr1.
    rewrite <- 3 app_assoc.
    replace (map ioc lw ++ l ++ A0 :: l0 ++ flat_map (app (map ioc lw)) L1)
      with (flat_map (app (map ioc lw)) ((l ++ A0 :: l0) :: L1)) by (list_simpl ; reflexivity).
    rewrite <- flat_map_app ; refine (IHpi2 _ _ _).
    rewrite ? flat_map_app ; list_simpl; reflexivity.
- elt_vs_app_flat_map_cst_inv Heq.
  + list_simpl ; apply with_ilr2.
    rewrite app_comm_cons, app_assoc; refine (IHpi2 _ _ _); list_simpl; reflexivity.
  + rewrite flat_map_app.
    list_simpl ; rewrite 3 app_assoc ; apply with_ilr2.
    rewrite <- 3 app_assoc.
    replace (map ioc lw ++ l ++ A0 :: l0 ++ flat_map (app (map ioc lw)) L1)
      with (flat_map (app (map ioc lw)) ((l ++ A0 :: l0) :: L1)) by (list_simpl ; reflexivity).
    rewrite <- flat_map_app ; refine (IHpi2 _ _ _).
    rewrite ? flat_map_app ; list_simpl; reflexivity.
- elt_vs_app_flat_map_cst_inv Heq.
  + list_simpl ; apply zero_ilr.
  + rewrite flat_map_app.
    list_simpl ; rewrite 3 app_assoc ; apply zero_ilr.
- apply plus_irr1.
  refine (IHpi2 _ _ _) ; subst ; list_simpl; reflexivity.
- apply plus_irr2.
  refine (IHpi2 _ _ _) ; subst ; list_simpl; reflexivity.
- elt_vs_app_flat_map_cst_inv Heq.
  + list_simpl ; apply plus_ilr.
    * rewrite app_comm_cons, app_assoc; refine (IHpi2_1 _ _ _); list_simpl; reflexivity.
    * rewrite app_comm_cons, app_assoc; refine (IHpi2_2 _ _ _); list_simpl; reflexivity.
  + rewrite flat_map_app.
    list_simpl ; rewrite 3 app_assoc ; apply plus_ilr ; rewrite <- 3 app_assoc.
    * replace (map ioc lw ++ l ++ A0 :: l0 ++ flat_map (app (map ioc lw)) L1)
        with (flat_map (app (map ioc lw)) ((l ++ A0 :: l0) :: L1)) by (list_simpl ; reflexivity).
      rewrite <- flat_map_app ; refine (IHpi2_1 _ _ _).
      rewrite ? flat_map_app ; list_simpl; reflexivity.
    * replace (map ioc lw ++ l ++ B :: l0 ++ flat_map (app (map ioc lw)) L1)
        with (flat_map (app (map ioc lw)) ((l ++ B :: l0) :: L1)) by (list_simpl ; reflexivity).
      rewrite <- flat_map_app ; refine (IHpi2_2 _ _ _).
      rewrite ? flat_map_app ; list_simpl; reflexivity.
- decomp_map_inf Heq; subst; cbn in Heq2; cbn.
  assert ({ Lw | flat_map (app (map ioc lw)) L = map ioc Lw }) as [Lw HeqLw].
  { clear pi2 IHpi2 ; revert l2 Heq2 ; clear ; induction L ; intros l2 Heq2.
    - exists nil; reflexivity.
    - cbn in Heq2.
      decomp_map_inf Heq2 ; subst.
      inversion Heq1 ; subst ; cbn.
      cbn in Heq4 ; apply IHL in Heq4.
      destruct Heq4 as [Lw Heq4].
      exists (lw ++ l1 ++ Lw) ; list_simpl ; rewrite <- Heq4; reflexivity. }
  rewrite HeqLw ; rewrite <- map_app ; apply oc_irr.
  list_simpl ; rewrite <- HeqLw ; refine (IHpi2 _ _ _).
  rewrite <- Heq2; list_simpl; reflexivity.
- elt_vs_app_flat_map_cst_inv Heq.
  + list_simpl ; apply de_ilr.
    rewrite app_comm_cons, app_assoc; refine (IHpi2 _ _ _); list_simpl; reflexivity.
  + rewrite flat_map_app.
    list_simpl ; rewrite 3 app_assoc ; apply de_ilr.
    rewrite <- 3 app_assoc.
    replace (map ioc lw ++ l ++ A0 :: l0 ++ flat_map (app (map ioc lw)) L1)
      with (flat_map (app (map ioc lw)) ((l ++ A0 :: l0) :: L1)) by (list_simpl ; reflexivity).
    rewrite <- flat_map_app ; refine (IHpi2 _ _ _).
    rewrite ? flat_map_app ; list_simpl; reflexivity.
  + inversion HeqA ; subst.
    induction L0 using rev_rect ; [ | clear IHL0 ].
    * list_simpl ; list_simpl in IHpi2.
      rewrite app_comm_cons in IHpi2 ; rewrite app_assoc in IHpi2.
      assert (pi2' := IHpi2 _ _ eq_refl).
      list_simpl in pi2' ; apply (IHcut _ _ _ _ pi1) in pi2'; assumption.
    * rewrite <- ? app_assoc in IHpi2.
      replace (flat_map (cons (ioc A)) (L0 ++ x :: nil) ++ A :: l ++ flat_map (cons (ioc A)) L1)
         with (flat_map (cons (ioc A)) (L0 ++ (x ++ A :: l) :: L1)) in IHpi2
        by (rewrite ? flat_map_app ; list_simpl ; reflexivity).
      assert (pi2' := IHpi2 _ _ eq_refl).
      rewrite flat_map_app in pi2' ; list_simpl in pi2'.
      rewrite 3 app_assoc in pi2' ; apply (IHcut _ _ _ _ pi1) in pi2'.
      list_simpl in pi2' ; rewrite ? flat_map_app ; list_simpl; assumption.
- elt_vs_app_flat_map_cst_inv Heq.
  + list_simpl ; apply wk_ilr.
    rewrite app_assoc ; refine (IHpi2 _ _ _) ; list_simpl; reflexivity.
  + rewrite flat_map_app.
    list_simpl ; rewrite 3 app_assoc ; apply wk_ilr.
    rewrite <- 3 app_assoc.
    replace (map ioc lw ++ l ++ l0 ++ flat_map (app (map ioc lw)) L1)
      with (flat_map (app (map ioc lw)) ((l ++ l0) :: L1)) by (list_simpl ; reflexivity).
    rewrite <- flat_map_app ; refine (IHpi2 _ _ _).
    rewrite ? flat_map_app ; list_simpl; reflexivity.
  + inversion HeqA ; subst.
    induction L0 using rev_rect ; [ | clear IHL0 ].
    * list_simpl ; apply wk_list_ilr.
      list_simpl in IHpi2 ; rewrite app_assoc in IHpi2.
      rewrite app_assoc ; refine (IHpi2 _ _ _); reflexivity.
    * rewrite <- ? app_assoc in IHpi2.
      replace (flat_map (cons (ioc A)) (L0 ++ x :: nil) ++ l ++ flat_map (cons (ioc A)) L1)
         with (flat_map (cons (ioc A)) (L0 ++ (x ++ l) :: L1)) in IHpi2
        by (rewrite ? flat_map_app ; list_simpl ; reflexivity).
      assert (pi2' := IHpi2 _ _ eq_refl).
      list_simpl in pi2'; list_simpl.
      rewrite 3 app_assoc ; apply wk_list_ilr ; list_simpl; assumption.
- elt_vs_app_flat_map_cst_inv Heq.
  + list_simpl ; apply co_ilr.
    rewrite 2 app_comm_cons, app_assoc; refine (IHpi2 _ _ _); list_simpl; reflexivity.
  + rewrite flat_map_app.
    list_simpl ; rewrite 3 app_assoc ; apply co_ilr.
    rewrite <- 3 app_assoc.
    replace (map ioc lw ++ l ++ ioc A0 :: ioc A0 :: l0 ++ flat_map (app (map ioc lw)) L1)
      with (flat_map (app (map ioc lw)) ((l ++ ioc A0 :: ioc A0 :: l0) :: L1))
      by (list_simpl; reflexivity).
    rewrite <- flat_map_app ; refine (IHpi2 _ _ _).
    rewrite ? flat_map_app ; list_simpl; reflexivity.
  + inversion HeqA ; subst.
    induction L0 using rev_rect ; [ | clear IHL0 ].
    * list_simpl ; apply co_list_ilr.
      list_simpl in IHpi2.
      replace (ioc A :: ioc A :: l ++ flat_map (cons (ioc A)) L1)
         with (flat_map (cons (ioc A)) (nil :: l :: L1)) in IHpi2
        by (list_simpl ; reflexivity).
      replace (map ioc lw ++ map ioc lw ++ l ++ flat_map (app (map ioc lw)) L1)
         with (flat_map (app (map ioc lw)) (nil :: l :: L1))
        by (list_simpl ; reflexivity).
      refine (IHpi2 _ _ _); reflexivity.
    * rewrite <- ? app_assoc in IHpi2.
      replace (flat_map (cons (ioc A)) (L0 ++ x :: nil) ++
                 ioc A :: ioc A :: l ++ flat_map (cons (ioc A)) L1)
         with (flat_map (cons (ioc A)) (L0 ++ x :: nil :: l :: L1)) in IHpi2
        by (rewrite ? flat_map_app ; list_simpl ; reflexivity).
      assert (pi2' := IHpi2 _ _ eq_refl).
      list_simpl in pi2'; list_simpl.
      rewrite 3 app_assoc ; apply co_list_ilr ; list_simpl; assumption.
- rewrite f in P_cutfree ; inversion P_cutfree.
- assert (L = nil) as Hnil ; subst.
  { specialize P_gax_at_l with a.
    rewrite Heq in P_gax_at_l.
    apply Forall_inf_app_r in P_gax_at_l.
    destruct L; inversion P_gax_at_l as [ | ? ? Hat]; [ reflexivity | ].
    inversion Hat. }
  list_simpl in Heq ; list_simpl ; subst ; apply gax_ir.
Qed.

Theorem cut_ir_gaxat : forall A l0 l1 l2 C,
  ill P l0 A -> ill P (l1 ++ A :: l2) C -> ill P (l1 ++ l0 ++ l2) C.
Proof.
case_eq (ipcut P); intros P_cutfree.
{ intros A l0 l1 l2 C pi1 pi2; eapply cut_ir; eassumption. }
enough (forall c s A l0 l1 l2 C (pi1 : ill P l0 A) (pi2 : ill P (l1 ++ A :: l2) C),
          s = ipsize pi1 + ipsize pi2 -> ifsize A <= c -> ill P (l1 ++ l0 ++ l2) C) as IH
  by (intros A l0 l1 l2 C pi1 pi2; refine (IH _ _ A _ _ _ _ pi1 pi2 _ _); reflexivity).
induction c as [c IHcut0] using lt_wf_rect.
assert (forall A, ifsize A < c -> forall l0 l1 l2 C,
          ill P l0 A -> ill P (l1 ++ A :: l2) C -> ill P (l1 ++ l0 ++ l2) C) as IHcut
  by (intros A Hs l0 l1 l2 C pi1 pi2; refine (IHcut0 _ _ _ _ _ _ _ _ pi1 pi2 _ _);
      try reflexivity; assumption);
  clear IHcut0.
induction s as [s IHsize0] using lt_wf_rect.
assert (forall A l0 l1 l2 C (pi1 : ill P l0 A) (pi2 : ill P (l1 ++ A :: l2) C),
          ipsize pi1 + ipsize pi2 < s -> ifsize A <= c -> ill P (l1 ++ l0 ++ l2) C)
  as IHsize by (intros; eapply IHsize0; try eassumption; reflexivity); clear IHsize0.
intros A l0 l1 l2 C pi1 pi2 Heqs Hc.
rewrite_all Heqs; clear s Heqs.
remember (l1 ++ A :: l2) as l; destruct_ill pi2 f X l Hl Hr HP a.
- (* ax_ir *)
  unit_vs_elt_inv Heql; list_simpl; assumption.
- (* ex_ir *)
  cbn in IHsize.
  apply PEPermutation_Type_vs_elt_subst in HP as [(l1',l2') HP ->].
  specialize (HP l0); symmetry in HP.
  refine (ex_ir _ _ _ _ HP).
  refine (IHsize _ _ _ _ _ pi1 Hl _ Hc); lia.
- (* ex_oc_ir *)
  cbn in IHsize.
  dichot_elt_app_inf_exec Heql ; subst.
  + rewrite 2 app_assoc.
    eapply ex_oc_ir; [ | eassumption ].
    revert Hl IHsize ; list_simpl ; intros Hl IHsize.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _); [ lia | assumption ].
  + dichot_elt_app_inf_exec Heql1 ; subst.
    * symmetry in Heql0; decomp_map_inf Heql0; subst; cbn in HP, pi1.
      assert (HP' := HP).
      apply Permutation_Type_vs_elt_inv in HP' ; destruct HP' as [(l1',l2') Heq] ;
        cbn in Heq ; subst.
      apply Permutation_Type_app_inv in HP.
      revert Hl IHsize; list_simpl; rewrite app_assoc; intros Hl IHsize.
      rewrite app_assoc; eapply (@cut_oc_comm_left P_cutfree (ipsize pi1)); [ | | reflexivity ].
      -- list_simpl ; rewrite app_comm_cons ; change (ioc x :: map ioc l7) with (map ioc (x :: l7));
           rewrite (app_assoc (map ioc l4)) ; rewrite <- map_app.
         apply (ex_oc_ir _ (l1' ++ x :: l2')); [ | now apply Permutation_Type_elt ].
         revert Hl IHsize; list_simpl; rewrite app_assoc; intros Hl IHsize; assumption.
      -- intros lw pi0 Hs'.
         list_simpl ; rewrite (app_assoc (map ioc l4)) ; rewrite (app_assoc _ (map ioc l7)) ;
           rewrite <- (app_assoc (map ioc l4)) ; rewrite <- 2 map_app ;
           apply (ex_oc_ir _ (l1' ++ lw ++ l2')); [ | now apply Permutation_Type_app_middle ].
         list_simpl ; rewrite app_assoc.
         refine (IHsize _ _ _ _ _ (oc_irr pi0) Hl _ _); cbn; [ lia | assumption ].
    * rewrite <- 2 app_assoc.
      eapply ex_oc_ir; [ | eassumption ].
      revert Hl IHsize; cbn; rewrite 2 app_assoc; intros Hl IHsize.
      rewrite 2 app_assoc; refine (IHsize _ _ _ _ _ pi1 Hl _ _); [ lia | assumption ].
- (* one_irr *)
  destruct l1 ; inversion Heql.
- (* one_ilr *)
  trichot_elt_elt_inf_exec Heql.
  + list_simpl.
    apply one_ilr.
    revert Hl IHsize ; cbn ; rewrite app_assoc ; intros Hl IHsize.
    rewrite app_assoc ; refine (IHsize _ _ _ _ _ pi1 Hl _ _); lia.
  + remember (one_ilr _ _ _ Hl) as Hone ; clear HeqHone.
    remember (ione) as C ; destruct_ill pi1 f X l Hl2 Hr2 HP a ; try inversion HeqC.
    * apply (ex_ir (l3 ++ l ++ l4)).
      -- cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hone _ _); lia.
      -- apply PEPermutation_Type_app_head ; apply PEPermutation_Type_app_tail; assumption.
    * list_simpl ; rewrite app_assoc ; eapply ex_oc_ir; [ | eassumption ].
      list_simpl ; rewrite (app_assoc l) ; rewrite (app_assoc _ l2) ; rewrite <- (app_assoc l).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hone _ _); lia.
    * list_simpl; assumption.
    * list_simpl ; rewrite app_assoc ; apply one_ilr.
      list_simpl ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hone _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply tens_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hone _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply lpam_ilr; [ assumption | ].
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hone _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply lmap_ilr; [ assumption | ].
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hone _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply with_ilr1.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hone _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply with_ilr2.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hone _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply zero_ilr.
    * list_simpl ; rewrite app_assoc ; apply plus_ilr.
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hone _ _); lia.
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         cbn in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hone _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply de_ilr.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hone _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply wk_ilr.
      list_simpl ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hone _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply co_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hone _ _); lia.
    * rewrite f in P_cutfree ; inversion P_cutfree.
    * exfalso ; assert (Hiq := P_gax_at_r a) ; rewrite H0 in Hiq ; inversion Hiq.
  + rewrite 2 app_assoc.
    apply one_ilr.
    revert Hl IHsize ; list_simpl ; intros Hl IHsize.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _); lia.
- (* tens_irr *)
  dichot_elt_app_inf_exec Heql ; subst.
  + rewrite 2 app_assoc ; apply tens_irr; [ | assumption ].
    revert Hl IHsize ; list_simpl ; intros Hl IHsize.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _); lia.
  + rewrite <- app_assoc ; apply tens_irr; [ assumption | ].
    revert Hl IHsize ; list_simpl ; intros Hl IHsize.
    refine (IHsize _ _ _ _ _ pi1 Hr _ _); lia.
- (* tens_ilr *)
  trichot_elt_elt_inf_exec Heql.
  + list_simpl.
    apply tens_ilr.
    revert Hl IHsize ; cbn ; rewrite 2 app_comm_cons ; rewrite app_assoc ; intros Hl IHsize.
    rewrite 2 app_comm_cons ; rewrite app_assoc.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _); lia.
  + remember (tens_ilr _ _ _ _ _ Hl) as Htens ; clear HeqHtens.
    remember (itens A0 B) as D ; destruct_ill pi1 f X l Hl2 Hr2 HP a ; try inversion HeqD.
    * apply (ex_ir (l3 ++ l ++ l4)).
      -- cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Htens _ _); lia.
      -- apply PEPermutation_Type_app_head ; apply PEPermutation_Type_app_tail; assumption.
    * list_simpl ; rewrite app_assoc ; eapply ex_oc_ir; [ | eassumption ].
      list_simpl ; rewrite (app_assoc l) ; rewrite (app_assoc _ l2) ; rewrite <- (app_assoc l).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Htens _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply one_ilr.
      list_simpl ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Htens _ _); lia.
    * rewrite <- app_assoc ; rewrite app_assoc.
      cbn in Hc ; subst ; refine (IHcut _ _ _ _ _ _ Hr2 _); [ lia | ].
      list_simpl ; refine (IHcut _ _ _ _ _ _ Hl2 Hl); lia.
    * list_simpl ; rewrite app_assoc ; apply tens_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Htens _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply lpam_ilr; [ assumption | ].
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Htens _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply lmap_ilr; [ assumption | ].
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Htens _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply with_ilr1.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Htens _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply with_ilr2.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Htens _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply zero_ilr.
    * list_simpl ; rewrite app_assoc ; apply plus_ilr.
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Htens _ _); lia.
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         cbn in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Htens _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply de_ilr.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Htens _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply wk_ilr.
      list_simpl ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Htens _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply co_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Htens _ _); lia.
    * rewrite f in P_cutfree ; inversion P_cutfree.
    * exfalso ; assert (Hiq := P_gax_at_r a) ; rewrite H0 in Hiq ; inversion Hiq.
  + rewrite 2 app_assoc.
    apply tens_ilr.
    revert Hl IHsize ; list_simpl ; intros Hl IHsize.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _); lia.
- (* lpam_irr *)
  revert Hl IHsize ; list_simpl ; intros Hl IHsize.
  apply lpam_irr.
  list_simpl ; refine (IHsize _ _ _ _ _ pi1 Hl _ _); lia.
- (* lpam_ilr *)
  cbn in IHsize ; trichot_elt_elt_inf_exec Heql.
  + dichot_elt_app_inf_exec Heql1 ; subst.
    * list_simpl ; rewrite 2 app_assoc.
      apply lpam_ilr; [ | assumption ].
      list_simpl ; refine (IHsize _ _ _ _ _ pi1 Hl _ _); lia.
    * list_simpl ; apply lpam_ilr; [ assumption | ].
      revert Hr IHsize ; rewrite app_comm_cons ; rewrite app_assoc ; intros Hr IHsize.
      rewrite app_comm_cons ; rewrite app_assoc.
      refine (IHsize _ _ _ _ _ pi1 Hr _ _); lia.
  + change (S (ipsize Hl + ipsize Hr)) with (ipsize (lpam_ilr _ _ _ _ _ _ Hl Hr)) in IHsize.
    remember (lpam_ilr _ _ _ _ _ _ Hl Hr) as Hlpam ; clear HeqHlpam.
    remember (ilpam A0 B) as D ; destruct_ill pi1 f X l Hl2 Hr2 HP a ; try inversion HeqD.
    * apply (ex_ir (l4 ++ l ++ l3 ++ l5)).
      -- cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlpam _ _); lia.
      -- apply PEPermutation_Type_app_head ; apply PEPermutation_Type_app_tail; assumption.
    * list_simpl ; rewrite app_assoc ; eapply ex_oc_ir; [ | eassumption ].
      list_simpl ; rewrite (app_assoc l) ; rewrite (app_assoc _ l2) ; rewrite <- (app_assoc l).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlpam _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply one_ilr.
      list_simpl ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlpam _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply tens_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlpam _ _); lia.
    * rewrite app_assoc.
      cbn in Hc ; subst ; refine (IHcut _ _ _ _ _ _ Hl _); [ lia | ].
      list_simpl ; change (A0 :: l5) with ((A0 :: nil) ++ l5) ; rewrite (app_assoc l).
      refine (IHcut _ _ _ _ _ _ Hl2 Hr); lia.
    * list_simpl ; rewrite app_assoc ; apply lpam_ilr; [ assumption | ].
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hlpam _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply lmap_ilr; [ assumption | ].
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hlpam _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply with_ilr1.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlpam _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply with_ilr2.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlpam _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply zero_ilr.
    * list_simpl ; rewrite app_assoc ; apply plus_ilr.
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlpam _ _); lia.
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         cbn in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hlpam _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply de_ilr.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlpam _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply wk_ilr.
      list_simpl ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlpam _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply co_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlpam _ _); lia.
    * rewrite f in P_cutfree ; inversion P_cutfree.
    * exfalso ; assert (Hiq := P_gax_at_r a) ; rewrite H0 in Hiq ; inversion Hiq.
  + rewrite 2 app_assoc ; apply lpam_ilr; [ assumption | ].
    revert Hr IHsize ; list_simpl ; intros Hr IHsize.
    refine (IHsize _ _ _ _ _ pi1 Hr _ _); lia.
- (* gen_irr *)
  cbn in IHsize.
  apply gen_irr.
  revert Hl IHsize ; list_simpl ; intros Hl IHsize.
  refine (IHsize _ _ _ _ _ pi1 Hl _ _); lia.
- (* gen_ilr *)
  destruct l1 ; inversion Heql ; subst.
  + remember (gen_ilr _ _ Hl) as Hgen ; clear HeqHgen.
    remember (igen A0) as D ; destruct_ill pi1 f X l' Hl2 Hr2 HP a ; try inversion HeqD.
    * apply (ex_ir (nil ++ l' ++ l2)).
      -- revert Hgen IHsize ; rewrite <- (app_nil_l _) ; intros Hgen IHsize.
         refine (IHsize _ _ _ _ _ Hl2 Hgen _ _); cbn; [ lia | assumption ].
      -- apply PEPermutation_Type_app_head ; apply PEPermutation_Type_app_tail; assumption.
    * rewrite <- ? app_assoc ; rewrite app_assoc ; eapply ex_oc_ir; [ | eassumption ].
      rewrite <- app_assoc, (app_assoc l'), (app_assoc _ l0), <- (app_assoc l').
      revert Hgen IHsize ; rewrite <- (app_nil_l _) ; intros Hgen IHsize.
      refine (IHsize _ _ _ _ _ Hl2 Hgen _ _) ; cbn; [ lia | assumption ].
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply one_ilr.
      list_simpl ; rewrite (app_assoc l1).
      revert Hgen IHsize ; rewrite <- (app_nil_l _) ; intros Hgen IHsize.
      refine (IHsize _ _ _ _ _ Hl2 Hgen _ _) ; cbn; [ lia | assumption ].
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply tens_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      revert Hgen IHsize ; rewrite <- (app_nil_l _) ; intros Hgen IHsize.
      refine (IHsize _ _ _ _ _ Hl2 Hgen _ _) ; cbn; [ lia | assumption ].
    * rewrite <- ? app_assoc ; rewrite <- app_comm_cons ; rewrite <- app_assoc ; rewrite app_assoc.
      apply lpam_ilr; [ assumption | ].
      rewrite <- app_assoc ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      revert Hgen IHsize ; rewrite <- (app_nil_l _) ; intros Hgen IHsize.
      refine (IHsize _ _ _ _ _ Hr2 Hgen  _ _) ; cbn; [ lia | assumption ].
    * subst ; list_simpl ; rewrite <- (app_nil_r _) ; rewrite <- app_assoc.
      refine (IHcut _ _ _ _ _ _ Hl Hl2) ; cbn; assumption.
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply lmap_ilr; [ assumption | ].
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      revert Hgen IHsize ; rewrite <- (app_nil_l _) ; intros Hgen IHsize.
      refine (IHsize _ _ _ _ _ Hr2 Hgen _ _) ; cbn; [ lia | assumption ].
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply with_ilr1.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      revert Hgen IHsize ; rewrite <- (app_nil_l _) ; intros Hgen IHsize.
      refine (IHsize _ _ _ _ _ Hl2 Hgen _ _) ; cbn; [ lia | assumption ].
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply with_ilr2.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      revert Hgen IHsize ; rewrite <- (app_nil_l _) ; intros Hgen IHsize.
      refine (IHsize _ _ _ _ _ Hl2 Hgen _ _) ; cbn; [ lia | assumption ].
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply zero_ilr.
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply plus_ilr.
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         revert Hgen IHsize ; rewrite <- (app_nil_l _) ; intros Hgen IHsize.
         refine (IHsize _ _ _ _ _ Hl2 Hgen _ _) ; cbn; [ lia | assumption ].
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         revert Hgen IHsize ; rewrite <- (app_nil_l _) ; intros Hgen IHsize.
         refine (IHsize _ _ _ _ _ Hr2 Hgen _ _) ; cbn; [ lia | assumption ].
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply de_ilr.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      revert Hgen IHsize ; rewrite <- (app_nil_l _) ; intros Hgen IHsize.
      refine (IHsize _ _ _ _ _ Hl2 Hgen _ _) ; cbn; [ lia | assumption ].
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply wk_ilr.
      list_simpl ; rewrite (app_assoc l1).
      revert Hgen IHsize ; rewrite <- (app_nil_l _) ; intros Hgen IHsize.
      refine (IHsize _ _ _ _ _ Hl2 Hgen _ _) ; cbn; [ lia | assumption ].
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply co_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      revert Hgen IHsize ; rewrite <- (app_nil_l _) ; intros Hgen IHsize.
      refine (IHsize _ _ _ _ _ Hl2 Hgen _ _) ; cbn; [ lia | assumption ].
    * rewrite f in P_cutfree ; inversion P_cutfree.
    * exfalso ; assert (Hiq := P_gax_at_r a) ; rewrite H0 in Hiq ; inversion Hiq.
  + list_simpl ; apply gen_ilr.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _) ; cbn; [ lia | assumption ].
- (* lmap_irr *)
  cbn in IHsize.
  apply lmap_irr.
  revert Hl IHsize ; rewrite app_comm_cons ; intros Hl IHsize.
  rewrite app_comm_cons ; refine (IHsize _ _ _ _ _ pi1 Hl _ _); [ lia | assumption ].
- (* lmap_ilr *)
  cbn in IHsize ; rewrite app_assoc in Heql ; trichot_elt_elt_inf_exec Heql.
  + list_simpl ; apply lmap_ilr; [ assumption | ].
    revert Hr IHsize ; rewrite app_comm_cons ; rewrite app_assoc ; intros Hr IHsize.
    rewrite app_comm_cons ; rewrite app_assoc.
    refine (IHsize _ _ _ _ _ pi1 Hr _ _); lia.
  + change (S (ipsize Hl + ipsize Hr)) with (ipsize (lmap_ilr _ _ _ _ _ _ Hl Hr)) in IHsize.
    remember (lmap_ilr _ _ _ _ _ _ Hl Hr) as Hlmap; clear HeqHlmap.
    revert Hlmap IHsize ; rewrite app_assoc ; intros Hlmap IHsize.
    remember (ilmap A0 B) as D ; destruct_ill pi1 f X l Hl2 Hr2 HP a ; try inversion HeqD.
    * apply (ex_ir ((l4 ++ l3) ++ l ++ l5)).
      -- cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlmap _ _); lia.
      -- apply PEPermutation_Type_app_head ; apply PEPermutation_Type_app_tail; assumption.
    * list_simpl ; rewrite 2 app_assoc ; eapply ex_oc_ir; [ | eassumption ].
      list_simpl ; rewrite (app_assoc l) ; rewrite (app_assoc _ l2) ;
        rewrite <- (app_assoc l) ; rewrite app_assoc ; cbn in IHsize.
      refine (IHsize _ _ _ _ _ Hl2 Hlmap _ _); lia.
    * list_simpl ; rewrite 2 app_assoc ; apply one_ilr.
      list_simpl ; rewrite (app_assoc l1) ; rewrite app_assoc.
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlmap _ _); lia.
    * list_simpl ; rewrite 2 app_assoc ; apply tens_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1) ; rewrite app_assoc.
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlmap _ _); lia.
    * list_simpl ; rewrite 2 app_assoc ; apply lpam_ilr; [ assumption | ].
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1) ; rewrite app_assoc.
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hlmap _ _); lia.
    * list_simpl ; cbn in Hc ; subst ; refine (IHcut _ _ _ _ _ _ Hl _); [ lia | ].
      rewrite app_comm_cons ; refine (IHcut _ _ _ _ _ _ Hl2 Hr); lia.
    * list_simpl ; rewrite 2 app_assoc ; apply lmap_ilr; [ assumption | ].
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1) ; rewrite app_assoc.
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hlmap _ _); lia.
    * list_simpl ; rewrite 2 app_assoc ; apply with_ilr1.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1) ; rewrite app_assoc.
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlmap _ _); lia.
    * list_simpl ; rewrite 2 app_assoc ; apply with_ilr2.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1) ; rewrite app_assoc.
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlmap _ _); lia.
    * list_simpl ; rewrite 2 app_assoc ; apply zero_ilr.
    * list_simpl ; rewrite 2 app_assoc ; apply plus_ilr.
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1) ; rewrite app_assoc.
         cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlmap _ _); lia.
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1) ; rewrite app_assoc.
         cbn in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hlmap _ _); lia.
    * list_simpl ; rewrite 2 app_assoc ; apply de_ilr.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1) ; rewrite app_assoc.
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlmap _ _); lia.
    * list_simpl ; rewrite 2 app_assoc ; apply wk_ilr.
      list_simpl ; rewrite (app_assoc l1) ; rewrite app_assoc.
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlmap _ _); lia.
    * list_simpl ; rewrite 2 app_assoc ; apply co_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1) ; rewrite app_assoc.
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hlmap _ _); lia.
    * rewrite f in P_cutfree ; inversion P_cutfree.
    * exfalso ; assert (Hiq := P_gax_at_r a) ; rewrite H0 in Hiq ; inversion Hiq.
  + dichot_elt_app_inf_exec Heql0 ; subst.
    * list_simpl ; rewrite 2 app_assoc.
      apply lmap_ilr; [ assumption | ].
      revert Hr IHsize ; list_simpl ; intros Hr IHsize.
      refine (IHsize _ _ _ _ _ pi1 Hr _ _); lia.
    * list_simpl; rewrite (app_assoc l6), (app_assoc _ l); apply lmap_ilr; [ | assumption ].
      list_simpl; refine (IHsize _ _ _ _ _ pi1 Hl _ _); lia.
- (* neg_irr *)
  cbn in IHsize.
  apply neg_irr.
  revert Hl IHsize ; rewrite app_comm_cons ; intros Hl IHsize.
  rewrite app_comm_cons ; refine (IHsize _ _ _ _ _ pi1 Hl _ _); lia.
- (* neg_ilr *)
  trichot_elt_elt_inf_exec Heql.
  + destruct l3 ; inversion Heql1.
  + remember (neg_ilr _ _ Hl) as Hneg; clear HeqHneg.
    remember (ineg A0) as D ; destruct_ill pi1 f X l' Hl2 Hr2 HP a ; try inversion HeqD.
    * apply (ex_ir (l ++ l' ++ nil)).
      -- cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hneg _ _); lia.
      -- apply PEPermutation_Type_app_head ; apply PEPermutation_Type_app_tail; assumption.
    * rewrite <- ? app_assoc ; rewrite app_assoc ; eapply ex_oc_ir; [ | eassumption ].
      rewrite <- app_assoc, (app_assoc l'), (app_assoc _ l2), <- (app_assoc l').
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hneg _ _); lia.
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply one_ilr.
      list_simpl ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hneg _ _); lia.
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply tens_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hneg _ _); lia.
    * rewrite <- ? app_assoc ; rewrite <- app_comm_cons ; rewrite <- app_assoc ; rewrite app_assoc.
      apply lpam_ilr; [ assumption | ].
      rewrite <- app_assoc ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hneg _ _); lia.
    * rewrite <- ? app_assoc, app_assoc; apply lmap_ilr; [ assumption | ].
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hneg _ _); lia.
    * clear IHsize ; rewrite <- (app_nil_l (A :: l0)) in Hl2.
      list_simpl ; cbn in Hc ; subst ; refine (IHcut _ _ _ _ _ _ Hl Hl2); lia.
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply with_ilr1.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hneg _ _); lia.
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply with_ilr2.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hneg _ _); lia.
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply zero_ilr.
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply plus_ilr.
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hneg _ _); lia.
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         cbn in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hneg _ _); lia.
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply de_ilr.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hneg _ _); lia.
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply wk_ilr.
      list_simpl ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hneg _ _); lia.
    * rewrite <- ? app_assoc ; rewrite app_assoc ; apply co_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hneg _ _); lia.
    * rewrite f in P_cutfree ; inversion P_cutfree.
    * exfalso ; assert (Hiq := P_gax_at_r a) ; rewrite H0 in Hiq ; inversion Hiq.
  + rewrite 2 app_assoc; apply neg_ilr.
    revert Hl IHsize ; list_simpl ; intros Hl IHsize.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _); lia.
- (* top_irr *)
  apply top_irr.
- (* with_irr *)
  cbn in IHsize.
  apply with_irr.
  + refine (IHsize _ _ _ _ _ pi1 Hl _ _); lia.
  + refine (IHsize _ _ _ _ _ pi1 Hr _ _); lia.
- (* with_ilr1 *)
  trichot_elt_elt_inf_exec Heql.
  + list_simpl.
    apply with_ilr1.
    revert Hl IHsize ; cbn ; rewrite app_comm_cons ; rewrite app_assoc ; intros Hl IHsize.
    rewrite app_comm_cons ; rewrite app_assoc.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _); lia.
  + remember (with_ilr1 _ _ _ _ _ Hl) as Hwith; clear HeqHwith.
    remember (iwith A0 B) as D ; destruct_ill pi1 f X l Hl2 Hr2 HP a ; try inversion HeqD.
    * apply (ex_ir (l3 ++ l ++ l4)).
      -- cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _); lia.
      -- apply PEPermutation_Type_app_head ; apply PEPermutation_Type_app_tail; assumption.
    * list_simpl ; rewrite app_assoc ; eapply ex_oc_ir; [ | eassumption ].
      list_simpl ; rewrite (app_assoc l) ; rewrite (app_assoc _ l2) ; rewrite <- (app_assoc l).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply one_ilr.
      list_simpl ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply tens_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply lpam_ilr; [ assumption | ].
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hwith _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply lmap_ilr; [ assumption | ].
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hwith _ _); lia.
    * cbn in Hc ; subst ; refine (IHcut _ _ _ _ _ _ Hl2 Hl); lia.
    * list_simpl ; rewrite app_assoc ; apply with_ilr1.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply with_ilr2.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply zero_ilr.
    * list_simpl ; rewrite app_assoc ; apply plus_ilr.
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _); lia.
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         cbn in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hwith _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply de_ilr.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply wk_ilr.
      list_simpl ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply co_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _); lia.
    * rewrite f in P_cutfree ; inversion P_cutfree.
    * exfalso ; assert (Hiq := P_gax_at_r a) ; rewrite H0 in Hiq ; inversion Hiq.
  + rewrite 2 app_assoc.
    apply with_ilr1.
    revert Hl IHsize ; list_simpl ; intros Hl IHsize.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _); lia.
- (* with_ilr2 *)
  trichot_elt_elt_inf_exec Heql.
  + list_simpl.
    apply with_ilr2.
    revert Hl IHsize ; cbn ; rewrite app_comm_cons ; rewrite app_assoc ; intros Hl IHsize.
    rewrite app_comm_cons ; rewrite app_assoc.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _); lia.
  + remember (with_ilr2 _ _ _ _ _ Hl) as Hwith; clear HeqHwith.
    remember (iwith B A0) as D ; destruct_ill pi1 f X l Hl2 Hr2 HP a ; try inversion HeqD.
    * apply (ex_ir (l3 ++ l ++ l4)).
      -- cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _); lia.
      -- apply PEPermutation_Type_app_head ; apply PEPermutation_Type_app_tail; assumption.
    * list_simpl ; rewrite app_assoc ; eapply ex_oc_ir; [ | eassumption ].
      list_simpl ; rewrite (app_assoc l) ; rewrite (app_assoc _ l2) ; rewrite <- (app_assoc l).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply one_ilr.
      list_simpl ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply tens_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply lpam_ilr; [ assumption | ].
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hwith _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply lmap_ilr; [ assumption | ].
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hwith _ _); lia.
    * cbn in Hc ; subst ; refine (IHcut _ _ _ _ _ _ Hr2 Hl); lia.
    * list_simpl ; rewrite app_assoc ; apply with_ilr1.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply with_ilr2.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply zero_ilr.
    * list_simpl ; rewrite app_assoc ; apply plus_ilr.
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _); lia.
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         cbn in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hwith _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply de_ilr.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply wk_ilr.
      list_simpl ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply co_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hwith _ _); lia.
    * rewrite f in P_cutfree ; inversion P_cutfree.
    * exfalso ; assert (Hiq := P_gax_at_r a) ; rewrite H0 in Hiq ; inversion Hiq.
  + rewrite 2 app_assoc.
    apply with_ilr2.
    revert Hl IHsize ; list_simpl ; intros Hl IHsize.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _); lia.
- (* zero_ilr *)
  trichot_elt_elt_inf_exec Heql.
  + list_simpl.
    apply zero_ilr.
  + remember (zero_ilr l3 l4 C) as Hzero ; clear HeqHzero.
    remember izero as D ; destruct_ill pi1 f X l Hl2 Hr2 HP a ; try inversion HeqD.
    * apply (ex_ir (l3 ++ l ++ l4)).
      -- cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hzero _ _); lia.
      -- apply PEPermutation_Type_app_head ; apply PEPermutation_Type_app_tail; assumption.
    * list_simpl ; rewrite app_assoc ; eapply ex_oc_ir; [ | eassumption ].
      list_simpl ; rewrite (app_assoc l) ; rewrite (app_assoc _ l2) ; rewrite <- (app_assoc l).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hzero _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply one_ilr.
      list_simpl ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hzero _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply tens_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hzero _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply lpam_ilr; [ assumption | ].
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hzero _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply lmap_ilr; [ assumption | ].
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hzero _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply with_ilr1.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hzero _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply with_ilr2.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hzero _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply zero_ilr.
    * list_simpl ; rewrite app_assoc ; apply plus_ilr.
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hzero _ _); lia.
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         cbn in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hzero _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply de_ilr.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hzero _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply wk_ilr.
      list_simpl ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hzero _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply co_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hzero _ _); lia.
    * rewrite f in P_cutfree ; inversion P_cutfree.
    * exfalso ; assert (Hiq := P_gax_at_r a) ; rewrite H0 in Hiq ; inversion Hiq.
  + rewrite 2 app_assoc.
    apply zero_ilr.
- (* plus_irr1 *)
  cbn in IHsize.
  apply plus_irr1.
  refine (IHsize _ _ _ _ _ pi1 Hl _ _); lia.
- (* plus_irr2 *)
  cbn in IHsize.
  apply plus_irr2.
  refine (IHsize _ _ _ _ _ pi1 Hl _ _); lia.
- (* plus_ilr *)
  trichot_elt_elt_inf_exec Heql.
  + list_simpl.
    apply plus_ilr.
    * revert Hl IHsize ; cbn ; rewrite app_comm_cons, app_assoc ; intros Hl IHsize.
      rewrite app_comm_cons ; rewrite app_assoc.
      refine (IHsize _ _ _ _ _ pi1 Hl _ _); lia.
    * revert Hr IHsize ; cbn ; rewrite app_comm_cons, app_assoc ; intros Hr IHsize.
      rewrite app_comm_cons ; rewrite app_assoc.
      refine (IHsize _ _ _ _ _ pi1 Hr _ _); lia.
  + remember (plus_ilr _ _ _ _ _ Hl Hr) as Hplus; clear HeqHplus.
    remember (iplus A0 B) as D ; destruct_ill pi1 f X l Hl2 Hr2 HP a ; try inversion HeqD.
    * apply (ex_ir (l3 ++ l ++ l4)).
      -- cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hplus _ _); lia.
      -- apply PEPermutation_Type_app_head ; apply PEPermutation_Type_app_tail; assumption.
    * list_simpl ; rewrite app_assoc ; eapply ex_oc_ir; [ | eassumption ].
      list_simpl ; rewrite (app_assoc l) ; rewrite (app_assoc _ l2) ; rewrite <- (app_assoc l).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hplus _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply one_ilr.
      list_simpl ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hplus _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply tens_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hplus _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply lpam_ilr; [ assumption | ].
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hplus _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply lmap_ilr; [ assumption | ].
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hplus _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply with_ilr1.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hplus _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply with_ilr2.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hplus _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply zero_ilr.
    * cbn in Hc ; subst ; refine (IHcut _ _ _ _ _ _ Hl2 Hl); lia.
    * cbn in Hc ; subst ; refine (IHcut _ _ _ _ _ _ Hl2 Hr); lia.
    * list_simpl ; rewrite app_assoc ; apply plus_ilr.
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hplus _ _); lia.
      -- list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
         cbn in IHsize ; refine (IHsize _ _ _ _ _ Hr2 Hplus _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply de_ilr.
      list_simpl ; rewrite app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hplus _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply wk_ilr.
      list_simpl ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hplus _ _); lia.
    * list_simpl ; rewrite app_assoc ; apply co_ilr.
      list_simpl ; rewrite 2 app_comm_cons ; rewrite (app_assoc l1).
      cbn in IHsize ; refine (IHsize _ _ _ _ _ Hl2 Hplus _ _); lia.
    * rewrite f in P_cutfree ; inversion P_cutfree.
    * exfalso ; assert (Hiq := P_gax_at_r a) ; rewrite H0 in Hiq ; inversion Hiq.
  + rewrite 2 app_assoc.
    apply plus_ilr.
    * revert Hl IHsize ; list_simpl ; intros Hl IHsize.
      list_simpl ; refine (IHsize _ _ _ _ _ pi1 Hl _ _); lia.
    * revert Hr IHsize ; list_simpl ; intros Hr IHsize.
      list_simpl ; refine (IHsize _ _ _ _ _ pi1 Hr _ _); lia.
- (* oc_irr *)
  remember (oc_irr Hl) as Hloc ; rewrite HeqHloc in IHsize ; clear HeqHloc.
  decomp_map_inf Heql; subst; cbn in pi1, IHsize, Hl; list_simpl.
  eapply (@cut_oc_comm_left P_cutfree (ipsize pi1)); [ | | reflexivity ].
  + change (ioc x :: map ioc l6) with (map ioc (x :: l6)).
    rewrite <- map_app; apply oc_irr; assumption.
  + intros lw Hs' pi.
    rewrite <- 2 map_app; apply oc_irr.
    revert Hl IHsize; list_simpl; intros Hl IHsize.
    refine (IHsize _ _ _ _ _ (oc_irr Hs') Hl _ _); cbn; [ lia | assumption ].
- (* de_ilr *)
  trichot_elt_elt_inf_exec Heql.
  + list_simpl.
    apply de_ilr.
    revert Hl IHsize; cbn; rewrite app_comm_cons, app_assoc; intros Hl IHsize.
    rewrite app_comm_cons, app_assoc.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _); lia.
  + eapply (@cut_oc_comm_left P_cutfree (ipsize pi1)); [ | | reflexivity ].
    * apply de_ilr; assumption.
    * intros lw Hs pi.
      cbn in Hc; refine (IHsize _ _ _ _ _ Hs Hl _ _); cbn; lia.
  + rewrite 2 app_assoc.
    apply de_ilr.
    revert Hl IHsize; list_simpl; intros Hl IHsize.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _); lia.
- (* wk_ilr *)
  trichot_elt_elt_inf_exec Heql.
  + list_simpl.
    apply wk_ilr.
    revert Hl IHsize; cbn; rewrite app_assoc; intros Hl IHsize.
    rewrite app_assoc.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _); lia.
  + eapply (@cut_oc_comm_left P_cutfree (ipsize pi1)); [ | | reflexivity ].
    * apply wk_ilr; assumption.
    * intros lw Hs pi.
      apply wk_list_ilr; assumption.
  + rewrite 2 app_assoc.
    apply wk_ilr.
    revert Hl IHsize; list_simpl; intros Hl IHsize.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _); lia.
- (* co_ilr *)
  trichot_elt_elt_inf_exec Heql.
  + list_simpl.
    apply co_ilr.
    revert Hl IHsize ; cbn ; rewrite 2 app_comm_cons, app_assoc ; intros Hl IHsize.
    rewrite 2 app_comm_cons ; rewrite app_assoc.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _); lia.
  + eapply (@cut_oc_comm_left P_cutfree (ipsize pi1)); [ | | reflexivity ].
    * apply co_ilr; assumption.
    * intros lw Hs _.
      replace (ioc A0 :: ioc A0 :: l4)
         with (flat_map (cons (ioc A0)) (nil :: l4 :: nil)) in Hl  by (list_simpl ; reflexivity).
      apply co_list_ilr.
      replace (map ioc lw ++ map ioc lw ++ l4)
         with (flat_map (app (map ioc lw)) (nil :: l4 :: nil)) by (list_simpl ; reflexivity).
      refine (substitution_ioc _ _ _ _ _ _ _ _);
        list_simpl; try eassumption; [ | reflexivity ].
      apply IHcut; assumption.
  + rewrite 2 app_assoc.
    apply co_ilr.
    revert Hl IHsize ; list_simpl ; intros Hl IHsize.
    refine (IHsize _ _ _ _ _ pi1 Hl _ _); lia.
- (* cut_ir *)
  rewrite f in P_cutfree; inversion P_cutfree.
- (* gax_ir *)
  assert (Hiq := P_gax_at_l a); rewrite Heql in Hiq.
  apply Forall_inf_elt in Hiq.
  inversion Hiq; subst.
  apply subs_gax_l with x; try assumption.
  intros b l l' Heq a' Heq'.
  rewrite <- Heq' in Heq.
  apply P_gax_cut in Heq; assumption.
Qed.

End Cut_Elim_Proof.

(** ** Variants on cut admissibility *)

(** If axioms are atomic and closed under cut, then the cut rule is admissible:
provability is preserved if we remove the cut rule. *)
Lemma cut_admissible_ill P :
  (forall a, In_inf N (fst (projT2 (ipgax P) a)) -> False) ->
  (forall a, Forall_inf iatomic (fst (projT2 (ipgax P) a))) ->
  (forall a, iatomic (snd (projT2 (ipgax P) a))) ->
  (forall a b l1 l2, fst (projT2 (ipgax P) b) = l1 ++ snd (projT2 (ipgax P) a) :: l2 -> 
                  { c | l1 ++ fst (projT2 (ipgax P) a) ++ l2 = fst (projT2 (ipgax P) c)
                      & snd (projT2 (ipgax P) b) = snd (projT2 (ipgax P) c) }) ->
  forall l C, ill P l C -> @ill preiatom (cutrm_ipfrag P) l C.
Proof.
intros HatNl Hatl Hatr Hcut l C pi.
induction pi; try (econstructor; eassumption).
- eapply cut_ir_gaxat; eassumption.
- revert a.
  change (ipgax P) with (ipgax (cutrm_ipfrag P)).
  apply gax_ir.
Qed.

(** If there are no axioms (except the identity rule), then the cut rule is valid. *)
Lemma cut_ir_axfree P : (projT1 (ipgax P) -> False) -> forall A l0 l1 l2 C, 
  ill P l0 A -> ill P (l1 ++ A :: l2) C -> @ill preiatom P (l1 ++ l0 ++ l2) C.
Proof.
intros P_axfree A l0 l1 l2 C pi1 pi2.
eapply cut_ir_gaxat ; try eassumption.
all: intros a ; exfalso ; apply (P_axfree a).
Qed.

(** If there are no axioms (except the identity rule), then the cut rule is admissible:
provability is preserved if we remove the cut rule. *)
Lemma cut_admissible_ill_axfree P : (projT1 (ipgax P) -> False) -> forall l C,
  ill P l C -> @ill preiatom (cutrm_ipfrag P) l C.
Proof.
intros P_axfree l C pi.
eapply cut_admissible_ill; try eassumption.
all: intros a; exfalso; apply (P_axfree a).
Qed.


(** ** Standard intuitionistic linear logic: [ill_ll] (no axiom, commutative) *)

(** cut / axioms / permutation *)
Definition ipfrag_ill := @mk_ipfrag preiatom  false NoIAxioms true.
(*                                  atoms     cut   axioms    perm  *)
Definition ill_ll := @ill preiatom ipfrag_ill.

Lemma cut_ll_ir A l0 l1 l2 C :
  ill_ll l0 A -> ill_ll (l1 ++ A :: l2) C -> ill_ll (l1 ++ l0 ++ l2) C.
Proof. now intros pi1 pi2; apply cut_ir_axfree with A. Qed.

Lemma cut_ll_admissible l C : ill (cutupd_ipfrag ipfrag_ill true) l C -> ill_ll l C.
Proof.
intros pi; induction pi; try (econstructor; eassumption).
- eapply cut_ll_ir; eassumption.
- destruct a.
Qed.

End Atoms.
