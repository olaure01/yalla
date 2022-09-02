(* ill library for yalla *)

(** * Intuitionistic Linear Logic *)
(* Cut admissibility, see ill_prop.v for other properties *)

From Coq Require Import PeanoNat Wf_nat List Lia.
From OLlibs Require Import funtheory dectype List_more flat_map_more Permutation_Type_more GPermutation_Type.
From Yalla Require Export ill_cut_at.

Set Implicit Arguments.


Section Atoms.

Context { preiatom : DecType }.

Section Cut_Elim_Proof.

Context { P : @ipfrag preiatom }.

Hypothesis P_gax_noN_l : noN_iax P.
Hypothesis P_gax_cut_r : forall a, ipcut P (snd (projT2 (ipgax P) a)) = false ->
    iatomic (snd (projT2 (ipgax P) a))
  * forall b l1 l2, fst (projT2 (ipgax P) b) = l1 ++ snd (projT2 (ipgax P) a) :: l2 ->
                          { c | l1 ++ fst (projT2 (ipgax P) a) ++ l2 = fst (projT2 (ipgax P) c)
                              & snd (projT2 (ipgax P) b) = snd (projT2 (ipgax P) c) }.
Hypothesis P_gax_cut_l : forall b A l1 l2,
  fst (projT2 (ipgax P) b) = l1 ++ A :: l2 -> ipcut P A = false ->
    iatomic A
  * forall a, snd (projT2 (ipgax P) a) = A ->
                          { c | l1 ++ fst (projT2 (ipgax P) a) ++ l2 = fst (projT2 (ipgax P) c)
                              & snd (projT2 (ipgax P) b) = snd (projT2 (ipgax P) c) }.

Lemma cut_oc_comm_left A C l1 l2 l0 : ill P l0 (ioc A) ->
  (forall lw, ill P (map ioc lw) A -> ill P (l1 ++ map ioc lw ++ l2) C) ->
  ill P (l1 ++ l0 ++ l2) C.
Proof.
intros pi IH; remember (ioc A) as B eqn:HeqB; induction pi in HeqB |- *; inversion HeqB; subst;
  try specialize (IHpi eq_refl); try specialize (IHpi1 eq_refl); try specialize (IHpi2 eq_refl);
  try (list_simpl; rewrite app_assoc; constructor;
       list_simpl; rewrite ? app_comm_cons, ? (app_assoc l0), ? (app_assoc l3); assumption).
- apply (ex_ir (l1 ++ l0 ++ l2)); [ assumption | ].
  apply PEPermutation_Type_app_head, PEPermutation_Type_app_tail; assumption.
- list_simpl; rewrite app_assoc; eapply ex_oc_ir; [ | eassumption ].
  list_simpl; rewrite (app_assoc l0), (app_assoc _ l3), <- (app_assoc l0); assumption.
- apply IH; assumption.
- list_simpl in IHpi2.
  list_simpl. rewrite app_assoc. apply (cut_ir _ f); list_simpl; assumption.
- assert (ipcut P (ioc A) = true) as Hcut.
  { specialize (P_gax_cut_r a).
    rewrite HeqB in P_gax_cut_r.
    destruct (ipcut P (ioc A)); [ reflexivity | exfalso ].
    specialize (P_gax_cut_r eq_refl) as [Hat _]; inversion Hat. }
  apply (cut_ir _ Hcut).
  + rewrite <- HeqB; apply gax_ir.
  + change (ioc A :: l2) with (map ioc (A :: nil) ++ l2).
    apply IH; rewrite <- (app_nil_l _); apply de_ilr, ax_exp_ill.
Qed.

Lemma substitution_ioc A lw :
  (ipcut P (ioc A) = true -> ill P (map ioc lw) (ioc A)) ->
  (forall l1 l2 C, ill P (l1 ++ A :: l2) C -> ill P (l1 ++ map ioc lw ++ l2) C) ->
  forall l' L C, ill P (l' ++ flat_map (cons (ioc A)) L) C ->
    ill P (l' ++ flat_map (app (map ioc lw)) L) C.
Proof.
intros Hoc IHcut l' L C pi.
remember (l' ++ flat_map (cons (ioc A)) L) as l eqn:Heq.
revert l' L Heq; induction pi; intros l' L Heq;
  try (constructor; rewrite ? app_comm_cons; apply IHpi; subst; list_simpl; reflexivity).
- destruct l', L; inversion Heq as [[H1 H2]]; destruct l'; inversion H2; list_simpl.
  apply ax_ir.
- case_eq (ipperm P); intros Hperm; rewrite Hperm in p; cbn in p; subst.
  + destruct (Permutation_Type_app_flat_map_cst _ (map ioc lw) _ _ p)
      as [[L' l''] (Hnil' & HeqL' & HPL')];
      cbn in Hnil', HeqL', HPL'; subst.
    eapply ex_ir; [ | rewrite Hperm; cbn; apply HPL' ].
    apply (IHpi _ _ eq_refl).
  + apply (IHpi _ _ eq_refl).
- assert (injective (@ioc preiatom)) as Hinj by (intros x y Hxy; inversion Hxy; reflexivity).
  destruct (Permutation_Type_flat_map_cons_flat_map_app_cst _ Hinj lw _ _ _ _ p Heq)
    as [(((((lw1', lw2'), l1'), l2'), l''), L') (H1 & H2 & H3 & H4)].
  rewrite <- H4; apply (ex_oc_ir _ lw1'); [ | assumption ].
  rewrite H3; apply IHpi; assumption.
- symmetry in Heq; apply app_eq_nil in Heq as [-> Heq].
  destruct L; inversion Heq.
  apply one_irr.
- elt_vs_app_flat_map_cst_inv Heq.
  + list_simpl; apply one_ilr.
    rewrite app_assoc; apply IHpi; list_simpl; reflexivity.
  + rewrite flat_map_app.
    list_simpl; rewrite 3 app_assoc; apply one_ilr.
    rewrite <- 3 app_assoc.
    replace (map ioc lw ++ l ++ l0 ++ flat_map (app (map ioc lw)) L1)
       with (flat_map (app (map ioc lw)) ((l ++ l0) :: L1)) by (list_simpl; reflexivity).
    rewrite <- flat_map_app; apply IHpi; rewrite ? flat_map_app; list_simpl; reflexivity.
- app_vs_app_flat_map_cst_inv Heq.
  + list_simpl; apply tens_irr; [ assumption | ].
    apply (IHpi2 _ _ eq_refl).
  + rewrite flat_map_app; list_simpl.
    rewrite 3 app_assoc; apply tens_irr.
    * list_simpl.
      replace (flat_map (app (map ioc lw)) L0 ++ map ioc lw ++ l)
         with (flat_map (app (map ioc lw)) (L0 ++ l :: nil))
        by (rewrite flat_map_app; list_simpl; reflexivity).
      apply (IHpi1 _ _ eq_refl).
    * apply (IHpi2 _ _ eq_refl).
  + rewrite flat_map_app; list_simpl.
    rewrite app_assoc; apply tens_irr.
    * apply (IHpi1 _ _ eq_refl).
    * rewrite <- (app_nil_l _); apply IHpi2; reflexivity.
- elt_vs_app_flat_map_cst_inv Heq.
  + list_simpl; apply tens_ilr.
    rewrite 2 app_comm_cons, app_assoc; apply IHpi; list_simpl; reflexivity.
  + rewrite flat_map_app.
    list_simpl; rewrite 3 app_assoc; apply tens_ilr.
    rewrite <- 3 app_assoc.
    replace (map ioc lw ++ l ++ A0 :: B :: l0 ++ flat_map (app (map ioc lw)) L1)
      with (flat_map (app (map ioc lw)) ((l ++ A0 :: B :: l0) :: L1)) by (list_simpl; reflexivity).
    rewrite <- flat_map_app; apply IHpi; rewrite ? flat_map_app; list_simpl; reflexivity.
- apply lpam_irr.
  induction L using rev_rect; list_simpl.
  + change nil with (nil ++ flat_map (app (map ioc lw)) nil).
    rewrite app_comm_cons, app_assoc; apply IHpi; subst; list_simpl; reflexivity.
  + replace (flat_map (app (map ioc lw)) L ++ map ioc lw ++ x ++ A0 :: nil)
       with (flat_map (app (map ioc lw)) (L ++ (x ++ (A0 :: nil)) :: nil))
      by now list_simpl.
    apply IHpi; subst; list_simpl; reflexivity.
- elt_vs_app_flat_map_cst_inv Heq.
  + app_vs_app_flat_map_cst_inv Heq1.
    * list_simpl; apply lpam_ilr; [ assumption | ].
      rewrite app_comm_cons, app_assoc; apply IHpi2; list_simpl; reflexivity.
    * list_simpl; rewrite ? flat_map_app; list_simpl.
      rewrite (app_assoc l), (app_assoc _ (map ioc lw)), (app_assoc _ l3).
      replace (((l ++ flat_map (app (map ioc lw)) L0) ++ map ioc lw) ++ l3)
         with (l ++ flat_map (app (map ioc lw)) (L0 ++ l3 :: nil))
        by (rewrite flat_map_app; list_simpl; reflexivity).
      apply lpam_ilr.
      -- apply (IHpi1 _ _ eq_refl).
      -- rewrite app_comm_cons, app_assoc; apply IHpi2; list_simpl; reflexivity.
    * list_simpl; rewrite (app_assoc l); apply lpam_ilr.
      -- apply (IHpi1 _ _ eq_refl).
      -- rewrite <- (app_nil_l (flat_map _ _)), app_comm_cons, app_assoc;
           apply IHpi2; list_simpl; reflexivity.
  + app_vs_app_flat_map_cst_inv Heq2.
    * list_simpl; rewrite ? flat_map_app; list_simpl.
      rewrite (app_assoc l'), (app_assoc _ (map ioc lw)), (app_assoc _ l).
      replace (((l' ++ flat_map (app (map ioc lw)) L0) ++ map ioc lw) ++ l)
         with (l' ++ flat_map (app (map ioc lw)) (L0 ++ l :: nil))
        by (rewrite flat_map_app; list_simpl; reflexivity).
      apply lpam_ilr; [ assumption | ].
      list_simpl.
      replace (flat_map (app (map ioc lw)) L0 ++ map ioc lw ++ l ++
                 B :: l1 ++ flat_map (app (map ioc lw)) L1)
         with (flat_map (app (map ioc lw)) (L0 ++ (l ++ B :: l1) :: L1))
        by now list_simpl.
      apply IHpi2; list_simpl; reflexivity.
    * list_simpl; rewrite (app_assoc l3), (app_assoc _ _ (l1 ++ _)), (app_assoc _ l1).
      replace (((l3 ++ flat_map (app (map ioc lw)) L) ++ map ioc lw) ++ l1)
         with (l3 ++ flat_map (app (map ioc lw)) (L ++ l1 :: nil))
        by (rewrite flat_map_app; list_simpl; reflexivity).
      rewrite 3 app_assoc; apply lpam_ilr.
      -- apply (IHpi1 _ _ eq_refl).
      -- list_simpl.
         replace (flat_map (app (map ioc lw)) L0 ++ map ioc lw ++ l ++ B :: l4
                                                 ++ flat_map (app (map ioc lw)) L2)
            with (flat_map (app (map ioc lw)) (L0 ++ (l ++ B :: l4) :: L2))
           by (rewrite ? flat_map_app ; list_simpl ; reflexivity).
         apply IHpi2; rewrite ? flat_map_app; list_simpl; reflexivity.
    * list_simpl; rewrite ? flat_map_app; list_simpl; rewrite ? flat_map_app; list_simpl.
      rewrite (app_assoc l3), 3 app_assoc; apply lpam_ilr.
      -- apply (IHpi1 _ _ eq_refl).
      -- list_simpl.
         replace (flat_map (app (map ioc lw)) L0 ++ map ioc lw ++ l
                                                 ++ B :: flat_map (app (map ioc lw)) L2)
            with (flat_map (app (map ioc lw)) (L0 ++ (l ++ B :: nil) :: L2))
           by (rewrite ? flat_map_app; list_simpl; reflexivity).
         apply IHpi2; rewrite ? flat_map_app; list_simpl; reflexivity.
- apply gen_irr.
  induction L using rev_rect; list_simpl.
  + change nil with (nil ++ flat_map (app (map ioc lw)) nil).
    rewrite app_comm_cons, app_assoc; apply IHpi; subst; list_simpl; reflexivity.
  + replace (flat_map (app (map ioc lw)) L ++ map ioc lw ++ x ++ A0 :: nil)
       with (flat_map (app (map ioc lw)) (L ++ (x ++ (A0 :: nil)) :: nil))
      by now list_simpl.
    apply IHpi; subst; list_simpl; reflexivity.
- destruct l'; inversion Heq as [Heq']; subst.
  + destruct L; inversion Heq'.
  + list_simpl; apply gen_ilr, IHpi; reflexivity.
- rewrite app_assoc in Heq; elt_vs_app_flat_map_cst_inv Heq.
  + list_simpl; apply lmap_ilr; [ assumption | ].
    rewrite app_comm_cons, app_assoc; apply IHpi2; list_simpl; reflexivity.
  + replace (flat_map (cons (ioc A)) L0 ++ ioc A :: l)
       with (flat_map (cons (ioc A)) (L0 ++ l :: nil))
      in Heq1 by (rewrite flat_map_app; list_simpl; reflexivity).
    app_vs_app_flat_map_cst_inv Heq1.
    * list_simpl; rewrite ? flat_map_app; list_simpl.
      rewrite (app_assoc l2), (app_assoc _ (map ioc lw)), (app_assoc _ l).
      replace (((l2 ++ flat_map (app (map ioc lw)) L0) ++ map ioc lw) ++ l)
         with (l2 ++ flat_map (app (map ioc lw)) (L0 ++ l :: nil))
        by (rewrite flat_map_app; list_simpl; reflexivity).
      apply lmap_ilr.
      -- apply (IHpi1 _ _ eq_refl).
      -- rewrite app_comm_cons, app_assoc; apply IHpi2; list_simpl; reflexivity.
    * induction L2 using rev_rect; [ | clear IHL2 ].
      -- assert (L0 = L /\ l = l2 ++ l4) as [Heq1 Heq2]; subst.
         { apply (f_equal (@rev _)) in Heq0.
           rewrite ? rev_app_distr in Heq0; inversion Heq0; subst.
           apply (f_equal (@rev _)) in H1.
           rewrite ? rev_involutive in H1; subst.
           split; reflexivity. }
         list_simpl; rewrite ? flat_map_app; list_simpl; rewrite ? flat_map_app; list_simpl.
         list_simpl in pi1.
         rewrite 3 app_assoc; apply lmap_ilr; [ assumption | ].
         list_simpl; rewrite <- app_assoc in IHpi2.
         replace (flat_map (cons (ioc A)) (L ++ l2 :: nil) ++ B :: l3 ++ flat_map (cons (ioc A)) L1)
            with (flat_map (cons (ioc A)) (L ++ (l2 ++ B :: l3) :: L1)) in IHpi2
           by (rewrite ? flat_map_app; list_simpl; reflexivity).
         specialize (IHpi2 _ _ eq_refl).
         rewrite ? flat_map_app in IHpi2; list_simpl in IHpi2; assumption.
      -- assert (L0 = L ++ (l2 ++ l4) :: L2 /\ l = x) as [Heq1 Heq2]; subst.
         { apply (f_equal (@rev _)) in Heq0.
           rewrite ? rev_app_distr in Heq0; list_simpl in Heq0; inversion Heq0; subst.
           apply (f_equal (@rev _)) in H1.
           rewrite ? rev_involutive in H1; subst.
           rewrite ? rev_app_distr; list_simpl; split; reflexivity. }
         list_simpl; rewrite ? flat_map_app; list_simpl; rewrite ? flat_map_app; list_simpl.
         rewrite 3 app_assoc, (app_assoc l4), (app_assoc (l4 ++ _)), (app_assoc _ x).
         apply lmap_ilr.
         ++ list_simpl.
            replace (flat_map (app (map ioc lw)) L2 ++ map ioc lw ++ x)
               with (flat_map (app (map ioc lw)) (L2 ++ x :: nil))
              by (rewrite flat_map_app; list_simpl; reflexivity).
            apply (IHpi1 _ _ eq_refl).
         ++ list_simpl; rewrite <- app_assoc in IHpi2.
            replace (flat_map (cons (ioc A)) (L ++ l2 :: nil) ++
                       B :: l3 ++ flat_map (cons (ioc A)) L1)
               with (flat_map (cons (ioc A)) (L ++ (l2 ++ B :: l3) :: L1)) in IHpi2
              by (rewrite ? flat_map_app; list_simpl; reflexivity).
            specialize (IHpi2 _ _ eq_refl).
            rewrite ? flat_map_app in IHpi2; list_simpl in IHpi2; assumption.
    * induction L2 using rev_rect; [ | clear IHL2 ].
      -- list_simpl in Heq0; subst.
         list_simpl; rewrite ? flat_map_app; list_simpl; rewrite ? flat_map_app; list_simpl.
         list_simpl in pi1.
         rewrite <- (app_nil_l (ilmap _ _ :: _)), 3 app_assoc; apply lmap_ilr; [ assumption | ].
         list_simpl; rewrite <- app_assoc in IHpi2.
         replace (flat_map (cons (ioc A)) (L0 ++ l :: nil) ++ B :: l3 ++ flat_map (cons (ioc A)) L1)
            with (flat_map (cons (ioc A)) (L0 ++ (l ++ B :: l3) :: L1)) in IHpi2
           by (rewrite ? flat_map_app; list_simpl; reflexivity).
         specialize (IHpi2 _ _ eq_refl).
         rewrite ? flat_map_app in IHpi2; list_simpl in IHpi2; assumption.
      -- assert (L0 = L ++ L2 /\ l = x) as [-> ->].
         { apply (f_equal (@rev _)) in Heq0.
           rewrite ? rev_app_distr in Heq0; list_simpl in Heq0; inversion Heq0; subst.
           apply (f_equal (@rev _)) in H1.
           rewrite rev_involutive in H1; subst.
           rewrite rev_app_distr; list_simpl; split; reflexivity. }
         list_simpl; rewrite ? flat_map_app; list_simpl; rewrite ? flat_map_app; list_simpl.
         rewrite app_assoc, (app_assoc _ (map ioc lw)), (app_assoc _ x); apply lmap_ilr.
         ++ list_simpl.
            replace (flat_map (app (map ioc lw)) L2 ++ map ioc lw ++ x)
               with (flat_map (app (map ioc lw)) (L2 ++ x :: nil))
              by (rewrite flat_map_app; list_simpl; reflexivity).
            rewrite <- (app_nil_l _); apply IHpi1; reflexivity.
         ++ induction L using rev_rect; [ | clear IHL ].
            ** list_simpl in IHpi2; list_simpl.
               rewrite app_comm_cons, app_assoc; apply IHpi2; list_simpl; reflexivity.
            ** list_simpl; rewrite <- app_assoc in IHpi2.
               replace (flat_map (cons (ioc A)) (L ++ x0 :: nil) ++
                          B :: l3 ++ flat_map (cons (ioc A)) L1)
                  with (flat_map (cons (ioc A)) (L ++ (x0 ++ B :: l3) :: L1)) in IHpi2
                 by (rewrite ? flat_map_app; list_simpl; reflexivity).
               specialize (IHpi2 _ _ eq_refl).
               rewrite ? flat_map_app in IHpi2; list_simpl in IHpi2;
                 rewrite ? flat_map_app; list_simpl; assumption.
- elt_vs_app_flat_map_cst_inv Heq.
  + symmetry in Heq1; apply app_eq_nil in Heq1 as [-> Heq1].
    destruct L; inversion Heq1.
    list_simpl; apply neg_ilr; assumption.
  + symmetry in Heq2; apply app_eq_nil in Heq2 as [-> Heq2].
    destruct L1; inversion Heq2.
    rewrite flat_map_app.
    list_simpl; rewrite 3 app_assoc; apply neg_ilr.
    rewrite <- 2 app_assoc.
    replace (map ioc lw ++ l0)
      with (flat_map (app (map ioc lw)) (l0 :: nil)) by (list_simpl; reflexivity).
    rewrite <- flat_map_app; apply IHpi; rewrite ? flat_map_app; list_simpl; reflexivity.
- apply with_irr; [ apply IHpi1 | apply IHpi2 ]; assumption.
- elt_vs_app_flat_map_cst_inv Heq.
  + list_simpl; apply with_ilr1.
    rewrite app_comm_cons, app_assoc; apply IHpi; list_simpl; reflexivity.
  + rewrite flat_map_app.
    list_simpl; rewrite 3 app_assoc; apply with_ilr1.
    rewrite <- 3 app_assoc.
    replace (map ioc lw ++ l ++ A0 :: l0 ++ flat_map (app (map ioc lw)) L1)
      with (flat_map (app (map ioc lw)) ((l ++ A0 :: l0) :: L1)) by (list_simpl; reflexivity).
    rewrite <- flat_map_app; apply IHpi; rewrite ? flat_map_app; list_simpl; reflexivity.
- elt_vs_app_flat_map_cst_inv Heq.
  + list_simpl; apply with_ilr2.
    rewrite app_comm_cons, app_assoc; apply IHpi; list_simpl; reflexivity.
  + rewrite flat_map_app.
    list_simpl; rewrite 3 app_assoc; apply with_ilr2.
    rewrite <- 3 app_assoc.
    replace (map ioc lw ++ l ++ A0 :: l0 ++ flat_map (app (map ioc lw)) L1)
      with (flat_map (app (map ioc lw)) ((l ++ A0 :: l0) :: L1)) by (list_simpl; reflexivity).
    rewrite <- flat_map_app; apply IHpi; rewrite ? flat_map_app; list_simpl; reflexivity.
- elt_vs_app_flat_map_cst_inv Heq.
  + list_simpl; apply zero_ilr.
  + rewrite flat_map_app.
    list_simpl; rewrite 3 app_assoc; apply zero_ilr.
- elt_vs_app_flat_map_cst_inv Heq.
  + list_simpl; apply plus_ilr.
    * rewrite app_comm_cons, app_assoc; apply IHpi1; list_simpl; reflexivity.
    * rewrite app_comm_cons, app_assoc; apply IHpi2; list_simpl; reflexivity.
  + rewrite flat_map_app.
    list_simpl; rewrite 3 app_assoc; apply plus_ilr; rewrite <- 3 app_assoc.
    * replace (map ioc lw ++ l ++ A0 :: l0 ++ flat_map (app (map ioc lw)) L1)
        with (flat_map (app (map ioc lw)) ((l ++ A0 :: l0) :: L1)) by (list_simpl; reflexivity).
      rewrite <- flat_map_app; apply IHpi1; rewrite ? flat_map_app; list_simpl; reflexivity.
    * replace (map ioc lw ++ l ++ B :: l0 ++ flat_map (app (map ioc lw)) L1)
        with (flat_map (app (map ioc lw)) ((l ++ B :: l0) :: L1)) by (list_simpl; reflexivity).
      rewrite <- flat_map_app; apply IHpi2; rewrite ? flat_map_app; list_simpl; reflexivity.
- decomp_map_inf Heq; subst; cbn in Heq2; cbn.
  assert ({ Lw | flat_map (app (map ioc lw)) L = map ioc Lw }) as [Lw HeqLw].
  { clear pi IHpi; revert l2 Heq2; clear; induction L; cbn; intros l2 Heq2.
    - exists nil; reflexivity.
    - decomp_map_inf Heq2; subst.
      inversion Heq1; subst; cbn.
      cbn in Heq4; apply IHL in Heq4 as [Lw Heq4].
      exists (lw ++ l1 ++ Lw); list_simpl; rewrite <- Heq4; reflexivity. }
  rewrite HeqLw, <- map_app; apply oc_irr.
  list_simpl; rewrite <- HeqLw; apply IHpi; rewrite <- Heq2; list_simpl; reflexivity.
- elt_vs_app_flat_map_cst_inv Heq.
  + list_simpl; apply de_ilr.
    rewrite app_comm_cons, app_assoc; apply IHpi; list_simpl; reflexivity.
  + rewrite flat_map_app.
    list_simpl; rewrite 3 app_assoc; apply de_ilr.
    rewrite <- 3 app_assoc.
    replace (map ioc lw ++ l ++ A0 :: l0 ++ flat_map (app (map ioc lw)) L1)
      with (flat_map (app (map ioc lw)) ((l ++ A0 :: l0) :: L1)) by (list_simpl; reflexivity).
    rewrite <- flat_map_app; apply IHpi; rewrite ? flat_map_app; list_simpl; reflexivity.
  + inversion HeqA; subst.
    induction L0 as [ | B L0 _] using rev_rect.
    * list_simpl; list_simpl in IHpi; rewrite app_comm_cons, app_assoc in IHpi.
      specialize (IHpi _ _ eq_refl); list_simpl in IHpi.
      apply IHcut, IHpi.
    * rewrite <- ? app_assoc in IHpi.
      replace (flat_map (cons (ioc A)) (L0 ++ B :: nil) ++ A :: l ++ flat_map (cons (ioc A)) L1)
         with (flat_map (cons (ioc A)) (L0 ++ (B ++ A :: l) :: L1)) in IHpi
        by (rewrite ? flat_map_app; list_simpl; reflexivity).
      specialize (IHpi _ _ eq_refl).
      rewrite flat_map_app in IHpi; list_simpl in IHpi.
      rewrite 3 app_assoc in IHpi; apply IHcut in IHpi.
      list_simpl in IHpi; rewrite ? flat_map_app; list_simpl; assumption.
- elt_vs_app_flat_map_cst_inv Heq.
  + list_simpl; apply wk_ilr.
    rewrite app_assoc; apply IHpi; list_simpl; reflexivity.
  + rewrite flat_map_app.
    list_simpl; rewrite 3 app_assoc; apply wk_ilr.
    rewrite <- 3 app_assoc.
    replace (map ioc lw ++ l ++ l0 ++ flat_map (app (map ioc lw)) L1)
      with (flat_map (app (map ioc lw)) ((l ++ l0) :: L1)) by (list_simpl ; reflexivity).
    rewrite <- flat_map_app; apply IHpi; rewrite ? flat_map_app; list_simpl; reflexivity.
  + inversion HeqA; subst.
    induction L0 as [ | B L0 _] using rev_rect.
    * list_simpl; apply wk_list_ilr.
      list_simpl in IHpi; rewrite app_assoc in IHpi.
      rewrite app_assoc; apply (IHpi _ _ eq_refl).
    * rewrite <- ? app_assoc in IHpi.
      replace (flat_map (cons (ioc A)) (L0 ++ B :: nil) ++ l ++ flat_map (cons (ioc A)) L1)
         with (flat_map (cons (ioc A)) (L0 ++ (B ++ l) :: L1)) in IHpi
        by (rewrite ? flat_map_app; list_simpl; reflexivity).
      specialize (IHpi _ _ eq_refl).
      list_simpl in IHpi; list_simpl.
      rewrite 3 app_assoc; apply wk_list_ilr; list_simpl; assumption.
- elt_vs_app_flat_map_cst_inv Heq.
  + list_simpl; apply co_ilr.
    rewrite 2 app_comm_cons, app_assoc; apply IHpi; list_simpl; reflexivity.
  + rewrite flat_map_app.
    list_simpl; rewrite 3 app_assoc; apply co_ilr.
    rewrite <- 3 app_assoc.
    replace (map ioc lw ++ l ++ ioc A0 :: ioc A0 :: l0 ++ flat_map (app (map ioc lw)) L1)
      with (flat_map (app (map ioc lw)) ((l ++ ioc A0 :: ioc A0 :: l0) :: L1))
      by (list_simpl; reflexivity).
    rewrite <- flat_map_app; apply IHpi; rewrite ? flat_map_app; list_simpl; reflexivity.
  + inversion HeqA; subst.
    induction L0 as [ | B L0 _] using rev_rect.
    * list_simpl; apply co_list_ilr.
      list_simpl in IHpi.
      replace (ioc A :: ioc A :: l ++ flat_map (cons (ioc A)) L1)
         with (flat_map (cons (ioc A)) (nil :: l :: L1)) in IHpi
        by (list_simpl; reflexivity).
      replace (map ioc lw ++ map ioc lw ++ l ++ flat_map (app (map ioc lw)) L1)
         with (flat_map (app (map ioc lw)) (nil :: l :: L1))
        by (list_simpl; reflexivity).
      apply (IHpi _ _ eq_refl).
    * rewrite <- ? app_assoc in IHpi.
      replace (flat_map (cons (ioc A)) (L0 ++ B :: nil) ++
                 ioc A :: ioc A :: l ++ flat_map (cons (ioc A)) L1)
         with (flat_map (cons (ioc A)) (L0 ++ B :: nil :: l :: L1)) in IHpi
        by (rewrite ? flat_map_app; list_simpl; reflexivity).
      specialize (IHpi _ _ eq_refl).
      list_simpl in IHpi; list_simpl; rewrite 3 app_assoc;
        apply co_list_ilr; list_simpl; assumption.
- app_vs_app_flat_map_cst_inv Heq.
  + app_vs_app_flat_map_cst_inv Heq1.
    * list_simpl; apply (cut_ir _ f); [ assumption | ].
      rewrite app_comm_cons, app_assoc; apply IHpi2; list_simpl; reflexivity.
    * list_simpl; rewrite (app_assoc l), (app_assoc _ (map ioc lw)), (app_assoc _ l3); apply (cut_ir _ f).
      -- list_simpl.
         replace (flat_map (app (map ioc lw)) L0 ++ map ioc lw ++ l3)
            with (flat_map (app (map ioc lw)) (L0 ++ l3 :: nil)) by (list_simpl; reflexivity).
         apply IHpi1; reflexivity.
      -- rewrite app_comm_cons, app_assoc; apply IHpi2; list_simpl; reflexivity.
    * list_simpl; rewrite (app_assoc l); apply (cut_ir _ f).
      -- apply IHpi1; reflexivity.
      -- cons2app; rewrite app_assoc; apply IHpi2; list_simpl; reflexivity.
  + app_vs_app_flat_map_cst_inv Heq2.
    * list_simpl; rewrite 3 app_assoc; apply (cut_ir _ f); [ assumption | list_simpl ].
      replace (l' ++ flat_map (app (map ioc lw)) L0 ++ map ioc lw ++ l ++ A0 :: l1
                        ++ flat_map (app (map ioc lw)) L1)
         with (l' ++ flat_map (app (map ioc lw)) (L0 ++ (l ++ A0 :: l1) :: L1))
        by (list_simpl; reflexivity).
      apply IHpi2; list_simpl; reflexivity.
    * list_simpl; rewrite 3 app_assoc, (app_assoc l3), (app_assoc _ (map ioc lw)), (app_assoc _ l1).
      apply (cut_ir _ f); list_simpl.
      -- replace (flat_map (app (map ioc lw)) L ++ map ioc lw ++ l1)
            with (flat_map (app (map ioc lw)) (L ++ l1 :: nil)) by (list_simpl; reflexivity).
         apply IHpi1; reflexivity.
      -- replace (flat_map (app (map ioc lw)) L0 ++ map ioc lw ++ l ++ A0 :: l4
                    ++ flat_map (app (map ioc lw)) L2)
            with (flat_map (app (map ioc lw)) (L0 ++ (l ++ A0 :: l4) :: L2))
           by (list_simpl; reflexivity).
         apply IHpi2; list_simpl; reflexivity.
    * list_simpl; rewrite 3 app_assoc, (app_assoc l3); apply (cut_ir _ f).
      -- apply IHpi1; reflexivity.
      -- list_simpl.
         replace (flat_map (app (map ioc lw)) L0 ++ map ioc lw ++ l ++ A0 :: flat_map (app (map ioc lw)) L2)
            with (flat_map (app (map ioc lw)) (L0 ++ (l ++ A0 :: nil) :: L2)) by (list_simpl; reflexivity).
         apply IHpi2; list_simpl; reflexivity.
  + app_vs_flat_map_cst_inv Heq2.
    * list_simpl; rewrite app_assoc, (app_assoc _ (map ioc lw)), (app_assoc _ l); apply (cut_ir _ f).
      -- replace ((flat_map (app (map ioc lw)) L ++ map ioc lw) ++ l)
            with (flat_map (app (map ioc lw)) (L ++ l :: nil)) by (list_simpl; reflexivity).
         rewrite <- (app_nil_l _); apply IHpi1; reflexivity.
      -- list_simpl; induction L0 using rev_rect.
         ++ cbn; rewrite app_comm_cons, app_assoc; apply IHpi2; list_simpl; reflexivity.
         ++ replace (flat_map (app (map ioc lw)) (L0 ++ x :: nil) ++ A0 :: l1 ++ flat_map (app (map ioc lw)) L2)
               with (flat_map (app (map ioc lw)) (L0 ++ (x ++ A0 :: l1) :: L2)) by (list_simpl; reflexivity).
            apply IHpi2; list_simpl; reflexivity.
    * list_simpl; rewrite app_assoc; apply (cut_ir _ f).
      -- rewrite <- (app_nil_l _); apply IHpi1; reflexivity.
      -- list_simpl; induction L0 using rev_rect.
         ++ cbn; cons2app; rewrite app_assoc; apply IHpi2; list_simpl; reflexivity.
         ++ replace (flat_map (app (map ioc lw)) (L0 ++ x :: nil) ++ A0 :: flat_map (app (map ioc lw)) L2)
               with (flat_map (app (map ioc lw)) (L0 ++ (x ++ A0 :: nil) :: L2)) by (list_simpl; reflexivity).
            apply IHpi2; list_simpl; reflexivity.
- assert (ill P (l' ++ flat_map (cons (ioc A)) L) (snd (projT2 (ipgax P) a))) as pi
    by (rewrite <- Heq; apply gax_ir).
  assert (L <> nil -> ipcut P (ioc A) = true) as Hcut.
  { destruct L; intros HL; [ exfalso; apply HL; reflexivity | ].
    specialize (P_gax_cut_l a (ioc A)); rewrite Heq in P_gax_cut_l.
    destruct (ipcut P (ioc A)); [ reflexivity | exfalso ].
    specialize (P_gax_cut_l _ _ eq_refl eq_refl) as [Hat _]; inversion Hat. }
  clear - Hoc Hcut pi.
  induction L as [|l L IHL] in l', Hcut, pi |- *; [ assumption | cbn ].
  assert (ipcut P (ioc A) = true) as Hcut' by (apply Hcut; intros Heq; inversion Heq).
  rewrite app_assoc; apply IHL; list_simpl; [ | intros _; apply Hcut' ].
  apply (cut_ir _ Hcut'); [ | assumption ].
  apply Hoc, Hcut'.
Qed.

Theorem cut_ir_gax A l0 l1 l2 C : ill P l0 A -> ill P (l1 ++ A :: l2) C -> ill P (l1 ++ l0 ++ l2) C.
Proof.
revert A l0 l1 l2 C.
enough (forall c A, ifsize A = c ->
        forall s l0 l1 l2 C (pi1 : ill P l0 A) (pi2 : ill P (l1 ++ A :: l2) C),
          s = ipsize pi1 + ipsize pi2 -> ill P (l1 ++ l0 ++ l2) C) as IH
  by (intros A l0 l1 l2 C pi1 pi2; apply (IH _ A eq_refl _ _ _ _ _ pi1 pi2 eq_refl)).
induction c as [c IHcut0] using lt_wf_rect.
assert (forall A, ifsize A < c -> forall l0 l1 l2 C,
          ill P l0 A -> ill P (l1 ++ A :: l2) C -> ill P (l1 ++ l0 ++ l2) C) as IHcut
  by (intros A' Hs l0' l1' l2' C' pi1 pi2; refine (IHcut0 _ _ _ _ _ _ _ _ _ pi1 pi2 _);
      try reflexivity; assumption);
  clear IHcut0.
intros A <- s; induction s as [s IHsize0] using lt_wf_rect.
assert (forall l0 l1 l2 C (pi1 : ill P l0 A) (pi2 : ill P (l1 ++ A :: l2) C),
          ipsize pi1 + ipsize pi2 < s -> ill P (l1 ++ l0 ++ l2) C)
  as IHsize by (intros; eapply IHsize0; try eassumption; reflexivity); clear IHsize0.
intros l0 l1 l2 C pi1 pi2 ->.
remember (l1 ++ A :: l2) as l; destruct_ill pi2 f X l Hl Hr HP a;
  try (revert IHsize; try revert Hl; list_simpl; rewrite ? (app_comm_cons _ _ A0);
       (try intros Hl IHsize); (try intros Hsize); constructor;
       list_simpl; rewrite ? (app_comm_cons _ _ A0); refine (IHsize _ _ _ _ pi1 Hl _); lia).
- (* ax_ir *)
  unit_vs_elt_inv Heql; list_simpl; assumption.
- (* ex_ir *)
  cbn in IHsize.
  apply PEPermutation_Type_vs_elt_subst in HP as [(l1',l2') HP ->].
  specialize (HP l0); symmetry in HP.
  refine (ex_ir _ _ _ _ HP).
  refine (IHsize _ _ _ _ pi1 Hl _); lia.
- (* ex_oc_ir *)
  cbn in IHsize.
  dichot_elt_app_inf_exec Heql ; subst.
  + rewrite 2 app_assoc.
    eapply ex_oc_ir; [ | eassumption ].
    revert Hl IHsize ; list_simpl ; intros Hl IHsize.
    refine (IHsize _ _ _ _ pi1 Hl _); lia.
  + dichot_elt_app_inf_exec Heql1 ; subst.
    * symmetry in Heql0; decomp_map_inf Heql0; subst.
      apply cut_oc_comm_left with x; try assumption.
      intros.
      enough (ill P ((l ++ map ioc l4) ++
                     flat_map (app (map ioc lw0)) ((map ioc l7 ++ l3) :: nil)) A0)
        as pi' by (list_simpl; list_simpl in pi'; assumption).
      apply substitution_ioc with x; [ intros _; apply oc_irr; assumption | | ].
      -- intros; apply IHcut with x; [ cbn; lia | | ]; assumption.
      -- list_simpl.
         replace (map ioc l4 ++ ioc x :: map ioc l7 ++ l3)
            with (map ioc (l4 ++ x :: l7) ++ l3) by (list_simpl; reflexivity).
         apply ex_oc_ir with lw; assumption.
    * rewrite <- 2 app_assoc.
      eapply ex_oc_ir; [ | eassumption ].
      revert Hl IHsize; cbn; rewrite 2 app_assoc; intros Hl IHsize.
      rewrite 2 app_assoc; refine (IHsize _ _ _ _ pi1 Hl _); lia.
- (* one_irr *)
  destruct l1; inversion Heql.
- (* one_ilr *)
  trichot_elt_elt_inf_exec Heql.
  + list_simpl; apply one_ilr.
    revert Hl IHsize; cbn; rewrite app_assoc; intros Hl IHsize.
    rewrite app_assoc; refine (IHsize _ _ _ _ pi1 Hl _); lia.
  + remember (one_ilr _ _ _ Hl) as Hone eqn:HeqHone; clear HeqHone.
    remember (ione) as C; destruct_ill pi1 f X l Hl2 Hr2 HP a; try inversion HeqC;
      try (list_simpl; rewrite app_assoc; constructor;
           list_simpl; rewrite ? app_comm_cons, (app_assoc l1);
           cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hone _); lia).
    * apply (ex_ir (l3 ++ l ++ l4)).
      -- cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hone _); lia.
      -- apply PEPermutation_Type_app_head, PEPermutation_Type_app_tail; assumption.
    * list_simpl; rewrite app_assoc; eapply ex_oc_ir; [ | eassumption ].
      list_simpl; rewrite (app_assoc l), (app_assoc _ l2), <- (app_assoc l).
      cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hone _); lia.
    * list_simpl; assumption.
    * list_simpl; rewrite app_assoc; apply lpam_ilr; [ assumption | ].
      list_simpl; rewrite app_comm_cons, (app_assoc l1).
      cbn in IHsize; refine (IHsize _ _ _ _ Hr2 Hone _); lia.
    * list_simpl; rewrite app_assoc; apply lmap_ilr; [ assumption | ].
      list_simpl; rewrite app_comm_cons, (app_assoc l1).
      cbn in IHsize; refine (IHsize _ _ _ _ Hr2 Hone _); lia.
    * list_simpl; rewrite app_assoc; apply plus_ilr.
      -- list_simpl; rewrite app_comm_cons, (app_assoc l1).
         cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hone _); lia.
      -- list_simpl; rewrite app_comm_cons, (app_assoc l1).
         cbn in IHsize; refine (IHsize _ _ _ _ Hr2 Hone _); lia.
    * list_simpl; rewrite app_assoc; apply (cut_ir _ f); [ assumption | ].
      list_simpl; rewrite app_comm_cons, (app_assoc l1); apply (IHsize _ _ _ _ Hr2 Hone); cbn; lia.
    * case_eq (ipcut P (snd (projT2 (ipgax P) a))); intros Hcut.
      -- apply (cut_ir _ Hcut); [ apply gax_ir | assumption ].
      -- specialize (P_gax_cut_r a Hcut) as [Hat _]; rewrite HeqC in Hat; inversion Hat.
  + rewrite 2 app_assoc; apply one_ilr.
    revert Hl IHsize; list_simpl; intros Hl IHsize.
    refine (IHsize _ _ _ _ pi1 Hl _); lia.
- (* tens_irr *)
  dichot_elt_app_inf_exec Heql; subst.
  + rewrite 2 app_assoc; apply tens_irr; [ | assumption ].
    revert Hl IHsize; list_simpl; intros Hl IHsize.
    refine (IHsize _ _ _ _ pi1 Hl _); lia.
  + rewrite <- app_assoc; apply tens_irr; [ assumption | ].
    revert Hl IHsize; list_simpl; intros Hl IHsize.
    refine (IHsize _ _ _ _ pi1 Hr _); lia.
- (* tens_ilr *)
  trichot_elt_elt_inf_exec Heql.
  + list_simpl; apply tens_ilr.
    revert Hl IHsize; cbn; rewrite 2 app_comm_cons, app_assoc; intros Hl IHsize.
    rewrite 2 app_comm_cons, app_assoc.
    refine (IHsize _ _ _ _ pi1 Hl _); lia.
  + remember (tens_ilr _ _ _ _ _ Hl) as Htens eqn:HeqHtens; clear HeqHtens.
    remember (itens A0 B) as D; destruct_ill pi1 f X l Hl2 Hr2 HP a; try inversion HeqD;
      try (list_simpl; rewrite app_assoc; constructor;
           list_simpl; rewrite ? app_comm_cons, (app_assoc l1);
           cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Htens _); lia).
    * apply (ex_ir (l3 ++ l ++ l4)).
      -- cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Htens _); lia.
      -- apply PEPermutation_Type_app_head, PEPermutation_Type_app_tail; assumption.
    * list_simpl; rewrite app_assoc; eapply ex_oc_ir; [ | eassumption ].
      list_simpl; rewrite (app_assoc l), (app_assoc _ l2), <- (app_assoc l).
      cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Htens _); lia.
    * subst; rewrite <- app_assoc, app_assoc.
      refine (IHcut _ _ _ _ _ _ Hr2 _); [ cbn; lia | ].
      list_simpl; refine (IHcut _ _ _ _ _ _ Hl2 Hl); cbn; lia.
    * list_simpl; rewrite app_assoc; apply lpam_ilr; [ assumption | ].
      list_simpl; rewrite app_comm_cons, (app_assoc l1).
      cbn in IHsize; refine (IHsize _ _ _ _ Hr2 Htens _); lia.
    * list_simpl; rewrite app_assoc; apply lmap_ilr; [ assumption | ].
      list_simpl; rewrite app_comm_cons, (app_assoc l1).
      cbn in IHsize; refine (IHsize _ _ _ _ Hr2 Htens _); lia.
    * list_simpl; rewrite app_assoc; apply plus_ilr.
      -- list_simpl; rewrite app_comm_cons, (app_assoc l1).
         cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Htens _); lia.
      -- list_simpl; rewrite app_comm_cons, (app_assoc l1).
         cbn in IHsize; refine (IHsize _ _ _ _ Hr2 Htens _); lia.
    * list_simpl; rewrite app_assoc; apply (cut_ir _ f); [ assumption | ].
      list_simpl; rewrite app_comm_cons, (app_assoc l1); apply (IHsize _ _ _ _ Hr2 Htens); cbn; lia.
    * case_eq (ipcut P (snd (projT2 (ipgax P) a))); intros Hcut.
      -- apply (cut_ir _ Hcut); [ apply gax_ir | assumption ].
      -- specialize (P_gax_cut_r a Hcut) as [Hat _]; rewrite HeqD in Hat; inversion Hat.
  + rewrite 2 app_assoc; apply tens_ilr.
    revert Hl IHsize; list_simpl; intros Hl IHsize.
    refine (IHsize _ _ _ _ pi1 Hl _); lia.
- (* lpam_ilr *)
  cbn in IHsize; trichot_elt_elt_inf_exec Heql.
  + dichot_elt_app_inf_exec Heql1 ; subst.
    * list_simpl; rewrite 2 app_assoc.
      apply lpam_ilr; [ | assumption ].
      list_simpl; refine (IHsize _ _ _ _ pi1 Hl _); lia.
    * list_simpl; apply lpam_ilr; [ assumption | ].
      revert Hr IHsize; rewrite app_comm_cons, app_assoc; intros Hr IHsize.
      rewrite app_comm_cons, app_assoc.
      refine (IHsize _ _ _ _ pi1 Hr _); lia.
  + change (S (ipsize Hl + ipsize Hr)) with (ipsize (lpam_ilr _ _ _ _ _ _ Hl Hr)) in IHsize.
    remember (lpam_ilr _ _ _ _ _ _ Hl Hr) as Hlpam eqn:HeqHlpam; clear HeqHlpam.
    remember (ilpam A0 B) as D; destruct_ill pi1 f X l Hl2 Hr2 HP a; try inversion HeqD;
      try (list_simpl; rewrite app_assoc; constructor;
           list_simpl; rewrite ? app_comm_cons, (app_assoc l1);
           cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hlpam _); lia).
    * apply (ex_ir (l4 ++ l ++ l3 ++ l5)).
      -- cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hlpam _); lia.
      -- apply PEPermutation_Type_app_head, PEPermutation_Type_app_tail; assumption.
    * list_simpl; rewrite app_assoc ; eapply ex_oc_ir; [ | eassumption ].
      list_simpl; rewrite (app_assoc l), (app_assoc _ l2), <- (app_assoc l).
      cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hlpam _); lia.
    * rewrite app_assoc; subst.
      refine (IHcut _ _ _ _ _ _ Hl _); [ cbn; lia | ].
      list_simpl; change (A0 :: l5) with ((A0 :: nil) ++ l5); rewrite (app_assoc l).
      refine (IHcut _ _ _ _ _ _ Hl2 Hr); cbn; lia.
    * list_simpl; rewrite app_assoc ; apply lpam_ilr; [ assumption | ].
      list_simpl; rewrite app_comm_cons, (app_assoc l1).
      cbn in IHsize; refine (IHsize _ _ _ _ Hr2 Hlpam _); lia.
    * list_simpl; rewrite app_assoc; apply lmap_ilr; [ assumption | ].
      list_simpl; rewrite app_comm_cons, (app_assoc l1).
      cbn in IHsize; refine (IHsize _ _ _ _ Hr2 Hlpam _); lia.
    * list_simpl; rewrite app_assoc; apply plus_ilr.
      -- list_simpl; rewrite app_comm_cons, (app_assoc l1).
         cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hlpam _); lia.
      -- list_simpl; rewrite app_comm_cons, (app_assoc l1).
         cbn in IHsize; refine (IHsize _ _ _ _ Hr2 Hlpam _); lia.
    * list_simpl; rewrite app_assoc; apply (cut_ir _ f); [ assumption | ].
      list_simpl; rewrite app_comm_cons, (app_assoc l1); apply (IHsize _ _ _ _ Hr2 Hlpam); cbn; lia.
    * case_eq (ipcut P (snd (projT2 (ipgax P) a))); intros Hcut.
      -- apply (cut_ir _ Hcut); [ apply gax_ir | assumption ].
      -- specialize (P_gax_cut_r a Hcut) as [Hat _]; rewrite HeqD in Hat; inversion Hat.
  + rewrite 2 app_assoc; apply lpam_ilr; [ assumption | ].
    revert Hr IHsize; list_simpl; intros Hr IHsize.
    refine (IHsize _ _ _ _ pi1 Hr _); lia.
- (* gen_ilr *)
  destruct l1; inversion Heql; subst.
  + remember (gen_ilr _ _ Hl) as Hgen eqn:HeqHgen; clear HeqHgen.
    remember (igen A0) as D; destruct_ill pi1 f X l' Hl2 Hr2 HP a; try inversion HeqD;
      try (rewrite <- ? app_assoc, app_assoc; constructor;
           list_simpl; rewrite ? app_comm_cons, (app_assoc l1);
           revert Hgen IHsize; rewrite <- (app_nil_l _); intros Hgen IHsize;
           refine (IHsize _ _ _ _ Hl2 Hgen _); cbn; lia).
    * apply (ex_ir (nil ++ l' ++ l2)).
      -- revert Hgen IHsize; rewrite <- (app_nil_l _); intros Hgen IHsize.
         refine (IHsize _ _ _ _ Hl2 Hgen _); cbn; lia.
      -- apply PEPermutation_Type_app_head, PEPermutation_Type_app_tail; assumption.
    * rewrite <- ? app_assoc, app_assoc; eapply ex_oc_ir; [ | eassumption ].
      rewrite <- app_assoc, (app_assoc l'), (app_assoc _ l0), <- (app_assoc l').
      revert Hgen IHsize; rewrite <- (app_nil_l _); intros Hgen IHsize.
      refine (IHsize _ _ _ _ Hl2 Hgen _); cbn; lia.
    * rewrite <- ? app_assoc, <- app_comm_cons, <- app_assoc, app_assoc.
      apply lpam_ilr; [ assumption | ].
      rewrite <- app_assoc, app_comm_cons, (app_assoc l1).
      revert Hgen IHsize; rewrite <- (app_nil_l _); intros Hgen IHsize.
      refine (IHsize _ _ _ _ Hr2 Hgen _); cbn; lia.
    * subst; list_simpl; rewrite <- (app_nil_r _), <- app_assoc.
      refine (IHcut _ _ _ _ _ _ Hl Hl2); cbn; lia.
    * rewrite <- ? app_assoc, app_assoc; apply lmap_ilr; [ assumption | ].
      list_simpl; rewrite app_comm_cons, (app_assoc l1).
      revert Hgen IHsize; rewrite <- (app_nil_l _); intros Hgen IHsize.
      refine (IHsize _ _ _ _ Hr2 Hgen _); cbn; lia.
    * rewrite <- ? app_assoc, app_assoc; apply plus_ilr.
      -- list_simpl; rewrite app_comm_cons, (app_assoc l1).
         revert Hgen IHsize; rewrite <- (app_nil_l _); intros Hgen IHsize.
         refine (IHsize _ _ _ _ Hl2 Hgen _); cbn; lia.
      -- list_simpl; rewrite app_comm_cons, (app_assoc l1).
         revert Hgen IHsize; rewrite <- (app_nil_l _); intros Hgen IHsize.
         refine (IHsize _ _ _ _ Hr2 Hgen _); cbn; lia.
    * list_simpl; apply (cut_ir _ f); [ assumption | ].
      list_simpl; rewrite app_comm_cons, (app_assoc l1).
      revert Hgen IHsize; rewrite <- (app_nil_l _); intros Hgen IHsize.
      apply (IHsize _ _ _ _ Hr2 Hgen); cbn; lia.
    * case_eq (ipcut P (snd (projT2 (ipgax P) a))); intros Hcut.
      -- apply (cut_ir _ Hcut); [ apply gax_ir | assumption ].
      -- specialize (P_gax_cut_r a Hcut) as [Hat _]; rewrite HeqD in Hat; inversion Hat.
  + list_simpl; apply gen_ilr.
    refine (IHsize _ _ _ _ pi1 Hl _); cbn; lia.
- (* lmap_ilr *)
  cbn in IHsize; rewrite app_assoc in Heql; trichot_elt_elt_inf_exec Heql.
  + list_simpl; apply lmap_ilr; [ assumption | ].
    revert Hr IHsize; rewrite app_comm_cons, app_assoc; intros Hr IHsize.
    rewrite app_comm_cons, app_assoc.
    refine (IHsize _ _ _ _ pi1 Hr _); lia.
  + change (S (ipsize Hl + ipsize Hr)) with (ipsize (lmap_ilr _ _ _ _ _ _ Hl Hr)) in IHsize.
    remember (lmap_ilr _ _ _ _ _ _ Hl Hr) as Hlmap; clear HeqHlmap.
    revert Hlmap IHsize; rewrite app_assoc; intros Hlmap IHsize.
    remember (ilmap A0 B) as D; destruct_ill pi1 f X l Hl2 Hr2 HP a; try inversion HeqD;
      try (list_simpl; rewrite 2 app_assoc; constructor;
           list_simpl; rewrite ? app_comm_cons, (app_assoc l1), app_assoc;
           cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hlmap _); lia).
    * apply (ex_ir ((l4 ++ l3) ++ l ++ l5)).
      -- cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hlmap _); lia.
      -- apply PEPermutation_Type_app_head, PEPermutation_Type_app_tail; assumption.
    * list_simpl; rewrite 2 app_assoc; eapply ex_oc_ir; [ | eassumption ].
      list_simpl; rewrite (app_assoc l), (app_assoc _ l2), <- (app_assoc l), app_assoc.
      cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hlmap _); lia.
    * list_simpl; rewrite 2 app_assoc; apply lpam_ilr; [ assumption | ].
      list_simpl; rewrite app_comm_cons, (app_assoc l1), app_assoc.
      cbn in IHsize; refine (IHsize _ _ _ _ Hr2 Hlmap _); lia.
    * list_simpl; subst; refine (IHcut _ _ _ _ _ _ Hl _); [ cbn; lia | ].
      rewrite app_comm_cons; refine (IHcut _ _ _ _ _ _ Hl2 Hr); cbn; lia.
    * list_simpl; rewrite 2 app_assoc; apply lmap_ilr; [ assumption | ].
      list_simpl; rewrite app_comm_cons, (app_assoc l1), app_assoc.
      cbn in IHsize; refine (IHsize _ _ _ _ Hr2 Hlmap _); lia.
    * list_simpl; rewrite 2 app_assoc; apply plus_ilr.
      -- list_simpl; rewrite app_comm_cons, (app_assoc l1), app_assoc.
         cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hlmap _); lia.
      -- list_simpl; rewrite app_comm_cons, (app_assoc l1), app_assoc.
         cbn in IHsize; refine (IHsize _ _ _ _ Hr2 Hlmap _); lia.
    * list_simpl; rewrite 2 app_assoc; apply (cut_ir _ f); [ assumption | ].
      list_simpl; rewrite app_comm_cons, app_assoc, (app_assoc l1).
      apply (IHsize _ _ _ _ Hr2 Hlmap); cbn; lia.
    * case_eq (ipcut P (snd (projT2 (ipgax P) a))); intros Hcut.
      -- apply (cut_ir _ Hcut); [ apply gax_ir | assumption ].
      -- specialize (P_gax_cut_r a Hcut) as [Hat _]; rewrite HeqD in Hat; inversion Hat.
  + dichot_elt_app_inf_exec Heql0; subst.
    * list_simpl; rewrite 2 app_assoc.
      apply lmap_ilr; [ assumption | ].
      revert Hr IHsize; list_simpl; intros Hr IHsize.
      refine (IHsize _ _ _ _ pi1 Hr _); lia.
    * list_simpl; rewrite (app_assoc l6), (app_assoc _ l); apply lmap_ilr; [ | assumption ].
      list_simpl; refine (IHsize _ _ _ _ pi1 Hl _); lia.
- (* neg_ilr *)
  trichot_elt_elt_inf_exec Heql.
  + destruct l3; inversion Heql1.
  + remember (neg_ilr _ _ Hl) as Hneg; clear HeqHneg.
    remember (ineg A0) as D; destruct_ill pi1 f X l' Hl2 Hr2 HP a; try inversion HeqD;
      try (rewrite <- ? app_assoc, app_assoc; constructor;
           list_simpl; rewrite ? app_comm_cons, (app_assoc l1);
           cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hneg _); lia).
    * apply (ex_ir (l ++ l' ++ nil)).
      -- cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hneg _); lia.
      -- apply PEPermutation_Type_app_head, PEPermutation_Type_app_tail; assumption.
    * rewrite <- ? app_assoc, app_assoc; eapply ex_oc_ir; [ | eassumption ].
      rewrite <- app_assoc, (app_assoc l'), (app_assoc _ l2), <- (app_assoc l').
      cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hneg _); lia.
    * rewrite <- ? app_assoc, <- app_comm_cons, <- app_assoc, app_assoc.
      apply lpam_ilr; [ assumption | ].
      rewrite <- app_assoc, app_comm_cons, (app_assoc l1).
      cbn in IHsize; refine (IHsize _ _ _ _ Hr2 Hneg _); lia.
    * rewrite <- ? app_assoc, app_assoc; apply lmap_ilr; [ assumption | ].
      list_simpl; rewrite app_comm_cons, (app_assoc l1).
      cbn in IHsize; refine (IHsize _ _ _ _ Hr2 Hneg _); lia.
    * clear IHsize; rewrite <- (app_nil_l (A :: l0)) in Hl2.
      list_simpl; subst; refine (IHcut _ _ _ _ _ _ Hl Hl2); cbn; lia.
    * rewrite <- ? app_assoc, app_assoc; apply plus_ilr.
      -- list_simpl; rewrite app_comm_cons, (app_assoc l1).
         cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hneg _); lia.
      -- list_simpl; rewrite app_comm_cons, (app_assoc l1).
         cbn in IHsize; refine (IHsize _ _ _ _ Hr2 Hneg _); lia.
    * list_simpl; rewrite app_assoc; apply (cut_ir _ f); [ assumption | ].
      list_simpl; rewrite <- (app_nil_r (l1 ++ A :: l2)); apply (IHsize _ _ _ _ Hr2 Hneg); cbn; lia.
    * case_eq (ipcut P (snd (projT2 (ipgax P) a))); intros Hcut.
      -- apply (cut_ir _ Hcut); [ apply gax_ir | assumption ].
      -- specialize (P_gax_cut_r a Hcut) as [Hat _]; rewrite HeqD in Hat; inversion Hat.
  + rewrite 2 app_assoc; apply neg_ilr.
    revert Hl IHsize; list_simpl; intros Hl IHsize.
    refine (IHsize _ _ _ _ pi1 Hl _); lia.
- (* with_irr *)
  cbn in IHsize; apply with_irr.
  + refine (IHsize _ _ _ _ pi1 Hl _); lia.
  + refine (IHsize _ _ _ _ pi1 Hr _); lia.
- (* with_ilr1 *)
  trichot_elt_elt_inf_exec Heql.
  + list_simpl; apply with_ilr1.
    revert Hl IHsize; cbn; rewrite app_comm_cons, app_assoc; intros Hl IHsize.
    rewrite app_comm_cons, app_assoc.
    refine (IHsize _ _ _ _ pi1 Hl _); lia.
  + remember (with_ilr1 _ _ _ _ _ Hl) as Hwith; clear HeqHwith.
    remember (iwith A0 B) as D; destruct_ill pi1 f X l Hl2 Hr2 HP a; try inversion HeqD;
      try (list_simpl; rewrite app_assoc; constructor;
           list_simpl; rewrite ? app_comm_cons, (app_assoc l1);
           cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hwith _); lia).
    * apply (ex_ir (l3 ++ l ++ l4)).
      -- cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hwith _); lia.
      -- apply PEPermutation_Type_app_head, PEPermutation_Type_app_tail; assumption.
    * list_simpl; rewrite app_assoc; eapply ex_oc_ir; [ | eassumption ].
      list_simpl; rewrite (app_assoc l), (app_assoc _ l2), <- (app_assoc l).
      cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hwith _); lia.
    * list_simpl; rewrite app_assoc; apply lpam_ilr; [ assumption | ].
      list_simpl; rewrite app_comm_cons, (app_assoc l1).
      cbn in IHsize; refine (IHsize _ _ _ _ Hr2 Hwith _); lia.
    * list_simpl; rewrite app_assoc; apply lmap_ilr; [ assumption | ].
      list_simpl; rewrite app_comm_cons, (app_assoc l1).
      cbn in IHsize; refine (IHsize _ _ _ _ Hr2 Hwith _); lia.
    * subst; refine (IHcut _ _ _ _ _ _ Hl2 Hl); cbn; lia.
    * list_simpl; rewrite app_assoc; apply plus_ilr.
      -- list_simpl; rewrite app_comm_cons, (app_assoc l1).
         cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hwith _); lia.
      -- list_simpl; rewrite app_comm_cons, (app_assoc l1).
         cbn in IHsize; refine (IHsize _ _ _ _ Hr2 Hwith _); lia.
    * list_simpl; rewrite app_assoc; apply (cut_ir _ f); [ assumption | ].
      list_simpl; rewrite app_comm_cons, (app_assoc l1); apply (IHsize _ _ _ _ Hr2 Hwith); cbn; lia.
    * case_eq (ipcut P (snd (projT2 (ipgax P) a))); intros Hcut.
      -- apply (cut_ir _ Hcut); [ apply gax_ir | assumption ].
      -- specialize (P_gax_cut_r a Hcut) as [Hat _]; rewrite HeqD in Hat; inversion Hat.
  + rewrite 2 app_assoc; apply with_ilr1.
    revert Hl IHsize; list_simpl; intros Hl IHsize.
    refine (IHsize _ _ _ _ pi1 Hl _); lia.
- (* with_ilr2 *)
  trichot_elt_elt_inf_exec Heql.
  + list_simpl; apply with_ilr2.
    revert Hl IHsize; cbn; rewrite app_comm_cons, app_assoc; intros Hl IHsize.
    rewrite app_comm_cons, app_assoc.
    refine (IHsize _ _ _ _ pi1 Hl _); lia.
  + remember (with_ilr2 _ _ _ _ _ Hl) as Hwith; clear HeqHwith.
    remember (iwith B A0) as D; destruct_ill pi1 f X l Hl2 Hr2 HP a; try inversion HeqD;
      try (list_simpl; rewrite app_assoc; constructor;
           list_simpl; rewrite ? app_comm_cons, (app_assoc l1);
           cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hwith _); lia).
    * apply (ex_ir (l3 ++ l ++ l4)).
      -- cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hwith _); lia.
      -- apply PEPermutation_Type_app_head, PEPermutation_Type_app_tail; assumption.
    * list_simpl; rewrite app_assoc; eapply ex_oc_ir; [ | eassumption ].
      list_simpl; rewrite (app_assoc l), (app_assoc _ l2), <- (app_assoc l).
      cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hwith _); lia.
    * list_simpl; rewrite app_assoc; apply lpam_ilr; [ assumption | ].
      list_simpl; rewrite app_comm_cons, (app_assoc l1).
      cbn in IHsize; refine (IHsize _ _ _ _ Hr2 Hwith _); lia.
    * list_simpl; rewrite app_assoc; apply lmap_ilr; [ assumption | ].
      list_simpl; rewrite app_comm_cons, (app_assoc l1).
      cbn in IHsize; refine (IHsize _ _ _ _ Hr2 Hwith _); lia.
    * subst; refine (IHcut _ _ _ _ _ _ Hr2 Hl); cbn; lia.
    * list_simpl; rewrite app_assoc; apply plus_ilr.
      -- list_simpl; rewrite app_comm_cons, (app_assoc l1).
         cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hwith _); lia.
      -- list_simpl; rewrite app_comm_cons, (app_assoc l1).
         cbn in IHsize; refine (IHsize _ _ _ _ Hr2 Hwith _); lia.
    * list_simpl; rewrite app_assoc; apply (cut_ir _ f); [ assumption | ].
      list_simpl; rewrite app_comm_cons, (app_assoc l1); apply (IHsize _ _ _ _ Hr2 Hwith); cbn; lia.
    * case_eq (ipcut P (snd (projT2 (ipgax P) a))); intros Hcut.
      -- apply (cut_ir _ Hcut); [ apply gax_ir | assumption ].
      -- specialize (P_gax_cut_r a Hcut) as [Hat _]; rewrite HeqD in Hat; inversion Hat.
  + rewrite 2 app_assoc; apply with_ilr2.
    revert Hl IHsize; list_simpl; intros Hl IHsize.
    refine (IHsize _ _ _ _ pi1 Hl _); lia.
- (* zero_ilr *)
  trichot_elt_elt_inf_exec Heql.
  + list_simpl; apply zero_ilr.
  + remember (zero_ilr l3 l4 C) as Hzero eqn:HeqHzero; clear HeqHzero.
    remember izero as D; destruct_ill pi1 f X l Hl2 Hr2 HP a; try inversion HeqD;
      try (list_simpl; rewrite app_assoc; constructor;
           list_simpl; rewrite ? app_comm_cons, (app_assoc l1);
           cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hzero _); lia).
    * apply (ex_ir (l3 ++ l ++ l4)).
      -- cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hzero _); lia.
      -- apply PEPermutation_Type_app_head, PEPermutation_Type_app_tail; assumption.
    * list_simpl; rewrite app_assoc; eapply ex_oc_ir; [ | eassumption ].
      list_simpl; rewrite (app_assoc l), (app_assoc _ l2), <- (app_assoc l).
      cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hzero _); lia.
    * list_simpl; rewrite app_assoc; apply lpam_ilr; [ assumption | ].
      list_simpl; rewrite app_comm_cons; rewrite (app_assoc l1).
      cbn in IHsize; refine (IHsize _ _ _ _ Hr2 Hzero _); lia.
    * list_simpl; rewrite app_assoc; apply lmap_ilr; [ assumption | ].
      list_simpl; rewrite app_comm_cons, (app_assoc l1).
      cbn in IHsize; refine (IHsize _ _ _ _ Hr2 Hzero _); lia.
    * list_simpl; rewrite app_assoc; apply plus_ilr.
      -- list_simpl; rewrite app_comm_cons, (app_assoc l1).
         cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hzero _); lia.
      -- list_simpl; rewrite app_comm_cons, (app_assoc l1).
         cbn in IHsize; refine (IHsize _ _ _ _ Hr2 Hzero _); lia.
    * list_simpl; rewrite app_assoc; apply (cut_ir _ f); [ assumption | ].
      list_simpl; rewrite app_comm_cons, (app_assoc l1); apply (IHsize _ _ _ _ Hr2 Hzero); cbn; lia.
    * case_eq (ipcut P (snd (projT2 (ipgax P) a))); intros Hcut.
      -- apply (cut_ir _ Hcut); [ apply gax_ir | assumption ].
      -- specialize (P_gax_cut_r a Hcut) as [Hat _]; rewrite HeqD in Hat; inversion Hat.
  + rewrite 2 app_assoc; apply zero_ilr.
- (* plus_ilr *)
  trichot_elt_elt_inf_exec Heql.
  + list_simpl; apply plus_ilr.
    * revert Hl IHsize; cbn; rewrite app_comm_cons, app_assoc; intros Hl IHsize.
      rewrite app_comm_cons, app_assoc.
      refine (IHsize _ _ _ _ pi1 Hl _); lia.
    * revert Hr IHsize; cbn; rewrite app_comm_cons, app_assoc; intros Hr IHsize.
      rewrite app_comm_cons, app_assoc.
      refine (IHsize _ _ _ _ pi1 Hr _); lia.
  + remember (plus_ilr _ _ _ _ _ Hl Hr) as Hplus eqn:HeqHplus; clear HeqHplus.
    remember (iplus A0 B) as D; destruct_ill pi1 f X l Hl2 Hr2 HP a; try inversion HeqD;
      try (list_simpl; rewrite app_assoc; constructor;
           list_simpl; rewrite ? app_comm_cons, (app_assoc l1);
           cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hplus _); lia).
    * apply (ex_ir (l3 ++ l ++ l4)).
      -- cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hplus _); lia.
      -- apply PEPermutation_Type_app_head, PEPermutation_Type_app_tail; assumption.
    * list_simpl; rewrite app_assoc; eapply ex_oc_ir; [ | eassumption ].
      list_simpl; rewrite (app_assoc l), (app_assoc _ l2), <- (app_assoc l).
      cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hplus _); lia.
    * list_simpl; rewrite app_assoc; apply lpam_ilr; [ assumption | ].
      list_simpl; rewrite app_comm_cons, (app_assoc l1).
      cbn in IHsize; refine (IHsize _ _ _ _ Hr2 Hplus _); lia.
    * list_simpl; rewrite app_assoc; apply lmap_ilr; [ assumption | ].
      list_simpl; rewrite app_comm_cons, (app_assoc l1).
      cbn in IHsize; refine (IHsize _ _ _ _ Hr2 Hplus _); lia.
    * subst; refine (IHcut _ _ _ _ _ _ Hl2 Hl); cbn; lia.
    * subst; refine (IHcut _ _ _ _ _ _ Hl2 Hr); cbn; lia.
    * list_simpl; rewrite app_assoc; apply plus_ilr.
      -- list_simpl; rewrite app_comm_cons, (app_assoc l1).
         cbn in IHsize; refine (IHsize _ _ _ _ Hl2 Hplus _); lia.
      -- list_simpl; rewrite app_comm_cons, (app_assoc l1).
         cbn in IHsize; refine (IHsize _ _ _ _ Hr2 Hplus _); lia.
    * list_simpl; rewrite app_assoc; apply (cut_ir _ f); [ assumption | ].
      list_simpl; rewrite app_comm_cons, (app_assoc l1); apply (IHsize _ _ _ _ Hr2 Hplus); cbn; lia.
    * case_eq (ipcut P (snd (projT2 (ipgax P) a))); intros Hcut.
      -- apply (cut_ir _ Hcut); [ apply gax_ir | assumption ].
      -- specialize (P_gax_cut_r a Hcut) as [Hat _]; rewrite HeqD in Hat; inversion Hat.
  + rewrite 2 app_assoc; apply plus_ilr.
    * revert Hl IHsize; list_simpl; intros Hl IHsize.
      list_simpl; refine (IHsize _ _ _ _ pi1 Hl _); lia.
    * revert Hr IHsize; list_simpl; intros Hr IHsize.
      list_simpl; refine (IHsize _ _ _ _ pi1 Hr _); lia.
- (* oc_irr *)
  decomp_map_inf Heql; subst; cbn in pi1, Hl; list_simpl.
  apply cut_oc_comm_left with x; try assumption.
  intros.
  enough (ill P (map ioc l4 ++ flat_map (app (map ioc lw)) (map ioc l6 :: nil)) (ioc A0))
    as pi' by (list_simpl; list_simpl in pi'; assumption).
  apply substitution_ioc with x; [ intros ?; apply oc_irr; assumption | | ].
  + intros; apply IHcut with x; [ cbn; lia | | ]; assumption.
  + clear IHsize; apply oc_irr in Hl; list_simpl in Hl; list_simpl; assumption.
- (* de_ilr *)
  trichot_elt_elt_inf_exec Heql.
  + list_simpl; apply de_ilr.
    revert Hl IHsize; cbn; rewrite app_comm_cons, app_assoc; intros Hl IHsize.
    rewrite app_comm_cons, app_assoc.
    refine (IHsize _ _ _ _ pi1 Hl _); lia.
  + apply cut_oc_comm_left with A0; try assumption.
    intros.
    enough (ill P (l3 ++ flat_map (app (map ioc lw)) (l4 :: nil)) C)
      as pi' by (list_simpl; list_simpl in pi'; assumption).
    apply substitution_ioc with A0; [ intros ?; apply oc_irr; assumption | | ].
    * intros; apply IHcut with A0; [ cbn; lia | | ]; assumption.
    * clear IHsize; apply de_ilr in Hl; list_simpl in Hl; list_simpl; assumption.
  + rewrite 2 app_assoc; apply de_ilr.
    revert Hl IHsize; list_simpl; intros Hl IHsize.
    refine (IHsize _ _ _ _ pi1 Hl _); lia.
- (* wk_ilr *)
  trichot_elt_elt_inf_exec Heql.
  + list_simpl; apply wk_ilr.
    revert Hl IHsize; cbn; rewrite app_assoc; intros Hl IHsize.
    rewrite app_assoc; refine (IHsize _ _ _ _ pi1 Hl _); lia.
  + apply cut_oc_comm_left with A0; try assumption; intros lw pi.
    enough (ill P (l3 ++ flat_map (app (map ioc lw)) (l4 :: nil)) C)
      as pi' by (list_simpl; list_simpl in pi'; assumption).
    apply substitution_ioc with A0; [ intros ?; apply oc_irr; assumption | | ].
    * intros; apply IHcut with A0; [ cbn; lia | | ]; assumption.
    * clear IHsize; apply (wk_ilr A0) in Hl; list_simpl in Hl; list_simpl; assumption.
  + rewrite 2 app_assoc; apply wk_ilr.
    revert Hl IHsize; list_simpl; intros Hl IHsize.
    refine (IHsize _ _ _ _ pi1 Hl _); lia.
- (* co_ilr *)
  trichot_elt_elt_inf_exec Heql.
  + list_simpl; apply co_ilr.
    revert Hl IHsize; cbn; rewrite 2 app_comm_cons, app_assoc; intros Hl IHsize.
    rewrite 2 app_comm_cons, app_assoc.
    refine (IHsize _ _ _ _ pi1 Hl _); lia.
  + apply cut_oc_comm_left with A0; try assumption; intros lw pi.
    enough (ill P (l3 ++ flat_map (app (map ioc lw)) (l4 :: nil)) C)
      as pi' by (list_simpl; list_simpl in pi'; assumption).
    apply substitution_ioc with A0; [ intros ?; apply oc_irr; assumption | | ].
    * intros; apply IHcut with A0; [ cbn; lia | | ]; assumption.
    * clear IHsize; apply co_ilr in Hl; list_simpl in Hl; list_simpl; assumption.
  + rewrite 2 app_assoc; apply co_ilr.
    revert Hl IHsize; list_simpl; intros Hl IHsize.
    refine (IHsize _ _ _ _ pi1 Hl _); lia.
- (* cut_ir *)
  trichot_elt_app_inf_exec Heql; subst.
  + rewrite 2 app_assoc; apply (cut_ir _ f); [ assumption | ].
    revert Hr IHsize; list_simpl; intros Hr IHsize.
    apply (IHsize _ _ _ _ pi1 Hr); lia.
  + destruct Heql1; subst.
    list_simpl; rewrite (app_assoc l), (app_assoc _ l6); apply (cut_ir _ f); [ | assumption ].
    list_simpl; apply (IHsize _ _ _ _ pi1 Hl); cbn; lia.
  + list_simpl; apply (cut_ir _ f); [ assumption | ].
    revert Hr IHsize; cbn; rewrite app_comm_cons, app_assoc; intros Hr IHsize.
    rewrite app_comm_cons, app_assoc; apply (IHsize _ _ _ _ pi1 Hr); lia.
- (* gax_ir *)
  destruct (ipcut P A) eqn:Hcut.
  + apply (cut_ir _ Hcut); [ assumption | rewrite <- Heql; apply gax_ir ].
  + destruct (P_gax_cut_l a _ _ _ Heql Hcut) as [Hat Ha].
    destruct A; inversion Hat; subst.
    apply subs_gax_l with i; try assumption.
    intros b l3 l4 Heq a' Hcut'.
    apply (P_gax_cut_l b _ _ _ Heq Hcut), Hcut'.
Qed.

End Cut_Elim_Proof.

(** ** Variants on cut admissibility *)

(** If axioms are atomic and closed under cut, then the cut rule is admissible:
provability is preserved if we remove the cut rule. *)
Lemma cut_admissible_ill P (HatN : noN_iax P) (Hat : atomic_iax P) (Hcut : icut_closed P) l C :
  ill P l C -> @ill preiatom (cutrm_ipfrag P) l C.
Proof.
intros pi. induction pi; try (econstructor; eassumption).
- eapply cut_ir_gax; try eassumption.
  + intros a Hcut'. split.
    * apply Hat.
    * intros b l3 l4 Hb. apply Hcut; assumption.
  + intros a D l3 l4 Ha Hcut'. split.
    * cbn in Ha. assert (Hatl := fst (Hat a)). rewrite Ha in Hatl.
      apply (Forall_inf_elt _ _ _ Hatl).
    * intros a' Ha'.
      apply Hcut.
      cbn in Ha, Ha'. rewrite Ha, Ha'. reflexivity.
- revert a. change (ipgax P) with (ipgax (cutrm_ipfrag P)). apply gax_ir.
Qed.

(** If there are no axioms (except the identity rule), then the cut rule is valid. *)
Lemma cut_ir_axfree P (P_axfree : no_iax P) A l0 l1 l2 C :
  ill P l0 A -> ill P (l1 ++ A :: l2) C -> @ill preiatom P (l1 ++ l0 ++ l2) C.
Proof.
intros pi1 pi2.
apply cut_ir_gax with A; try assumption.
all: intros a; contradiction (P_axfree a).
Qed.

(** If there are no axioms (except the identity rule), then the cut rule is admissible:
provability is preserved if we remove the cut rule. *)
Lemma cut_admissible_ill_axfree P (P_axfree : no_iax P) l C : ill P l C -> @ill preiatom (cutrm_ipfrag P) l C.
Proof.
intros pi. apply cut_admissible_ill; [ | | | assumption ].
all: intros a; contradiction (P_axfree a).
Qed.


(** ** Standard intuitionistic linear logic: [ill_ll] (no axiom, commutative) *)

(** cut / axioms / permutation *)
Definition ipfrag_ill := @mk_ipfrag preiatom ipcut_none NoIAxioms true.
(*                                  atoms    cut        axioms    perm  *)
Definition ill_ll := @ill preiatom ipfrag_ill.

Lemma cut_ll_ir A l0 l1 l2 C : ill_ll l0 A -> ill_ll (l1 ++ A :: l2) C -> ill_ll (l1 ++ l0 ++ l2) C.
Proof. now intros pi1 pi2; apply cut_ir_axfree with A. Qed.

Lemma cut_ll_admissible l C : ill (cutupd_ipfrag ipfrag_ill ipcut_all) l C -> ill_ll l C.
Proof.
intros pi. induction pi; try (econstructor; eassumption).
- apply cut_ll_ir with A; assumption.
- destruct a.
Qed.

End Atoms.
