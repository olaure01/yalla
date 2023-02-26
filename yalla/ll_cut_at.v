(** * Cut admissibility for atomic cut-formula for [ll] *)

From Coq Require Import Wf_nat Lia.
From OLlibs Require Import List_more Dependent_Forall_Type GPermutation_Type.
From Yalla Require Export ll_def.

Set Implicit Arguments.


Lemma cut_gax_l At P A a l1 l2 l3 l4 :
  atomic A -> projT2 (pgax P) a = l1 ++ dual A :: l2 ->
  (forall b l l', projT2 (pgax P) b = (l ++ A :: l') -> ll P (l1 ++ l' ++ l ++ l2)) ->
  ll P (l3 ++ A :: l4) -> @ll At P (l1 ++ l4 ++ l3 ++ l2).
Proof.
intros Hat Hgax Hcut pi.
remember (l3 ++ A :: l4) as l.
revert l3 l4 Heql. induction pi using ll_nested_ind; intros l4 l5 Heq; subst.
- destruct l4; inversion Heq; subst.
  + cbn in Hgax. list_simpl. rewrite <- Hgax; apply (gax_r a).
  + destruct l4; inversion H1; subst.
    * cbn in Hgax. list_simpl. rewrite <- Hgax; apply (gax_r a).
    * destruct l4; inversion H2.
- apply PCPermutation_Type_vs_elt_subst in p as [[l4' l5'] HP ->].
  specialize (HP (l2 ++ l1)); list_simpl in HP.
  assert (PCPermutation_Type (pperm P) (l1 ++ l5' ++ l4' ++ l2) (l1 ++ l5 ++ l4 ++ l2)) as HP'.
  { etransitivity; [ rewrite app_assoc; apply PCPermutation_Type_app_rot | ].
    etransitivity; [ | apply PCPermutation_Type_app_rot ].
    list_simpl. symmetry. assumption. }
  refine (ex_r _ _ _ HP').
  now apply IHpi.
- symmetry in Heq. trichot_elt_app_inf_exec Heq; subst.
  + list_simpl. rewrite app_assoc.
     apply (ex_wn_r _ lw); [ list_simpl | assumption ].
     rewrite (app_assoc l), (app_assoc _ l3), <- (app_assoc l).
     now apply IHpi; list_simpl.
  + destruct Heq1 as [Heq1 Heq2]; symmetry in Heq1; decomp_map_inf Heq1.
    exfalso. rewrite <- Heq1 in Hat. inversion Hat.
  + list_simpl. rewrite 2 app_assoc.
    apply (ex_wn_r _ lw); [ | assumption ].
    list_simpl. rewrite (app_assoc l0), (app_assoc _ l6).
    now apply IHpi; list_simpl.
- apply concat_vs_elt in Heq as ((((L1 & L2) & l1') & l2') & (Heqb & (Heqt & HeqL))); subst.
  apply ex_r with (concat L1 ++ (l1' ++ l2 ++ l1 ++ l2') ++ concat L2);
    [ | list_simpl; rewrite (app_assoc _ l2), (app_assoc _ (l1' ++ l2)),
                            (app_assoc _ (concat L2)), (app_assoc _ (l2' ++ concat L2));
        apply PCPermutation_Type_app_comm ].
  change ((l1' ++ l2 ++ l1 ++ l2') ++ concat L2) with (concat ((l1' ++ l2 ++ l1 ++ l2') :: L2)).
  rewrite <- concat_app. apply mix_r.
  + rewrite app_length. cbn. rewrite app_length in eqpmix. cbn in eqpmix. assumption.
  + assert (FL1 := Forall_inf_app_l _ _ PL).
    assert (FL2 := Forall_inf_app_r _ _ PL).
    inversion FL2; subst; clear FL2 X0; rename X1 into FL2.
    apply Forall_inf_app; [ assumption | ].
    apply Forall_inf_cons; [ | assumption ].
    apply ex_r with (l1 ++ l2' ++ l1' ++ l2);
      [ | list_simpl; rewrite app_assoc, (app_assoc _ l2); apply PCPermutation_Type_app_comm ].
    destruct (In_Forall_inf_elt _ _ (l1' ++ A :: l2') PL) as [pi Hin].
    refine (Dependent_Forall_inf_forall_formula _ _ X Hin _ _ eq_refl).
- exfalso. destruct l4; inversion Heq.
  + rewrite <- H0 in Hat. inversion Hat.
  + destruct l4; inversion H1.
- destruct l4; inversion Heq; subst; try (exfalso; inversion Hat; fail).
  eapply ex_r; [ | apply PCPermutation_Type_app_rot ]; list_simpl.
  apply bot_r.
  eapply ex_r; [ | apply PCPermutation_Type_app_rot ]; list_simpl.
  apply IHpi; list_simpl; reflexivity.
- destruct l4; inversion Heq; subst; try (exfalso; inversion Hat; fail).
  dichot_elt_app_inf_exec H1; subst.
  + list_simpl.
    eapply ex_r; [ | apply PCPermutation_Type_app_rot ]; list_simpl.
    rewrite app_comm_cons; eapply ex_r; [ list_simpl | symmetry; apply PCPermutation_Type_app_rot ].
    rewrite 3 app_assoc; cbn; apply tens_r; [ assumption | ].
    list_simpl. rewrite app_comm_cons. eapply ex_r; [ | apply PCPermutation_Type_app_rot ].
    list_simpl. rewrite app_comm_cons. apply IHpi2; list_simpl; reflexivity.
  + eapply ex_r; [ | apply PCPermutation_Type_app_rot ]; list_simpl.
    apply tens_r; [ | assumption ].
    list_simpl; rewrite app_comm_cons; eapply ex_r; [ | apply PCPermutation_Type_app_rot ].
    list_simpl. rewrite app_comm_cons. apply IHpi1; list_simpl; reflexivity.
- destruct l4; inversion Heq; subst; try (exfalso; inversion Hat; fail).
  eapply ex_r; [ | apply PCPermutation_Type_app_rot ]; list_simpl.
  apply parr_r.
  rewrite 2 app_comm_cons. eapply ex_r; [ | apply PCPermutation_Type_app_rot ]; list_simpl.
  rewrite 2 app_comm_cons. apply IHpi; list_simpl; reflexivity.
- destruct l4; inversion Heq; subst;  try (exfalso; inversion Hat; fail).
  eapply ex_r; [ | apply PCPermutation_Type_app_rot ]; list_simpl.
  apply top_r.
- destruct l4; inversion Heq; subst; try (exfalso; inversion Hat; fail).
  eapply ex_r; [ | apply PCPermutation_Type_app_rot ]; list_simpl.
  apply plus_r1.
  rewrite app_comm_cons. eapply ex_r; [ | apply PCPermutation_Type_app_rot ]; list_simpl.
  rewrite app_comm_cons. apply IHpi; list_simpl; reflexivity.
- destruct l4; inversion Heq; subst; try (exfalso; inversion Hat; fail).
  eapply ex_r; [ | apply PCPermutation_Type_app_rot ]; list_simpl.
  apply plus_r2.
  rewrite app_comm_cons. eapply ex_r; [ | apply PCPermutation_Type_app_rot ]; list_simpl.
  rewrite app_comm_cons. apply IHpi; list_simpl; reflexivity.
- destruct l4; inversion Heq; subst; try (exfalso; inversion Hat; fail).
  eapply ex_r; [ | apply PCPermutation_Type_app_rot ]; list_simpl.
  apply with_r; rewrite app_comm_cons.
  + eapply ex_r; [ | apply PCPermutation_Type_app_rot ]; list_simpl.
    rewrite app_comm_cons. apply IHpi1; list_simpl; reflexivity.
  + eapply ex_r; [ | apply PCPermutation_Type_app_rot ]; list_simpl.
    rewrite app_comm_cons. apply IHpi2; list_simpl; reflexivity.
- destruct l4; inversion Heq; subst; try (exfalso; inversion Hat; fail).
  exfalso; decomp_map_inf H1; destruct A; inversion Hat; inversion H1.
- destruct l4; inversion Heq; subst; try (exfalso; inversion Hat; fail).
  eapply ex_r; [ | apply PCPermutation_Type_app_rot ]; list_simpl.
  apply de_r.
  rewrite app_comm_cons; eapply ex_r; [ | apply PCPermutation_Type_app_rot ]; list_simpl.
  rewrite app_comm_cons. apply IHpi; list_simpl; reflexivity.
- destruct l4; inversion Heq; subst; try (exfalso; inversion Hat; fail).
  eapply ex_r; [ | apply PCPermutation_Type_app_rot ]; list_simpl.
  apply wk_r.
  eapply ex_r; [ | apply PCPermutation_Type_app_rot ]; list_simpl.
  apply IHpi; list_simpl; reflexivity.
- destruct l4; inversion Heq; subst; try (exfalso; inversion Hat; fail).
  eapply ex_r; [ | apply PCPermutation_Type_app_rot ]; list_simpl.
  apply co_r.
  rewrite 2 app_comm_cons; eapply ex_r; [ | apply PCPermutation_Type_app_rot ]; list_simpl.
  rewrite 2 app_comm_cons. apply IHpi; list_simpl; reflexivity.
- dichot_elt_app_inf_exec Heq; subst.
  + apply (ex_r ((l4 ++ l2 ++ l1 ++ l) ++ l0)).
    * apply (cut_r _ f); [ assumption | ].
      apply (ex_r (l1 ++ l ++ (A0 :: l4) ++ l2)).
      -- now apply IHpi2.
      -- rewrite app_assoc, app_comm_cons, (app_assoc (A0 :: _)).
         apply PCPermutation_Type_app_comm.
    * list_simpl; rewrite app_assoc, (app_assoc _ _ (l0 ++ _)), (app_assoc l1), (app_assoc _ l0).
      apply PCPermutation_Type_app_comm.
  + apply (ex_r (l3 ++ l6 ++ l2 ++ l1 ++ l5)).
    * apply (cut_r _ f); [ | assumption ].
      apply (ex_r (l1 ++ l5 ++ (dual A0 :: l6) ++ l2)).
      -- now apply IHpi1.
      -- rewrite app_assoc, app_comm_cons, (app_assoc (dual A0 :: _)).
         apply PCPermutation_Type_app_comm.
    * list_simpl; rewrite 2 app_assoc, (app_assoc l3), (app_assoc l1).
      apply PCPermutation_Type_app_comm.
- apply (Hcut a0), Heq.
Qed.

Theorem cut_at At P X (P_gax_cut : cut_closed_form P (var X)) l1 l2 l3 l4 :
  ll P (l1 ++ var X :: l2) -> ll P (l3 ++ covar X :: l4) -> @ll At P (l1 ++ l4 ++ l3 ++ l2).
Proof.
enough (forall s A l0 l1 l2 (pi1: ll P (A :: l0)) (pi2 : ll P (l1 ++ dual A :: l2)),
       s = psize pi1 + psize pi2 -> { A = var X } + { A = covar X } -> ll P (l1 ++ l0 ++ l2))
  as Hat.
{ intros pi1 pi2.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  rewrite app_assoc, <- 2 app_assoc.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  rewrite <- app_assoc.
  apply (ex_r _ ((var X :: l2) ++ l1)) in pi1; [ | apply PCPermutation_Type_app_comm ].
  rewrite <- app_comm_cons in pi1.
  refine (Hat (psize pi1 + psize pi2) (var X) (l2 ++ l1) l3 l4 pi1 pi2 _ _); [ reflexivity | ].
  left. reflexivity. }
clear l1 l2 l3 l4.
induction s as [s IHsize0] using lt_wf_rect; intros A l0 l1 l2 pi1 pi2 -> Hat.
remember (l1 ++ dual A :: l2) as l; destruct_ll pi2 f Y l Hl Hr HP FL a; cbn in IHsize0.
- destruct l1; inversion Heql; subst.
  + apply codual in H0; cbn; subst.
    eapply ex_r; [ | apply PCPermutation_Type_app_comm ]; assumption.
  + destruct l1; inversion H1; [ | destruct l1; inversion H2 ]; subst.
    apply codual in H0; cbn; subst; list_simpl; assumption.
- apply PCPermutation_Type_vs_elt_subst in HP as [(l1',l2') HP ->].
  specialize (HP l0); symmetry in HP.
  refine (ex_r _ _ _ HP).
  refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
- trichot_elt_app_inf_exec Heql; subst.
  + rewrite 2 app_assoc.
    eapply ex_wn_r; [ | apply HP ].
    revert Hl IHsize0; list_simpl; intros Hl IHsize0.
    refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
  + destruct Heql1 as [H _].
    symmetry in H; decomp_map_inf H.
    destruct Hat as [-> | ->]; inversion H3.
  + list_simpl.
    eapply ex_wn_r; [ | apply HP ].
    revert Hl IHsize0; rewrite 2 app_assoc; intros Hl IHsize0.
    rewrite 2 app_assoc.
    refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
- apply concat_vs_elt in Heql as ((((L1 &L2) & l1') & l2') & (Heqb & (Heqt & HeqL))); subst.
  rewrite <- app_assoc.
  replace (l1' ++ l0 ++ l2' ++ concat L2)
     with ((l1' ++ l0 ++ l2') ++ concat L2) by (rewrite ? app_assoc; reflexivity).
  change ((l1' ++ l0 ++ l2') ++ concat L2) with (concat ((l1' ++ l0 ++ l2') :: L2)).
  rewrite <- concat_app.
  apply mix_r.
  + rewrite app_length.
    rewrite app_length in f; cbn; cbn in f; assumption.
  + assert (FL1 := Forall_inf_app_l _ _ FL).
    assert (FL2 := Forall_inf_app_r _ _ FL).
    inversion FL2; subst; clear FL2; rename X1 into FL2; rename X0 into pi.
    apply Forall_inf_app; [ assumption | ].
    apply Forall_inf_cons; [ | assumption ].
    clear pi.
    destruct (In_Forall_inf_elt _ _ (l1' ++ dual A :: l2') FL) as [pi Hin].
    refine (IHsize0 _ _ _ _ _ _ pi1 pi _ _); [ | reflexivity | assumption ].
    assert (psize pi < psize (mix_r f FL)) as H by (eapply psize_inf_mix; eassumption).
    cbn in H; lia.
- destruct l1; inversion Heql; [ | destruct l1; inversion H1 ].
  destruct Hat as [-> | ->]; inversion H0.
- destruct l1; inversion Heql; subst.
  + destruct Hat as [-> | ->]; inversion H0.
  + cbn; apply bot_r.
    refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
- destruct l1; inversion Heql; subst.
  + destruct Hat as [-> | ->]; inversion H0.
  + dichot_elt_app_inf_exec H1; subst.
    * list_simpl; rewrite 2 app_assoc; apply tens_r; [ assumption | ].
      list_simpl; rewrite app_comm_cons.
      revert Hr IHsize0; rewrite app_comm_cons; intros Hr IHsize0.
      refine (IHsize0 (psize pi1 + psize Hr) _ _ _ _ _ pi1 Hr _ Hat); lia.
    * list_simpl; apply tens_r; [ | assumption ].
      list_simpl; rewrite app_comm_cons.
      revert Hl IHsize0; rewrite app_comm_cons; intros Hl IHsize0.
      refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
- destruct l1; inversion Heql; subst.
  + destruct Hat as [-> | ->]; inversion H0.
  + cbn; apply parr_r.
    revert Hl IHsize0; rewrite 2 app_comm_cons; intros Hl IHsize0.
    refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
- destruct l1; inversion Heql; subst.
  + destruct Hat as [-> | ->]; inversion H0.
  + apply top_r.
- destruct l1; inversion Heql; subst.
  + destruct Hat as [-> | ->]; inversion H0.
  + cbn; apply plus_r1.
    revert Hl IHsize0; rewrite app_comm_cons; intros Hl IHsize0.
    refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
- destruct l1; inversion Heql; subst.
  + destruct Hat as [-> | ->]; inversion H0.
  + cbn; apply plus_r2.
    revert Hl IHsize0; rewrite app_comm_cons; intros Hl IHsize0.
    refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
- destruct l1; inversion Heql; subst.
  + destruct Hat as [-> | ->]; inversion H0.
  + cbn; apply with_r.
    * revert Hl IHsize0; rewrite app_comm_cons; intros Hl IHsize0.
      refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
    * revert Hr IHsize0; rewrite app_comm_cons; intros Hr IHsize0.
      refine (IHsize0 (psize pi1 + psize Hr) _ _ _ _ _ pi1 Hr _ Hat); lia.
- destruct l1; inversion Heql; subst.
  + destruct Hat as [-> | ->]; inversion H0.
  + decomp_map_inf H1.
    destruct Hat as [-> | ->]; inversion H1.
- destruct l1; inversion Heql; subst.
  + destruct Hat as [-> | ->]; inversion H0.
  + cbn; apply de_r.
    revert Hl IHsize0; rewrite app_comm_cons; intros Hl IHsize0.
    refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
- destruct l1; inversion Heql; subst.
  + destruct Hat as [-> | ->]; inversion H0.
  + cbn; apply wk_r.
    refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
- destruct l1; inversion Heql; subst.
  + destruct Hat as [-> | ->]; inversion H0.
  + cbn; apply co_r.
    revert Hl IHsize0; rewrite 2 app_comm_cons; intros Hl IHsize0.
    refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
- dichot_elt_app_inf_exec Heql; subst.
  + rewrite 2 app_assoc.
    apply (cut_r _ f); [ assumption | ].
    list_simpl; rewrite app_comm_cons.
    revert Hr IHsize0; rewrite app_comm_cons; intros Hr IHsize0.
    refine (IHsize0 (psize pi1 + psize Hr) _ _ _ _ _ pi1 Hr _ Hat); lia.
  + list_simpl.
    apply (cut_r _ f); [ | assumption ].
    list_simpl; rewrite app_comm_cons.
    revert Hl IHsize0; rewrite app_comm_cons; intros Hl IHsize0.
    refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
- destruct Hat as [-> | ->].
  + rewrite <- (app_nil_r l0), <- app_assoc.
    apply cut_gax_l with (var X) a; try assumption.
    * constructor.
    * intros b l l' Hb.
      destruct (P_gax_cut b a _ _ _ _ Hb Heql) as [c <-]. apply gax_r.
  + rewrite <- (app_nil_r l0), <- app_assoc.
    apply cut_gax_l with (covar X) a; try assumption.
    * constructor.
    * intros b l l' Hb.
      apply (ex_r (l ++ l2 ++ l1 ++ l'));
        [ | rewrite app_assoc, (app_assoc l1); apply PCPermutation_Type_app_comm ].
      destruct (P_gax_cut a b _ _ _ _ Heql Hb) as [c <-]. apply gax_r.
Qed.
