(* ll_cut_at library for yalla *)

(** * Cut admissibility for atomic cut-formula for [ll] *)

From Coq Require Import Wf_nat Lia.
From OLlibs Require Import List_more Dependent_Forall_Type GPermutation_Type.
From Yalla Require Export ll_def.

Set Implicit Arguments.


Lemma cut_gax_l At P :
  (forall a b x l1 l2 l3 l4,
    projT2 (pgax P) a = (l1 ++ dual x :: l2) -> projT2 (pgax P) b = (l3 ++ x :: l4) ->
    { c | projT2 (pgax P) c = l3 ++ l2 ++ l1 ++ l4 }) ->
forall A a l1 l2 l3 l4, atomic A -> projT2 (pgax P) a = l1 ++ dual A :: l2 ->
  ll P (l3 ++ A :: l4) -> @ll At P (l1 ++ l4 ++ l3 ++ l2).
Proof with try eassumption; try reflexivity.
intros Hcut A a l1 l2 l3 l4 Hat Hgax pi.
remember (l3 ++ A :: l4) as l.
revert l3 l4 Heql; induction pi using ll_nested_ind; intros l4 l5 Heq; subst.
- destruct l4 ; inversion Heq ; subst.
  + cbn in Hgax; list_simpl ; rewrite <- Hgax ; apply (gax_r a).
  + destruct l4 ; inversion H1 ; subst.
    * cbn in Hgax; list_simpl ; rewrite <- Hgax ; apply (gax_r a).
    * destruct l4 ; inversion H2.
- apply PCPermutation_Type_vs_elt_inv in p.
  destruct p as [[l4' l5'] Heq p] ; cbn in Heq ; cbn in p ; subst.
  assert (PEPermutation_Type (pperm P) (l1 ++ l5' ++ l4' ++ l2) (l1 ++ l5 ++ l4 ++ l2)) as HP'.
  { apply PEPermutation_Type_app_head.
    rewrite 2 app_assoc ; apply PEPermutation_Type_app_tail; symmetry... }
  apply PEPermutation_PCPermutation_Type in HP'.
  apply (ex_r (l1 ++ l5' ++ l4' ++ l2)).
  apply IHpi...
  apply PEPermutation_PCPermutation_Type; symmetry; apply PEPermutation_Type_app_head.
  rewrite 2 (app_assoc _ _ l2); apply PEPermutation_Type_app_tail...
- symmetry in Heq; trichot_elt_app_inf_exec Heq; subst.
  + list_simpl; rewrite app_assoc.
     eapply ex_wn_r...
     list_simpl.
     rewrite (app_assoc l) ; rewrite (app_assoc _ l3) ; rewrite <- (app_assoc l).
     apply IHpi ; list_simpl; reflexivity.
  + destruct Heq1 as [Heq1 Heq2]; symmetry in Heq1; decomp_map_inf Heq1.
    exfalso; rewrite <- Heq1 in Hat; inversion Hat.
  + list_simpl ; rewrite 2 app_assoc.
    eapply ex_wn_r...
    list_simpl ; rewrite (app_assoc l0) ; rewrite (app_assoc _ l6).
    apply IHpi ; list_simpl...
- apply concat_vs_elt in Heq as ((((L1 & L2) & l1') & l2') & (Heqb & (Heqt & HeqL))); subst.
  apply ex_r with (concat L1 ++ (l1' ++ l2 ++ l1 ++ l2') ++ concat L2); [ | GPermutation_Type_solve].
  change ((l1' ++ l2 ++ l1 ++ l2') ++ concat L2) with (concat ((l1' ++ l2 ++ l1 ++ l2') :: L2)).
  rewrite <- concat_app.
  apply mix_r.
  + rewrite app_length; cbn; rewrite app_length in eqpmix; cbn in eqpmix; assumption.
  + assert (FL1 := Forall_inf_app_l _ _ PL).
    assert (FL2 := Forall_inf_app_r _ _ PL).
    inversion FL2; subst; clear FL2 X0; rename X1 into FL2.
    apply Forall_inf_app...
    apply Forall_inf_cons...
    apply ex_r with (l1 ++ l2' ++ l1' ++ l2) ; [ | GPermutation_Type_solve].
    destruct (In_Forall_inf_elt _ _ (l1' ++ A :: l2') PL) as (pi & Hin).
    refine (Dependent_Forall_inf_forall_formula _ _ X Hin _ _ eq_refl).
- exfalso ; destruct l4 ; inversion Heq.
  + rewrite <- H0 in Hat; inversion Hat.
  + destruct l4 ; inversion H1.
- destruct l4 ; inversion Heq ; subst ; try (exfalso ; inversion Hat ; fail).
  eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  apply bot_r.
  eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  apply IHpi ; list_simpl...
- destruct l4 ; inversion Heq ; subst ; try (exfalso ; inversion Hat ; fail).
  dichot_elt_app_inf_exec H1 ; subst.
  + list_simpl.
    eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    rewrite app_comm_cons ; eapply ex_r ; [ | symmetry ; apply PCPermutation_Type_app_rot ] ; list_simpl.
    rewrite 3 app_assoc ; apply tens_r...
    list_simpl ; rewrite app_comm_cons ; eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    rewrite app_comm_cons ; apply IHpi2 ; list_simpl...
  + eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    apply tens_r...
    list_simpl ; rewrite app_comm_cons ; eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    rewrite app_comm_cons ; apply IHpi1 ; list_simpl...
- destruct l4 ; inversion Heq ; subst ; try (exfalso ; inversion Hat ; fail).
  eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  apply parr_r.
  rewrite 2 app_comm_cons ; eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  rewrite 2 app_comm_cons ; apply IHpi ; list_simpl...
- destruct l4 ; inversion Heq ; subst ;  try (exfalso ; inversion Hat ; fail).
  eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  apply top_r...
- destruct l4 ; inversion Heq ; subst ; try (exfalso ; inversion Hat ; fail).
  eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  apply plus_r1...
  rewrite app_comm_cons ; eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  rewrite app_comm_cons ; apply IHpi ; list_simpl...
- destruct l4 ; inversion Heq ; subst ; try (exfalso ; inversion Hat ; fail).
  eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  apply plus_r2.
  rewrite app_comm_cons ; eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  rewrite app_comm_cons ; apply IHpi ; list_simpl...
- destruct l4 ; inversion Heq ; subst ; try (exfalso ; inversion Hat ; fail).
  eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  apply with_r.
  + rewrite app_comm_cons ; eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    rewrite app_comm_cons ; apply IHpi1 ; list_simpl...
  + rewrite app_comm_cons ; eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    rewrite app_comm_cons ; apply IHpi2 ; list_simpl...
- destruct l4 ; inversion Heq ; subst ; try (exfalso ; inversion Hat ; fail).
  exfalso; decomp_map_inf H1; destruct A; inversion Hat; inversion H1.
- destruct l4 ; inversion Heq ; subst ; try (exfalso ; inversion Hat ; fail).
  eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  apply de_r.
  rewrite app_comm_cons ; eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  rewrite app_comm_cons ; apply IHpi ; list_simpl...
- destruct l4 ; inversion Heq ; subst ; try (exfalso ; inversion Hat ; fail).
  eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  apply wk_r.
  eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  apply IHpi ; list_simpl...
- destruct l4 ; inversion Heq ; subst ; try (exfalso ; inversion Hat ; fail).
  eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  apply co_r.
  rewrite 2 app_comm_cons ; eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  rewrite 2 app_comm_cons ; apply IHpi ; list_simpl...
- dichot_elt_app_inf_exec Heq; subst.
  + apply (ex_r (l0 ++ l4 ++ l2 ++ l1 ++ l)).
    * eapply (cut_r (dual A0)); try rewrite bidual...
      apply (ex_r ((l2 ++ l1) ++ l ++ A0 :: l4)).
      -- eapply (cut_r (dual A)); try rewrite bidual.
         ++ eapply ex_r; [ apply pi2 | ].
            rewrite 2 app_comm_cons; apply PCPermutation_Type_app_comm.
         ++ eapply ex_r; [ apply (gax_r a) | ].
             rewrite Hgax.
             rewrite app_comm_cons; apply PCPermutation_Type_app_comm.
      -- rewrite app_comm_cons.
         etransitivity; [ | apply PCPermutation_Type_app_comm ]; list_simpl...
    * rewrite 2 app_assoc.
      etransitivity; [ apply PCPermutation_Type_app_comm | ]; list_simpl...
  + apply (ex_r (l3 ++ l6 ++ l2 ++ l1 ++ l5)).
    * eapply (cut_r A0)...
      apply (ex_r ((l2 ++ l1) ++ l5 ++ dual A0 :: l6)).
      -- eapply (cut_r (dual A)); try rewrite bidual.
         ++ eapply ex_r; [ apply pi1 | ].
            rewrite 2 app_comm_cons; apply PCPermutation_Type_app_comm.
         ++ eapply ex_r; [ apply (gax_r a) | ].
            rewrite Hgax, app_comm_cons; apply PCPermutation_Type_app_comm.
      -- rewrite app_comm_cons.
         etransitivity; [ | apply PCPermutation_Type_app_comm ]; list_simpl...
    * rewrite 2 app_assoc.
      etransitivity; [ apply PCPermutation_Type_app_comm | ]; list_simpl...
    Unshelve. all: assumption.
- destruct (Hcut _ _ _ _ _ _ _ Hgax Heq) as [x Hcut'].
  apply (ex_r (l4 ++ l2 ++ l1 ++ l5)).
  + rewrite <- Hcut' ; apply (gax_r x).
  + rewrite app_assoc, (app_assoc _ _ (l4 ++ _)).
    apply PCPermutation_Type_app_comm.
Qed.

Theorem cut_at {At} {P} :
  (forall a b x l1 l2 l3 l4,
    projT2 (pgax P) a = (l1 ++ dual x :: l2) -> projT2 (pgax P) b = (l3 ++ x :: l4) ->
    { c | projT2 (pgax P) c = l3 ++ l2 ++ l1 ++ l4 }) ->
forall X l1 l2 l3 l4,
    ll P (l1 ++ var X :: l2) -> ll P (l3 ++ covar X :: l4) -> @ll At P (l1 ++ l4 ++ l3 ++ l2).
Proof with try assumption; try reflexivity.
intros P_gax_cut.
enough (forall s A l0 l1 l2 (pi1: ll P (A :: l0)) (pi2 : ll P (l1 ++ dual A :: l2)),
       s = psize pi1 + psize pi2 -> { X & A = var X } + { X & A = covar X } -> ll P (l1 ++ l0 ++ l2))
  as Hat.
{ intros X l1 l2 l3 l4 pi1 pi2.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  rewrite app_assoc; rewrite <- 2 app_assoc.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  rewrite <- app_assoc.
  apply (ex_r _ ((var X :: l2) ++ l1)) in pi1 ; [ | apply PCPermutation_Type_app_comm ].
  rewrite <- app_comm_cons in pi1.
  refine (Hat (psize pi1 + psize pi2) (var X) (l2 ++ l1) l3 l4 pi1 pi2 _ _)...
  left; eexists... }
induction s as [s IHsize0] using lt_wf_rect; intros A l0 l1 l2 pi1 pi2 Heqs Hat; subst.
remember (l1 ++ dual A :: l2) as l; destruct_ll pi2 f X l Hl Hr HP FL a; cbn in IHsize0.
- destruct l1; inversion Heql; subst.
  + apply codual in H0; cbn; subst.
    eapply ex_r; [ | apply PCPermutation_Type_app_comm ]...
  + destruct l1; inversion H1; [ | destruct l1; inversion H2 ]; subst.
    apply codual in H0; cbn; subst; list_simpl...
- apply PCPermutation_Type_vs_elt_inv in HP.
  destruct HP as [(l1',l2') Heq HP']; subst.
  apply (ex_r (l1' ++ l0 ++ l2')).
  + refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
  + etransitivity; [ apply PCPermutation_Type_app_comm | ].
    etransitivity; [ | apply PCPermutation_Type_app_comm ].
    list_simpl; symmetry.
    apply PEPermutation_PCPermutation_Type.
    apply PEPermutation_Type_app_head...
- trichot_elt_app_inf_exec Heql; subst.
  + rewrite 2 app_assoc.
    eapply ex_wn_r; [ | apply HP ].
    revert Hl IHsize0; list_simpl; intros Hl IHsize0.
    refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
  + destruct Heql1 as [H _].
    symmetry in H; decomp_map_inf H.
    destruct A; inversion H3; destruct Hat as [[? Heq] | [? Heq]]; inversion Heq.
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
    rewrite app_length in f; cbn; cbn in f...
  + assert (FL1 := Forall_inf_app_l _ _ FL).
    assert (FL2 := Forall_inf_app_r _ _ FL).
    inversion FL2; subst; clear FL2; rename X0 into FL2; rename X into pi.
    apply Forall_inf_app...
    apply Forall_inf_cons...
    clear pi.
    destruct (In_Forall_inf_elt _ _ (l1' ++ dual A :: l2') FL) as (pi & Hin).
    refine (IHsize0 _ _ _ _ _ _ pi1 pi _ _)...
    assert (psize pi < psize (mix_r f FL))
      by (eapply psize_inf_mix; eassumption).
    cbn in H; lia.
- destruct l1; inversion Heql; [ | destruct l1; inversion H1 ].
  destruct A; inversion H0.
  destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
- destruct l1; inversion Heql; subst.
  + destruct A; inversion H0.
    destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
  + cbn; apply bot_r.
    refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
- destruct l1; inversion Heql; subst.
  + destruct A; inversion H0.
    destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
  + dichot_elt_app_inf_exec H1; subst.
    * list_simpl; rewrite 2 app_assoc.
      apply tens_r...
      list_simpl; rewrite app_comm_cons.
      revert Hr IHsize0; rewrite app_comm_cons; intros Hr IHsize0.
      refine (IHsize0 (psize pi1 + psize Hr) _ _ _ _ _ pi1 Hr _ Hat); lia.
    * list_simpl.
      apply tens_r...
      list_simpl; rewrite app_comm_cons.
      revert Hl IHsize0; rewrite app_comm_cons; intros Hl IHsize0.
      refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
- destruct l1; inversion Heql; subst.
  + destruct A; inversion H0.
    destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
  + cbn; apply parr_r.
    revert Hl IHsize0; rewrite 2 app_comm_cons; intros Hl IHsize0.
    refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
- destruct l1; inversion Heql; subst.
  + destruct A; inversion H0.
    destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
  + apply top_r.
- destruct l1; inversion Heql; subst.
  + destruct A; inversion H0.
    destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
  + cbn; apply plus_r1.
    revert Hl IHsize0; rewrite app_comm_cons; intros Hl IHsize0.
    refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
- destruct l1; inversion Heql; subst.
  + destruct A; inversion H0.
    destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
  + cbn; apply plus_r2.
    revert Hl IHsize0; rewrite app_comm_cons; intros Hl IHsize0.
    refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
- destruct l1; inversion Heql; subst.
  + destruct A; inversion H0.
    destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
  + cbn; apply with_r.
    * revert Hl IHsize0; rewrite app_comm_cons; intros Hl IHsize0.
      refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
    * revert Hr IHsize0; rewrite app_comm_cons; intros Hr IHsize0.
      refine (IHsize0 (psize pi1 + psize Hr) _ _ _ _ _ pi1 Hr _ Hat); lia.
- destruct l1; inversion Heql; subst.
  + destruct A; inversion H0.
    destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
  + decomp_map_inf H1.
    destruct A; inversion H1.
    destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
- destruct l1; inversion Heql; subst.
  + destruct A; inversion H0.
    destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
  + cbn; apply de_r.
    revert Hl IHsize0; rewrite app_comm_cons; intros Hl IHsize0.
    refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
- destruct l1; inversion Heql; subst.
  + destruct A; inversion H0.
    destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
  + cbn; apply wk_r.
    refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
- destruct l1; inversion Heql; subst.
  + destruct A; inversion H0.
    destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
  + cbn; apply co_r.
    revert Hl IHsize0; rewrite 2 app_comm_cons; intros Hl IHsize0.
    refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
- dichot_elt_app_inf_exec Heql; subst.
  + rewrite 2 app_assoc.
    eapply (cut_r A0)...
    list_simpl; rewrite app_comm_cons.
    revert Hr IHsize0; rewrite app_comm_cons; intros Hr IHsize0.
    refine (IHsize0 (psize pi1 + psize Hr) _ _ _ _ _ pi1 Hr _ Hat); lia.
  + list_simpl.
    eapply (cut_r A0)...
    list_simpl; rewrite app_comm_cons.
    revert Hl IHsize0; rewrite app_comm_cons; intros Hl IHsize0.
    refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
  Unshelve. all: assumption.
- rewrite <- (app_nil_r l0); rewrite <- app_assoc.
  apply cut_gax_l with A a...
  destruct Hat as [[X HX] | [X HX]]; subst; constructor.
Qed.
