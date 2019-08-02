(* ll_cut_at library for yalla *)

(** * Cut admissibility for atomic cut-formula for [ll] *)

Require Import Lia.

Require Import List_more.
Require Import List_Type_more.
Require Import genperm_Type.
Require Import Wf_nat_more.

Require Export ll_def.

Lemma cut_gax_l {P} :
  (forall a b x l1 l2 l3 l4,
    projT2 (pgax P) a = (l1 ++ dual x :: l2) -> projT2 (pgax P) b = (l3 ++ x :: l4) ->
    { c | projT2 (pgax P) c = l3 ++ l2 ++ l1 ++ l4 }) ->
forall A a l1 l2 l3 l4, atomic A -> projT2 (pgax P) a = l1 ++ dual A :: l2 ->
  ll P (l3 ++ A :: l4) -> ll P (l1 ++ l4 ++ l3 ++ l2).
Proof with try eassumption; try reflexivity.
intros Hcut A a l1 l2 l3 l4 Hat Hgax pi.
remember (l3 ++ A :: l4) as l.
revert l3 l4 Heql; induction pi using ll_nested_ind ; intros l4 l5 Heq ; subst.
- destruct l4 ; inversion Heq ; subst.
  + simpl in Hgax; list_simpl ; rewrite <- Hgax ; apply (gax_r _ a).
  + destruct l4 ; inversion H1 ; subst.
    * simpl in Hgax; list_simpl ; rewrite <- Hgax ; apply (gax_r _ a).
    * destruct l4 ; inversion H2.
- apply PCperm_Type_vs_elt_inv in p.
  destruct p as [[l4' l5'] Heq p] ; simpl in Heq ; simpl in p ; subst.
  assert (PEperm_Type (pperm P) (l1 ++ l5' ++ l4' ++ l2) (l1 ++ l5 ++ l4 ++ l2)) as HP'.
  { apply PEperm_Type_app_head.
    rewrite 2 app_assoc ; apply PEperm_Type_app_tail; symmetry... }
  apply PEperm_PCperm_Type in HP'.
  apply (ex_r _ (l1 ++ l5' ++ l4' ++ l2)).
  apply IHpi...
  apply PEperm_PCperm_Type; symmetry; apply PEperm_Type_app_head.
  rewrite 2 (app_assoc _ _ l2); apply PEperm_Type_app_tail...
- symmetry in Heq ; trichot_Type_elt_app_exec Heq ; subst.
  + list_simpl ; rewrite app_assoc.
     eapply ex_wn_r...
     list_simpl.
     rewrite (app_assoc l6) ; rewrite (app_assoc _ l3) ; rewrite <- (app_assoc l6).
     apply IHpi ; list_simpl; reflexivity.
  + destruct Heq1 as [Heq1 Heq2] ; decomp_map_Type Heq1.
    exfalso; rewrite Heq1 in Hat; inversion Hat.
  + list_simpl ; rewrite 2 app_assoc.
    eapply ex_wn_r...
    list_simpl ; rewrite (app_assoc l0) ; rewrite (app_assoc _ l7).
    apply IHpi ; list_simpl...
- apply concat_elt in Heq as ((((L1 & L2) & l1') & l2') & (Heqb & (Heqt & HeqL))); subst.
  apply ex_r with (concat L1 ++ (l1' ++ l2 ++ l1 ++ l2') ++ concat L2); [ | PCperm_Type_solve].
  change ((l1' ++ l2 ++ l1 ++ l2') ++ concat L2) with (concat ((l1' ++ l2 ++ l1 ++ l2') :: L2)).
  rewrite <- concat_app.
  apply mix_r.
  + rewrite app_length; simpl; rewrite app_length in eqpmix; simpl in eqpmix; assumption.
  + destruct (Forall_Type_app_inv _ _ _ PL) as (FL1 & FL2).
    inversion FL2; subst; clear FL2 X0; rename X1 into FL2.
    apply Forall_Type_app...
    apply Forall_Type_cons...
    apply ex_r with (l1 ++ l2' ++ l1' ++ l2) ; [ | PCperm_Type_solve].
    destruct (In_Forall_Type_elt _ _ _ (l1' ++ A :: l2') PL) as (pi & Hin).
    refine (Dependent_Forall_Type_forall_formula _ _ _ _ PL X Hin _ _ eq_refl).
- exfalso ; destruct l4 ; inversion Heq.
  + rewrite <- H0 in Hat; inversion Hat.
  + destruct l4 ; inversion H1.
- destruct l4 ; inversion Heq ; subst ; try (exfalso ; inversion Hat ; fail).
  eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  apply bot_r.
  eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  apply IHpi ; list_simpl...
- destruct l4 ; inversion Heq ; subst ; try (exfalso ; inversion Hat ; fail).
  dichot_Type_elt_app_exec H1 ; subst.
  + list_simpl.
    eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    rewrite app_comm_cons ; eapply ex_r ; [ | symmetry ; apply PCperm_Type_app_rot ] ; list_simpl.
    rewrite 3 app_assoc ; apply tens_r...
    list_simpl ; rewrite app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    rewrite app_comm_cons ; apply IHpi2 ; list_simpl...
  + eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    apply tens_r...
    list_simpl ; rewrite app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    rewrite app_comm_cons ; apply IHpi1 ; list_simpl...
- destruct l4 ; inversion Heq ; subst ; try (exfalso ; inversion Hat ; fail).
  eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  apply parr_r.
  rewrite 2 app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  rewrite 2 app_comm_cons ; apply IHpi ; list_simpl...
- destruct l4 ; inversion Heq ; subst ;  try (exfalso ; inversion Hat ; fail).
  eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  apply top_r...
- destruct l4 ; inversion Heq ; subst ; try (exfalso ; inversion Hat ; fail).
  eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  apply plus_r1...
  rewrite app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  rewrite app_comm_cons ; apply IHpi ; list_simpl...
- destruct l4 ; inversion Heq ; subst ; try (exfalso ; inversion Hat ; fail).
  eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  apply plus_r2.
  rewrite app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  rewrite app_comm_cons ; apply IHpi ; list_simpl...
- destruct l4 ; inversion Heq ; subst ; try (exfalso ; inversion Hat ; fail).
  eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  apply with_r.
  + rewrite app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    rewrite app_comm_cons ; apply IHpi1 ; list_simpl...
  + rewrite app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    rewrite app_comm_cons ; apply IHpi2 ; list_simpl...
- destruct l4 ; inversion Heq ; subst ; try (exfalso ; inversion Hat ; fail).
  exfalso ; symmetry in H1 ; decomp_map_Type H1 ; destruct A ; inversion Hat; inversion H1.
- destruct l4 ; inversion Heq ; subst ; try (exfalso ; inversion Hat ; fail).
  eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  apply de_r.
  rewrite app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  rewrite app_comm_cons ; apply IHpi ; list_simpl...
- destruct l4 ; inversion Heq ; subst ; try (exfalso ; inversion Hat ; fail).
  eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  apply wk_r.
  eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  apply IHpi ; list_simpl...
- destruct l4 ; inversion Heq ; subst ; try (exfalso ; inversion Hat ; fail).
  eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  apply co_r.
  rewrite 2 app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  rewrite 2 app_comm_cons ; apply IHpi ; list_simpl...
- dichot_Type_elt_app_exec Heq; subst.
  + apply (ex_r _ (l0 ++ l4 ++ l2 ++ l1 ++ l6)).
    * eapply (cut_r _ (dual A0)); try rewrite bidual...
      apply (ex_r _ ((l2 ++ l1) ++ l6 ++ A0 :: l4)).
      -- eapply (cut_r _ (dual A)); try rewrite bidual.
         ++ eapply ex_r; [ apply pi2 | ].
            rewrite 2 app_comm_cons; apply PCperm_Type_app_comm.
         ++ eapply ex_r; [ apply (gax_r _ a) | ].
             rewrite Hgax.
             rewrite app_comm_cons; apply PCperm_Type_app_comm.
      -- rewrite app_comm_cons.
         etransitivity; [ | apply PCperm_Type_app_comm ]; list_simpl...
    * rewrite 2 app_assoc.
      etransitivity; [ apply PCperm_Type_app_comm | ]; list_simpl...
  + apply (ex_r _ (l3 ++ l7 ++ l2 ++ l1 ++ l5)).
    * eapply (cut_r _ A0)...
      apply (ex_r _ ((l2 ++ l1) ++ l5 ++ dual A0 :: l7)).
      -- eapply (cut_r _ (dual A)); try rewrite bidual.
         ++ eapply ex_r; [ apply pi1 | ].
            rewrite 2 app_comm_cons; apply PCperm_Type_app_comm.
         ++ eapply ex_r; [ apply (gax_r _ a) | ].
            rewrite Hgax.
            rewrite app_comm_cons; apply PCperm_Type_app_comm.
      -- rewrite app_comm_cons.
         etransitivity; [ | apply PCperm_Type_app_comm ]; list_simpl...
    * rewrite 2 app_assoc.
      etransitivity; [ apply PCperm_Type_app_comm | ]; list_simpl...
    Unshelve. all: assumption.
- destruct (Hcut _ _ _ _ _ _ _ Hgax Heq) as [x Hcut'].
  apply (ex_r _ (l4 ++ l2 ++ l1 ++ l5)).
  + rewrite <- Hcut' ; apply (gax_r _ x).
  + rewrite app_assoc.
    rewrite (app_assoc _ _ (l4 ++ _)).
    apply PCperm_Type_app_comm.
Qed.

Theorem cut_at {P} :
  (forall a b x l1 l2 l3 l4,
    projT2 (pgax P) a = (l1 ++ dual x :: l2) -> projT2 (pgax P) b = (l3 ++ x :: l4) ->
    { c | projT2 (pgax P) c = l3 ++ l2 ++ l1 ++ l4 }) ->
forall X l1 l2 l3 l4,
    ll P (l1 ++ var X :: l2) -> ll P (l3 ++ covar X :: l4) -> ll P (l1 ++ l4 ++ l3 ++ l2).
Proof with try assumption; try reflexivity.
intros P_gax_cut.
enough (forall s A l0 l1 l2 (pi1: ll P (A :: l0)) (pi2 : ll P (l1 ++ dual A :: l2)),
       s = psize pi1 + psize pi2 -> { X & A = var X } + { X & A = covar X } -> ll P (l1 ++ l0 ++ l2))
  as Hat.
{ intros X l1 l2 l3 l4 pi1 pi2.
  eapply ex_r; [ | apply PCperm_Type_app_comm ].
  rewrite app_assoc; rewrite <- 2 app_assoc.
  eapply ex_r; [ | apply PCperm_Type_app_comm ].
  rewrite <- app_assoc.
  apply (ex_r _ _ ((var X :: l2) ++ l1)) in pi1 ; [ | apply PCperm_Type_app_comm ].
  rewrite <- app_comm_cons in pi1.
  refine (Hat (psize pi1 + psize pi2) (var X) (l2 ++ l1) l3 l4 pi1 pi2 _ _)...
  left; eexists... }
induction s as [s IHsize0] using lt_wf_rect; intros A l0 l1 l2 pi1 pi2 Heqs Hat; subst.
remember (l1 ++ dual A :: l2) as l; destruct_ll pi2 f X l Hl Hr HP FL a; simpl in IHsize0.
- destruct l1; inversion Heql; subst.
  + apply codual in H0; simpl; subst.
    eapply ex_r; [ | apply PCperm_Type_app_comm ]...
  + destruct l1; inversion H1; [ | destruct l1; inversion H2 ]; subst.
    apply codual in H0; simpl; subst; list_simpl...
- apply PCperm_Type_vs_elt_inv in HP.
  destruct HP as [(l1',l2') Heq HP']; subst.
  apply (ex_r _ (l1' ++ l0 ++ l2')).
  + refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
  + etransitivity; [ apply PCperm_Type_app_comm | ].
    etransitivity; [ | apply PCperm_Type_app_comm ].
    list_simpl; symmetry.
    apply PEperm_PCperm_Type.
    apply PEperm_Type_app_head...
- trichot_Type_elt_app_exec Heql; subst.
  + rewrite 2 app_assoc.
    eapply ex_wn_r; [ | apply HP ].
    revert Hl IHsize0; list_simpl; intros Hl IHsize0.
    refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
  + destruct Heql1 as [H _].
    decomp_map_Type H.
    destruct A; inversion H3; destruct Hat as [[? Heq] | [? Heq]]; inversion Heq.
  + list_simpl.
    eapply ex_wn_r; [ | apply HP ].
    revert Hl IHsize0; rewrite 2 app_assoc; intros Hl IHsize0.
    rewrite 2 app_assoc.
    refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
- apply concat_elt in Heql as ((((L1 &L2) & l1') & l2') & (Heqb & (Heqt & HeqL))); subst.
  rewrite <- app_assoc.
  replace (l1' ++ l0 ++ l2' ++ concat L2)
     with ((l1' ++ l0 ++ l2') ++ concat L2) by (rewrite ? app_assoc; reflexivity).
  change ((l1' ++ l0 ++ l2') ++ concat L2) with (concat ((l1' ++ l0 ++ l2') :: L2)).
  rewrite <- concat_app.
  apply mix_r.
  + rewrite app_length.
    rewrite app_length in f; simpl; simpl in f...
  + assert (FL' := FL).
    apply Forall_Type_app_inv in FL' as (FL1 & FL2).
    inversion FL2; subst; clear FL2; rename X0 into FL2; rename X into pi.
    apply Forall_Type_app...
    apply Forall_Type_cons...
    clear pi.
    destruct (In_Forall_Type_elt _ _ _ (l1' ++ dual A :: l2') FL) as (pi & Hin).
    refine (IHsize0 _ _ _ _ _ _ pi1 pi _ _)...
    assert (psize pi < psize (mix_r P (L1 ++ (l1' ++ dual A :: l2') :: L2) f FL))
      by (eapply psize_inf_mix; eassumption).
    simpl in H; lia.
- destruct l1; inversion Heql; [ | destruct l1; inversion H1 ].
  destruct A; inversion H0.
  destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
- destruct l1; inversion Heql; subst.
  + destruct A; inversion H0.
    destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
  + simpl; apply bot_r.
    refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
- destruct l1; inversion Heql; subst.
  + destruct A; inversion H0.
    destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
  + dichot_Type_elt_app_exec H1; subst.
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
  + simpl; apply parr_r.
    revert Hl IHsize0; rewrite 2 app_comm_cons; intros Hl IHsize0.
    refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
- destruct l1; inversion Heql; subst.
  + destruct A; inversion H0.
    destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
  + apply top_r.
- destruct l1; inversion Heql; subst.
  + destruct A; inversion H0.
    destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
  + simpl; apply plus_r1.
    revert Hl IHsize0; rewrite app_comm_cons; intros Hl IHsize0.
    refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
- destruct l1; inversion Heql; subst.
  + destruct A; inversion H0.
    destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
  + simpl; apply plus_r2.
    revert Hl IHsize0; rewrite app_comm_cons; intros Hl IHsize0.
    refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
- destruct l1; inversion Heql; subst.
  + destruct A; inversion H0.
    destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
  + simpl; apply with_r.
    * revert Hl IHsize0; rewrite app_comm_cons; intros Hl IHsize0.
      refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
    * revert Hr IHsize0; rewrite app_comm_cons; intros Hr IHsize0.
      refine (IHsize0 (psize pi1 + psize Hr) _ _ _ _ _ pi1 Hr _ Hat); lia.
- destruct l1; inversion Heql; subst.
  + destruct A; inversion H0.
    destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
  + symmetry in H1; decomp_map_Type H1.
    destruct A; inversion H1.
    destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
- destruct l1; inversion Heql; subst.
  + destruct A; inversion H0.
    destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
  + simpl; apply de_r.
    revert Hl IHsize0; rewrite app_comm_cons; intros Hl IHsize0.
    refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
- destruct l1; inversion Heql; subst.
  + destruct A; inversion H0.
    destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
  + simpl; apply wk_r.
    refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
- destruct l1; inversion Heql; subst.
  + destruct A; inversion H0.
    destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
  + simpl; apply co_r.
    revert Hl IHsize0; rewrite 2 app_comm_cons; intros Hl IHsize0.
    refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
- dichot_Type_elt_app_exec Heql; subst.
  + rewrite 2 app_assoc.
    eapply (cut_r _ A0)...
    list_simpl; rewrite app_comm_cons.
    revert Hr IHsize0; rewrite app_comm_cons; intros Hr IHsize0.
    refine (IHsize0 (psize pi1 + psize Hr) _ _ _ _ _ pi1 Hr _ Hat); lia.
  + list_simpl.
    eapply (cut_r _ A0)...
    list_simpl; rewrite app_comm_cons.
    revert Hl IHsize0; rewrite app_comm_cons; intros Hl IHsize0.
    refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); lia.
  Unshelve. all: assumption.
- rewrite <- (app_nil_r l0); rewrite <- app_assoc.
  apply cut_gax_l with A a...
  destruct Hat as [[X HX] | [X HX]]; subst; constructor.
Qed.

