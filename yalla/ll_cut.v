(** * Cut admissibility for [ll] *)

From Coq Require Import Wf_nat Lia.
From OLlibs Require Import dectype funtheory List_more Permutation_Type_more GPermutation_Type
                           flat_map_more Dependent_Forall_Type.
From Yalla Require Import ll_cut_at.
From Yalla Require Export ll_def.

Set Default Proof Using "Type".
Set Implicit Arguments.


Section Atoms.

Context {atom : DecType}.

Section Cut_Elim_Proof.

Context {P : @pfrag atom}.

Lemma cut_oc_comm A l1 l2 l3 l4 (Hgax : gax_excludes P (oc A)) :
  forall pi : ll P (l3 ++ oc A :: l4),
  (forall lw (pi' : ll P (A :: map wn lw)), psize pi' < psize pi ->
  ll P (l1 ++ map wn lw ++ l2)) -> ll P (l1 ++ l4 ++ l3 ++ l2).
Proof.
intros pi IH. remember (l3 ++ oc A :: l4) as l eqn:Heql.
induction pi using ll_nested_ind in l3, l4, Heql, IH |- *; try inversion Heql as [Heql']; subst;
cbn in IH;
try (destruct l3; destr_eq Heql'; subst;
     eapply ex_r; [ | apply PCPermutation_Type_app_rot ]; list_simpl;
     constructor;
     (rewrite ? app_comm_cons; eapply ex_r; [ | apply PCPermutation_Type_app_rot ]; list_simpl;
     rewrite ? app_comm_cons;
       try (apply IHpi; [ reflexivity | intros ? pi' Hs; apply (IH _ pi'); lia ]);
       try (apply IHpi1; [ reflexivity | intros ? pi' Hs; apply (IH _ pi'); lia ]);
       (try apply IHpi2;  [ reflexivity | intros ? pi' Hs; apply (IH _ pi'); lia ])));
try now do 3 (destruct l3; inversion Heql).
- apply PCPermutation_Type_vs_elt_subst in p as [[l3' l4'] HP ->].
  specialize (HP (l2 ++ l1)). list_simpl in HP.
  assert (PCPermutation_Type (pperm P) (l1 ++ l4' ++ l3' ++ l2) (l1 ++ l4 ++ l3 ++ l2)) as HP'.
  { etransitivity; [ rewrite app_assoc; apply PCPermutation_Type_app_rot | ].
    etransitivity; [ | apply PCPermutation_Type_app_rot ].
    list_simpl; symmetry; assumption. }
  refine (ex_r _ _ _ HP').
  apply IHpi; [ reflexivity | intros ? pi' Hs; apply (IH _ pi'); lia ].
- symmetry in Heql'. decomp_elt_eq_app_app Heql'; subst.
  + list_simpl. rewrite app_assoc.
    apply (ex_wn_r _ lw); [ | assumption ].
    list_simpl. rewrite (app_assoc l), (app_assoc _ l5).
    apply IHpi; [ list_simpl; reflexivity | ].
    intros ? pi' Hs. apply (IH _ pi'); lia.
  + decomp_map Heql'1 eqn:Hwo. discriminate Hwo.
  + list_simpl. rewrite 2 app_assoc.
    apply (ex_wn_r _ lw); [ | assumption ].
    list_simpl. rewrite (app_assoc l0), (app_assoc _ l6).
    apply IHpi; [ list_simpl; reflexivity | intros ? pi' Hs; apply (IH _ pi'); lia ].
- apply concat_eq_elt in Heql' as [(((L3, L4), l3'), l4') [-> ->] ->].
  apply ex_r with ((l3' ++ l2 ++ l1 ++ l4') ++ concat L4 ++ concat L3).
  2:{ list_simpl. rewrite app_assoc.
      etransitivity; [ apply PCPermutation_Type_app_comm | list_simpl; reflexivity ]. }
  rewrite <- concat_app.
  change ((l3' ++ l2 ++ l1 ++ l4') ++ concat (L4 ++ L3))
    with (concat ((l3' ++ l2 ++ l1 ++ l4') :: L4 ++ L3)).
  apply mix_r.
  + cbn. rewrite length_app.
    replace (S (length L4 + length L3))
       with (length L3 + length ((l3' ++ oc A :: l4') :: L4)) by (cbn; lia).
    rewrite <- length_app; assumption.
  + change ((l3' ++ l2 ++ l1 ++ l4') :: L4 ++ L3) with (((l3' ++ l2 ++ l1 ++ l4') :: L4) ++ L3).
    assert (FL3 := Forall_inf_app_l _ _ PL).
    assert (FL4 := Forall_inf_app_r _ _ PL).
    apply Forall_inf_app; [ | assumption ].
    inversion FL4; subst.
    apply Forall_inf_cons; [ | assumption ].
    apply ex_r with (l1 ++ l4' ++ l3' ++ l2).
    2:{ list_simpl. rewrite app_assoc.
        etransitivity; [ apply PCPermutation_Type_app_comm | list_simpl; reflexivity ]. }
    clear FL4 Heql. rename X0 into FL4.
    destruct (In_Forall_inf_elt _ _ _ PL) as [pi Hin].
    assert (IHpi := Hin).
    eapply Dependent_Forall_inf_forall_formula in IHpi; [ | eassumption ].
    apply IHpi; [ list_simpl; reflexivity | ].
    intros ? pi' Hs. apply (IH _ pi').
    transitivity (psize pi); [ assumption | ].
    apply (psize_inf_mix eqpmix _ _ Hin).
- destruct l3; inversion Heql' as [[Heql'' Heq]]. subst.
  decomp_elt_eq_app Heq; subst.
  + apply ex_r with (tens A0 B :: (((l3 ++ l2) ++ l1) ++ l) ++ l0).
    * apply tens_r; [ assumption | list_simpl ].
      rewrite app_comm_cons. eapply ex_r; [ | apply PCPermutation_Type_app_rot ]; list_simpl.
      rewrite app_comm_cons. apply IHpi2; [ reflexivity | intros ? pi' Hs; apply (IH _ pi'); lia ].
    * list_simpl. rewrite ? app_comm_cons.
      etransitivity; [ apply PCPermutation_Type_app_rot |  ].
      etransitivity; [ apply PCPermutation_Type_app_rot |  ].
      list_simpl. reflexivity.
  + eapply ex_r; [ | apply PCPermutation_Type_app_rot ]; list_simpl.
    apply tens_r; [ list_simpl | assumption ].
    rewrite app_comm_cons. eapply ex_r; [ | apply PCPermutation_Type_app_rot ]; list_simpl.
    rewrite app_comm_cons. apply IHpi1; [ reflexivity | intros ? pi' Hs; apply (IH _ pi'); lia ].
- destruct l3; inversion Heql as [[Heql'' Heq]]; subst.
  + apply (IH _ pi). lia.
  + decomp_map Heq eqn:Hwo. discriminate Hwo.
- decomp_elt_eq_app Heql'; subst.
  + apply ex_r with ((((l3 ++ l2) ++ l1) ++ l) ++ l0).
    * apply (cut_r _ f); [ assumption | list_simpl ].
      rewrite app_comm_cons; eapply ex_r; [ | apply PCPermutation_Type_app_rot ]; list_simpl.
      rewrite app_comm_cons; apply IHpi2; [ reflexivity | intros ? pi' Hs; apply (IH _ pi'); lia ].
    * list_simpl; rewrite ? app_comm_cons.
      etransitivity; [ apply PCPermutation_Type_app_rot |  ].
      etransitivity; [ apply PCPermutation_Type_app_rot |  ].
      list_simpl; reflexivity.
  + eapply ex_r; [ | apply PCPermutation_Type_app_rot ]; list_simpl.
    apply (cut_r _ f); [ list_simpl | assumption ].
    rewrite app_comm_cons; eapply ex_r; [ | apply PCPermutation_Type_app_rot ]; list_simpl.
    rewrite app_comm_cons; apply IHpi1; [ reflexivity | intros ? pi' Hs; apply (IH _ pi'); lia ].
- contradiction (Hgax a). rewrite Heql. apply in_inf_elt.
Qed.
Arguments cut_oc_comm : clear implicits.

Lemma substitution_oc A lw :
  (forall a n l1 l2, projT2 (pgax P) a = l1 ++ wn_n (S n) A :: l2 ->
     (pcut P (wn_n (S n) A) = true) * ll P (oc (dual A) :: map wn lw)) ->
  (forall l1 l2, ll P (l1 ++ A :: l2) -> ll P (l1 ++ map wn lw ++ l2)) ->
  forall l' L, ll P (l' ++ flat_map (fun '(p1, p2) => wn_n p1 (wn A) :: p2) L) ->
    ll P (l' ++ flat_map (fun '(_, p2) => app (map wn lw) p2) L).
Proof.
intros Hgax IHcut l' L pi;
  remember (l' ++ flat_map (fun '(p1,p2) => wn_n p1 (wn A) :: p2) L) as l eqn:Heql; revert l' L Heql;
  induction pi using ll_nested_ind; intros l' L' Heq; try (rename L' into L); subst.
- destruct L; list_simpl in Heq; subst.
  + list_simpl. apply ax_r.
  + exfalso.
    destruct p; destruct l'; inversion Heq; destruct n; cbn in H0; inversion H0;
      destruct l'; destr_eq H1; destruct l'; discriminate.
- destruct (PCPermutation_Type_app_flat_map_cons_fun_inv _ (fun p => wn_n p (wn A)) (map wn lw) _ _ _ p)
      as [[L' l''] Hnil' [-> HPL']].
    eapply ex_r; [ | apply HPL' ].
    apply IHpi. reflexivity.
- assert (injective (@wn atom)) as Hinj by (intros x y [= ->]; reflexivity).
  destruct (Permutation_Type_app_map_app_eq_app_flat_map_cons_fun_inv
              (fun p => wn_n p (wn A)) Hinj lw _ _ _ _ p Heq)
    as [(((((lw1', lw2'), l1'), l2'), l''), L') (H1 & H2 & H3 & <-)].
  apply (ex_wn_r _ lw1'); [ | assumption ].
  rewrite H3. apply IHpi. assumption.
- assert ({L0 & ((concat L0 = l' ++ flat_map (fun '(p1,p2) => app (map wn lw) p2) L')
              * ((length L0 = length L)
              *  (Forall_inf (fun l =>
                   {'(l0, L0) & (l = l0 ++ flat_map (fun '(p1,p2) => app (map wn lw) p2) L0)
                          * (In_inf (l0 ++ flat_map (fun '(p1,p2) => wn_n p1 (wn A) :: p2) L0) L)})
                   L0)))%type})
    as (L0 & (<- & (Heql & FL))).
  { clear - Heq.
    induction L in lw, L', l', Heq |- *.
    - exists nil. repeat split.
      + cbn in Heq. destruct l'; inversion Heq.
        destruct L'; try destruct p; destr_eq H0; assumption.
      + apply Forall_inf_nil.
    - cbn in Heq. decomp_app_eq_app Heq; subst.
      + destruct (IHL lw _ _ Heq1) as (L0 & (Heq0 & (Heql & FL))).
        exists (a :: L0). repeat split.
        * cbn. rewrite Heq0. apply app_assoc.
        * cbn. rewrite Heql. reflexivity.
        * apply Forall_inf_cons.
          -- exists (a, nil). split; cbn; [ | left ]; symmetry; apply app_nil_r.
          -- apply forall_Forall_inf.
             intros l0 Hin.
             destruct (Forall_inf_forall FL l0 Hin) as ((l0', L0') & (Heq' & Hin')).
             exists (l0', L0'). split; [ | right ]; assumption.
      + change (fun '(p1,p2) => (wn_n p1 (wn A) :: p2))
          with (fun '(p1,p2) => (fun k => wn_n k (wn A)) p1 :: p2) in Heq1.
        decomp_app_eq_flat_map_cons_fun Heq1.
        * destruct (IHL lw _ _ Heq3) as (L2 & (Heq & (Heql & FL))).
          split with
            ((l' ++ (flat_map (fun '(p1,p2) => app (map wn lw) p2) (L0 ++ (n, l0) :: nil))) :: L2);
            repeat split.
          -- cbn. rewrite Heq, ? flat_map_app. cbn. rewrite app_nil_r, ? app_assoc. reflexivity.
          -- cbn. rewrite Heql. reflexivity.
          -- apply Forall_inf_cons.
             ++ exists (l', (L0 ++ (n, l0) :: nil)). split; [ | left ]; reflexivity.
             ++ apply forall_Forall_inf.
                intros l Hin.
                destruct (Forall_inf_forall FL l Hin) as [(l0', L0') [Heq' Hin']].
                exists (l0', L0'). split; [ | right ]; assumption.
        * change (flat_map (fun '(p1,p2) => wn_n p1 (wn A) :: p2) L1)
            with (nil ++ (flat_map (fun '(p1,p2) => wn_n p1 (wn A) :: p2) L1)) in Heq3.
          destruct (IHL lw _ _ Heq3) as (L2 & (Heq & (Heql & FL))).
          exists ((l' ++ (flat_map (fun '(p1,p2) => app (map wn lw) p2) L0)) :: L2). repeat split.
          -- cbn. rewrite Heq, ? flat_map_app. cbn. rewrite ? app_assoc. reflexivity.
          -- cbn. rewrite Heql. reflexivity.
          -- apply Forall_inf_cons.
             ++ exists (l', L0). split; [ | left ]; reflexivity.
             ++ apply forall_Forall_inf.
                intros l0 Hin.
                destruct (Forall_inf_forall FL l0 Hin) as [(l0', L0') [Heq' Hin']].
                exists (l0', L0'). split; [ | right ]; assumption. }
  apply mix_r.
  + rewrite Heql. assumption.
  + apply forall_Forall_inf.
    intros l0 Hin.
    destruct (Forall_inf_forall FL l0 Hin) as [(l0', L0') [-> [pi0 Hin0']%(In_Forall_inf_in _ PL)]].
    refine (Dependent_Forall_inf_forall_formula _ _ X Hin0' l0' L0' eq_refl).
- destruct L; list_simpl in Heq; subst.
  + list_simpl. apply one_r.
  + exfalso.
    destruct p, l'; inversion Heq; try now inversion H0; destruct n; destr_eq H0.
    destruct l'; discriminate H1.
- destruct l'; inversion Heq;
    [ destruct L; try destruct p; destr_eq H0; try now (destruct n; destr_eq H1) | ]; subst.
  cbn. apply bot_r.
  apply IHpi. reflexivity.
- destruct l'; inversion Heq;
    [ destruct L; try destruct p; destr_eq H0; try now (destruct n; destr_eq H1) | ]; subst.
  change (fun '(p1,p2) => wn_n p1 (wn A) :: p2)
    with (fun '(p1,p2) => (fun k => wn_n k (wn A)) p1 :: p2) in H1.
  decomp_app_eq_app_flat_map_cons_fun H1.
  + list_simpl; apply tens_r; [ | assumption ].
    rewrite app_comm_cons in IHpi1. rewrite app_comm_cons. apply IHpi1. reflexivity.
  + rewrite flat_map_app. list_simpl. rewrite 3 app_assoc. apply tens_r.
    * rewrite app_comm_cons in IHpi1. rewrite app_comm_cons. apply IHpi1. reflexivity.
    * list_simpl.
      replace (flat_map (fun '(p1,p2) => app (map wn lw) p2) L0 ++ map wn lw ++ l)
         with (flat_map (fun '(p1,p2) => app (map wn lw) p2) (L0 ++ (n , l) :: nil))
        by (rewrite flat_map_app; list_simpl; reflexivity).
      rewrite app_comm_cons in IHpi2. rewrite app_comm_cons. apply IHpi2. reflexivity.
  + rewrite flat_map_app, app_assoc; cbn; apply tens_r.
    * rewrite <- (app_nil_l (flat_map _ _)), app_comm_cons. apply IHpi1. reflexivity.
    * rewrite app_comm_cons in IHpi2. rewrite app_comm_cons. apply IHpi2. reflexivity.
- destruct l'; inversion Heq;
    [ destruct L; try destruct p; destr_eq H0; try now (destruct n; destr_eq H1) | ]; subst.
  cbn; apply parr_r.
  rewrite 2 app_comm_cons; apply IHpi; reflexivity.
- destruct l'; inversion Heq;
    [ destruct L; try destruct p; destr_eq H0; try now (destruct n; destr_eq H1) | ]; subst.
  apply top_r.
- destruct l'; inversion Heq;
    [ destruct L; try destruct p; destr_eq H0; try now (destruct n; destr_eq H1) | ]; subst.
  cbn; apply plus_r1.
  rewrite app_comm_cons; apply IHpi; reflexivity.
- destruct l'; inversion Heq;
    [ destruct L; try destruct p; destr_eq H0; try now (destruct n; destr_eq H1)| ]; subst.
  cbn; apply plus_r2.
  rewrite app_comm_cons; apply IHpi; reflexivity.
- destruct l'; inversion Heq;
    [ destruct L; try destruct p; destr_eq H0; try now (destruct n; destr_eq H1) | ]; subst.
  cbn; apply with_r.
  + rewrite app_comm_cons; apply IHpi1; reflexivity.
  + rewrite app_comm_cons; apply IHpi2; reflexivity.
- destruct l'; inversion Heq;
    [ destruct L; try destruct p; destr_eq H0; try now (destruct n; destr_eq H1)| ]; subst.
  assert ({ Lw | flat_map (fun '(p1,p2) => app (map wn lw) p2) L = map wn Lw }) as [Lw HeqLw].
  { clear Heq pi IHpi; revert l' H1; clear; induction L; intros l' Heq.
    - exists nil; reflexivity.
    - cbn in Heq.
      remember (let '(p1, p2) := a in wn_n p1 (wn A) :: p2) as l2.
      remember (flat_map (fun '(p1, p2) => wn_n p1 (wn A) :: p2) L) as l1.
      decomp_map Heq eqn:Heq'. subst. destruct Heq' as [Heq1 Heq2].
      destruct a. cbn.
      destruct l2; destr_eq Heq1. subst.
      list_simpl in IHL. rewrite <- Heq2, app_comm_cons, app_assoc in IHL.
      destruct (IHL _ eq_refl) as [Lw Heq'].
      exists (lw ++ l2 ++ Lw). list_simpl. rewrite <- Heq'. reflexivity. }
  decomp_map H1 eqn:Heq1. subst.
  list_simpl. rewrite HeqLw, <- map_app. apply oc_r.
  list_simpl in IHpi. rewrite Heq1 in IHpi.
  list_simpl. rewrite <- HeqLw, app_comm_cons. apply IHpi. reflexivity.
- destruct l'; inversion Heq; subst; list_simpl.
  + destruct L as [ | ([ | n], l') L]; destr_eq H0; subst.
    * list_simpl. apply (IHcut nil _ (IHpi (A :: l') L eq_refl)).
    * apply (IHpi nil ((n, l') :: L) eq_refl).
  + apply de_r.
    rewrite app_comm_cons in IHpi. rewrite app_comm_cons. apply IHpi. reflexivity.
- destruct l'; inversion Heq; subst; list_simpl.
  + destruct L as [ | (n, l') L]; destr_eq H0.
    list_simpl. apply wk_list_r, IHpi. assumption.
  + apply wk_r, IHpi. reflexivity.
- destruct l'; inversion Heq; subst; list_simpl.
  + destruct L as [ | (n, l') L]; inversion H0.
    list_simpl. apply co_list_r.
    replace (map wn lw ++ map wn lw ++ l' ++ flat_map (fun '(p1,p2) => app (map wn lw) p2) L)
       with (nil ++ flat_map (fun '(p1,p2) => app (map wn lw) p2)
                             (((n, nil) :: nil) ++ ((n, l') :: nil) ++ L))
     by (rewrite flat_map_app; list_simpl; reflexivity).
    apply IHpi. list_simpl. rewrite H1, H2. reflexivity.
  + apply co_r.
    rewrite 2 app_comm_cons in IHpi; rewrite 2 app_comm_cons; apply IHpi; reflexivity.
- change (fun '(p1,p2) => wn_n p1 (wn A) :: p2)
    with (fun '(p1,p2) => (fun k => wn_n k (wn A)) p1 :: p2) in Heq.
  decomp_app_eq_app_flat_map_cons_fun Heq.
  + list_simpl; apply (cut_r _ f); [ | assumption ].
    rewrite app_comm_cons in IHpi1; rewrite app_comm_cons; apply IHpi1; reflexivity.
  + rewrite flat_map_app; list_simpl.
    rewrite 3 app_assoc; apply (cut_r _ f).
    * rewrite app_comm_cons in IHpi1; rewrite app_comm_cons; apply IHpi1; reflexivity.
    * list_simpl.
      replace (flat_map (fun '(p1,p2) => app (map wn lw) p2) L0 ++ map wn lw ++ l)
         with (flat_map (fun '(p1,p2) => app (map wn lw) p2) (L0 ++ (n , l) :: nil))
        by (rewrite flat_map_app; list_simpl; reflexivity).
      rewrite app_comm_cons in IHpi2; rewrite app_comm_cons; apply IHpi2; reflexivity.
  + rewrite flat_map_app, app_assoc; cbn; apply (cut_r _ f).
    * rewrite <- (app_nil_l (flat_map _ _)), app_comm_cons.
      apply IHpi1; reflexivity.
    * rewrite app_comm_cons in IHpi2; rewrite app_comm_cons; apply IHpi2; reflexivity.
- assert (ll P (l' ++ flat_map (fun '(p1, p2) => wn_n p1 (wn A) :: p2) L)) as pi
    by (rewrite <- Heq; apply gax_r).
  assert (L <> nil -> ll P (oc (dual A) :: map wn lw)) as Hoc.
  { intros HL. destruct L as [|(p, l) L].
    - contradiction HL. reflexivity.
    - cbn in Heq. rewrite wn_n_wn in Heq. eapply (Hgax a). eassumption. }
  assert (Forall_inf (fun '(p,_) => pcut P (wn_n (S p) A) = true) L) as HcutL.
  { clear - Heq Hgax.
    induction L as [| (k, l) L IHL] in l', Heq |- *; constructor; cbn; cbn in Heq.
    - rewrite wn_n_wn in Heq.
      eapply (Hgax a); eassumption.
    - apply IHL with (l' ++ wn_n k (wn A) :: l).
      list_simpl; assumption. }
  clear - pi HcutL Hoc.
  induction L as [| (k, l) L IHL] in l', pi, HcutL, Hoc |- *; [ assumption | cbn ].
  inversion HcutL; subst.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ]; list_simpl.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  apply (cut_r _ X).
  + assert ((k, l) :: L <> nil) as HL by (intros Heq; inversion Heq).
    specialize (Hoc HL); clear - Hoc.
    rewrite dual_wn_n, <- oc_n_oc.
    induction k as [|k IH]; [ | apply oc_r ]; assumption.
  + rewrite app_comm_cons, app_assoc; eapply ex_r; [ | apply PCPermutation_Type_app_comm ]; rewrite app_assoc.
    apply IHL; try assumption.
    * cbn in pi. rewrite wn_n_wn in pi. list_simpl. assumption.
    * intros _. apply Hoc. intros [=].
Qed.

Variable P_gax_cut : forall a C l1 l2,
  projT2 (pgax P) a = l1 ++ C :: l2 -> pcut P C = false ->
    atomic C
  * forall b l3 l4, projT2 (pgax P) b = l3 ++ dual C :: l4 -> { c | projT2 (pgax P) c = l3 ++ l2 ++ l1 ++ l4 }.

Lemma oc_notin_gax A (Hcut : pcut P (oc A) = false) : gax_excludes P (oc A).
Proof using P_gax_cut.
intros a [(l1, l2) Ha]%in_inf_split. specialize (P_gax_cut _ _ _ _ Ha).
destruct (pcut P (oc A)); [ discriminate Hcut | ].
destruct (P_gax_cut eq_refl) as [Hgax _]. inversion Hgax.
Qed.

Lemma cut_r_gax A l1 l2 : ll P (dual A :: l1) -> ll P (A :: l2) -> ll P (l2 ++ l1).
Proof using P_gax_cut.
enough (forall c s A l0 l1 l2 (pi1 : ll P (dual A :: l0)) (pi2 : ll P (l1 ++ A :: l2)),
          s = psize pi1 + psize pi2 -> fsize A = c -> ll P (l1 ++ l0 ++ l2)) as IH.
{ intros pi1 pi2.
  rewrite <- (app_nil_l _) in pi2.
  apply (ex_r (nil ++ l1 ++ l2)); [ | cbn; apply PCPermutation_Type_app_comm ].
  exact (IH _ _ A _ _ _ pi1 pi2 eq_refl eq_refl). }
clear A l1 l2. induction c as [c IHcut0] using lt_wf_rect.
assert (forall A, fsize A < c -> forall l0 l1 l2,
          ll P (dual A :: l0) -> ll P (l1 ++ A :: l2) -> ll P (l1 ++ l0 ++ l2)) as IHcut
  by (intros A Hs l0 l1 l2 pi1 pi2; apply (IHcut0 _ Hs _ _ _ _ _ pi1 pi2 eq_refl eq_refl)). clear IHcut0.
induction s as [s IHsize0] using lt_wf_rect.
assert (forall A l0 l1 l2 (pi1 : ll P (dual A :: l0)) (pi2 : ll P (l1 ++ A :: l2)),
          psize pi1 + psize pi2 < s -> fsize A = c -> ll P (l1 ++ l0 ++ l2)) as IHsize
  by (intros; eapply (IHsize0 (psize pi1 + psize pi2)); [ | reflexivity | ]; assumption). clear IHsize0.
intros A l0 l1 l2 pi1 pi2 -> <-.
remember (l1 ++ A :: l2) as l eqn:Heql. destruct_ll pi2 f X l Hl Hr HP Hax a.
- (* ax_r *)
  destruct l1; injection Heql as [= <- Heql].
  + subst l2. eapply ex_r; [ apply pi1 | apply PCPermutation_Type_cons_append ].
  + decomp_unit_eq_elt Heql. list_simpl. assumption.
- (* ex_r *)
  cbn in IHsize.
  apply PCPermutation_Type_vs_elt_subst in HP as [[l1' l2'] HP ->].
  eapply ex_r; [ refine (IHsize _ _ _ _ pi1 Hl _ _); lia | ].
  symmetry. apply HP.
- (* ex_wn_r *)
  symmetry in Heql. decomp_elt_eq_app_app Heql; list_simpl; subst.
  + rewrite 2 app_assoc. eapply ex_wn_r, HP. rewrite <- 2 app_assoc.
    revert Hl IHsize. list_simpl. intros Hl IHsize.
    refine (IHsize _ _ _ _ pi1 Hl _ _); lia.
  + decomp_map Heql1. subst. cbn in pi1.
    rewrite <- (app_nil_l (map wn l5 ++ l3)).
    case_eq (pcut P (oc (dual A))); intros Hcut.
    * eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
      list_simpl; apply (cut_r _ Hcut); [ | assumption ].
      cbn; rewrite bidual, app_comm_cons, app_assoc.
      eapply ex_r; [ | apply PCPermutation_Type_app_comm ]; list_simpl.
      replace (map wn l4 ++ wn A :: map wn l5 ++ l3) with (map wn (l4 ++ A :: l5) ++ l3)
        by (list_simpl; reflexivity).
      eapply ex_wn_r; eassumption.
    * assert (Hgax := (oc_notin_gax _ Hcut)).
      refine (cut_oc_comm (dual A) _ _ nil _ Hgax pi1 _).
      intros lw' pi0 Hs; list_simpl; cbn in IHsize.
      apply Permutation_Type_vs_elt_subst in HP as [(l2', l3') HP ->].
      specialize (HP lw'); symmetry in HP.
      rewrite (app_assoc (map wn l4)), (app_assoc _ _ l3), <- (app_assoc (map wn l4)), <- 2 map_app.
      refine (ex_wn_r _ _ _ _ _ HP).
      revert Hl IHsize. list_simpl. rewrite ? (app_assoc l (map wn _)). intros Hl IHsize.
      simple refine (IHsize _ _ _ _ _ Hl _ _); [ exact (oc_r pi0) | cbn in *; lia | reflexivity ].
  + rewrite <- 2 app_assoc.
    eapply ex_wn_r, HP.
    rewrite (app_assoc (map wn lw)), (app_assoc l).
    revert Hl IHsize. cbn. rewrite (app_assoc (map wn lw) l5), (app_assoc l). intros Hl IHsize.
    refine (IHsize _ _ _ _ pi1 Hl _ _); lia.
- (* mix_r *)
  apply concat_eq_elt in Heql as [(((L1, L2), l1'), l2') [-> ->] ->].
  rewrite <- app_assoc.
  replace (l1' ++ l0 ++ l2' ++ concat L2)
     with ((l1' ++ l0 ++ l2') ++ concat L2) by (rewrite ? app_assoc; reflexivity).
  change ((l1' ++ l0 ++ l2') ++ concat L2) with (concat ((l1' ++ l0 ++ l2') :: L2)).
  rewrite <- concat_app.
  apply mix_r.
  + clear IHsize.
    rewrite length_app; rewrite length_app in f; apply f.
  + assert (FL1 := Forall_inf_app_l _ _ Hax).
    assert (FL2 := Forall_inf_app_r _ _ Hax).
    inversion FL2; subst; clear FL2; rename X0 into FL2; rename X into pi.
    apply Forall_inf_app; [ assumption | ].
    apply Forall_inf_cons; [ | assumption ].
    clear pi.
    destruct (In_Forall_inf_elt _ _ (l1' ++ A :: l2') Hax) as [pi Hin].
    refine (IHsize _ _ _ _ pi1 pi _ eq_refl).
    enough (psize pi < psize (mix_r f Hax)) by lia.
    apply psize_inf_mix; assumption.
- (* one_r *)
  decomp_unit_eq_elt Heql; list_simpl.
  remember one_r as Hone eqn:Hdel. clear Hdel.
  remember (dual one :: l0) as l'; destruct_ll pi1 f X l Hl2 Hr2 HP Hax a; try inversion Heql';
    cbn in IHsize.
  + (* ex_r *)
    destruct (PCPermutation_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] HP' Heq];
      cbn in Heq, HP'; subst.
    apply PEPermutation_PCPermutation_Type in HP'; unfold id in HP'; cbn in HP'.
    eapply ex_r; [ | etransitivity; [ apply PCPermutation_Type_app_comm | symmetry; apply HP' ] ].
    revert Hone IHsize. change one with (@dual atom bot). intros Hone IHsize.
    refine (IHsize _ _ _ _ Hone Hl2 _ eq_refl). lia.
  + (* ex_wn_r *)
    destruct l; destr_eq Heql'; [ destruct lw'; destr_eq Heql' | ]; subst.
    * assert (lw = nil) by (clear - HP; symmetry in HP; apply (Permutation_Type_nil HP)); subst.
      list_simpl in Heql'. subst. list_simpl in Hl2.
      revert Hl2 IHsize. cbn. change bot with (@dual atom one). intros Hl2 IHsize.
      revert Hone IHsize. rewrite <- (app_nil_l (one :: _)). intros Hone IHsize.
      replace l0 with (nil ++ l0 ++ nil) by (list_simpl; reflexivity).
      refine (IHsize _ _ _ _ Hl2 Hone _ eq_refl). lia.
    * eapply ex_wn_r; [ | apply HP ].
      revert Hl2 IHsize. cbn. change bot with (@dual atom one). intros Hl2 IHsize.
      revert Hone IHsize. rewrite <- (app_nil_l (one :: _)). intros Hone IHsize.
      replace (l ++ map wn lw ++ l2)
         with (nil ++ (l ++ map wn lw ++ l2) ++ nil) by (list_simpl; reflexivity).
      refine (IHsize _ _ _ _ Hl2 Hone _ eq_refl). lia.
  + (* mix_r *)
    change (bot :: l0) with (nil ++ bot :: l0) in H0.
    apply concat_eq_elt in H0 as [(((L1, L2), l1'), l2') [Heqb ->] ->].
    symmetry in Heqb. apply app_eq_nil in Heqb as [Heqb1 Heqb2].
    change (l2' ++ concat L2) with ((nil ++ l2') ++ concat L2).
    rewrite <- Heqb2.
    change ((l1' ++ l2') ++ concat L2) with (nil ++ (l1' ++ l2') ++ concat L2).
    rewrite <- Heqb1.
    change ((l1' ++ l2') ++ concat L2) with (concat ((l1' ++ l2') :: L2)).
    rewrite <- concat_app.
    apply mix_r.
    * clear IHsize.
      rewrite length_app; rewrite length_app in f; apply f.
    * assert (FL1 := Forall_inf_app_l _ _ Hax).
      assert (FL2 := Forall_inf_app_r _ _ Hax).
      inversion FL2; subst; clear FL2; rename X0 into FL2; rename X into pi.
      apply Forall_inf_app; [ assumption | ].
      apply Forall_inf_cons; [ | assumption ].
      clear pi.
      change one with (@dual atom bot) in Hone.
      destruct (In_Forall_inf_elt _ _ (nil ++ bot :: l2') Hax) as [pi Hin].
      change (nil ++ l2') with (nil ++ nil ++ l2').
      refine (IHsize _ _ _ _ Hone pi _ eq_refl).
      apply (psize_inf_mix f) in Hin; cbn; cbn in Hin; lia.
  + (* bot_r *)
    inversion Heql'; subst; assumption.
  + (* cut_r *)
    destruct l2; destr_eq Heql'; subst.
    * cbn in Heql'; subst.
      rewrite <- app_nil_l; apply (cut_r _ f); [ | assumption ].
      change one with (@dual atom bot) in Hone.
      revert Hl2 IHsize; cons2app; intros Hl2 IHsize.
      refine (IHsize _ _ _ _ Hone Hl2 _ eq_refl); cbn; lia.
    * apply (cut_r _ f); [ assumption | ].
      change one with (@dual atom bot) in Hone.
      revert Hr2 IHsize; cons2app; intros Hr2 IHsize.
      refine (IHsize _ _ _ _ Hone Hr2 _ eq_refl); cbn; lia.
  + (* gax_r *)
    specialize (P_gax_cut _ _ nil _ Heql').
    case_eq (pcut P (dual one)); intros Hcut.
    * rewrite <- app_nil_r; apply (cut_r _ Hcut); [ assumption | ].
      rewrite <- Heql'; apply gax_r.
    * exfalso.
      destruct (P_gax_cut Hcut) as [Hat _]; inversion Hat.
- (* bot_r *)
  destruct l1; destr_eq Heql; subst; list_simpl.
  + (* main case *)
    remember (bot_r Hl) as Hbot eqn:Hdel. clear Hdel.
    remember (dual bot :: l0) as l'; destruct_ll pi1 f X l Hl2 Hr2 HP Hax a; try inversion Heql';
      cbn in IHsize.
    * (* ex_r *)
      destruct (PCPermutation_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] HP' Heq];
        cbn in Heq, HP'; subst.
      apply (PEPermutation_Type_app_tail _ _ _ l2) in HP'.
      apply PEPermutation_PCPermutation_Type in HP'; unfold id in HP'; list_simpl in HP'.
      eapply ex_r; [ | symmetry; apply HP' ].
      eapply ex_r; [ | symmetry; apply PCPermutation_Type_app_rot ].
      revert Hbot IHsize; change bot with (@dual atom one); intros Hbot IHsize.
      refine (IHsize _ _ _ _ Hbot Hl2 _ _); cbn; lia.
    * (* ex_wn_r *)
      destruct l; destr_eq Heql'; [ destruct lw'; destr_eq Heql' | ]; subst.
      -- assert (lw = nil)
           by (clear - HP; symmetry in HP; apply (Permutation_Type_nil HP)); subst.
         list_simpl in Heql'. subst. list_simpl in Hl2.
         revert Hl2 IHsize. cbn. change one with (@dual atom bot). intros Hl2 IHsize.
         revert Hbot IHsize. rewrite <- (app_nil_l (bot :: _)). intros Hbot IHsize.
         refine (IHsize _ _ _ _ Hl2 Hbot _ _); cbn; lia.
      -- list_simpl. eapply ex_wn_r; [ | apply HP ]. rewrite 2 app_assoc, <- (app_assoc l).
         revert Hl2 IHsize. cbn. change one with (@dual atom bot). intros Hl2 IHsize.
         revert Hbot IHsize. rewrite <- (app_nil_l (bot :: _)). intros Hbot IHsize.
         refine (IHsize _ _ _ _ Hl2 Hbot _ _); cbn; lia.
    * (* mix_r *)
      change (one :: l0) with (nil ++ one :: l0) in H0.
      apply concat_eq_elt in H0 as [(((L1, L2), l1'), l2') [Heqb ->] ->].
      symmetry in Heqb. apply app_eq_nil in Heqb as [Heqb1 Heqb2].
      apply ex_r with ((l2 ++ l2') ++ concat L2); [ | rewrite <- app_assoc; apply PCPermutation_Type_app_comm ].
      rewrite <- (app_nil_l _), <- Heqb1.
      change ((l2 ++ l2') ++ concat L2) with (concat ((l2 ++ l2') :: L2)).
      rewrite <- concat_app. apply mix_r.
      ++ rewrite length_app. rewrite length_app in f. cbn. cbn in f. assumption.
      ++ assert (FL1 := Forall_inf_app_l _ _ Hax).
         assert (FL2 := Forall_inf_app_r _ _ Hax).
         inversion FL2. subst. clear FL2. rename X0 into FL2. rename X into pi.
         apply Forall_inf_app; [ assumption | apply Forall_inf_cons; [ | assumption ] ].
         clear pi.
         change bot with (@dual atom one) in Hbot.
         destruct (In_Forall_inf_elt _ _ (nil ++ one :: l2') Hax) as [pi Hin%(psize_inf_mix f)].
         rewrite <- (app_nil_l _).
         refine (IHsize _ _ _ _ Hbot pi _ _); cbn; cbn in Hin; lia.
    * (* one_r *)
      assumption.
    * (* cut_r *)
      destruct l3; destr_eq Heql'; subst.
      -- cbn in Heql'. subst.
         eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
         rewrite <- app_nil_l; apply (cut_r _ f); [ | assumption ].
         change bot with (@dual atom one) in Hbot.
         revert Hl2 IHsize; cons2app; intros Hl2 IHsize.
         refine (IHsize _ _ _ _ Hbot Hl2 _ eq_refl); cbn; lia.
      -- list_simpl. eapply ex_r; [ | apply PCPermutation_Type_app_rot ].
         rewrite app_assoc. apply (cut_r _ f); [ assumption | ].
         change bot with (@dual atom one) in Hbot.
         revert Hr2 IHsize. cons2app. intros Hr2 IHsize.
         refine (IHsize _ _ _ _ Hbot Hr2 _ eq_refl); cbn; lia.
    * (* gax_r *)
      specialize (P_gax_cut _ _ nil _ Heql').
      case_eq (pcut P (dual bot)); intros Hcut.
      -- apply (cut_r _ Hcut); [ assumption | ].
         rewrite <- Heql'; apply gax_r.
      -- exfalso.
         destruct (P_gax_cut Hcut) as [Hat _]; inversion Hat.
  + (* commutative case *)
    apply bot_r.
    refine (IHsize _ _ _ _ pi1 Hl _ _); cbn; lia.
- (* tens_r *)
  destruct l1; inversion Heql; subst; list_simpl.
  + (* main case *)
    remember (dual (tens A0 B) :: l0) as l'; destruct_ll pi1 f X l Hl2 Hr2 HP Hax a;
      try inversion Heql'.
    * (* ex_r *)
      remember (tens_r Hl Hr) as Htens eqn:Hdel. clear Hdel.
      destruct (PCPermutation_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] HP' Heq];
        cbn in Heq, HP'; subst.
      apply (PEPermutation_Type_app_tail _ _ _ (l4 ++ l3)) in HP'.
      apply PEPermutation_PCPermutation_Type in HP'; unfold id in HP'; list_simpl in HP'.
      eapply ex_r; [ | symmetry; apply HP' ].
      eapply ex_r; [ | symmetry; apply PCPermutation_Type_app_rot ].
      revert Htens IHsize; cbn;
        replace (tens A0 B) with (dual (parr (dual B) (dual A0)))
          by (cbn; rewrite 2 bidual; reflexivity);
        intros Htens IHsize.
      refine (IHsize _ _ _ _ Htens Hl2 _ _); cbn; rewrite ? fsize_dual; lia.
    * (* ex_wn_r *)
      remember (tens_r Hl Hr) as Htens eqn:Hdel. clear Hdel.
      destruct l; destr_eq Heql'; [ destruct lw'; destr_eq Heql' | ]; subst.
      -- assert (lw = nil)
           by (clear - HP; symmetry in HP; apply (Permutation_Type_nil HP)); subst.
         list_simpl in Heql'; subst; list_simpl in Hl2.
         revert Hl2 IHsize; cbn; change (parr (dual B) (dual A0)) with (dual (tens A0 B));
           intros Hl2 IHsize.
         revert Htens IHsize; rewrite <- (app_nil_l (tens _ _ :: _)); intros Htens IHsize.
         refine (IHsize _ _ _ _ Hl2 Htens _ _); cbn; lia.
      -- list_simpl; eapply ex_wn_r; [ | apply HP ]; rewrite 2 app_assoc, <- (app_assoc l).
         revert Hl2 IHsize; cbn; change (parr (dual B) (dual A0)) with (dual (tens A0 B));
           intros Hl2 IHsize.
         revert Htens IHsize; rewrite <- (app_nil_l (tens _ _ :: _)); intros Htens IHsize.
         refine (IHsize _ _ _ _ Hl2 Htens _ _); cbn; lia.
    * (* mix_r *)
      remember (tens_r Hl Hr) as Htens eqn:Hdel. clear Hdel.
      change (parr (dual B) (dual A0) :: l0) with (nil ++ parr (dual B) (dual A0) :: l0) in H0.
      apply concat_eq_elt in H0 as [(((L1, L2), l1'), l2') [Heqb ->] ->].
      symmetry in Heqb. apply app_eq_nil in Heqb as [Heqb1 Heqb2].
      apply ex_r with (((l4 ++ l3) ++ l2') ++ concat L2).
      2:{ list_simpl. rewrite app_assoc.
          etransitivity; [ apply PCPermutation_Type_app_comm | list_simpl; reflexivity ]. }
      change (((l4 ++ l3) ++ l2') ++ concat L2) with (nil ++ ((l4 ++ l3) ++ l2') ++ concat L2).
      rewrite <- Heqb1.
      change (((l4 ++ l3) ++ l2') ++ concat L2) with (concat (((l4 ++ l3) ++ l2') :: L2)).
      rewrite <- concat_app.
      apply mix_r.
      -- clear IHsize.
         rewrite length_app; rewrite length_app in f; cbn; cbn in f; assumption.
      -- assert (FL1 := Forall_inf_app_l _ _ Hax).
         assert (FL2 := Forall_inf_app_r _ _ Hax).
         inversion FL2; subst; clear FL2; rename X0 into FL2; rename X into pi.
         apply Forall_inf_app; [ assumption |].
         apply Forall_inf_cons; [| assumption ].
         clear pi.
         destruct (In_Forall_inf_elt _ _ (nil ++ (parr (dual B) (dual A0)) :: l2') Hax) as [pi Hin].
         change ((l4 ++ l3) ++ l2') with (nil ++ (l4 ++ l3) ++ l2').
         revert Htens IHsize;
           replace (tens A0 B)
              with (dual (parr (dual B) (dual A0))) by (cbn; rewrite 2 bidual; reflexivity);
           intros Htens IHsize.
         refine (IHsize _ _ _ _ Htens pi _ _).
         ++ apply (psize_inf_mix f) in Hin; cbn; cbn in Hin; lia.
         ++ cbn; rewrite ? fsize_dual; lia.
    * (* parr_r *)
      clear IHsize; subst.
      rewrite <- (app_nil_l (A0 :: _)) in Hl; list_simpl.
      rewrite <- (bidual B) in Hr.
      refine (IHcut _ _ _ _ _ Hr _).
      -- cbn; rewrite fsize_dual; lia.
      -- eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
         list_simpl in Hl; rewrite <- (bidual A0) in Hl.
         change ((dual B :: l3) ++ l0) with ((dual B :: nil) ++ l3 ++ l0).
         refine (IHcut _ _ _ _ _ Hl _); [| assumption ].
         cbn; rewrite fsize_dual; lia.
    * (* cut_r *)
      remember (tens_r Hl Hr) as Htens eqn:Hdel. clear Hdel.
      destruct l2; destr_eq Heql'; subst.
      -- cbn in Heql'; subst.
         eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
         rewrite <- app_nil_l; apply (cut_r _ f); [ | assumption ].
         revert Htens IHsize;
           replace (tens A0 B)
              with (dual (parr (dual B) (dual A0))) by (cbn; rewrite 2 bidual; reflexivity);
           intros Htens IHsize.
         revert Hl2 IHsize; change (dual A :: parr (dual B) (dual A0) :: l0)
                              with ((dual A :: nil) ++ parr (dual B) (dual A0) :: l0);
           intros Hl2 IHsize.
         refine (IHsize _ _ _ _ Htens Hl2 _ _); rewrite ? fsize_dual; cbn; lia.
      -- list_simpl; eapply ex_r; [ | apply PCPermutation_Type_app_comm ]; list_simpl.
         eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
         apply (cut_r _ f); [ assumption | ].
         revert Htens IHsize;
           replace (tens A0 B)
              with (dual (parr (dual B) (dual A0))) by (cbn; rewrite 2 bidual; reflexivity);
           intros Htens IHsize.
         revert Hr2 IHsize; change (A :: parr (dual B) (dual A0) :: l2)
                              with ((A :: nil) ++ parr (dual B) (dual A0) :: l2);
           intros Hr2 IHsize.
         change (A :: l4 ++ l3 ++ l2) with ((A :: nil) ++ l4 ++ l3 ++ l2); rewrite (app_assoc l4).
         refine (IHsize _ _ _ _ Htens Hr2 _ _); rewrite ? fsize_dual; cbn; lia.
    * (* gax_r *)
      specialize (P_gax_cut _ _ nil _ Heql').
      case_eq (pcut P (dual (tens A0 B))); intros Hcut.
      -- apply (cut_r _ Hcut); [ rewrite bidual; constructor; assumption | ].
         rewrite <- Heql'; apply gax_r.
      -- exfalso.
         destruct (P_gax_cut Hcut) as [Hat _]; inversion Hat.
  + (* commutative case *)
    decomp_elt_eq_app H1; subst.
    * rewrite 2 app_assoc; apply tens_r; [ assumption |].
      revert Hr IHsize; cbn; rewrite (app_comm_cons _ _ B); intros Hr IHsize.
      rewrite <- app_assoc; refine (IHsize _ _ _ _ pi1 Hr _ _); cbn; lia.
    * list_simpl; apply tens_r; [| assumption ].
      revert Hl IHsize; cbn; rewrite (app_comm_cons _ _ A0); intros Hl IHsize.
      refine (IHsize _ _ _ _ pi1 Hl _ _); cbn; lia.
- (* parr_r *)
  destruct l1; destr_eq Heql; subst; list_simpl.
  + (* main case *)
    remember (dual (parr A0 B) :: l0) as l'; destruct_ll pi1 f X l Hl2 Hr2 HP Hax a;
      try inversion Heql'.
    * (* ex_r *)
      remember (parr_r Hl) as Hparr eqn:Hdel. clear Hdel.
      destruct (PCPermutation_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] HP' Heq];
        cbn in Heq, HP'; subst.
      apply (PEPermutation_Type_app_tail _ _ _ l2) in HP'.
      apply PEPermutation_PCPermutation_Type in HP'; unfold id in HP'; list_simpl in HP'.
      eapply ex_r; [ | symmetry; apply HP' ].
      eapply ex_r; [ | symmetry; apply PCPermutation_Type_app_rot ].
      revert Hparr IHsize. cbn.
      replace (parr A0 B) with (dual (tens (dual B) (dual A0)))
        by (cbn; rewrite 2 bidual; reflexivity).
      intros Hparr IHsize.
      refine (IHsize _ _ _ _ Hparr Hl2 _ _); cbn; rewrite ? fsize_dual; lia.
    * (* ex_wn_r *)
      remember (parr_r Hl) as Hparr eqn:Hdel. clear Hdel.
      destruct l; destr_eq Heql'; [ destruct lw'; destr_eq Heql' | ]; subst.
      -- assert (lw = nil)
           by (clear - HP; symmetry in HP; apply (Permutation_Type_nil HP)); subst.
         list_simpl in Heql'; subst; list_simpl in Hl2.
         revert Hl2 IHsize; cbn; change (tens (dual B) (dual A0)) with (dual (parr A0 B));
           intros Hl2 IHsize.
         revert Hparr IHsize; rewrite <- (app_nil_l (parr _ _ :: _)); intros Hparr IHsize.
         refine (IHsize _ _ _ _ Hl2 Hparr _ _); cbn; lia.
      -- list_simpl; eapply ex_wn_r; [ | apply HP ]; rewrite 2 app_assoc, <- (app_assoc l).
         revert Hl2 IHsize; cbn; change (tens (dual B) (dual A0)) with (dual (parr A0 B));
           intros Hl2 IHsize.
         revert Hparr IHsize; rewrite <- (app_nil_l (parr _ _ :: _)); intros Hparr IHsize.
         refine (IHsize _ _ _ _ Hl2 Hparr _ _); cbn; lia.
    * (* mix_r *)
      remember (parr_r Hl) as Hparr eqn:Hdel. clear Hdel.
      change (tens (dual B) (dual A0) :: l0) with (nil ++ tens (dual B) (dual A0) :: l0) in H0.
      apply concat_eq_elt in H0 as [(((L1, L2), l1'), l2') [Heqb ->] ->].
      symmetry in Heqb. apply app_eq_nil in Heqb as [Heqb1 Heqb2].
      apply ex_r with ((l2 ++ l2') ++ concat L2); [ | rewrite <- app_assoc; apply PCPermutation_Type_app_comm ].
      change ((l2 ++ l2') ++ concat L2) with (nil ++ (l2 ++ l2') ++ concat L2).
      rewrite <- Heqb1.
      change ((l2 ++ l2') ++ concat L2) with (concat ((l2 ++ l2') :: L2)).
      rewrite <- concat_app.
      apply mix_r.
      -- clear IHsize.
         rewrite length_app; rewrite length_app in f; cbn; cbn in f; assumption.
      -- assert (FL1 := Forall_inf_app_l _ _ Hax).
         assert (FL2 := Forall_inf_app_r _ _ Hax).
         inversion FL2; subst; clear FL2; rename X0 into FL2; rename X into pi.
         apply Forall_inf_app; [ assumption |].
         apply Forall_inf_cons; [| assumption ].
         clear pi.
         destruct (In_Forall_inf_elt _ _ (nil ++ (tens (dual B) (dual A0)) :: l2') Hax) as [pi Hin].
         change (l2 ++ l2') with (nil ++ l2 ++ l2').
         revert Hparr IHsize;
           replace (parr A0 B)
              with (dual (tens (dual B) (dual A0))) by (cbn; rewrite 2 bidual; reflexivity);
           intros Hparr IHsize.
         apply (psize_inf_mix f) in Hin.
         refine (IHsize _ _ _ _ Hparr pi _ _); cbn in Hin; cbn; rewrite ? fsize_dual; lia.
    * (* tens_r *)
      clear IHsize; subst.
      rewrite <- (app_nil_l (A0 :: _)) in Hl; list_simpl.
      refine (IHcut _ _ _ _ _ Hl2 _); [ cbn; lia |].
      rewrite <- (app_nil_l _); refine (IHcut _ _ _ _ _ Hr2 Hl); cbn; lia.
    * (* cut_r *)
      remember (parr_r Hl) as Hparr eqn:Hdel. clear Hdel.
      destruct l3; destr_eq Heql'; subst.
      -- cbn in Heql'; subst.
         eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
         rewrite <- app_nil_l; apply (cut_r _ f); [ | assumption ].
         revert Hparr IHsize;
           replace (parr A0 B) with (dual (tens (dual B) (dual A0))) by (now cbn; rewrite ? bidual);
           intros Hparr IHsize.
         revert Hl2 IHsize;
           change (dual A :: tens (dual B) (dual A0) :: l0)
             with ((dual A :: nil) ++ tens (dual B) (dual A0) :: l0);
           intros Hl2 IHsize.
         refine (IHsize _ _ _ _ Hparr Hl2 _ _); rewrite ? fsize_dual; cbn; lia.
      -- list_simpl; eapply ex_r; [ | apply PCPermutation_Type_app_rot ].
         rewrite app_assoc; apply (cut_r _ f); [ assumption | ].
         revert Hparr IHsize;
           replace (parr A0 B) with (dual (tens (dual B) (dual A0))) by (now cbn; rewrite ? bidual);
           intros Hparr IHsize.
         revert Hr2 IHsize;
           change (A :: tens (dual B) (dual A0) :: l3) with ((A :: nil) ++ tens (dual B) (dual A0) :: l3);
           intros Hr2 IHsize.
         refine (IHsize _ _ _ _ Hparr Hr2 _ _); rewrite ? fsize_dual; cbn; lia.
    * (* gax_r *)
      specialize (P_gax_cut _ _ nil _ Heql').
      case_eq (pcut P (dual (parr A0 B))); intros Hcut.
      -- apply (cut_r _ Hcut); [ rewrite bidual; constructor; assumption | ].
         rewrite <- Heql'; apply gax_r.
      -- exfalso.
         destruct (P_gax_cut Hcut) as [Hat _]; inversion Hat.
  + (* commutative case *)
    apply parr_r.
    revert Hl IHsize. cbn. rewrite (app_comm_cons l1 _ B), (app_comm_cons _ _ A0). intros Hl IHsize.
    refine (IHsize _ _ _ _ pi1 Hl _ _); cbn; lia.
- (* top_r *)
  destruct l1; destr_eq Heql; subst; list_simpl.
  + (* main case *)
    remember (dual top :: l0) as l' eqn:Heql'. destruct_ll pi1 f X l Hl2 Hr2 HP Hax a; try inversion Heql'.
    * (* ex_r *)
      remember (top_r l2) as Htop eqn:Hdel. clear Hdel.
      destruct (PCPermutation_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] HP' Heq];
        cbn in Heq, HP'; subst.
      apply (PEPermutation_Type_app_tail _ _ _ l2) in HP'.
      apply PEPermutation_PCPermutation_Type in HP'. unfold id in HP'. list_simpl in HP'.
      eapply ex_r; [ | symmetry; apply HP' ].
      eapply ex_r; [ | symmetry; apply PCPermutation_Type_app_rot ].
      revert Htop IHsize. cbn. change top with (@dual atom zero). intros Hplus IHsize.
      refine (IHsize _ _ _ _ Hplus Hl2 _ _); cbn; lia.
    * (* ex_wn_r *)
      remember (top_r l2) as Htop eqn:Hdel. clear Hdel.
      destruct l; destr_eq Heql'; [ destruct lw'; destr_eq Heql' | ]; subst.
      -- assert (lw = nil)
           by (clear - HP; symmetry in HP; apply (Permutation_Type_nil HP)); subst.
         list_simpl in Heql'. subst. list_simpl in Hl2.
         revert Hl2 IHsize. cbn. change zero with (@dual atom top). intros Hl2 IHsize.
         revert Htop IHsize. rewrite <- (app_nil_l (top :: _)). intros Htop IHsize.
         refine (IHsize _ _ _ _ Hl2 Htop _ _); cbn; lia.
      -- list_simpl; eapply ex_wn_r; [ | apply HP ]; rewrite 2 app_assoc, <- (app_assoc l).
         revert Hl2 IHsize. cbn. change zero with (@dual atom top). intros Hl2 IHsize.
         revert Htop IHsize. rewrite <- (app_nil_l (top :: _)). intros Htop IHsize.
         refine (IHsize _ _ _ _ Hl2 Htop _ _); cbn; lia.
    * (* mix_r *)
      remember (top_r l2 ) as Htop eqn:Hdel. clear Hdel.
      change (zero :: l0) with (nil ++ zero :: l0) in H0.
      apply concat_eq_elt in H0 as [(((L1, L2), l1'), l2') [Heqb ->] ->].
      symmetry in Heqb. apply app_eq_nil in Heqb as [Heqb1 Heqb2].
      apply ex_r with ((l2 ++ l2') ++ concat L2); [ | list_simpl; apply PCPermutation_Type_app_rot ].
      rewrite <- (app_nil_l _), <- Heqb1.
      change ((l2 ++ l2') ++ concat L2) with (concat ((l2 ++ l2') :: L2)).
      rewrite <- concat_app.
      apply mix_r.
      -- clear IHsize.
         rewrite length_app; rewrite length_app in f; cbn; cbn in f; assumption.
      -- assert (FL1 := Forall_inf_app_l _ _ Hax).
         assert (FL2 := Forall_inf_app_r _ _ Hax).
         inversion FL2; subst; clear FL2; rename X0 into FL2; rename X into pi.
         apply Forall_inf_app; [ assumption |].
         apply Forall_inf_cons; [| assumption ].
         clear pi.
         destruct (In_Forall_inf_elt _ _ (nil ++ (zero) :: l2') Hax) as [pi Hin].
         rewrite <- (app_nil_l _).
         change top with (@dual atom zero) in Htop.
         apply (psize_inf_mix f) in Hin.
         refine (IHsize _ _ _ _ Htop pi _ _); cbn; cbn in Hin; lia.
    * (* cut_r *)
      destruct l3; destr_eq Heql'; subst.
      -- cbn in Heql'; subst.
         eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
         rewrite <- app_nil_l; apply (cut_r _ f); [ | assumption ].
         revert Hl2 IHsize;
           change (dual A :: zero :: l0) with ((dual A :: nil) ++ zero :: l0);
           intros Hl2 IHsize.
         refine (IHsize zero _ _ _  (top_r l2) Hl2 _ _); cbn; lia.
      -- list_simpl; eapply ex_r; [ | apply PCPermutation_Type_app_rot ].
         rewrite app_assoc; apply (cut_r _ f); [ assumption | ].
         revert Hr2 IHsize;
           change (A :: zero :: l3) with ((A :: nil) ++ zero :: l3);
           intros Hr2 IHsize.
         refine (IHsize zero _ _ _ (top_r l2) Hr2 _ _); cbn; lia.
    * (* gax_r *)
      specialize (P_gax_cut _ _ nil _ Heql').
      case_eq (pcut P (dual top)); intros Hcut.
      -- apply (cut_r _ Hcut); [ rewrite bidual; constructor; assumption | ].
         rewrite <- Heql'; apply gax_r.
      -- exfalso.
         destruct (P_gax_cut Hcut) as [Hat _]; inversion Hat.
  + (* commutative case *)
    apply top_r.
- (* plus_r1 *)
  destruct l1; destr_eq Heql; subst; list_simpl.
  + (* main case *)
    remember (dual (aplus A0 B) :: l0) as l'; destruct_ll pi1 f X l Hl2 Hr2 HP Hax a;
      try inversion Heql'.
    * (* ex_r *)
      remember (plus_r1 _ Hl) as Hplus eqn:Hdel. clear Hdel.
      destruct (PCPermutation_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] HP' Heq];
        cbn in Heq, HP'; subst.
      apply (PEPermutation_Type_app_tail _ _ _ l2) in HP'.
      apply PEPermutation_PCPermutation_Type in HP'; unfold id in HP'; list_simpl in HP'.
      eapply ex_r; [ | symmetry; apply HP' ].
      eapply ex_r; [ | symmetry; apply PCPermutation_Type_app_rot ].
      revert Hplus IHsize; cbn;
        replace (aplus A0 B) with (dual (awith (dual A0) (dual B)))
          by (cbn; rewrite 2 bidual; reflexivity);
        intros Hplus IHsize.
      refine (IHsize _ _ _ _ Hplus Hl2 _ _); cbn; rewrite ? fsize_dual; lia.
    * (* ex_wn_r *)
      remember (plus_r1 _ Hl) as Hplus eqn:Hdel. clear Hdel.
      destruct l; destr_eq Heql'; [ destruct lw'; destr_eq Heql' | ]; subst.
      -- assert (lw = nil)
           by (clear - HP; symmetry in HP; apply (Permutation_Type_nil HP)); subst.
         list_simpl in Heql'; subst; list_simpl in Hl2.
         revert Hl2 IHsize; cbn; change (awith (dual A0) (dual B)) with (dual (aplus A0 B));
           intros Hl2 IHsize.
         revert Hplus IHsize; rewrite <- (app_nil_l (aplus _ _ :: _)); intros Hplus IHsize.
         refine (IHsize _ _ _ _ Hl2 Hplus _ _); cbn; lia.
      -- list_simpl; eapply ex_wn_r; [ | apply HP ]; rewrite 2 app_assoc, <- (app_assoc l).
         revert Hl2 IHsize; cbn; change (awith (dual A0) (dual B)) with (dual (aplus A0 B));
           intros Hl2 IHsize.
         revert Hplus IHsize; rewrite <- (app_nil_l (aplus _ _ :: _)); intros Hplus IHsize.
         refine (IHsize _ _ _ _ Hl2 Hplus _ _); cbn; lia.
    * (* mix_r *)
      remember (plus_r1 _ Hl) as Hplus eqn:Hdel. clear Hdel.
      change (awith (dual A0) (dual B) :: l0) with (nil ++ awith (dual A0) (dual B) :: l0) in H0.
      apply concat_eq_elt in H0 as [(((L1, L2), l1'), l2') [Heqb ->] ->].
      symmetry in Heqb. apply app_eq_nil in Heqb as [Heqb ->].
      apply ex_r with ((l2 ++ l2') ++ concat L2); [ | rewrite <- app_assoc; apply PCPermutation_Type_app_comm ].
      rewrite <- (app_nil_l _), <- Heqb.
      change ((l2 ++ l2') ++ concat L2) with (concat ((l2 ++ l2') :: L2)).
      rewrite <- concat_app.
      apply mix_r.
      -- clear IHsize.
         rewrite length_app; rewrite length_app in f; cbn; cbn in f; assumption.
      -- assert (FL1 := Forall_inf_app_l _ _ Hax).
         assert (FL2 := Forall_inf_app_r _ _ Hax).
         inversion FL2; subst; clear FL2; rename X0 into FL2; rename X into pi.
         apply Forall_inf_app; [ assumption |].
         apply Forall_inf_cons; [| assumption ].
         clear pi.
         destruct (In_Forall_inf_elt _ _ (nil ++ (awith (dual A0) (dual B)) :: l2') Hax) as [pi Hin].
         change (l2 ++ l2') with (nil ++ l2 ++ l2').
         revert Hplus IHsize; 
           replace (aplus A0 B)
              with (dual (awith (dual A0) (dual B))) by (cbn; rewrite 2 bidual; reflexivity);
           intros Hplus IHsize.
         apply (psize_inf_mix f) in Hin.
         refine (IHsize _ _ _ _ Hplus pi _ _); cbn; cbn in Hin; rewrite ? fsize_dual; lia.
    * (* with_r *)
      clear IHsize; subst.
      rewrite <- (app_nil_l (A0 :: _)) in Hl; refine (IHcut _ _ _ _ _ Hl2 Hl); cbn; lia.
    * (* cut_r *)
      remember (plus_r1 B Hl) as Hplus eqn:Hdel. clear Hdel.
      destruct l3; destr_eq Heql'; subst.
      -- cbn in Heql'; subst.
         eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
         rewrite <- app_nil_l; apply (cut_r _ f); [ | assumption ].
         revert Hplus IHsize;
           replace (aplus A0 B) with (dual (awith (dual A0) (dual B))) by (now cbn; rewrite ? bidual);
           intros Hplus IHsize.
         revert Hl2 IHsize;
           change (dual A :: awith (dual A0) (dual B) :: l0)
             with ((dual A :: nil) ++ awith (dual A0) (dual B) :: l0);
           intros Hl2 IHsize.
         refine (IHsize _ _ _ _ Hplus Hl2 _ _); rewrite ? fsize_dual; cbn; lia.
      -- list_simpl; eapply ex_r; [ | apply PCPermutation_Type_app_rot ].
         rewrite app_assoc; apply (cut_r _ f); [ assumption | ].
         revert Hplus IHsize;
           replace (aplus A0 B) with (dual (awith (dual A0) (dual B))) by (now cbn; rewrite ? bidual);
           intros Hplus IHsize.
         revert Hr2 IHsize;
           change (A :: awith (dual A0) (dual B) :: l3) with ((A :: nil) ++ awith (dual A0) (dual B) :: l3);
           intros Hr2 IHsize.
         refine (IHsize _ _ _ _ Hplus Hr2 _ _); rewrite ? fsize_dual; cbn; lia.
    * (* gax_r *)
      specialize (P_gax_cut _ _ nil _ Heql').
      case_eq (pcut P (dual (aplus A0 B))); intros Hcut.
      -- apply (cut_r _ Hcut); [ rewrite bidual; constructor; assumption | ].
         rewrite <- Heql'; apply gax_r.
      -- exfalso.
         destruct (P_gax_cut Hcut) as [Hat _]; inversion Hat.
  + (* commutative case *)
    apply plus_r1.
    revert Hl IHsize; cbn; rewrite (app_comm_cons l1 _ A0); intros Hl IHsize.
    refine (IHsize _ _ _ _ pi1 Hl _ _); cbn; lia.
- (* plus_r2 *)
  destruct l1; destr_eq Heql; subst; list_simpl.
  + (* main case *)
    remember (dual (aplus B A0) :: l0) as l'; destruct_ll pi1 f X l Hl2 Hr2 HP Hax a;
      try inversion Heql'.
    * (* ex_r *)
      remember (plus_r2 _ Hl) as Hplus eqn:Hdel. clear Hdel.
      destruct (PCPermutation_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] HP' Heq];
        cbn in Heq, HP'; subst.
      apply (PEPermutation_Type_app_tail _ _ _ l2) in HP'.
      apply PEPermutation_PCPermutation_Type in HP'; unfold id in HP'; list_simpl in HP'.
      eapply ex_r; [ | symmetry; apply HP' ].
      eapply ex_r; [ | symmetry; apply PCPermutation_Type_app_rot ].
      revert Hplus IHsize. cbn.
      replace (aplus B A0) with (dual (awith (dual B) (dual A0)))
        by (cbn; rewrite 2 bidual; reflexivity).
      intros Hplus IHsize.
      refine (IHsize _ _ _ _ Hplus Hl2 _ _); cbn; rewrite ? fsize_dual; lia.
    * (* ex_wn_r *)
      remember (plus_r2 _ Hl) as Hplus eqn:Hdel. clear Hdel.
      destruct l; destr_eq Heql'; [ destruct lw'; destr_eq Heql' | ]; subst.
      -- assert (lw = nil)
           by (clear - HP; symmetry in HP; apply (Permutation_Type_nil HP)); subst.
         list_simpl in Heql'. subst. list_simpl in Hl2.
         revert Hl2 IHsize. cbn. change (awith (dual B) (dual A0)) with (dual (aplus B A0)). intros Hl2 IHsize.
         revert Hplus IHsize. rewrite <- (app_nil_l (aplus _ _ :: _)). intros Hplus IHsize.
         refine (IHsize _ _ _ _ Hl2 Hplus _ _); cbn; lia.
      -- list_simpl. eapply ex_wn_r; [ | apply HP ]; rewrite 2 app_assoc, <- (app_assoc l).
         revert Hl2 IHsize. cbn. change (awith (dual B) (dual A0)) with (dual (aplus B A0)). intros Hl2 IHsize.
         revert Hplus IHsize. rewrite <- (app_nil_l (aplus _ _ :: _)). intros Hplus IHsize.
         refine (IHsize _ _ _ _ Hl2 Hplus _ _); cbn; lia.
    * (* mix_r *)
      remember (plus_r2 _ Hl) as Hplus eqn:Hdel. clear Hdel.
      change (awith (dual B) (dual A0) :: l0) with (nil ++ awith (dual B) (dual A0) :: l0) in H0.
      apply concat_eq_elt in H0 as [(((L1, L2), l1'), l2') [Heqb ->] ->].
      symmetry in Heqb. apply app_eq_nil in Heqb as [Heqb1 Heqb2].
      apply ex_r with ((l2 ++ l2') ++ concat L2); [ | rewrite <- app_assoc; apply PCPermutation_Type_app_comm ].
      rewrite <- (app_nil_l _), <- Heqb1.
      change ((l2 ++ l2') ++ concat L2) with (concat ((l2 ++ l2') :: L2)).
      rewrite <- concat_app. apply mix_r.
      -- clear IHsize. rewrite length_app. rewrite length_app in f. cbn. cbn in f. assumption.
      -- assert (FL1 := Forall_inf_app_l _ _ Hax).
         assert (FL2 := Forall_inf_app_r _ _ Hax).
         inversion FL2; subst; clear FL2; rename X0 into FL2; rename X into pi.
         apply Forall_inf_app; [ assumption |].
         apply Forall_inf_cons; [| assumption ].
         clear pi.
         destruct (In_Forall_inf_elt _ _ (nil ++ (awith (dual B) (dual A0)) :: l2') Hax) as [pi Hin].
         change (l2 ++ l2') with (nil ++ l2 ++ l2').
         revert Hplus IHsize.
         replace (aplus B A0)
           with (dual (awith (dual B) (dual A0))) by (cbn; rewrite 2 bidual; reflexivity).
         intros Hplus IHsize.
         apply (psize_inf_mix f) in Hin.
         refine (IHsize _ _ _ _ Hplus pi _ _); cbn; cbn in Hin; rewrite ? fsize_dual; lia.
    * (* with_r *)
      clear IHsize; subst.
      rewrite <- (app_nil_l (A0 :: _)) in Hl; refine (IHcut _ _ _ _ _ Hr2 Hl); cbn; lia.
    * (* cut_r *)
      remember (plus_r2 B Hl) as Hplus eqn:Hdel. clear Hdel.
      destruct l3; destr_eq Heql'; subst.
      -- cbn in Heql'; subst.
         eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
         rewrite <- app_nil_l; apply (cut_r _ f); [ | assumption ].
         revert Hplus IHsize;
           replace (aplus B A0) with (dual (awith (dual B) (dual A0))) by (now cbn; rewrite ? bidual);
           intros Hplus IHsize.
         revert Hl2 IHsize;
           change (dual A :: awith (dual B) (dual A0) :: l0)
             with ((dual A :: nil) ++ awith (dual B) (dual A0) :: l0);
           intros Hl2 IHsize.
         refine (IHsize _ _ _ _ Hplus Hl2 _ _); rewrite ? fsize_dual; cbn; lia.
      -- list_simpl; eapply ex_r; [ | apply PCPermutation_Type_app_rot ].
         rewrite app_assoc; apply (cut_r _ f); [ assumption | ].
         revert Hplus IHsize;
           replace (aplus B A0) with (dual (awith (dual B) (dual A0))) by (now cbn; rewrite ? bidual);
           intros Hplus IHsize.
         revert Hr2 IHsize;
           change (A :: awith (dual B) (dual A0) :: l3) with ((A :: nil) ++ awith (dual B) (dual A0) :: l3);
           intros Hr2 IHsize.
         refine (IHsize _ _ _ _ Hplus Hr2 _ _); rewrite ? fsize_dual; cbn; lia.
    * (* gax_r *)
      specialize (P_gax_cut _ _ nil _ Heql').
      case_eq (pcut P (dual (aplus B A0))); intros Hcut.
      -- apply (cut_r _ Hcut); [ rewrite bidual; constructor; assumption | ].
         rewrite <- Heql'; apply gax_r.
      -- exfalso.
         destruct (P_gax_cut Hcut) as [Hat _]; inversion Hat.
  + (* commutative case *)
    apply plus_r2.
    revert Hl IHsize; cbn; rewrite (app_comm_cons l1 _ A0); intros Hl IHsize.
    refine (IHsize _ _ _ _ pi1 Hl _ _); cbn; lia.
- (* with_r *)
  destruct l1; injection Heql as [= <- ->]; list_simpl.
  + (* main case *)
    remember (dual (awith A0 B) :: l0) as l' eqn:Heql'.
    destruct_ll pi1 f X l Hl2 Hr2 HP Hax a; try inversion Heql'.
    * (* ex_r *)
      remember (with_r Hl Hr) as Hwith eqn:Hdel. clear Hdel.
      destruct (PCPermutation_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] HP' ->].
      apply (PEPermutation_Type_app_tail _ _ _ l2) in HP'.
      apply PEPermutation_PCPermutation_Type in HP'. unfold id in HP'. list_simpl in HP'.
      eapply ex_r; [ | symmetry; apply HP' ].
      eapply ex_r; [ | symmetry; apply PCPermutation_Type_app_rot ].
      revert Hwith IHsize. cbn.
      replace (awith A0 B) with (dual (aplus (dual A0) (dual B))) by (cbn; rewrite 2 bidual; reflexivity).
      intros Hwith IHsize.
      refine (IHsize _ _ _ _ Hwith Hl2 _ _); [ | cbn; rewrite ! fsize_dual]; lia.
    * (* ex_wn_r *)
      remember (with_r Hl Hr) as Hwith eqn:Hdel. clear Hdel.
      destruct l; destr_eq Heql'; [ destruct lw'; destr_eq Heql' | ]; subst.
      -- assert (lw = nil) as ->
           by (clear - HP; symmetry in HP; apply (Permutation_Type_nil HP)).
         list_simpl in Heql'. subst. list_simpl in Hl2.
         revert Hl2 IHsize. cbn. change (aplus (dual A0) (dual B)) with (dual (awith A0 B)). intros Hl2.
         revert Hwith. rewrite <- (app_nil_l (awith _ _ :: _)). intros Hwith IHsize.
         refine (IHsize _ _ _ _ Hl2 Hwith _ _); [ | cbn ]; lia.
      -- list_simpl. eapply ex_wn_r; [ | apply HP ]; rewrite 2 app_assoc, <- (app_assoc l).
         revert Hl2 IHsize. cbn. change (aplus (dual A0) (dual B)) with (dual (awith A0 B)). intros Hl2.
         revert Hwith. rewrite <- (app_nil_l (awith _ _ :: _)). intros Hwith IHsize.
         refine (IHsize _ _ _ _ Hl2 Hwith _ _); [ | cbn ]; lia.
    * (* mix_r *)
      remember (with_r Hl) as Hwith eqn:Hdel. clear Hdel.
      rewrite <- (app_nil_l (aplus _ _ :: _)) in H0.
      apply concat_eq_elt in H0 as [(((L1, L2), l1'), l2') [Heqb ->] ->].
      symmetry in Heqb. apply app_eq_nil in Heqb as [Heqb ->].
      apply ex_r with ((l2 ++ l2') ++ concat L2); [ | list_simpl; apply PCPermutation_Type_app_rot ].
      change ((l2 ++ l2') ++ concat L2) with (nil ++ (l2 ++ l2') ++ concat L2).
      rewrite <- Heqb.
      change ((l2 ++ l2') ++ concat L2) with (concat ((l2 ++ l2') :: L2)).
      rewrite <- concat_app.
      apply mix_r.
      -- clear IHsize. rewrite length_app. rewrite length_app in f. cbn. cbn in f. assumption.
      -- assert (FL1 := Forall_inf_app_l _ _ Hax).
         assert (FL2 := Forall_inf_app_r _ _ Hax).
         inversion FL2; subst. clear FL2. rename X0 into FL2. rename X into pi.
         apply Forall_inf_app; [ assumption | ].
         apply Forall_inf_cons; [ | assumption ].
         clear pi.
         destruct (In_Forall_inf_elt _ _ (nil ++ (aplus (dual A0) (dual B)) :: l2') Hax) as [pi Hin].
         change (l2 ++ l2') with (nil ++ l2 ++ l2').
         revert Hwith IHsize.
         replace (awith A0 B) with (dual (aplus (dual A0) (dual B))) by (cbn; rewrite 2 bidual; reflexivity).
         intros Hwith IHsize.
         apply (psize_inf_mix f) in Hin. cbn in Hin.
         refine (IHsize _ _ _ _ (Hwith Hr) pi _ _); cbn; rewrite ? fsize_dual; lia.
    * (* plus_r1 *)
      clear IHsize. subst.
      rewrite <- (app_nil_l (A0 :: _)) in Hl. refine (IHcut _ _ _ _ _ Hl2 Hl). cbn. lia.
    * (* plus_r2 *)
      clear IHsize. subst.
      rewrite <- (app_nil_l (B :: _)) in Hr. refine (IHcut _ _ _ _ _ Hl2 Hr). cbn. lia.
    * (* cut_r *)
      remember (with_r Hl Hr) as Hwith eqn:Hdel. clear Hdel.
      destruct l3; destr_eq Heql'; subst.
      -- cbn in Heql'; subst.
         eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
         rewrite <- app_nil_l; apply (cut_r _ f); [ | assumption ].
         revert Hwith IHsize;
           replace (awith A0 B) with (dual (aplus (dual A0) (dual B))) by (now cbn; rewrite ? bidual);
           intros Hwith IHsize.
         revert Hl2 IHsize;
           change (dual A :: aplus (dual A0) (dual B) :: l0)
             with ((dual A :: nil) ++ aplus (dual A0) (dual B) :: l0);
           intros Hl2 IHsize.
         refine (IHsize _ _ _ _ Hwith Hl2 _ _); rewrite ? fsize_dual; cbn; lia.
      -- list_simpl; eapply ex_r; [ | apply PCPermutation_Type_app_rot ].
         rewrite app_assoc; apply (cut_r _ f); [ assumption | ].
         revert Hwith IHsize;
           replace (awith A0 B) with (dual (aplus (dual A0) (dual B))) by (now cbn; rewrite ? bidual);
           intros Hwith IHsize.
         revert Hr2 IHsize;
           change (A :: aplus (dual A0) (dual B) :: l3) with ((A :: nil) ++ aplus (dual A0) (dual B) :: l3);
           intros Hr2 IHsize.
         refine (IHsize _ _ _ _ Hwith Hr2 _ _); rewrite ? fsize_dual; cbn; lia.
    * (* gax_r *)
      specialize (P_gax_cut _ _ nil _ Heql').
      case_eq (pcut P (dual (awith A0 B))); intros Hcut.
      -- apply (cut_r _ Hcut); [ rewrite bidual; constructor; assumption | ].
         rewrite <- Heql'; apply gax_r.
      -- exfalso.
         destruct (P_gax_cut Hcut) as [Hat _]; inversion Hat.
  + (* commutative case *)
    apply with_r.
    * revert Hl IHsize. cbn. rewrite (app_comm_cons l1 _ A0). intros Hl IHsize.
      refine (IHsize _ _ _ _ pi1 Hl _ _); cbn; lia.
    * revert Hr IHsize. cbn. rewrite (app_comm_cons l1 _ B). intros Hr IHsize.
      refine (IHsize _ _ _ _ pi1 Hr _ _); cbn; lia.
- (* oc_r *)
  destruct l1; inversion Heql; subst; list_simpl.
  + (* main case *)
    remember (dual (oc A0) :: l0) as l'; destruct_ll pi1 f X lo Hl2 Hr2 HP Hax a;
      try inversion Heql'.
    * (* ex_r *)
      remember (oc_r Hl) as Hoc eqn:Hdel. clear Hdel.
      destruct (PCPermutation_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] HP' Heq];
        cbn in Heq, HP'; subst.
      apply (PEPermutation_Type_app_tail _ _ _ (map wn l)) in HP'.
      apply PEPermutation_PCPermutation_Type in HP'; unfold id in HP'; list_simpl in HP'.
      eapply ex_r; [ | symmetry; apply HP' ].
      eapply ex_r; [ | symmetry; apply PCPermutation_Type_app_rot ].
      revert Hoc IHsize; cbn;
        replace (oc A0) with (dual (wn (dual A0))) by (cbn; rewrite bidual; reflexivity);
        intros Hoc IHsize.
      refine (IHsize _ _ _ _ Hoc Hl2 _ _); cbn; rewrite ? fsize_dual; lia.
    * (* ex_wn_r *)
      remember (oc_r Hl) as Hoc eqn:Hdel. clear Hdel.
      destruct lo; destr_eq H0; [ destruct lw'; destr_eq H0 | ]; subst.
      -- assert (lw = nil) by (clear - HP; symmetry in HP; apply (Permutation_Type_nil HP)); subst.
         list_simpl in Heql'; subst; list_simpl in Hl2.
         revert Hl2 IHsize; cbn; change (wn (dual A0)) with (dual (oc A0)); intros Hl2 IHsize.
         revert Hoc IHsize; rewrite <- (app_nil_l (oc _ :: _)); intros Hoc IHsize.
         refine (IHsize _ _ _ _ Hl2 Hoc _ _); cbn; lia.
      -- destruct (Permutation_Type_vs_cons_inv HP) as [[lw1 lw2] Heq]; cbn in Heq; subst.
         assert (Permutation_Type (lw1 ++ l ++ lw2) (l ++ lw')) as HP'.
         { rewrite <- (app_nil_l (l ++ lw')).
           apply Permutation_Type_app_middle.
           rewrite <- (app_nil_l lw').
           apply (Permutation_Type_app_inv _ _ _ _ (dual A0)); assumption. }
         eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
         rewrite app_assoc, <- map_app, <- (app_nil_l _); eapply ex_wn_r; [ | apply HP' ].
         list_simpl.
         revert Hl2 IHsize; list_simpl; intros Hl2 IHsize.
         revert Hoc IHsize; replace (oc A0) with (dual (wn (dual A0)))
                               by (list_simpl; rewrite bidual; reflexivity); intros Hoc IHsize.
         refine (IHsize _ _ _ _ Hoc Hl2 _ _); cbn; rewrite ? fsize_dual; lia.
      -- list_simpl; eapply ex_wn_r; [ | apply HP ]; rewrite 2 app_assoc, <- (app_assoc lo).
         revert Hl2 IHsize; cbn; change (wn (dual A0)) with (dual (oc A0)); intros Hl2 IHsize.
         revert Hoc IHsize; rewrite <- (app_nil_l (oc _ :: _)); intros Hoc IHsize.
         refine (IHsize _ _ _ _ Hl2 Hoc _ _); cbn; lia.
    * (* mix_r *)
      remember (oc_r Hl) as Hoc eqn:Hdel. clear Hdel.
      change (wn (dual A0) :: l0) with (nil ++ wn (dual A0) :: l0) in H0.
      apply concat_eq_elt in H0 as [(((L1, L2), l1'), l2') [Heqb ->] ->].
      symmetry in Heqb. apply app_eq_nil in Heqb as [Heqb1 Heqb2].
      apply ex_r with ((map wn l ++ l2') ++ concat L2);
        [ | rewrite <- app_assoc; apply PCPermutation_Type_app_comm ].
      change ((map wn l ++ l2') ++ concat L2) with (nil ++ (map wn l ++ l2') ++ concat L2).
      rewrite <- Heqb1.
      change ((map wn l ++ l2') ++ concat L2) with (concat ((map wn l ++ l2') :: L2)).
      rewrite <- concat_app.
      apply mix_r.
      -- clear IHsize.
         rewrite length_app; rewrite length_app in f; cbn; cbn in f; assumption.
      -- assert (FL1 := Forall_inf_app_l _ _ Hax).
         assert (FL2 := Forall_inf_app_r _ _ Hax).
         inversion FL2; subst; clear FL2; rename X0 into FL2; rename X into pi.
         apply Forall_inf_app; [ assumption |].
         apply Forall_inf_cons; [| assumption ].
         clear pi.
         destruct (In_Forall_inf_elt _ _ (nil ++ (wn (dual A0)) :: l2') Hax) as [pi Hin].
         rewrite <- (app_nil_l _).
         revert Hoc IHsize;
           replace (oc A0) with (dual (wn (dual A0))) by (cbn; rewrite bidual; reflexivity);
           intros Hparr IHsize.
         apply (psize_inf_mix f) in Hin.
         refine (IHsize _ _ _ _ Hparr pi _ _); cbn; cbn in Hin; rewrite ? fsize_dual; lia.
    * (* oc_r *)
      clear IHsize; subst.
      rewrite <- (app_nil_l (A0 :: _)) in Hl; refine (IHcut _ _ _ _ _ Hl2 Hl); cbn; lia.
    * (* wk_r *)
      clear IHsize; subst.
      eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
      apply wk_list_r; assumption.
    * (* co_r *)
      clear IHsize; subst.
      eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
      apply co_list_r.
      replace (map wn l ++ map wn l ++ l0)
         with (nil ++ flat_map (app (map wn l)) (nil :: nil ++ l0 :: nil))
        by (list_simpl; reflexivity).
      rewrite <- (bidual A0) in Hl.
      replace (flat_map (app (map wn l)) (nil :: nil ++ l0 :: nil)) with
              (flat_map (fun '(p1,p2) => app (map wn l) p2) ((0 , nil) :: nil ++ (0 , l0) :: nil));
        [| reflexivity ].
      refine (substitution_oc (dual A0) _ _ _ _ _ _); list_simpl; try assumption.
      -- intros a n l1 l2 Ha.
         specialize (P_gax_cut _ _ _ _ Ha); split.
         ++ destruct (pcut P (wn (wn_n n (dual A0)))); [ reflexivity | ].
            destruct (P_gax_cut eq_refl) as [Hat _]; inversion Hat.
         ++ apply oc_r, Hl.
      -- intros l1 l2 pi.
         apply (IHcut (dual A0)); [ rewrite fsize_dual; cbn; lia | assumption | assumption ].
    * (* cut_r *)
      remember (oc_r Hl) as Hoc eqn:Hdel. clear Hdel.
      destruct l2; destr_eq Heql'; subst.
      -- cbn in Heql'. subst.
         eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
         rewrite <- app_nil_l; apply (cut_r _ f); [ | assumption ].
         revert Hoc IHsize;
           replace (oc A0) with (dual (wn (dual A0))) by (cbn; rewrite bidual; reflexivity);
           intros Hoc IHsize.
         revert Hl2 IHsize; change (dual A :: wn (dual A0) :: l0)
                              with ((dual A :: nil) ++ wn (dual A0) :: l0);
           intros Hl2 IHsize.
         refine (IHsize _ _ _ _ Hoc Hl2 _ _); rewrite ? fsize_dual; cbn; lia.
      -- list_simpl; eapply ex_r; [ | apply PCPermutation_Type_app_comm ]; list_simpl.
         eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
         apply (cut_r _ f); [ assumption | ].
         revert Hoc IHsize;
           replace (oc A0) with (dual (wn (dual A0))) by (cbn; rewrite bidual; reflexivity);
           intros Hoc IHsize.
         revert Hr2 IHsize; change (A :: wn (dual A0) :: l2)
                              with ((A :: nil) ++ wn (dual A0) :: l2);
           intros Hr2 IHsize.
         change (A :: map wn l ++ l2) with ((A :: nil) ++ map wn l ++ l2).
         refine (IHsize _ _ _ _ Hoc Hr2 _ _); rewrite ? fsize_dual; cbn; lia.
    * (* gax_r *)
      specialize (P_gax_cut _ _ nil _ Heql').
      case_eq (pcut P (dual (oc A0))); intros Hcut.
      -- apply (cut_r _ Hcut); [ rewrite bidual; constructor; assumption | ].
         rewrite <- Heql'; apply gax_r.
      -- exfalso.
         destruct (P_gax_cut Hcut) as [Hat _]; inversion Hat.
  + (* commutative case *)
    decomp_map H1. subst. cbn in pi1.
    rewrite app_comm_cons, <- (app_nil_l (map wn l2)).
    destruct (pcut P (oc (dual A))) eqn:Hcut.
    * eapply ex_r; [ | apply PCPermutation_Type_app_comm ]; list_simpl.
      apply (cut_r _ Hcut); [ | assumption ].
      list_simpl. rewrite bidual.
      rewrite app_comm_cons. eapply ex_r; [ | apply PCPermutation_Type_app_comm ]; list_simpl.
      replace (map wn l1 ++ wn A :: map wn l2) with (map wn (l1 ++ A :: l2)) by (list_simpl; reflexivity).
      apply oc_r. assumption.
    * assert (Hgax := (oc_notin_gax _ Hcut)).
      refine (cut_oc_comm (dual A) _ _ nil _ Hgax pi1 _).
      intros lw' pi0 Hs. list_simpl. cbn in IHsize.
      rewrite <- ? map_app. apply oc_r.
      revert Hl IHsize. list_simpl. rewrite ? app_comm_cons. intros Hl IHsize.
      simple refine (IHsize _ _ _ _ _ Hl _ _); [ exact (oc_r pi0) | cbn in *; lia | reflexivity ].
- (* de_r *)
  destruct l1; destr_eq Heql; subst; list_simpl.
  + (* main case *)
    remember (dual (wn A0) :: l0) as l'; destruct_ll pi1 f X l Hl2 Hr2 HP Hax a;
      try inversion Heql'.
    * (* ex_r *)
      remember (de_r Hl) as Hde eqn:Hdel. clear Hdel.
      destruct (PCPermutation_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] HP' Heq];
        cbn in Heq, HP'; subst.
      apply (PEPermutation_Type_app_tail _ _ _ l2) in HP'.
      apply PEPermutation_PCPermutation_Type in HP'; unfold id in HP'; list_simpl in HP'.
      eapply ex_r; [ | symmetry; apply HP' ].
      eapply ex_r; [ | symmetry; apply PCPermutation_Type_app_rot ].
      revert Hde IHsize; cbn;
        replace (wn A0) with (dual (oc (dual A0))) by (cbn; rewrite bidual; reflexivity);
        intros Hde IHsize.
      refine (IHsize _ _ _ _ Hde Hl2 _ _); cbn; rewrite ? fsize_dual; lia.
    * (* ex_wn_r *)
      remember (de_r Hl) as Hde eqn:Hdel. clear Hdel.
      destruct l; destr_eq Heql'; [ destruct lw'; destr_eq Heql' | ]; subst.
      -- assert (lw = nil) by (clear - HP; symmetry in HP; apply (Permutation_Type_nil HP)); subst.
         list_simpl in Heql'; subst; list_simpl in Hl2.
         revert Hl2 IHsize; cbn; change (oc (dual A0)) with (dual (wn A0)); intros Hl2 IHsize.
         revert Hde IHsize; rewrite <- (app_nil_l (wn _ :: _)); intros Hde IHsize.
         refine (IHsize _ _ _ _ Hl2 Hde _ _); cbn; lia.
      -- list_simpl; eapply ex_wn_r; [ | apply HP ]; rewrite 2 app_assoc, <- (app_assoc l).
         revert Hl2 IHsize; cbn; change (oc (dual A0)) with (dual (wn A0)); intros Hl2 IHsize.
         revert Hde IHsize; rewrite <- (app_nil_l (wn _ :: _)); intros Hde IHsize.
         refine (IHsize _ _ _ _ Hl2 Hde _ _); cbn; lia.
    * (* mix_r *)
      remember (de_r Hl) as Hde eqn:Hdel. clear Hdel.
      change (oc (dual A0) :: l0) with (nil ++ oc (dual A0) :: l0) in H0.
      apply concat_eq_elt in H0 as [(((L1, L2), l1'), l2') [Heqb ->] ->].
      symmetry in Heqb. apply app_eq_nil in Heqb as [Heqb1 Heqb2].
      apply ex_r with ((l2 ++ l2') ++ concat L2); [ | rewrite <- app_assoc; apply PCPermutation_Type_app_comm ].
      rewrite <- (app_nil_l _), <- Heqb1.
      change ((l2 ++ l2') ++ concat L2) with (concat ((l2 ++ l2') :: L2)).
      rewrite <- concat_app.
      apply mix_r.
      -- clear IHsize.
         rewrite length_app; rewrite length_app in f; cbn; cbn in f; assumption.
      -- assert (FL1 := Forall_inf_app_l _ _ Hax).
         assert (FL2 := Forall_inf_app_r _ _ Hax).
         inversion FL2; subst; clear FL2; rename X0 into FL2; rename X into pi.
         apply Forall_inf_app; [ assumption |].
         apply Forall_inf_cons; [| assumption ].
         clear pi.
         destruct (In_Forall_inf_elt _ _ (nil ++ (oc (dual A0)) :: l2') Hax) as (pi & Hin).
         rewrite <- (app_nil_l _).
         revert Hde IHsize;
           replace (wn A0) with (dual (oc (dual A0))) by (cbn; rewrite bidual; reflexivity);
           intros Hde IHsize.
         apply (psize_inf_mix f) in Hin.
         refine (IHsize _ _ _ _ Hde pi _ _); cbn; cbn in Hin; rewrite ? fsize_dual; lia.
    * (* oc_r *)
      clear IHsize; subst.
      rewrite <- (app_nil_l (A0 :: _)) in Hl; refine (IHcut _ _ _ _ _ Hl2 Hl); cbn; lia.
    * (* cut_r *)
      remember (de_r Hl) as Hwn eqn:Hdel. clear Hdel.
      destruct l3; destr_eq Heql'; subst.
      -- cbn in Heql'; subst.
         eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
         rewrite <- app_nil_l; apply (cut_r _ f); [ | assumption ].
         revert Hwn IHsize;
           replace (wn A0) with (dual (oc (dual A0))) by (now cbn; rewrite ? bidual);
           intros Hwn IHsize.
         revert Hl2 IHsize;
           change (dual A :: oc (dual A0) :: l0) with ((dual A :: nil) ++ oc (dual A0) :: l0);
           intros Hl2 IHsize.
         refine (IHsize _ _ _ _ Hwn Hl2 _ _); rewrite ? fsize_dual; cbn; lia.
      -- list_simpl; eapply ex_r; [ | apply PCPermutation_Type_app_rot ].
         rewrite app_assoc; apply (cut_r _ f); [ assumption | ].
         revert Hwn IHsize;
           replace (wn A0) with (dual (oc (dual A0))) by (now cbn; rewrite ? bidual);
           intros Hwn IHsize.
         revert Hr2 IHsize;
           change (A :: oc (dual A0) :: l3) with ((A :: nil) ++ oc (dual A0) :: l3);
           intros Hr2 IHsize.
         refine (IHsize _ _ _ _ Hwn Hr2 _ _); rewrite ? fsize_dual; cbn; lia.
    * (* gax_r *)
      specialize (P_gax_cut _ _ nil _ Heql').
      case_eq (pcut P (dual (wn A0))); intros Hcut.
      -- apply (cut_r _ Hcut); [ rewrite bidual; constructor; assumption | ].
         rewrite <- Heql'; apply gax_r.
      -- exfalso.
         destruct (P_gax_cut Hcut) as [Hat _]; inversion Hat.
  + (* commutative case *)
    apply de_r.
    revert Hl IHsize; cbn; rewrite (app_comm_cons l1 _ A0); intros Hl IHsize.
    refine (IHsize _ _ _ _ pi1 Hl _ _); cbn; lia.
- (* wk_r *)
  destruct l1; destr_eq Heql; subst; list_simpl.
  + (* main case *)
    remember (dual (wn A0) :: l0) as l'; destruct_ll pi1 f X l Hl2 Hr2 HP Hax a;
      try inversion Heql'.
    * (* ex_r *)
      remember (wk_r A0 Hl) as Hwk eqn:Hdel. clear Hdel.
      destruct (PCPermutation_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] HP' Heq];
        cbn in Heq, HP'; subst.
      apply (PEPermutation_Type_app_tail _ _ _ l2) in HP'.
      apply PEPermutation_PCPermutation_Type in HP'; unfold id in HP'; list_simpl in HP'.
      eapply ex_r; [ | symmetry; apply HP' ].
      eapply ex_r; [ | symmetry; apply PCPermutation_Type_app_rot ].
      revert Hwk IHsize; cbn;
        replace (wn A0) with (dual (oc (dual A0))) by (cbn; rewrite bidual; reflexivity);
        intros Hwk IHsize.
      refine (IHsize _ _ _ _ Hwk Hl2 _ _); cbn; rewrite ? fsize_dual; lia.
    * (* ex_wn_r *)
      remember (wk_r A0 Hl) as Hwk eqn:Hdel. clear Hdel.
      destruct l; destr_eq Heql'; [ destruct lw'; destr_eq Heql' | ]; subst.
      -- assert (lw = nil) by (clear - HP; symmetry in HP; apply (Permutation_Type_nil HP)); subst.
         list_simpl in Heql'; subst; list_simpl in Hl2.
         revert Hl2 IHsize; cbn; change (oc (dual A0)) with (dual (wn A0)); intros Hl2 IHsize.
         revert Hwk IHsize; rewrite <- (app_nil_l (wn _ :: _)); intros Hwk IHsize.
         refine (IHsize _ _ _ _ Hl2 Hwk _ _); cbn; lia.
      -- list_simpl; eapply ex_wn_r; [ | apply HP ]; rewrite 2 app_assoc, <- (app_assoc l).
         revert Hl2 IHsize; cbn; change (oc (dual A0)) with (dual (wn A0)); intros Hl2 IHsize.
         revert Hwk IHsize; rewrite <- (app_nil_l (wn _ :: _)); intros Hwk IHsize.
         refine (IHsize _ _ _ _ Hl2 Hwk _ _); cbn; lia.
    * (* mix_r *)
      remember (wk_r A0 Hl) as Hwk eqn:Hdel. clear Hdel.
      change (oc (dual A0) :: l0) with (nil ++ oc (dual A0) :: l0) in H0.
      apply concat_eq_elt in H0 as [(((L1, L2), l1'), l2') [Heqb ->] ->].
      symmetry in Heqb. apply app_eq_nil in Heqb as [Heqb1 Heqb2].
      apply ex_r with ((l2 ++ l2') ++ concat L2); [ | rewrite <- app_assoc; apply PCPermutation_Type_app_comm ].
      rewrite <- (app_nil_l _ ), <- Heqb1.
      change ((l2 ++ l2') ++ concat L2) with (concat ((l2 ++ l2') :: L2)).
      rewrite <- concat_app.
      apply mix_r.
      -- clear IHsize.
         rewrite length_app; rewrite length_app in f; cbn; cbn in f; assumption.
      -- assert (FL1 := Forall_inf_app_l _ _ Hax).
         assert (FL2 := Forall_inf_app_r _ _ Hax).
         inversion FL2; subst; clear FL2; rename X0 into FL2; rename X into pi.
         apply Forall_inf_app; [ assumption |].
         apply Forall_inf_cons; [| assumption ].
         clear pi.
         destruct (In_Forall_inf_elt _ _ (nil ++ (oc (dual A0)) :: l2') Hax) as (pi & Hin).
         change (l2 ++ l2') with (nil ++ l2 ++ l2').
         revert Hwk IHsize;
           replace (wn A0) with (dual (oc (dual A0))) by (cbn; rewrite bidual; reflexivity);
           intros Hwk IHsize.
         apply (psize_inf_mix f) in Hin.
         refine (IHsize _ _ _ _ Hwk pi _ _); cbn; cbn in Hin; rewrite ? fsize_dual; lia.
    * (* oc_r *)
      clear IHsize. subst. apply wk_list_r. assumption.
    * (* cut_r *)
      remember (wk_r A0 Hl) as Hwn eqn:Hdel. clear Hdel.
      destruct l3; destr_eq Heql'; subst.
      -- cbn in Heql'; subst.
         eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
         rewrite <- app_nil_l; apply (cut_r _ f); [ | assumption ].
         revert Hwn IHsize;
           replace (wn A0) with (dual (oc (dual A0))) by (now cbn; rewrite ? bidual);
           intros Hwn IHsize.
         revert Hl2 IHsize;
           change (dual A :: oc (dual A0) :: l0) with ((dual A :: nil) ++ oc (dual A0) :: l0);
           intros Hl2 IHsize.
         refine (IHsize _ _ _ _ Hwn Hl2 _ _); rewrite ? fsize_dual; cbn; lia.
      -- list_simpl; eapply ex_r; [ | apply PCPermutation_Type_app_rot ].
         rewrite app_assoc; apply (cut_r _ f); [ assumption | ].
         revert Hwn IHsize;
           replace (wn A0) with (dual (oc (dual A0))) by (now cbn; rewrite ? bidual);
           intros Hwn IHsize.
         revert Hr2 IHsize;
           change (A :: oc (dual A0) :: l3) with ((A :: nil) ++ oc (dual A0) :: l3);
           intros Hr2 IHsize.
         refine (IHsize _ _ _ _ Hwn Hr2 _ _); rewrite ? fsize_dual; cbn; lia.
    * (* gax_r *)
      specialize (P_gax_cut _ _ nil _ Heql').
      case_eq (pcut P (dual (wn A0))); intros Hcut.
      -- apply (cut_r _ Hcut); [ rewrite bidual; constructor; assumption | ].
         rewrite <- Heql'; apply gax_r.
      -- exfalso.
         destruct (P_gax_cut Hcut) as [Hat _]; inversion Hat.
  + (* commutative case *)
    apply wk_r.
    refine (IHsize _ _ _ _ pi1 Hl _ _); cbn; lia.
- (* co_r *)
  destruct l1; destr_eq Heql; subst; list_simpl.
  + (* main case *)
    remember (dual (wn A0) :: l0) as l'; destruct_ll pi1 f X l Hl2 Hr2 HP Hax a;
      try inversion Heql'.
    * (* ex_r *)
      remember (co_r  Hl) as Hco eqn:Hdel. clear Hdel.
      destruct (PCPermutation_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] HP' Heq];
        cbn in Heq, HP'; subst.
      apply (PEPermutation_Type_app_tail _ _ _ l2) in HP'.
      apply PEPermutation_PCPermutation_Type in HP'; unfold id in HP'; list_simpl in HP'.
      eapply ex_r; [ | symmetry; apply HP' ].
      eapply ex_r; [ | symmetry; apply PCPermutation_Type_app_rot ].
      revert Hco IHsize; cbn;
        replace (wn A0) with (dual (oc (dual A0)))
          by (cbn; rewrite bidual; reflexivity);
        intros Hco IHsize.
      refine (IHsize _ _ _ _ Hco Hl2 _ _); cbn; rewrite ? fsize_dual; lia.
    * (* ex_wn_r *)
      remember (co_r Hl) as Hco eqn:Hdel. clear Hdel.
      destruct l; destr_eq Heql'; [ destruct lw'; destr_eq Heql' | ]; subst.
      -- assert (lw = nil) by (clear - HP; symmetry in HP; apply (Permutation_Type_nil HP)); subst.
         list_simpl in Heql'; subst; list_simpl in Hl2.
         revert Hl2 IHsize. cbn. change (oc (dual A0)) with (dual (wn A0)). intros Hl2 IHsize.
         revert Hco IHsize. rewrite <- (app_nil_l (wn _ :: _)). intros Hco IHsize.
         refine (IHsize _ _ _ _ Hl2 Hco _ _); cbn; lia.
      -- list_simpl; eapply ex_wn_r; [ | apply HP ]; rewrite 2 app_assoc, <- (app_assoc l).
         revert Hl2 IHsize. cbn. change (oc (dual A0)) with (dual (wn A0)). intros Hl2 IHsize.
         revert Hco IHsize. rewrite <- (app_nil_l (wn _ :: _)). intros Hco IHsize.
         refine (IHsize _ _ _ _ Hl2 Hco _ _); cbn; lia.
    * (* mix_r *)
      remember (co_r Hl) as Hco eqn:Hdel. clear Hdel.
      change (oc (dual A0) :: l0) with (nil ++ oc (dual A0) :: l0) in H0.
      apply concat_eq_elt in H0 as [(((L1, L2), l1'), l2') [Heqb ->] ->].
      symmetry in Heqb. apply app_eq_nil in Heqb as [Heqb1 Heqb2].
      apply ex_r with ((l2 ++ l2') ++ concat L2); [ | rewrite <- app_assoc; apply PCPermutation_Type_app_comm ].
      rewrite <- (app_nil_l _), <- Heqb1.
      change ((l2 ++ l2') ++ concat L2) with (concat ((l2 ++ l2') :: L2)).
      rewrite <- concat_app.
      apply mix_r.
      -- clear IHsize.
         rewrite length_app; rewrite length_app in f; cbn; cbn in f; assumption.
      -- assert (FL1 := Forall_inf_app_l _ _ Hax).
         assert (FL2 := Forall_inf_app_r _ _ Hax).
         inversion FL2; subst; clear FL2; rename X0 into FL2; rename X into pi.
         apply Forall_inf_app; [ assumption |].
         apply Forall_inf_cons; [| assumption ].
         clear pi.
         destruct (In_Forall_inf_elt _ _ (nil ++ (oc (dual A0)) :: l2') Hax) as (pi & Hin).
         change (l2 ++ l2') with (nil ++ l2 ++ l2').
         revert Hco IHsize;
           replace (wn A0) with (dual (oc (dual A0))) by (cbn; rewrite bidual; reflexivity);
           intros Hco IHsize.
         apply (psize_inf_mix f) in Hin.
         refine (IHsize _ _ _ _ Hco pi _ _); cbn; cbn in Hin; rewrite ? fsize_dual; lia.
    * (* oc_r *)
      clear IHsize; subst.
      apply co_list_r.
      replace (map wn l ++ map wn l ++ l2)
         with (nil ++ flat_map (fun '(p1,p2) => app (map wn l) p2)
                               ((0, nil) :: nil ++ (0, l2) :: nil))
        by (list_simpl; reflexivity).
      refine (substitution_oc A0 _ _ _ _ _ _); list_simpl; try assumption.
      -- intros a n l1' l2' Ha.
         specialize (P_gax_cut _ _ _ _ Ha); split.
         ++ destruct (pcut P (wn (wn_n n A0))); [ reflexivity | ].
            destruct (P_gax_cut eq_refl) as [Hat _]; inversion Hat.
         ++ apply oc_r, Hl2.
      -- intros l1' l2' pi.
         apply (IHcut A0); [ cbn; lia | assumption | assumption ].
    * (* cut_r *)
      remember (co_r Hl) as Hwn eqn:Hdel. clear Hdel.
      destruct l3; destr_eq Heql'; subst.
      -- cbn in Heql'; subst.
         eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
         rewrite <- app_nil_l; apply (cut_r _ f); [ | assumption ].
         revert Hwn IHsize;
           replace (wn A0) with (dual (oc (dual A0))) by (now cbn; rewrite ? bidual);
           intros Hwn IHsize.
         revert Hl2 IHsize;
           change (dual A :: oc (dual A0) :: l0) with ((dual A :: nil) ++ oc (dual A0) :: l0);
           intros Hl2 IHsize.
         refine (IHsize _ _ _ _ Hwn Hl2 _ _); rewrite ? fsize_dual; cbn; lia.
      -- list_simpl; eapply ex_r; [ | apply PCPermutation_Type_app_rot ].
         rewrite app_assoc; apply (cut_r _ f); [ assumption | ].
         revert Hwn IHsize;
           replace (wn A0) with (dual (oc (dual A0))) by (now cbn; rewrite ? bidual);
           intros Hwn IHsize.
         revert Hr2 IHsize;
           change (A :: oc (dual A0) :: l3) with ((A :: nil) ++ oc (dual A0) :: l3);
           intros Hr2 IHsize.
         refine (IHsize _ _ _ _ Hwn Hr2 _ _); rewrite ? fsize_dual; cbn; lia.
    * (* gax_r *)
      specialize (P_gax_cut _ _ nil _ Heql').
      case_eq (pcut P (dual (wn A0))); intros Hcut.
      -- apply (cut_r _ Hcut); [ rewrite bidual; constructor; assumption | ].
         rewrite <- Heql'; apply gax_r.
      -- exfalso.
         destruct (P_gax_cut Hcut) as [Hat _]; inversion Hat.
  + (* commutative case *)
    apply co_r.
    revert Hl IHsize; cbn; rewrite (app_comm_cons l1 _ (wn A0)), (app_comm_cons _ _ (wn A0));
      intros Hl IHsize.
    refine (IHsize _ _ _ _ pi1 Hl _ _); cbn; lia.
- (* cut_r *)
  decomp_elt_eq_app Heql; subst.
  + rewrite 2 app_assoc; apply (cut_r _ f); [ assumption | ].
    revert Hr IHsize; list_simpl; rewrite ? app_comm_cons; intros Hr IHsize.
    refine (IHsize _ _ _ _ pi1 Hr _ eq_refl); lia.
  + list_simpl; apply (cut_r _ f); [ | assumption ].
    revert Hl IHsize; list_simpl; rewrite ? app_comm_cons; intros Hl IHsize.
    refine (IHsize _ _ _ _ pi1 Hl _ eq_refl); lia.
- (* gax_r *)
  destruct (pcut P A) eqn:Hcut.
  + rewrite app_assoc. eapply ex_r; [ | apply PCPermutation_Type_app_comm ]; rewrite app_assoc.
    apply (cut_r _ Hcut pi1).
    rewrite app_comm_cons. eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
    rewrite <- Heql. apply gax_r.
  + destruct (P_gax_cut _ _ _ _ Heql Hcut) as [Hat Hgax].
    rewrite <- (app_nil_r l0), <- app_assoc. rewrite <- (bidual A) in Heql.
    refine (cut_gax_l a _ _ nil _ _ Heql _ pi1).
    * apply atomic_dual in Hat. exact Hat.
    * intros b l l' [c Hc]%Hgax.
      apply (ex_r (l ++ l2 ++ l1 ++ l'));
        [ | rewrite app_assoc, (app_assoc l1); apply PCPermutation_Type_app_comm].
      rewrite <- Hc. apply gax_r.
Qed.

End Cut_Elim_Proof.

Context {P : @pfrag atom}.

(** ** Variants on cut admissibility *)

(** If axioms are atomic and closed under cut, then the cut rule is admissible:
provability is preserved if we remove the cut rule. *)
Lemma cut_admissible (Hgax_at : atomic_ax P) (Hgax_cut : cut_closed P) l : ll P l -> ll (cutrm_pfrag P) l.
Proof.
intros pi.
induction pi using ll_nested_ind; try (econstructor; eassumption).
- apply mix_r; cbn; [ assumption | ].
  apply forall_Forall_inf.
  intros x Hin.
  apply In_Forall_inf_in with _ _ _ _ PL in Hin as [pi Hin].
  refine (Dependent_Forall_inf_forall_formula _ _ X Hin).
- eapply cut_r_gax; [ | eassumption | eassumption ].
  clear - Hgax_at Hgax_cut. intros a C l1 l2 Ha Hcut. split.
  + cbn in Ha. specialize (Hgax_at a). rewrite Ha in Hgax_at.
    apply (Forall_inf_elt _ _ _ Hgax_at).
  + intros b l3 l4 Hb. eapply (Hgax_cut C); eassumption.
- revert a. change (pgax P) with (pgax (cutrm_pfrag P)). apply gax_r.
Qed.

(** If there are no axioms (except the identity rule), then the cut rule is valid. *)
Lemma cut_r_axfree (P_axfree : no_ax P) A l1 l2 : ll P (dual A :: l1) -> ll P (A :: l2) -> ll P (l2 ++ l1).
Proof. apply cut_r_gax. intro. contradiction P_axfree. Qed.

(** If there are no axioms (except the identity rule), then the cut rule is admissible:
provability is preserved if we remove the cut rule. *)
Lemma cut_admissible_axfree (P_axfree : no_ax P) l : ll P l -> ll (cutrm_pfrag P) l.
Proof. apply cut_admissible; [ intro | intros ? ? ]; contradiction P_axfree. Qed.

End Atoms.
