(** * Study of Linear Logic enriched with [bot = oc bot] *)

From OLlibs Require Import infinite List_more Permutation_Type_more Dependent_Forall_Type.
From Yalla Require Import ll_fragments.

Set Implicit Arguments.


Section Atoms.

Context {atom : InfDecType}.
Notation formula := (@formula atom).
Notation llR := (@llR atom).

(** ** The system [ll_bbb] *)
(** It contains [ll_mix2] but allows [mix0] as well above one side of each [mix2] rule. *)

Inductive ll_bbb : list formula -> Type :=
| ax_bbb_r X : ll_bbb (covar X :: var X :: nil)
| ex_bbb_r l1 l2 : ll_bbb l1 -> Permutation_Type l1 l2 -> ll_bbb l2
| mix2_bbb_r l1 l2 : ll_bbb l1 -> ll_mix02 l2 -> ll_bbb (l2 ++ l1)
| one_bbb_r : ll_bbb (one :: nil)
| bot_bbb_r l : ll_bbb l -> ll_bbb (bot :: l)
| tens_bbb_r A B l1 l2 : ll_bbb (A :: l1) -> ll_bbb (B :: l2) -> ll_bbb (tens A B :: l2 ++ l1)
| parr_bbb_r A B l : ll_bbb (A :: B :: l) -> ll_bbb (parr A B :: l)
| top_bbb_r l : ll_bbb (top :: l)
| plus_bbb_r1 A B l : ll_bbb (A :: l) -> ll_bbb (aplus A B :: l)
| plus_bbb_r2 A B l : ll_bbb (A :: l) -> ll_bbb (aplus B A :: l)
| with_bbb_r A B l : ll_bbb (A :: l) -> ll_bbb (B :: l) -> ll_bbb (awith A B :: l)
| oc_bbb_r A l : ll_bbb (A :: map wn l) -> ll_bbb (oc A :: map wn l)
| de_bbb_r A l : ll_bbb (A :: l) -> ll_bbb (wn A :: l)
| wk_bbb_r A l : ll_bbb l -> ll_bbb (wn A :: l)
| co_bbb_r A l : ll_bbb (wn A :: wn A :: l) -> ll_bbb (wn A :: l).
Arguments ex_bbb_r _ [_].

(** Generalized weakening for lists *)
Lemma wk_list_bbb_r l l' : ll_bbb l' -> ll_bbb (map wn l ++ l').
Proof. induction l; intros; [ | cbn; apply wk_bbb_r, IHl ]; assumption. Qed.

(** Generalized contraction for lists *)
Lemma co_list_bbb_r l l' : ll_bbb (map wn l ++ map wn l ++ l') -> ll_bbb (map wn l ++ l').
Proof.
induction l in l' |- *; intros; [ assumption | ].
apply (ex_bbb_r (map wn l ++ wn a :: l')); [ | symmetry; apply Permutation_Type_middle ].
apply IHl.
apply (ex_bbb_r (wn a :: map wn l ++ map wn l ++ l')); [ | rewrite ? app_assoc; apply Permutation_Type_middle ].
apply co_bbb_r.
eapply ex_bbb_r; [ eassumption | ].
apply Permutation_Type_cons; [ reflexivity | ].
symmetry. apply Permutation_Type_middle.
Qed.

(** Reversibility of [bot] in [ll_bbb] *)
Lemma bot_rev_bbb l : ll_bbb l -> forall l1 l2, l = l1 ++ bot :: l2 -> ll_bbb (l1 ++ l2).
Proof.
intros pi. induction pi; intros l1' l2' Heq; subst;
  try (destruct l1'; inversion Heq; subst;
       list_simpl; constructor;
       rewrite ? app_comm_cons; apply IHpi; reflexivity).
- exfalso. destruct l1' as [|? [|? [|? l1']]]; discriminate Heq.
- destruct (Permutation_Type_vs_elt_inv _ _ _ p) as [(l3, l4) ->].
  apply Permutation_Type_app_inv in p.
  eapply ex_bbb_r, p.
  apply IHpi. reflexivity.
- dichot_elt_app_inf_exec Heq; subst.
  + rewrite app_assoc. apply mix2_bbb_r; [ assumption | ].
    apply bot_rev; [ intros [] | assumption ].
  + rewrite <- app_assoc. apply mix2_bbb_r; [ | assumption ].
    apply IHpi. reflexivity.
- exfalso. destruct l1' as [|? [|? [|? l1']]]; discriminate Heq.
- destruct l1'; inversion Heq ; subst; [ assumption | ].
  list_simpl. apply bot_bbb_r, IHpi. reflexivity.
- rewrite app_comm_cons in Heq. dichot_elt_app_inf_exec Heq; subst.
  + destruct l1'; inversion Heq0; subst.
    list_simpl. rewrite app_assoc. apply tens_bbb_r; [ assumption | ].
    rewrite app_comm_cons. apply IHpi2. reflexivity.
  + list_simpl. apply tens_bbb_r; [ | assumption ].
    rewrite app_comm_cons. apply IHpi1. reflexivity.
- destruct l1'; inversion Heq; subst.
  list_simpl. apply with_bbb_r; rewrite app_comm_cons; [ apply IHpi1 | apply IHpi2 ]; reflexivity.
- exfalso.
  destruct l1'; inversion Heq.
  decomp_map H1; discriminate.
Qed.

(** [ll_mix2] is contained in [ll_bbb] *)
Lemma mix2_to_bbb l : ll_mix2 l -> ll_bbb l.
Proof.
intros pi. induction pi using ll_nested_ind; try now constructor.
- apply (ex_bbb_r l1); assumption.
- apply (Permutation_Type_map wn) in p.
  eapply ex_bbb_r; [ eassumption | ].
  apply Permutation_Type_app_head, Permutation_Type_app_tail, p.
- repeat (destruct L; try now inversion eqpmix).
  cbn. rewrite app_nil_r.
  assert (ll_bbb l0) as pi1.
  { destruct (In_Forall_inf_in _ PL (in_inf_elt l0 (l :: nil) nil)) as [pi Hin].
    apply (Dependent_Forall_inf_forall_formula _ _ X Hin). }
  inversion PL; inversion X1. subst. clear X1 X2 X3.
  apply mix2_bbb_r; [ assumption | ].
  eapply stronger_pfrag; [ | eassumption ].
  repeat split.
  + intros a. exists a. reflexivity.
  + intro n. repeat (destruct n; try apply BoolOrder.le_refl; try apply BoolOrder.le_true).
- destruct a.
Qed.

(** [ll_bbb] is contained in [ll_mix02] *)
Lemma bbb_to_mix02 l : ll_bbb l -> ll_mix02 l.
Proof.
intros pi. induction pi; try now constructor.
- apply (ex_r l1); assumption.
- rewrite <- (app_nil_r _), <- app_assoc.
  change (l2 ++ l1 ++ nil) with (concat (l2 :: l1 :: nil)).
  apply mix_r; repeat constructor; assumption.
Qed.

Lemma mix2_std_bbb_r l1 l2 : ll_bbb l1 -> ll_bbb l2 -> ll_bbb (l2 ++ l1).
Proof. intros pi1 pi2%bbb_to_mix02. apply mix2_bbb_r; assumption. Qed.

(** [ll_bbb] as an enriched [ll] system *)

Lemma bbb_to_ll l : ll_bbb l -> ll_ll (wn (tens (wn one) bot) :: l).
Proof.
intros pi. induction pi;
  (try now (apply wk_r; constructor));
  try now (eapply ex_r; [ | apply Permutation_Type_swap ];
           constructor; eapply ex_r; [ eassumption | try apply Permutation_Type_swap ]).
- eapply ex_r; [ eassumption | now cbn; apply Permutation_Type_cons ].
- apply co_r, co_r, de_r.
  apply (ex_r (tens (wn one) bot :: (wn (tens (wn one) bot) :: l1)
                                 ++ (wn (tens (wn one) bot) :: l2))).
  2:{ cbn. do 2 (apply Permutation_Type_cons; [ reflexivity | ]).
      symmetry. apply Permutation_Type_cons_app, Permutation_Type_app_comm. }
  apply tens_r.
  + apply mix02_to_ll'' with true true true; [ reflexivity | ].
    apply stronger_pfrag with (pfrag_mix02); [ | assumption ].
    repeat split.
    * intro a. exists a. reflexivity.
    * intros n. repeat (destruct n; try reflexivity).
  + apply bot_r. assumption.
- apply co_r.
  apply (ex_r (tens A B :: (wn (tens (wn one) bot) :: l2)
                        ++ (wn (tens (wn one) bot) :: l1))).
  2:{ cbn. etransitivity; [ apply Permutation_Type_swap | ].
      apply Permutation_Type_cons; [ reflexivity | ].
      cons2app. rewrite ? app_assoc. apply Permutation_Type_app_tail. cbn.
      rewrite app_comm_cons. etransitivity; [ apply Permutation_Type_app_comm | reflexivity ]. }
  apply tens_r; eapply ex_r; [ apply IHpi1 | | apply IHpi2 | ]; apply Permutation_Type_swap.
- eapply ex_r; [ | apply Permutation_Type_swap ].
  apply parr_r.
  eapply ex_r; [ eassumption | ].
  cons2app. rewrite ? app_assoc. apply Permutation_Type_middle.
- eapply ex_r; [ | apply Permutation_Type_swap ].
  apply with_r.
  + eapply ex_r; [ apply IHpi1 | cbn; apply Permutation_Type_swap ].
  + eapply ex_r; [ apply IHpi2 | cbn; apply Permutation_Type_swap ].
- apply (ex_r (oc A :: map wn (tens (wn one) bot :: l)));
    [ | cbn; apply Permutation_Type_swap ].
  apply oc_r.
  eapply ex_r; [ eassumption | cbn; apply Permutation_Type_swap ].
- eapply ex_r; [ | apply Permutation_Type_swap ].
  apply co_r.
  eapply ex_r; [ eassumption | ].
  cons2app. rewrite ? app_assoc. apply Permutation_Type_middle.
Qed.

Lemma ll_to_bbb l : ll_ll l ->
  forall l' n m,
    Permutation_Type l (l' ++ repeat (tens (wn one) bot) n ++ repeat (wn (tens (wn one) bot)) m) -> ll_bbb l'.
Proof.
intros pi. induction pi using ll_nested_ind; intros l' n m HP.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP' as [[l'l l'r] Heq].
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  apply Permutation_Type_length_1_inv in HP.
  apply app_eq_unit_inf in HP as [[-> ->] | [-> ->]]; destruct l'; inversion Heq as [[Heq' Heq'']]; subst.
  + destruct n; inversion Heq as [Heq''].
    destruct m; discriminate Heq''.
  + destruct l'; inversion Heq'' as [[Heq1 Heq2]].
    * destruct n; inversion Heq1 as [Heq2].
      destruct m; discriminate Heq2.
    * destruct l'; inversion Heq2 as [Heq3]. rewrite Heq3.
      apply ax_bbb_r.
  + destruct n; inversion Heq as [Heq''].
    destruct m; discriminate Heq''.
  + destruct l'; inversion Heq'' as [[Heq1 Heq2]].
    * destruct n; inversion Heq1 as [Heq2].
      destruct m; discriminate Heq2.
    * destruct l'; inversion Heq2 as [Heq3]. rewrite Heq3.
      eapply ex_bbb_r; [ apply ax_bbb_r | apply Permutation_Type_swap ].
- cbn in p.
  eapply IHpi.
  transitivity l2; eassumption.
- eapply IHpi.
  etransitivity; [ | eassumption ].
  apply Permutation_Type_app_head, Permutation_Type_app_tail, Permutation_Type_map, p.
- discriminate eqpmix.
- apply Permutation_Type_length_1_inv in HP.
  destruct l'; inversion HP as [[Heq Heq0]].
  + destruct n; inversion Heq as [Heq'].
    destruct m; discriminate Heq'.
  + apply app_eq_nil in Heq0 as [-> _].
    apply one_bbb_r.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP' as [[l'l l'r] Heq].
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_elt_app_inf_exec Heq; subst.
  + rewrite app_assoc in HP.
    apply IHpi in HP.
    eapply ex_bbb_r; [ apply bot_bbb_r; eassumption | apply Permutation_Type_middle ].
  + dichot_elt_app_inf_exec Heq1; subst.
    * symmetry in Heq0. apply repeat_eq_app in Heq0 as [_ Heq0]. inversion Heq0.
    * symmetry in Heq2. apply repeat_eq_app in Heq2 as [_ Heq2]. inversion Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP' as [[l'l l'r] Heq].
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_elt_app_inf_exec Heq; subst.
  + rewrite app_assoc in HP.
    apply Permutation_Type_app_app_inv in HP as [[[[l1a l2a] l3a] l4a] [[HP1 HP2] [HP3 HP4]]].
    apply Permutation_Type_app_app_inv in HP4 as [[[[l1b l2b] l3b] l4b] [[HP1b HP2b] [HP3b HP4b]]].
    assert (repeat (tens (wn one) bot) (length l1b) = l1b /\ repeat (tens (wn one) bot) (length l3b) = l3b)
       as [Heql1b Heql3b]
       by now apply repeat_eq_app with n; symmetry;
          apply Permutation.Permutation_repeat, Permutation_Type_Permutation.
    assert (repeat (wn (tens (wn one) bot)) (length l2b) = l2b /\
            repeat (wn (tens (wn one) bot)) (length l4b) = l4b)
       as [Heql2b Heql4b]
       by now apply repeat_eq_app with m; symmetry;
          apply Permutation.Permutation_repeat, Permutation_Type_Permutation.
    rewrite <- Heql1b in HP1b, HP3b.
    rewrite <- Heql2b in HP2b, HP3b.
    rewrite <- Heql3b in HP1b, HP4b.
    rewrite <- Heql4b in HP2b, HP4b.
    clear Heql1b Heql2b Heql3b Heql4b.
    apply (Permutation_Type_app_head l2a) in HP4b.
    assert (IHP1 := Permutation_Type_trans HP2 HP4b).
    apply (@Permutation_Type_cons _ A _ eq_refl) in IHP1.
    rewrite app_comm_cons in IHP1.
    apply (Permutation_Type_app_head l1a) in HP3b.
    assert (IHP2 := Permutation_Type_trans HP1 HP3b).
    apply (@Permutation_Type_cons _ B _ eq_refl) in IHP2.
    rewrite app_comm_cons in IHP2.
    apply IHpi1 in IHP1.
    apply IHpi2 in IHP2.
    symmetry in HP3.
    apply (Permutation_Type_cons_app _ _ (tens A B)) in HP3.
    eapply ex_bbb_r; [ apply tens_bbb_r | apply HP3 ]; assumption.
  + dichot_elt_app_inf_exec Heq1; subst.
    * symmetry in Heq0. apply repeat_eq_app in Heq0 as [Heql0 Heq]; inversion Heq as [[HeqA HeqB Heql]]. subst.
      list_simpl in HP. rewrite <- Heql0, <- Heql in HP.
      rewrite (app_assoc (repeat _ _)), <- repeat_app in HP.
      remember (length l0 + length l) as k eqn:Heqk. clear Heqk Heql0 Heq Heql.
      apply Permutation_Type_app_app_inv in HP as [[[[l1a l2a] l3a] l4a] [[HP1 HP2] [HP3 HP4]]].
      apply Permutation_Type_app_app_inv in HP4 as [[[[l1b l2b] l3b] l4b] [[HP1b HP2b] [HP3b HP4b]]].
      assert (repeat (tens (wn one) bot) (length l1b) = l1b /\ repeat (tens (wn one) bot) (length l3b) = l3b)
         as [Heql1b Heql3b]
         by now apply repeat_eq_app with k; symmetry;
            apply Permutation.Permutation_repeat, Permutation_Type_Permutation.
      assert (repeat (wn (tens (wn one) bot)) (length l2b) = l2b /\
              repeat (wn (tens (wn one) bot)) (length l4b) = l4b)
         as [Heql2b Heql4b]
         by now apply repeat_eq_app with m; symmetry;
            apply Permutation.Permutation_repeat, Permutation_Type_Permutation.
      rewrite <- Heql1b in HP1b, HP3b.
      rewrite <- Heql2b in HP2b, HP3b.
      rewrite <- Heql3b in HP1b, HP4b.
      rewrite <- Heql4b in HP2b, HP4b.
      clear Heql1b Heql2b Heql3b Heql4b.
      apply (ex_r _ (repeat (tens (wn one) bot) (length l3b) ++ 
                     l2a ++ wn one :: repeat (wn (tens (wn one) bot)) (length l4b))) in pi1.
      2:{ cbn. etransitivity; [ apply Permutation_Type_cons; [ reflexivity | apply HP2 ] | ].
          rewrite app_comm_cons. etransitivity; [ apply Permutation_Type_app_head, HP4b | ].
          cons2app. rewrite ? app_assoc. apply Permutation_Type_app_tail. cbn.
          etransitivity; [ | apply Permutation_Type_cons_append ].
          apply Permutation_Type_cons; [ reflexivity | apply Permutation_Type_app_comm ]. }
      assert (ll pfrag_ll (l2a ++ wn one :: repeat (wn (tens (wn one) bot)) (length l3b + length l4b)))
        as pi1'.
      { rewrite repeat_app.
        apply (ex_r (repeat (wn (tens (wn one) bot)) (length l3b) ++ 
                     l2a ++ wn one :: repeat (wn (tens (wn one) bot)) (length l4b))).
      2:{ cbn. cons2app. rewrite ? app_assoc. apply Permutation_Type_app_tail.
          rewrite <- app_assoc. apply Permutation_Type_app_comm. }
        remember (l2a ++ wn one :: repeat (wn (tens (wn one) bot)) (length l4b)) as ld eqn:Heqld.
        remember (length l3b) as p eqn:Heqp.
        clear - pi1. induction p as [|p IHp] in ld, pi1 |- *; [ assumption | ].
        cbn; apply de_r.
        apply (ex_r (repeat (wn (tens (wn one) bot)) p ++ tens (wn one) bot :: ld));
          [ | cbn; symmetry; apply Permutation_Type_middle ].
        apply IHp.
        apply (ex_r (tens (wn one) bot :: repeat (tens (wn one) bot) p ++ ld));
          [ assumption | cbn; apply Permutation_Type_middle ]. }
      apply (Permutation_Type_app_head l1a) in HP3b.
      assert (IHP2 := Permutation_Type_trans HP1 HP3b).
      apply (@Permutation_Type_cons _ bot _ eq_refl) in IHP2.
      rewrite app_comm_cons in IHP2.
      apply IHpi2 in IHP2.
      assert (Permutation_Type (l2a ++ l1a) l') as HP'
        by (symmetry; transitivity (l1a ++ l2a); [ assumption | apply Permutation_Type_app_comm ]).
      eapply ex_bbb_r; [ apply mix2_bbb_r | apply HP' ].
      -- rewrite <- app_nil_l.
         eapply bot_rev_bbb; [ eassumption | reflexivity ].
      -- apply (stronger_pfrag (pmixupd_point_pfrag (pmixupd_point_pfrag pfrag_ll 0 true) 2 true)) ;
           [ | eapply ll_to_mix02'''_axcut ]; try reflexivity.
         ++ repeat split .
            ** intros a. exists a. reflexivity.
            ** intro nn. repeat (destruct nn; try reflexivity; try now constructor).
         ++ intros [].
         ++ intros _ [].
         ++ eapply ex_r in pi1'; [ | apply Permutation_Type_app_comm ]; eassumption.
    * symmetry in Heq2. apply repeat_eq_app in Heq2 as [_ Heq2]; discriminate Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP' as [[l'l l'r] Heq].
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_elt_app_inf_exec Heq; subst.
  + rewrite app_assoc in HP.
    apply (@Permutation_Type_cons _ B _ eq_refl) in HP.
    apply (@Permutation_Type_cons _ A _ eq_refl) in HP.
    rewrite 2 app_comm_cons in HP.
    apply IHpi in HP.
    eapply ex_bbb_r; [ apply parr_bbb_r; eassumption | apply Permutation_Type_middle ].
  + dichot_elt_app_inf_exec Heq1; subst.
    * symmetry in Heq0. apply repeat_eq_app in Heq0 as [_ Heq0]. discriminate Heq0.
    * symmetry in Heq2. apply repeat_eq_app in Heq2 as [_ Heq2]. discriminate Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP' as [[l'l l'r] Heq].
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_elt_app_inf_exec Heq; subst.
  + eapply ex_bbb_r; [ apply top_bbb_r | apply Permutation_Type_middle ].
  + dichot_elt_app_inf_exec Heq1; subst.
    * symmetry in Heq0. apply repeat_eq_app in Heq0 as [_ Heq0]. discriminate Heq0.
    * symmetry in Heq2. apply repeat_eq_app in Heq2 as [_ Heq2]. discriminate Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP' as [[l'l l'r] Heq].
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_elt_app_inf_exec Heq; subst.
  + rewrite app_assoc in HP.
    apply (@Permutation_Type_cons _ A _ eq_refl) in HP.
    rewrite app_comm_cons in HP.
    apply IHpi in HP.
    eapply ex_bbb_r; [ apply plus_bbb_r1; eassumption | apply Permutation_Type_middle ].
  + dichot_elt_app_inf_exec Heq1; subst.
    * symmetry in Heq0. apply repeat_eq_app in Heq0 as [_ Heq0]. discriminate Heq0.
    * symmetry in Heq2. apply repeat_eq_app in Heq2 as [_ Heq2]. discriminate Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP' as [[l'l l'r] Heq].
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_elt_app_inf_exec Heq; subst.
  + rewrite app_assoc in HP.
    apply (@Permutation_Type_cons _ A _ eq_refl) in HP.
    rewrite app_comm_cons in HP.
    apply IHpi in HP.
    eapply ex_bbb_r; [ apply plus_bbb_r2; eassumption | apply Permutation_Type_middle ].
  + dichot_elt_app_inf_exec Heq1; subst.
    * symmetry in Heq0. apply repeat_eq_app in Heq0 as [_ Heq0]. discriminate Heq0.
    * symmetry in Heq2. apply repeat_eq_app in Heq2 as [_ Heq2]. discriminate Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP' as [[l'l l'r] Heq].
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_elt_app_inf_exec Heq; subst.
  + rewrite app_assoc in HP.
    assert (HP2 := HP).
    apply (@Permutation_Type_cons _ A _ eq_refl) in HP.
    rewrite app_comm_cons in HP.
    apply IHpi1 in HP.
    apply (@Permutation_Type_cons _ B _ eq_refl) in HP2.
    rewrite app_comm_cons in HP2.
    apply IHpi2 in HP2.
    eapply ex_bbb_r; [ apply with_bbb_r | apply Permutation_Type_middle ]; assumption.
  + dichot_elt_app_inf_exec Heq1; subst.
    * symmetry in Heq0. apply repeat_eq_app in Heq0 as [_ Heq0]. discriminate Heq0.
    * symmetry in Heq2. apply repeat_eq_app in Heq2 as [_ Heq2]. discriminate Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP' as [[l'l l'r] Heq].
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_elt_app_inf_exec Heq; subst.
  + symmetry in HP.
    apply Permutation_Type_map_inv in HP as [l' Heq HP].
    symmetry in Heq. decomp_map_inf Heq; cbn in Heq1, Heq2, Heq3, Heq5; subst; cbn in HP.
    apply (Permutation_Type_map wn) in HP.
    list_simpl in HP.
    rewrite app_assoc, <- map_app in HP.
    apply (@Permutation_Type_cons _ A _ eq_refl) in HP.
    rewrite app_comm_cons, Heq2, Heq5 in HP.
    apply IHpi in HP.
    eapply ex_bbb_r;
      [ apply oc_bbb_r; eassumption | list_simpl; apply Permutation_Type_middle ].
  + dichot_elt_app_inf_exec Heq1; subst.
    * symmetry in Heq0. apply repeat_eq_app in Heq0 as [_ Heq0]. discriminate Heq0.
    * symmetry in Heq2. apply repeat_eq_app in Heq2 as [_ Heq2]. discriminate Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP' as [[l'l l'r] Heq].
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_elt_app_inf_exec Heq; subst.
  + rewrite app_assoc in HP.
    apply (@Permutation_Type_cons _ A _ eq_refl) in HP.
    rewrite app_comm_cons in HP.
    apply IHpi in HP.
    eapply ex_bbb_r; [ apply de_bbb_r; eassumption | apply Permutation_Type_middle ].
  + dichot_elt_app_inf_exec Heq1; subst.
    * symmetry in Heq0. apply repeat_eq_app in Heq0 as [_ Heq0]. discriminate Heq0.
    * symmetry in Heq2. apply repeat_eq_app in Heq2 as [Heq Heq2]; inversion Heq2 as [[Heq0 Heq1]]; subst.
      rewrite <- Heq, <- Heq1 in HP.
      apply (@Permutation_Type_cons _ (tens (wn one) bot) _ eq_refl) in HP.
      assert (Permutation_Type (tens (wn one) bot :: l)
                               (l' ++ repeat (tens (wn one) bot) (S n)
                                   ++ repeat (wn (tens (wn one) bot)) (length l2 + length l'r))) as HP'.
      { etransitivity; [ apply HP | ].
        cbn. rewrite repeat_app. apply Permutation_Type_cons_app. list_simpl. reflexivity. }
      exact (IHpi _ _ _ HP').
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP' as [[l'l l'r] Heq].
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_elt_app_inf_exec Heq; subst.
  + rewrite app_assoc in HP.
    apply IHpi in HP.
    eapply ex_bbb_r; [ apply wk_bbb_r; eassumption | apply Permutation_Type_middle ].
  + dichot_elt_app_inf_exec Heq1; subst.
    * symmetry in Heq0. apply repeat_eq_app in Heq0 as [_ Heq0]. discriminate Heq0.
    * symmetry in Heq2. apply repeat_eq_app in Heq2 as [Heq Heq2]; inversion Heq2 as [[Heq0 Heq1]]; subst.
      list_simpl in HP. rewrite <- Heq, <- Heq1, <- repeat_app in HP.
      apply IHpi in HP. assumption.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP' as [[l'l l'r] Heq].
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_elt_app_inf_exec Heq; subst.
  + rewrite app_assoc in HP.
    apply (@Permutation_Type_cons _ (wn A) _ eq_refl) in HP.
    apply (@Permutation_Type_cons _ (wn A) _ eq_refl) in HP.
    rewrite 2 app_comm_cons in HP.
    apply IHpi in HP.
    eapply ex_bbb_r; [ apply co_bbb_r; eassumption | apply Permutation_Type_middle ].
  + dichot_elt_app_inf_exec Heq1; subst.
    * symmetry in Heq0. apply repeat_eq_app in Heq0 as [_ Heq0]. discriminate Heq0.
    * symmetry in Heq2. apply repeat_eq_app in Heq2 as [Heq Heq2]; inversion Heq2 as [[Heq0 Heq1]]; subst.
      list_simpl in HP; rewrite <- Heq, <- Heq1, <- repeat_app in HP.
      apply (@Permutation_Type_cons _ (wn (tens (wn one) bot)) _ eq_refl) in HP.
      apply (@Permutation_Type_cons _ (wn (tens (wn one) bot)) _ eq_refl) in HP.
      apply (@Permutation_Type_trans _ (wn (tens (wn one) bot) ::
                                        wn (tens (wn one) bot) :: l)) in HP; [ | reflexivity ].
      assert (Permutation_Type (wn (tens (wn one) bot) :: wn (tens (wn one) bot) :: l)
         (l' ++ repeat (tens (wn one) bot) n ++
                repeat (wn (tens (wn one) bot)) (S (S (length l2 + length l'r)))))
        as HP'.
      { etransitivity; [ apply HP | ].
        cbn. cons2app. rewrite ? app_assoc. apply Permutation_Type_app_tail.
        list_simpl. cons2app. rewrite app_assoc. etransitivity; [ apply Permutation_Type_app_comm | ].
        list_simpl. reflexivity. }
      exact (IHpi _ _ _ HP').
- discriminate f.
- destruct a.
Qed.

(** ** Cut admissibility for [ll_bbb] *)

Theorem cut_bbb_r A l1 l2 : ll_bbb (dual A :: l1) -> ll_bbb (A :: l2) -> ll_bbb (l2 ++ l1).
Proof.
intros pi1%bbb_to_ll pi2%bbb_to_ll.
eapply ex_r in pi1; [ | apply Permutation_Type_swap ].
eapply ex_r in pi2; [ | apply Permutation_Type_swap ].
apply (cut_ll_r pi1) in pi2.
apply (ex_r _ ((l2 ++ l1) ++ repeat (tens (wn one) bot) 0 ++ repeat (wn (tens (wn one) bot)) 2)) in pi2.
2:{  etransitivity; [ apply Permutation_Type_cons_append | ].
     list_simpl. apply Permutation_Type_app_head, Permutation_Type_middle. }
eapply ll_to_bbb in pi2; [ eassumption | reflexivity ].
Qed.


(** ** Comparison with LL + [bot = oc bot] *)

Lemma mix2_bb_r l1 l2 : llR (oc bot) l1 -> llR (oc bot) l2 -> llR (oc bot) (l2 ++ l1).
Proof.
intros pi1 pi2.
assert (forall C, pcut (pfrag_llR (oc bot : formula)) C = true) as Hcut by reflexivity.
apply (cut_r one (Hcut _)).
- apply bot_r. assumption.
- cons2app. apply (cut_r (oc bot) (Hcut _)).
  + apply wk_r. assumption.
  + apply (@gax_r _ (pfrag_llR (oc bot)) false).
Qed.

Lemma mix2_to_bb l : ll_mix2 l -> llR (oc bot) l.
Proof.
intros pi. induction pi using ll_nested_ind;
  try (now constructor); try (econstructor; eassumption); try now econstructor.
repeat (destruct L; try now discriminate eqpmix).
cbn. rewrite app_nil_r.
apply mix2_bb_r.
- assert (In_inf l0 (l :: l0 :: nil)) as Hin by (right; left; reflexivity).
  apply (In_Forall_inf_in _ PL) in Hin as [pi Hin].
  apply (Dependent_Forall_inf_forall_formula _ _ X Hin).
- assert (In_inf l (l :: l0 :: nil)) as Hin by now left.
  apply (In_Forall_inf_in _ PL) in Hin as [pi Hin].
  apply (Dependent_Forall_inf_forall_formula _ _ X Hin).
Qed.

Theorem bb_to_bbb l : llR (oc bot) l -> ll_bbb l.
Proof.
intros pi. induction pi; try (constructor; assumption).
- econstructor; eassumption.
- eapply ex_bbb_r; [ eassumption | ].
  apply Permutation_Type_app_head, Permutation_Type_app_tail, Permutation_Type_map, p.
- discriminate f.
- eapply cut_bbb_r; eassumption.
- destruct a; cbn.
  + apply de_bbb_r, one_bbb_r.
  + rewrite <- (app_nil_l (one :: _)), app_comm_cons.
    apply mix2_bbb_r.
    * apply one_bbb_r.
    * change nil with (map (@wn atom) nil).
      apply oc_r, bot_r.
      change (map wn nil) with (concat (@nil (list formula))).
      apply mix_r; constructor.
Qed.

(** The converse of [bb_to_bbb] is proved in the [nn] library. *)

(** *** Examples *)
(*
Goal ll_bbb (one :: oc (parr one one) :: nil).
Proof.
change (one :: oc (parr one one) :: nil)
  with ((one :: nil) ++ oc (parr one one) :: nil : list formula).
apply mix2_bbb_r.
- change nil with (map wn nil : list formula).
  apply oc_bbb_r, parr_bbb_r.
  cbn. change (one :: one :: nil) with ((one :: nil) ++ one :: nil : list formula).
  apply mix2_bbb_r; [ apply one_bbb_r | apply one_r ].
- apply one_r.
Qed.

Goal llR (oc bot) (one :: oc (parr one one) :: nil).
Proof.
assert (llR (oc bot) ((one :: nil) ++ one :: nil)) as Hr by (eapply mix2_bb_r; apply one_r).
change (one :: oc (parr one one) :: nil)
  with ((one :: nil) ++ oc (parr one one) :: nil : list formula).
apply mix2_bb_r.
- change nil with (map wn nil : list formula).
  apply oc_r, parr_r. assumption.
- apply one_r.
Qed.
*)

Example bbb_ex : ll_bbb (one :: oc (tens (parr one one) bot) :: nil).
Proof.
change (one :: oc (tens (parr one one) bot) :: nil)
  with ((@one atom :: nil) ++ (oc (tens (parr one one) bot) :: nil)).
apply (ex_bbb_r ((oc (tens (parr one one) bot) :: nil) ++ one :: nil)); [ | apply Permutation_Type_swap ].
apply mix2_bbb_r.
- apply one_bbb_r.
- change (oc (tens (parr one one) bot) :: nil)
    with (@oc atom (tens (parr one one) bot) :: map wn (nil ++ nil)).
  apply oc_r.
  rewrite map_app. apply tens_r.
  + apply parr_r.
    cbn. change (one :: one :: nil) with (concat ((@one atom :: nil) :: (one :: nil) :: nil)).
    apply mix_r; [ reflexivity | ].
    repeat constructor.
  + apply bot_r.
    change (map wn nil) with (concat (@nil (list formula))).
    apply mix_r; constructor.
Qed.

Example bb_ex : llR (oc bot) (one :: oc (tens (parr one one) bot) :: nil).
Proof.
assert (Hax := @gax_r _ (@pfrag_llR atom (oc bot)) false); cbn in Hax.
assert (llR (oc bot) ((one :: nil) ++ one :: nil)) as Hr by (eapply mix2_bb_r; apply one_r).
refine (cut_r _ _ _ Hax).
- reflexivity.
- eapply ex_r; [ | apply Permutation_Type_swap ].
  cbn. change (wn one :: nil) with (map (@wn atom) (one :: nil)).
  apply oc_r.
  cbn. rewrite <- (app_nil_l nil), app_comm_cons. apply tens_r.
  + apply parr_r. assumption.
  + apply bot_r, de_r, one_r.
Qed.


(** ** Additional results on a weakened version of [ll_bbb]
 without [mix2] above [mix2] on the [mix0] side *)
Inductive ll_bbb0 : list formula -> Type :=
| ax_bbb0_r X : ll_bbb0 (covar X :: var X :: nil)
| ex_bbb0_r l1 l2 : ll_bbb0 l1 -> Permutation_Type l1 l2 -> ll_bbb0 l2
| mix2_bbb0_r l1 l2 : ll_bbb0 l1 -> ll_mix0 l2 -> ll_bbb0 (l2 ++ l1)
| one_bbb0_r : ll_bbb0 (one :: nil)
| bot_bbb0_r l : ll_bbb0 l -> ll_bbb0 (bot :: l)
| tens_bbb0_r A B l1 l2 : ll_bbb0 (A :: l1) -> ll_bbb0 (B :: l2) -> ll_bbb0 (tens A B :: l2 ++ l1)
| parr_bbb0_r A B l : ll_bbb0 (A :: B :: l) -> ll_bbb0 (parr A B :: l)
| top_bbb0_r l : ll_bbb0 (top :: l)
| plus_bbb0_r1 A B l : ll_bbb0 (A :: l) -> ll_bbb0 (aplus A B :: l)
| plus_bbb0_r2 A B l : ll_bbb0 (A :: l) -> ll_bbb0 (aplus B A :: l)
| with_bbb0_r A B l : ll_bbb0 (A :: l) -> ll_bbb0 (B :: l) -> ll_bbb0 (awith A B :: l)
| oc_bbb0_r A l : ll_bbb0 (A :: map wn l) -> ll_bbb0 (oc A :: map wn l)
| de_bbb0_r A l : ll_bbb0 (A :: l) -> ll_bbb0 (wn A :: l)
| wk_bbb0_r A l : ll_bbb0 l -> ll_bbb0 (wn A :: l)
| co_bbb0_r A l : ll_bbb0 (wn A :: wn A :: l) -> ll_bbb0 (wn A :: l).

(** The example given above in [ll_bbb] and [llR (oc bot)] is not cut-free provable
    in [ll_bbb0]. *)
Lemma mix0_bbb0_false : notT (ll_bbb0 nil).
Proof.
intros pi.
remember nil as l eqn:Heql. induction pi in Heql |- *; inversion Heql; subst.
- symmetry in p. now apply Permutation_Type_nil in p.
- now apply app_eq_nil in Heql as [-> ->].
Qed.

Lemma ex_implies_mix2_mix02 l : ll_bbb0 l -> Permutation_Type l (one :: oc (tens (parr one one) bot) :: nil) ->
  @ll_mix0 atom (one :: one :: nil).
Proof.
intros pi. induction pi; intro HP;
  try now (apply Permutation_Type_sym, Permutation_Type_length_2_inv in HP as [HP | HP];
           discriminate HP).
- apply IHpi. etransitivity; eassumption.
- apply Permutation_Type_sym, Permutation_Type_length_2_inv in HP as [HP | HP].
  + symmetry in HP.
    rewrite <- (app_nil_l (one :: _)) in HP.
    dichot_elt_app_inf_exec HP; subst.
    * apply eq_sym in HP1.
      apply app_eq_unit_inf in HP1 as [[-> ->] | [-> ->]].
      -- clear - pi. exfalso.
         remember (oc (tens (parr one one) bot) :: nil) as l.
         induction pi in Heql |- *; inversion Heql; subst.
         ++ symmetry in p.
            apply Permutation_Type_length_1_inv in p.
            apply IHpi. assumption.
         ++ apply app_eq_unit in Heql as [[-> ->] | [-> ->]].
            ** apply IHpi. reflexivity.
            ** apply mix0_bbb0_false. assumption.
         ++ rewrite ? H1 in *. clear - pi.
            remember (tens (parr one one) bot :: nil) as l.
            induction pi in Heql |- *; inversion Heql; subst.
            ** symmetry in p.
               apply Permutation_Type_length_1_inv in p.
               apply IHpi; assumption.
            ** apply app_eq_unit in Heql as [[-> ->] | [-> ->]].
               --- apply IHpi. reflexivity.
               --- apply mix0_bbb0_false. assumption.
            ** apply app_eq_nil in H2 as [-> ->].
               clear - pi2. remember (bot :: nil) as l.
               induction pi2 in Heql |- *; inversion Heql; subst.
               --- symmetry in p.
                   apply Permutation_Type_length_1_inv in p as ->.
                   apply IHpi2. reflexivity.
               --- apply app_eq_unit in Heql as [[-> ->] | [-> ->]].
                   +++ apply IHpi2. reflexivity.
                   +++ apply mix0_bbb0_false. assumption.
               --- apply mix0_bbb0_false. assumption.
      -- exfalso. apply mix0_bbb0_false. assumption.
    * symmetry in HP0. apply app_eq_nil in HP0 as [-> ->].
      apply IHpi. reflexivity.
  + symmetry in HP.
    rewrite <- (app_nil_l (oc _::_)) in HP.
    dichot_elt_app_inf_exec HP; subst.
    * symmetry in HP1. apply app_eq_unit_inf in HP1 as [[-> ->] | [-> ->]].
      -- clear - l. rename l into pi. cbn in pi.
         remember (oc (tens (parr one one) bot) :: nil) as l.
         induction pi in Heql |- *; inversion Heql; subst.
         ++ symmetry in p. cbn in p.
            apply Permutation_Type_length_1_inv in p as ->.
            apply IHpi. reflexivity.
         ++ destruct l1; inversion Heql.
            ** destruct lw'; inversion Heql. cbn in H. subst.
               symmetry in p. apply Permutation_Type_nil in p as ->. apply IHpi. reflexivity.
            ** apply app_eq_nil in H2 as [-> [Heq2 ->]%app_eq_nil].
               destruct lw'; inversion Heq2. subst.
               symmetry in p. apply Permutation_Type_nil in p as ->. apply IHpi. reflexivity.
         ++ repeat (destruct L; inversion f; try discriminate).
         ++ rewrite ? H1 in *. clear - pi.
            remember (tens (parr one one) bot :: nil) as l.
            induction pi in Heql |- *; inversion Heql; subst.
            ** symmetry in p. cbn in p.
               apply Permutation_Type_length_1_inv in p as ->. apply IHpi. reflexivity.
            ** destruct l1; inversion Heql.
               --- destruct lw'; inversion Heql.
                   symmetry in p. apply Permutation_Type_nil in p as ->. apply IHpi. assumption.
               --- apply app_eq_nil in H2 as [-> [Heq2 ->]%app_eq_nil].
                   destruct lw'; inversion Heq2. subst.
                   symmetry in p. apply Permutation_Type_nil in p as ->. apply IHpi. reflexivity.
            ** repeat (destruct L; inversion f; try discriminate).
            ** apply app_eq_nil in H2 as [-> ->].
               clear - pi1.
               remember (parr one one :: nil) as l.
               induction pi1 in Heql |- *; inversion Heql; subst.
               --- symmetry in p. cbn in p.
                   apply Permutation_Type_length_1_inv in p as ->.
                   apply IHpi1. reflexivity.
               --- destruct l1; inversion Heql.
                   +++ destruct lw'; inversion Heql. subst.
                       symmetry in p. apply Permutation_Type_nil in p as ->. apply IHpi1. assumption.
                   +++ apply app_eq_nil in H2 as [-> [Heq2 ->]%app_eq_nil].
                       destruct lw'; inversion Heq2. subst.
                       symmetry in p. apply Permutation_Type_nil in p as ->. apply IHpi1. reflexivity.
               --- repeat (destruct L; inversion f; try discriminate).
               --- assumption.
               --- discriminate f.
               --- destruct a.
            ** discriminate f.
            ** destruct a.
         ++ discriminate f.
         ++ destruct a.
      -- exfalso. apply mix0_bbb0_false. assumption.
    * symmetry in HP0.
      apply app_eq_nil in HP0 as [-> ->].
      apply IHpi, Permutation_Type_swap.
- symmetry in HP.
  apply Permutation_Type_length_2_inv in HP as [HP | HP] ; inversion HP.
  destruct l; discriminate H1.
Qed.

Lemma ex_not_bbb0 : notT (ll_bbb0 (one :: oc (tens (parr one one) bot) :: nil)).
Proof.
intros pi.
apply (@mix0_not_mix2 atom).
eapply ex_implies_mix2_mix02; [ eassumption | reflexivity ].
Qed.

Lemma bbb_neq_bbb0 : { l & ll_bbb l & notT (ll_bbb0 l) }.
Proof. eexists; [ apply bbb_ex | apply ex_not_bbb0 ]. Qed.

(** The same example is provable in [ll_bbb0] with cut,
    thus cut admissibility does not hold for [ll_bbb0]. *)

Section bbb0_with_cut.

Variable cut_bbb0_r : forall A l1 l2, ll_bbb0 (dual A :: l1) -> ll_bbb0 (A :: l2) -> ll_bbb0 (l2 ++ l1).

Theorem llR_oc_bot_to_bbb0_cut l : llR (oc bot) l -> ll_bbb0 l.
Proof.
intros pi. induction pi; (try discriminate); try now constructor.
- eapply ex_bbb0_r; eassumption.
- eapply ex_bbb0_r; [ eassumption | ].
  apply Permutation_Type_app_head, Permutation_Type_app_tail, Permutation_Type_map, p.
- eapply cut_bbb0_r; eassumption.
- destruct a; cbn.
  + apply de_bbb0_r, one_bbb0_r.
  + rewrite <- (app_nil_l (one :: _)), app_comm_cons. apply mix2_bbb0_r.
    * apply one_bbb0_r.
    * change nil with (map (@wn atom) nil).
      apply oc_r, bot_r.
      change (map wn nil) with (concat (@nil (list formula))).
      apply mix_r; constructor.
Qed.

Example bbb0_cut_ex : ll_bbb0 (one :: oc (tens (parr one one) bot) :: nil).
Proof. apply llR_oc_bot_to_bbb0_cut, bb_ex. Qed.

End bbb0_with_cut.

Lemma cut_not_rule_bbb0 :
  notT (forall A l1 l2, ll_bbb0 (dual A :: l1) -> ll_bbb0 (A :: l2) -> ll_bbb0 (l2 ++ l1)).
Proof. intros Hcut. apply ex_not_bbb0, bbb0_cut_ex, Hcut. Qed.

End Atoms.
