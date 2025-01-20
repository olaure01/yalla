(** * Example of a concrete use of the yalla library: tensorial logic *)

Set Implicit Arguments.


(** ** 0. load the [ill] library *)

From Yalla Require Import List_more Permutation_Type_more ill_cut.
Import ListNotations.


(** ** 1. define formulas *)

(* Tensorial formulas *)
Inductive tformula :=
| tvar (_ : yalla_ax.Atom) | ttens (_ _ : tformula) | tone
| tneg (_ : tformula) | tbot.


(** ** 2. define embedding into [iformula] *)

Fixpoint t2i A :=
match A with
| tvar X => ivar (yalla_ax.a2i X)
| ttens A B => itens (t2i A) (t2i B)
| tone => ione
| tneg A => ineg (t2i A)
| tbot => N
end.


(** ** 3. define proofs *)

Inductive tl : list tformula -> tformula -> Type :=
| ax_tr A : tl [A] A
| cut_tr A l0 l1 l2 B : tl l0 A -> tl (l1 ++ A :: l2) B -> tl (l1 ++ l0 ++ l2) B
| neg_trr A l : tl (A :: l) tbot -> tl l (tneg A)
| neg_tlr A l : tl l A -> tl (l ++ [tneg A]) tbot
| tens_trr A B l1 l2 : tl l1 A -> tl l2 B -> tl (l1 ++ l2) (ttens A B)
| tens_tlr A B l1 l2 C : tl (l1 ++ A :: B :: l2) C -> tl (l1 ++ ttens A B :: l2) C
| one_trr : tl [] tone
| one_tlr l1 l2 A : tl (l1 ++ l2) A ->tl (l1 ++ tone :: l2) A
| ex_tr A B l1 l2 C : tl (l1 ++ A :: B :: l2) C -> tl (l1 ++ B :: A :: l2) C.
Arguments cut_tr [_ _ _ _ _] _ _, _ [_ _ _ _] _ _, _ _ _ _ _ _ _.
Arguments tens_tlr [_ _ _ _ _] _.
Arguments one_tlr [_ _ _] _.
Arguments ex_tr [_ _ _ _ _] _.

Fixpoint cut_free_tl l A (pi : tl l A) :=
match pi with
| ax_tr _ | one_trr => true
| cut_tr _ _ => false
| neg_trr pi1 | neg_tlr pi1 | tens_tlr pi1| one_tlr pi1 | ex_tr pi1 => cut_free_tl pi1
| tens_trr pi1 pi2 => andb (cut_free_tl pi1) (cut_free_tl pi2)
end.


(** ** 4. characterize corresponding [ill] fragment *)

(* already defined as [ill_ll] *)


(** ** 5. prove equivalence of proof predicates *)

Lemma tl2ill l C : tl l C -> ill_ll (map t2i l) (t2i C).
Proof.
intro pi. induction pi; list_simpl in *; try now constructor.
- apply ax_exp_ill.
- apply (cut_ll_ir _ _ _ _ _ IHpi1 IHpi2).
- apply (ex_ir _ _ _ _ IHpi).
  cbn. apply Permutation_Type_app_head. constructor.
Qed.

Lemma ill2tl l C : ill_ll (map t2i l) (t2i C) -> { pi : tl l C | cut_free_tl pi = true }.
Proof.
intro pi.
remember (map t2i l) as l0 eqn:Hl.
remember (t2i C) as D eqn:HC.
induction pi in l, C, Hl, HC |- *; subst;
  try (destruct C; discriminate HC);
  try (decomp_map Hl; destruct x; discriminate Heq).
- destruct l as [ | A [ | ] ]; inversion Hl; subst.
  destruct C, A; inversion HC; inversion H0; subst.
  + apply (f_equal yalla_ax.i2a) in H2.
    rewrite ! yalla_ax.a2a_i in H2. subst.
    exists (ax_tr _). reflexivity.
  + discriminate H2.
  + discriminate H2.
  + exists (ax_tr _). reflexivity.
- cbn in p. apply Permutation_Type_map_inv in p as [l' -> p]. symmetry in p.
  apply perm_perm_t_Type in p.
  destruct (IHpi _ _ eq_refl eq_refl) as [IH Hc].
  clear - p IH Hc. induction p in IH, Hc |- *.
  + exists IH. assumption.
  + exists (ex_tr IH). cbn. assumption.
  + destruct (IHp1 _ Hc) as [pi' Hc'].
    apply (IHp2 _ Hc').
- decomp_map Hl. destruct lw' as [ | w lw' ].
  + symmetry in p. apply Permutation_Type_nil in p as ->.
    destruct l4; inversion Heq. subst.
    now apply IHpi; list_simpl.
  + destruct l4; inversion Heq.
    destruct t; inversion H0.
- destruct l as [ | A [ | ] ]; inversion Hl; subst.
  destruct C; inversion HC; subst.
  exists one_trr. reflexivity.
- decomp_map Hl; destruct x; destr_eq Heq; subst.
  specialize (IHpi (l1 ++ l2) C). list_simpl in IHpi.
  destruct (IHpi eq_refl eq_refl) as [IH Hc].
  exists (one_tlr IH). cbn. assumption.
- decomp_map Hl. destruct C; inversion HC. subst.
  destruct (IHpi1 _ _ eq_refl eq_refl) as [IH1 Hc1].
  destruct (IHpi2 _ _ eq_refl eq_refl) as [IH2 Hc2].
  exists (tens_trr IH1 IH2). cbn. rewrite Hc1, Hc2. reflexivity.
- decomp_map Hl; destruct x; destr_eq Heq; subst.
  specialize (IHpi (l1 ++ x1 :: x2 :: l2) C). list_simpl in IHpi.
  destruct (IHpi eq_refl eq_refl) as [IH Hc].
  exists (tens_tlr IH). cbn. assumption.
- destruct C; inversion HC. subst.
  specialize (IHpi (C :: l) tbot). list_simpl in IHpi.
  destruct (IHpi eq_refl eq_refl) as [IH Hc].
  exists (neg_trr IH). cbn. assumption.
- decomp_map Hl. destruct Heq as [Heq Hll]. destruct x; destr_eq Heq. subst.
  destruct C; inversion HC.
  apply map_eq_nil in Hll as ->.
  destruct (IHpi _ _ eq_refl eq_refl) as [IH Hc].
  exists (neg_tlr IH). cbn. assumption.
- discriminate f.
- destruct a.
Qed.


(** ** 6. import properties *)

(** *** cut admissibility *)

Lemma cut_admissibility_tl l A : tl l A -> { pi : tl l A | cut_free_tl pi = true }.
Proof. intros pi%tl2ill%ill2tl. assumption. Qed.


(** ** 7. prove additional properties *)

Lemma tbot_tneg_tone : tl [tbot] (tneg tone).
Proof. apply neg_trr, (@one_tlr nil), ax_tr. Qed.

Lemma tneg_tone_tbot : tl [tneg tone] tbot.
Proof. apply (@neg_tlr _ nil), one_trr. Qed.

Lemma double_neg_intro A : tl [A] (tneg (tneg A)).
Proof. apply neg_trr, (@ex_tr _ _ nil), (@neg_tlr _ [A]), ax_tr. Qed.

Lemma triple_tneg_elim A : tl [tneg (tneg (tneg A))] (tneg A).
Proof.
apply neg_trr, (@neg_tlr _ [A]).
apply neg_trr, (@ex_tr _ _ nil), (@neg_tlr _ [A]).
apply ax_tr.
Qed.

Fixpoint bot_neg_free A :=
match A with
| tbot | tneg _ => false
| ttens A B => andb (bot_neg_free A) (bot_neg_free B)
| _ => true
end.

Lemma neg_neg_elim_is_bot_neg A :
  tl [tneg (tneg A)] A -> bot_neg_free A = false.
Proof.
intro pi. destruct (cut_admissibility_tl pi) as [pi0 Hc]. clear pi.
remember (tneg A) as B eqn:HB. clear HB.
remember [tneg B] as l eqn:Hl.
induction pi0 in Hc, Hl |- *; subst; try reflexivity.
- injection Hl as [= Hl]. subst. reflexivity.
- discriminate Hc.
- cbn. apply Bool.andb_false_iff.
  cbn in Hc. apply andb_prop in Hc.
  destruct l1 as [ | C l1 ].
  + cbn in Hl. subst.
    right. now apply IHpi0_2.
  + injection Hl as [= -> Hl].
    apply app_eq_nil in Hl as [-> ->].
    left. now apply IHpi0_1.
- destruct l1; inversion Hl. nil_vs_elt_inv H1.
- discriminate Hl.
- destruct l1; inversion Hl. nil_vs_elt_inv H1.
- destruct l1; inversion Hl. injection Hl as [= ? Hl]. nil_vs_elt_inv Hl.
Qed.
