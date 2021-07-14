(* formulas library for yalla *)

From Coq Require Import Bool List EqNat RelationClasses Lia.
From OLlibs Require Import funtheory dectype.
From Yalla Require Export atoms.

Set Implicit Arguments.

(** * Linear Logic formulas *)

Section Atoms.

(** A set of atoms for building formulas *)
Context {atom : DecType}.

(** ** Definition and main properties of formulas *)

(** Formulas *)
Inductive formula :=
| var : atom -> formula
| covar : atom -> formula
| one : formula
| bot : formula
| tens : formula -> formula -> formula
| parr : formula -> formula -> formula
| zero : formula
| top : formula
| aplus : formula -> formula -> formula
| awith : formula -> formula -> formula
| oc : formula -> formula
| wn : formula -> formula.


(** n-ary operators *)

Fixpoint tens_n n A :=
match n with
| 0 => one
| 1 => A
| S n => tens (tens_n n A) A
end.

Fixpoint parr_n n A :=
match n with
| 0 => bot
| 1 => A
| S n => parr A (parr_n n A)
end.

Fixpoint wn_n n A :=
match n with
| 0 => A
| S n => wn (wn_n n A)
end.

Lemma wn_n_wn n A : wn_n n (wn A) = wn_n (S n) A.
Proof. induction n; [ | cbn in *; rewrite IHn ]; reflexivity. Qed.

Fixpoint oc_n n A :=
match n with
| 0 => A
| S n => oc (oc_n n A)
end.

Lemma oc_n_oc n A : oc_n n (oc A) = oc_n (S n) A.
Proof. induction n; [ | cbn in *; rewrite IHn ]; reflexivity. Qed.


(** Orthogonal / dual of a [formula] *)

(** (the dual of [tens] and [parr] is the one compatible with non-commutative systems) *)
Fixpoint dual A :=
match A with
| var x => covar x
| covar x => var x
| one => bot
| bot => one
| tens A B  => parr (dual B) (dual A)
| parr A B  => tens (dual B) (dual A)
| zero => top
| top => zero
| aplus A B => awith (dual A) (dual B)
| awith A B => aplus (dual A) (dual B)
| oc A => wn (dual A)
| wn A => oc (dual A)
end.

Lemma bidual A : dual (dual A) = A.
Proof. now induction A; cbn; rewrite ? IHA1, ? IHA2, ? IHA. Qed.

Lemma codual A B : dual A = B <-> A = dual B.
Proof. now split; intro H; rewrite <- (bidual A), <- (bidual B), H, ? bidual. Qed.

Lemma dual_inj : injective dual.
Proof. now intros A B H; rewrite <- (bidual A), <- (bidual B), H. Qed.

Lemma dual_tens_n n A : dual (tens_n n A) = parr_n n (dual A).
Proof. induction n as [|[|n] IHn]; [ | | cbn in *; rewrite <- IHn ]; reflexivity. Qed.

Lemma dual_parr_n n A : dual (parr_n n A) = tens_n n (dual A).
Proof. induction n as [|[|n] IHn]; [ | | cbn in *; rewrite <- IHn ]; reflexivity. Qed.

Lemma dual_wn_n n A : dual (wn_n n A) = oc_n n (dual A).
Proof. induction n as [|[|n] IHn]; [ | | cbn in *; rewrite <- IHn ]; reflexivity. Qed.

Lemma dual_oc_n n A : dual (oc_n n A) = wn_n n (dual A).
Proof. induction n as [|[|n] IHn]; [ | | cbn in *; rewrite <- IHn ]; reflexivity. Qed.

(** Size of a [formula] as its number of symbols *)
Fixpoint fsize A :=
match A with
| var X | covar X => 1
| one | bot | zero | top => 1
| tens A B | parr A B | aplus A B | awith A B => S (fsize A + fsize B)
| oc A | wn A => S (fsize A)
end.

Lemma fsize_pos A : 0 < fsize A.
Proof. induction A; cbn; lia. Qed.

Lemma fsize_dual A : fsize (dual A) = fsize A.
Proof. induction A; cbn; rewrite ? IHA1, ? IHA2; lia. Qed.

Lemma fsize_wn_n n A : fsize (wn_n n A) = n + fsize A.
Proof. induction n; [ | cbn; rewrite IHn ]; reflexivity. Qed.

Lemma fsize_oc_n n A : fsize (oc_n n A) = n + fsize A.
Proof. induction n; [ | cbn; rewrite IHn ]; reflexivity. Qed.

Ltac fsize_auto :=
cbn; repeat rewrite fsize_dual; cbn;
match goal with
| H: fsize _ < _ |- _ => cbn in H
| H: fsize _ <= _ |- _ => cbn in H
| H: fsize _ = _ |- _ => cbn in H
end; lia.

(** Atomic [formula] *)
Inductive atomic : formula -> Type :=
| atomic_var : forall x, atomic (var x)
| atomic_covar : forall x, atomic (covar x).

(* Unused
Inductive atomic_Prop : formula -> Prop :=
| atomic_Prop_var : forall x, atomic_Prop (var x)
| atomic_Prop_covar : forall x, atomic_Prop (covar x).

Lemma atomic_Prop_atomic A : atomic_Prop A -> atomic A.
Proof.
induction A; intros Hat;
  try (now exfalso; inversion Hat);
  now constructor.
Qed.
*)


(** ** Sub-formulas *)

(** First argument is a sub-formula of the second: *)
Inductive subform : formula -> formula -> Prop :=
| sub_id : forall A, subform A A
| sub_tens_l : forall A B C, subform A B -> subform A (tens B C)
| sub_tens_r : forall A B C, subform A B -> subform A (tens C B)
| sub_parr_l : forall A B C, subform A B -> subform A (parr B C)
| sub_parr_r : forall A B C, subform A B -> subform A (parr C B)
| sub_plus_l : forall A B C, subform A B -> subform A (aplus B C)
| sub_plus_r : forall A B C, subform A B -> subform A (aplus C B)
| sub_with_l : forall A B C, subform A B -> subform A (awith B C)
| sub_with_r : forall A B C, subform A B -> subform A (awith C B)
| sub_oc : forall A B, subform A B -> subform A (oc B)
| sub_wn : forall A B, subform A B -> subform A (wn B).

Lemma sub_trans A B C : subform A B -> subform B C -> subform A C.
Proof.
intros Hl Hr; revert A Hl; induction Hr; intros A' Hl;
  try (constructor; apply IHHr); assumption.
Qed.

Global Instance sub_po : PreOrder subform | 50.
Proof. split; repeat intro; [ apply sub_id | eapply sub_trans; eassumption ]. Qed.

(** Each element of the first list is a sub-formula of some element of the second. *)
Definition subform_list l1 l2 := Forall (fun A => Exists (subform A) l2) l1.

Lemma sub_id_list l l0 : subform_list l (l0 ++ l).
Proof.
revert l0; induction l; intros l0; constructor.
- induction l0.
  + constructor; apply sub_id.
  + apply Exists_cons_tl; assumption.
- replace (l0 ++ a :: l) with ((l0 ++ a :: nil) ++ l) by (rewrite <- app_assoc; reflexivity).
  apply IHl.
Qed.

Lemma sub_trans_list l1 l2 l3 :
  subform_list l1 l2 -> subform_list l2 l3 -> subform_list l1 l3.
Proof.
revert l2 l3; induction l1; intros l2 l3 Hl Hr; constructor.
- inversion Hl; subst.
  revert Hr H1; clear; induction l2; intros Hr Hl; inversion Hl; subst.
  + inversion Hr; subst.
    inversion H2; subst.
    * apply Exists_cons_hd.
      transitivity a0; assumption.
    * apply Exists_cons_tl.
      revert H; clear - H0; induction l; intro H; inversion H; subst.
      -- apply Exists_cons_hd.
         transitivity a0; assumption.
      -- apply Exists_cons_tl, IHl; assumption.
  + inversion Hr; subst.
    apply IHl2; assumption.
- inversion Hl; subst.
  apply IHl1 with l2; assumption.
Qed.

Instance sub_list_po : PreOrder subform_list.
Proof.
split.
- intros l.
  rewrite <- app_nil_l.
  apply sub_id_list.
- intros l1 l2 l3.
  apply sub_trans_list.
Qed.

(* Unused
From OLlibs Require Import GPermutation_Type.

Lemma sub_perm_list b l l1 l2 : subform_list l l1 ->
    PCPermutation_Type b l1 l2 -> subform_list l l2.
Proof.
intros H1 HP; revert H1; induction l; intro H1.
- constructor.
- inversion H1; subst.
  constructor.
  + apply (PCPermutation_Type_Exists _ _ HP); assumption.
  + apply IHl; assumption.
Qed.
*)


(** ** Equality in [bool] *)

Fixpoint eqb_form A B :=
match A, B with
| var X, var Y | covar X, covar Y => eqb X Y
| one, one | bot, bot | zero, zero | top, top => true
| tens A1 A2, tens B1 B2 | parr A1 A2, parr B1 B2
| aplus A1 A2, aplus B1 B2 | awith A1 A2, awith B1 B2 => eqb_form A1 B1 && eqb_form A2 B2
| oc A1, oc B1 | wn A1, wn B1 => eqb_form A1 B1
| _, _ => false
end.

Lemma eqb_eq_form A B : eqb_form A B = true <-> A = B.
Proof.
revert B; induction A; intros B; destruct B; (split ; intros Heq) ;
  inversion Heq; try reflexivity.
- apply eqb_eq in H0; subst; reflexivity.
- subst; cbn; apply eqb_eq; reflexivity.
- apply eqb_eq in H0; subst; reflexivity.
- subst; cbn; apply eqb_eq; reflexivity.
- apply andb_true_iff in H0 as [H1 H2].
  apply IHA1 in H1; apply IHA2 in H2; subst; reflexivity.
- subst; cbn; apply andb_true_iff.
  split; [ apply IHA1 | apply IHA2 ]; reflexivity.
- apply andb_true_iff in H0 as [H1 H2].
  apply IHA1 in H1; apply IHA2 in H2; subst; reflexivity.
- subst; cbn; apply andb_true_iff.
  split; [ apply IHA1 | apply IHA2 ]; reflexivity.
- apply andb_true_iff in H0 as [H1 H2].
  apply IHA1 in H1; apply IHA2 in H2; subst; reflexivity.
- subst; cbn; apply andb_true_iff.
  split; [ apply IHA1 | apply IHA2 ]; reflexivity.
- apply andb_true_iff in H0 as [H1 H2].
  apply IHA1 in H1; apply IHA2 in H2; subst; reflexivity.
- subst; cbn; apply andb_true_iff.
  split; [ apply IHA1 | apply IHA2 ]; reflexivity.
- apply IHA in H0; subst; reflexivity.
- subst; cbn; apply IHA; reflexivity.
- apply IHA in H0; subst; reflexivity.
- subst; cbn; apply IHA; reflexivity.
Qed.

Definition formulas_dectype := {|
  car := formula;
  eqb := eqb_form;
  eqb_eq := eqb_eq_form |}.

(* Unused
Fixpoint eqb_formlist l1 l2 :=
match l1, l2 with
| nil, nil => true
| cons A t1, cons B t2 => eqb_form A B && eqb_formlist t1 t2
| _, _ => false
end.

Lemma eqb_eq_formlist l1 l2 : eqb_formlist l1 l2 = true <-> l1 = l2.
Proof.
revert l2; induction l1; intros [| b l2]; split; intros Heq; inversion Heq; try reflexivity.
- apply andb_true_iff in H0 as [H1 H2].
  apply eqb_eq_form in H1; apply IHl1 in H2; subst; reflexivity.
- subst; cbn; apply andb_true_iff.
  split; [ apply eqb_eq_form | apply IHl1 ]; reflexivity.
Qed.
*)

(* Unused
(** * In with [bool] output for formula list *)
Fixpoint inb_form A l :=
match l with
| nil => false
| cons hd tl => eqb_form A hd || inb_form A tl
end.

Lemma inb_in_form A l : is_true (inb_form A l) <-> In A l.
Proof.
induction l; split; intros Heq; inversion Heq; subst.
- apply orb_true_iff in H0.
  destruct H0.
  + constructor.
    symmetry; apply eqb_eq_form; assumption.
  + apply in_cons, IHl; assumption.
- cbn; apply orb_true_iff; left.
  apply eqb_eq_form; reflexivity.
- cbn; apply orb_true_iff; right.
  apply IHl; assumption.
Qed.
*)


(** ** Sub-formulas in [bool] *)

(** First argument is a sub-formula of the second: *)
Fixpoint subformb A B :=
eqb_form A B ||
match B with
| tens B1 B2 | parr B1 B2 | awith B1 B2 | aplus B1 B2 => subformb A B1 || subformb A B2
| oc B1 | wn B1 => subformb A B1
| _ => false
end.

Lemma subb_sub A B : is_true (subformb A B) <-> subform A B.
Proof.
split; intros H; induction B;
  try (now (inversion H; constructor)) ;
  try (now (destruct A; cbn in H; inversion H));
  try (cbn in H;
       apply orb_true_elim in H as [ H | H ] ;
       [ | apply orb_true_elim in H as [ H | H ] ]; 
       (try (apply eqb_eq_form in H; subst)); now constructor; auto).
- destruct A; cbn in H; try (now inversion H).
  rewrite orb_false_r in H.
  apply eqb_eq in H; subst; constructor.
- destruct A; cbn in H; try (now inversion H).
  rewrite orb_false_r in H.
  apply eqb_eq in H; subst; constructor.
- cbn in H.
  apply orb_true_elim in H as [ H | H ].
  + apply eqb_eq_form in H; subst; constructor.
  + now constructor; auto.
- cbn in H.
  apply orb_true_elim in H as [ H | H ].
  + apply eqb_eq_form in H; subst; constructor.
  + now constructor; auto.
- inversion H; subst.
  cbn; rewrite (proj2 (eqb_eq _ _) eq_refl).
  constructor.
- inversion H; subst.
  cbn; rewrite (proj2 (eqb_eq _ _) eq_refl).
  constructor.
- inversion H; subst.
  + unfold subformb.
    replace (eqb_form (tens B1 B2) (tens B1 B2)) with true
      by (symmetry; apply eqb_eq_form; reflexivity); reflexivity.
  + apply IHB1 in H2.
    cbn; rewrite H2; cbn.
    rewrite orb_true_r; reflexivity.
  + apply IHB2 in H2.
    cbn; rewrite H2; cbn.
    rewrite 2 orb_true_r; reflexivity.
- inversion H; subst.
  + unfold subformb.
    replace (eqb_form (parr B1 B2) (parr B1 B2)) with true
      by (symmetry ; apply eqb_eq_form ; reflexivity); reflexivity.
  + apply IHB1 in H2.
    cbn; rewrite H2; cbn.
    rewrite orb_true_r; reflexivity.
  + apply IHB2 in H2.
    cbn; rewrite H2; cbn.
    rewrite 2 orb_true_r; reflexivity.
- inversion H; subst.
  + unfold subformb.
    replace (eqb_form (aplus B1 B2) (aplus B1 B2)) with true
      by (symmetry; apply eqb_eq_form; reflexivity); reflexivity.
  + apply IHB1 in H2.
    cbn; rewrite H2; cbn.
    rewrite orb_true_r; reflexivity.
  + apply IHB2 in H2.
    cbn; rewrite H2; cbn.
    rewrite 2 orb_true_r; reflexivity.
- inversion H; subst.
  + unfold subformb.
    replace (eqb_form (awith B1 B2) (awith B1 B2)) with true
      by (symmetry ; apply eqb_eq_form ; reflexivity); reflexivity.
  + apply IHB1 in H2.
    cbn; rewrite H2; cbn.
    rewrite orb_true_r; reflexivity.
  + apply IHB2 in H2.
    cbn; rewrite H2; cbn.
    rewrite 2 orb_true_r; reflexivity.
- inversion H; subst.
  + unfold subformb.
    replace (eqb_form (oc B) (oc B)) with true
      by (symmetry ; apply eqb_eq_form ; reflexivity); reflexivity.
  + apply IHB in H2.
    cbn; rewrite H2; cbn.
    rewrite orb_true_r; reflexivity.
- inversion H; subst.
  + unfold subformb.
    replace (eqb_form (wn B) (wn B)) with true
      by (symmetry; apply eqb_eq_form ; reflexivity); reflexivity.
  + apply IHB in H2.
    cbn; rewrite H2; cbn.
    rewrite orb_true_r; reflexivity.
Qed.

Lemma subb_trans A B C :
  is_true (subformb A B) -> is_true (subformb B C) -> is_true (subformb A C).
Proof.
intros Hl%subb_sub Hr%subb_sub; apply subb_sub.
transitivity B; assumption.
Qed.

(** Each element of the first list is a sub-formula of some element of the second. *)
Definition subformb_list l1 l2 := forallb (fun A => existsb (subformb A) l2) l1.

Lemma subb_sub_list l1 l2 : is_true (subformb_list l1 l2) <-> subform_list l1 l2.
Proof.
split; intros H; induction l1; try (now (inversion H; constructor)).
- unfold subformb_list in H.
  unfold is_true in H; rewrite forallb_forall, <- Forall_forall in H.
  inversion H; subst.
  apply existsb_exists, Exists_exists in H2.
  constructor.
  + clear - H2; induction l2; inversion H2; subst.
    * constructor.
      apply subb_sub; assumption.
    * apply Exists_cons_tl, IHl2; assumption.
  + apply IHl1, forallb_forall, Forall_forall; assumption.
- inversion H; subst.
  unfold subformb_list; cbn.
  apply andb_true_iff; split.
  + apply existsb_exists, Exists_exists.
    clear - H2; induction l2; inversion H2; subst.
    * constructor.
      apply subb_sub; assumption.
    * apply Exists_cons_tl, IHl2; assumption.
  + apply IHl1; assumption.
Qed.

Lemma subb_id_list l l0 : is_true (subformb_list l (l0 ++ l)).
Proof. apply subb_sub_list, sub_id_list. Qed.

Lemma subb_trans_list l1 l2 l3 :
  is_true (subformb_list l1 l2) -> is_true (subformb_list l2 l3) -> is_true (subformb_list l1 l3).
Proof.
intros Hl%subb_sub_list Hr%subb_sub_list.
apply subb_sub_list.
transitivity l2; assumption.
Qed.

End Atoms.
