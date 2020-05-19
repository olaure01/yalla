(** Order structure on [comparison]
[Lt] < [Eq] < [Gt] *)

From Coq Require Import Orders.

Set Implicit Arguments.


Ltac destr_comparison :=
  intros; destruct_all comparison; simpl in *; trivial; try discriminate.

Lemma comparison_dec : forall c1 c2 : comparison, {c1 = c2} + {c1 <> c2}.
Proof.
  decide equality.
Defined.


(** * [eqb] *)

Definition eqb (c1 c2 : comparison) :=
  match c1, c2 with
  | Gt, Gt => true
  | Eq, Eq => true
  | Lt, Lt => true
  | _, _ => false
  end.

Lemma eqb_eq : forall c1 c2, eqb c1 c2 = true <-> c1 = c2.
Proof. destr_comparison; intuition; try now inversion H. Qed.

(** * [le] *)

Definition le (c1 c2 : comparison) :=
  match c1 with
  | Gt => c2 = Gt
  | Eq => match c2 with
          | Eq | Gt => True
          | Lt => False
          end
  | Lt => True
  end.

Lemma le_refl c : le c c.
Proof. destr_comparison. Qed.

Lemma le_trans c1 c2 c3 :
  le c1 c2 -> le c2 c3 -> le c1 c3.
Proof. destr_comparison. Qed.

Lemma le_Gt c : le c Gt.
Proof. destr_comparison. Qed.

Lemma Lt_le c : le Lt c.
Proof. destr_comparison. Qed.

Instance le_compat : Proper (eq ==> eq ==> iff) le.
Proof. intuition. Qed.


(** * [lt] *)

Definition lt (c1 c2 : comparison) :=
  match c1 with
  | Gt => False
  | Eq => match c2 with
          | Gt => True
          | Lt | Eq => False
          end
  | Lt => match c2 with
          | Eq | Gt => True
          | Lt => False
          end
  end.

Lemma lt_irrefl : forall c, ~ lt c c.
Proof. destr_comparison; auto. Qed.

Lemma lt_trans c1 c2 c3 :
  lt c1 c2 -> lt c2 c3 -> lt c1 c3.
Proof. destr_comparison. Qed.

Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
Proof. intuition. Qed.

Lemma lt_total : forall c1 c2, lt c1 c2 \/ c1 = c2 \/ lt c2 c1.
Proof. destr_comparison; auto. Qed.

Lemma le_lteq : forall c1 c2, le c1 c2 <-> lt c1 c2 \/ c1 = c2.
Proof. destr_comparison; intuition. inversion H0. Qed.


(** * [compare] *)

Definition compare (c1 c2 : comparison) :=
  match c1 with
  | Gt => match c2 with
          | Gt => Eq
          | Lt | Eq => Gt
          end
  | Eq => match c2 with
          | Gt => Lt
          | Eq => Eq
          | Lt => Gt
          end
  | Lt => match c2 with
          | Eq | Gt => Lt
          | Lt => Eq
          end
  end.

Lemma compare_spec : forall c1 c2,
  CompareSpec (c1 = c2) (lt c1 c2) (lt c2 c1) (compare c1 c2).
Proof. destr_comparison; intuition. Qed.


(** * Order structures *)

(* Class structure *)
Instance le_preorder : PreOrder le.
Proof.
split.
- intros c; apply le_refl.
- intros c1 c2 c3; apply le_trans.
Qed.

Instance lt_strorder : StrictOrder lt.
Proof.
split.
- intros c; apply lt_irrefl.
- intros c1 c2 c3; apply lt_trans.
Qed.

(* Module structure *)
Module ComparisonOrd <: UsualDecidableTypeFull <: OrderedTypeFull <: TotalOrder.
  Definition t := comparison.
  Definition eq := @eq comparison.
  Definition eq_equiv := @eq_equivalence comparison.
  Definition lt := lt.
  Definition lt_strorder := lt_strorder.
  Definition lt_compat := lt_compat.
  Definition le := le.
  Definition le_lteq := le_lteq.
  Definition lt_total := lt_total.
  Definition compare := compare.
  Definition compare_spec := compare_spec.
  Definition eq_dec := comparison_dec.
  Definition eq_refl := @eq_Reflexive comparison.
  Definition eq_sym := @eq_Symmetric comparison.
  Definition eq_trans := @eq_Transitive comparison.
  Definition eqb := eqb.
  Definition eqb_eq := eqb_eq.
End ComparisonOrd.
