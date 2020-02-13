(* Bool_more Library *)

(** * Add-ons for Bool library
Usefull properties apparently missing in the Bool library. *)

Require Export Bool.
Require Import Orders.


(** * Some properties of [leb] *)

Lemma leb_refl : forall b, leb b b.
Proof. intro b; destruct b; reflexivity. Qed.

Lemma leb_trans : forall b1 b2 b3,
  leb b1 b2 -> leb b2 b3 -> leb b1 b3.
Proof. intros b1 b2 b3; destruct b1; destruct b2; destruct b3; intuition. Qed.

Lemma leb_true : forall b, leb b true.
Proof. destruct b; constructor. Qed.

Lemma false_leb : forall b, leb false b.
Proof. intros; constructor. Qed.

Instance leb_compat : Proper (eq ==> eq ==> iff) leb.
Proof. intuition. Qed.


(** * Strict order [ltb] *)

Definition ltb (b1 b2:bool) :=
  match b1 with
    | true => False
    | false => b2 = true
  end.
Hint Unfold ltb: bool.

Lemma ltb_irrefl : forall b, ~ ltb b b.
Proof. intros b; destruct b; simpl; intros Heq; inversion Heq. Qed.

Lemma ltb_trans : forall b1 b2 b3,
  ltb b1 b2 -> ltb b2 b3 -> ltb b1 b3.
Proof. intros b1 b2 b3; destruct b1; destruct b2; destruct b3; intuition. Qed.

Instance ltb_compat : Proper (eq ==> eq ==> iff) ltb.
Proof. intuition. Qed.

Lemma ltb_trichotomy : forall x y, { ltb x y } + { x = y } + { ltb y x }.
Proof. intros x y; destruct x; destruct y; simpl; auto. Qed.

Lemma ltb_total : forall x y, ltb x y \/ x = y \/ ltb y x.
Proof. intros x y; destruct (ltb_trichotomy x y) as [ [ Hlt | Heq ] | Hlt ]; auto. Qed.

Lemma ltb_leb_incl : forall x y, ltb x y -> leb x y.
Proof. intros x y; destruct x; intuition. Qed.

Lemma leb_ltbeq_dec : forall x y, leb x y -> { ltb x y } + { x = y }.
Proof. intros x y; destruct x; destruct y; simpl; auto. Qed.

Lemma leb_ltbeq : forall x y, leb x y <-> ltb x y \/ x = y.
Proof.
intros x y; split; intros Hl.
- apply leb_ltbeq_dec in Hl; intuition.
- destruct Hl; [ now apply ltb_leb_incl | subst; apply leb_refl ].
Qed.


(** * Compare *)

Definition compareb (b1 b2 : bool) :=
  match b1, b2 with
   | false, true => Lt
   | true, false => Gt
   | _, _ => Eq
  end.

Lemma compareb_spec : forall x y, CompareSpec (x = y) (ltb x y) (ltb y x) (compareb x y).
Proof. intros x y; destruct x; destruct y; intuition. Qed.


(** * Order structures *)

(* Class structure *)
Instance leb_preorder : PreOrder leb.
Proof.
split.
- intros b; apply leb_refl.
- intros b1 b2 b3; apply leb_trans.
Qed.

Instance ltb_strorder : StrictOrder ltb.
Proof.
split.
- intros b; apply ltb_irrefl.
- intros b1 b2 b3; apply ltb_trans.
Qed.

(* Module structure *)
Module BoolOrd <: UsualDecidableTypeFull <: OrderedTypeFull <: TotalOrder.
  Definition t := bool.
  Definition eq := @eq bool.
  Definition eq_equiv := @eq_equivalence bool.
  Definition lt := ltb.
  Definition lt_strorder := ltb_strorder.
  Definition lt_compat := ltb_compat.
  Definition le := leb.
  Definition le_lteq := leb_ltbeq.
  Definition lt_total := ltb_total.
  Definition compare := compareb.
  Definition compare_spec := compareb_spec.
  Definition eq_dec := bool_dec.
  Definition eq_refl := @eq_Reflexive bool.
  Definition eq_sym := @eq_Symmetric bool.
  Definition eq_trans := @eq_Transitive bool.
  Definition eqb := eqb.
  Definition eqb_eq := eqb_true_iff.
End BoolOrd.

(* TODO add in Structures.OrdersEx
Module Bool_as_OT := Bool.BoolOrd.
Module Bool_as_DT <: UsualDecidableType := Bool_as_OT.
*)


(** * Uniqueness of Identity Proofs (UIP) at [bool] type (direct proof) *)
(* begin hide *)
Lemma eq_refl_bool_ext : forall b1 b2 : bool, b1 = b2 -> b1 = b2.
Proof. destruct b1; destruct b2; intros; ( apply eq_refl || assumption ). Defined.
(* end hide *)

Lemma UIP_bool : forall (b1 b2 : bool) (f1 f2 : b1 = b2), f1 = f2.
Proof.
intros b1 b2 f1 f2.
assert (forall f, f = eq_refl_bool_ext b1 b2 f1) as Heq
  by (destruct f; revert f1; destruct b1; reflexivity).
rewrite (Heq f1), (Heq f2); reflexivity.
Qed.

