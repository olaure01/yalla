(* TODO submit to stdlib, except part already in ssreflect *)

From Coq Require Export Bool.
From Yalla.OLlibs Require Import Datatypes_more.

Lemma reflect_neg P b : reflect P b -> reflect (not P) (negb b).
Proof. intros H. now inversion H; constructor. Qed.

(* ssr.ssrbool.andPP *)
Lemma and_andb_reflect P1 b1 P2 b2 : reflect P1 b1 -> reflect P2 b2 -> reflect (P1 /\ P2) (b1 && b2).
Proof. intros Hspec1 Hspec2. destruct b1, b2; cbn; constructor; inversion Hspec1; inversion Hspec2; tauto. Qed.

(* ssr.ssrbool.orPP *)
Lemma or_orb_reflect P1 b1 P2 b2 : reflect P1 b1 -> reflect P2 b2 -> reflect (P1 \/ P2) (b1 || b2).
Proof. intros Hspec1 Hspec2. destruct b1, b2; cbn; constructor; inversion Hspec1; inversion Hspec2; tauto. Qed.

(* ssr.ssrbool.implyPP *)
Lemma impl_implb_reflect P1 b1 P2 b2 : reflect P1 b1 -> reflect P2 b2 -> reflect (P1 -> P2) (implb b1 b2).
Proof. intros Hspec1 Hspec2. destruct b1, b2; cbn; constructor; inversion Hspec1; inversion Hspec2; tauto. Qed.


(** * ReflectT *)

Variant reflectT (P : Type) : bool -> Type :=
  | ReflectTT : P -> reflectT P true
  | ReflectTF : notT P -> reflectT P false.
#[global] Hint Constructors reflectT : bool.

Lemma reflectT_iffT P b : reflectT P b -> iffT P (b = true).
Proof. now destruct 1; split; [ | | | discriminate ]. Qed.

Lemma iffT_reflectT P b : iffT P (b = true) -> reflectT P b.
Proof.
intros Hiff. destr_bool; constructor.
- apply Hiff. reflexivity.
- intros HP. apply Hiff in HP as [=].
Defined.

Lemma reflectT_dec P b : reflectT P b -> P + notT P.
Proof. intros [|]; [ left | right ]; assumption. Defined.

Lemma eqb_specT b b' : reflectT (b = b') (eqb b b').
Proof. destruct b, b'; now constructor. Defined.

Lemma reflectT_neg P b : reflectT P b -> reflectT (notT P) (negb b).
Proof. intros H. now inversion H; constructor. Qed.

Lemma and_andb_reflectT P1 b1 P2 b2 : reflectT P1 b1 -> reflectT P2 b2 -> reflectT (P1 * P2) (b1 && b2).
Proof.
intros Hspec1 Hspec2.
destruct b1, b2; cbn; constructor; inversion Hspec1; inversion Hspec2; try intro; intuition.
Qed.

Lemma or_orb_reflectT P1 b1 P2 b2 : reflectT P1 b1 -> reflectT P2 b2 -> reflectT (P1 + P2) (b1 || b2).
Proof.
intros Hspec1 Hspec2.
destruct b1, b2; cbn; constructor; inversion Hspec1; inversion Hspec2; try intro; intuition.
Qed.

Lemma impl_implb_reflectT P1 b1 P2 b2 : reflectT P1 b1 -> reflectT P2 b2 -> reflectT (P1 -> P2) (implb b1 b2).
Proof.
intros Hspec1 Hspec2.
destruct b1, b2; cbn; constructor; inversion Hspec1; inversion Hspec2; try intro; intuition contradiction.
Qed.
