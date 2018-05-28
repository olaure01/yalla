(* Bool_more Library *)
(* Coq 8.6 *)
(* v0   Olivier Laurent *)


(** * Add-ons for Bool library
Usefull properties apparently missing in the Bool library. *)

Require Export Bool.
Require Import RelationClasses.

(** * Some basic properties of [leb] *)

Lemma leb_refl : forall b, leb b b.
Proof.
intro b ; destruct b ; reflexivity.
Qed.

Lemma leb_trans : forall b1 b2 b3,
  leb b1 b2 -> leb b2 b3 -> leb b1 b3.
Proof.
intros b1 b2 b3 ; destruct b1 ; destruct b2 ; destruct b3 ;
  simpl ; intros Ht Hf ; try reflexivity.
- inversion Hf.
- inversion Ht.
Qed.

Instance leb_preorder : PreOrder leb.
Proof.
split.
- intros b ; apply leb_refl.
- intros b1 b2 b3 ; apply leb_trans.
Qed.

Lemma leb_true : forall b, leb b true.
Proof.
destruct b ; constructor.
Qed.

Lemma false_leb : forall b, leb false b.
Proof.
intros ; constructor.
Qed.

(** * Uniqueness of Identity Proofs at [bool] type *)
(* begin hide *)
Lemma eq_refl_bool_ext : forall b1 b2 : bool, b1 = b2 -> b1 = b2.
Proof.
intros b1 b2 Heq.
destruct b1 ; destruct b2 ; intros ;
  try (apply eq_refl) ;
  subst ; rewrite Heq ; apply eq_refl.
Defined.
(* end hide *)

Lemma UIP_bool : forall (b1 b2 : bool) (f1 f2 : b1 = b2), f1 = f2.
Proof.
intros b1 b2 f1 f2.
assert (forall f, f = eq_refl_bool_ext b1 b2 f1) as Heq.
{ destruct f.
  revert f1.
  destruct b1 ; reflexivity.
}
rewrite (Heq f2).
apply Heq.
Qed.


