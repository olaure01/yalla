(* wf_prod Library *)
(* v0   Olivier Laurent *)


(** * Well-founded order on product and applications to products of nat *)

Require Import Relation_Definitions.
Require Import RelationClasses.
Require Import Lt.
Require Import Wf_nat.

Require Import Omega.

(** * Product of two [well_founded] relations *)

Section Product.

Variable A B : Type.
Variable RA : relation A.
Variable RB : relation B.
Hypothesis WA : well_founded RA.
Hypothesis WB : well_founded RB.

Definition lt_prod v1 v2 := RA (fst v1) (fst v2)
     \/ (fst v1 = fst v2 /\ RB (snd v1) (snd v2)).

Lemma wf_prod : well_founded lt_prod.
Proof with assumption.
intros [a b].
revert b.
induction a using (well_founded_induction WA) ;
induction b using (well_founded_induction WB).
constructor.
intros [a' b'] [Ho | [L R]].
- apply H...
- simpl in L ; subst.
  apply H0...
Qed.

End Product.

(** * Well founded order on pairs of [nat] *)

Definition lt_nat_nat := lt_prod _ _ lt lt.
Definition wf_nat_nat := wf_prod _ _ _ _ lt_wf lt_wf.

Ltac lt_nat_nat_solve :=
  match goal with
  | |- lt_nat_nat ?v1 ?v2 => try (left ; simpl ; omega) ;
                             try (right ; split ; simpl ; omega) ;
                             fail
  | |- lt_prod _ _ lt lt ?v1 ?v2 => try (left ; simpl ; omega) ;
                                    try (right ; split ; simpl ; omega) ;
                                    fail
  end.

(** * Well founded order on triples of [nat] *)

Definition lt_nat_nat_nat := lt_prod _ _ lt lt_nat_nat.
Definition wf_nat_nat_nat := wf_prod _ _ _ _ lt_wf wf_nat_nat.

Ltac lt_nat_nat_nat_solve :=
  match goal with 
  | |- lt_nat_nat_nat ?v1 ?v2 =>
     try (left ; simpl ; omega) ;
     try (right ; split ; [ | left ] ; simpl ; omega) ;
     try (right ; split ; [ | right ; split ] ; simpl ; omega) ;
     fail
  | |- lt_prod _ _ lt lt_nat_nat ?v1 ?v2 =>
     try (left ; simpl ; omega) ;
     try (right ; split ; [ | left ] ; simpl ; omega) ;
     try (right ; split ; [ | right ; split ] ; simpl ; omega) ;
     fail
  | |- lt_prod _ _ lt (lt_prod _ _ lt lt) ?v1 ?v2 =>
     try (left ; simpl ; omega) ;
     try (right ; split ; [ | left ] ; simpl ; omega) ;
     try (right ; split ; [ | right ; split ] ; simpl ; omega) ;
     fail
  end.

