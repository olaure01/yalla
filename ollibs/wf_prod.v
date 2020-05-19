(** Well-founded order on product and applications to products of nat *)

From Coq Require Import Relation_Definitions Wf_nat Lia.

Set Implicit Arguments.


(** * Non-Dependant Product of two [well_founded] relations *)

Section Product.

  Variable A B : Type.
  Variable RA : relation A.
  Variable RB : relation B.
  Hypothesis WA : well_founded RA.
  Hypothesis WB : well_founded RB.

  (* more general but slightly different type
  Definition lt_prod v1 v2 := lexprod _ _ RA (fun _ => RB) v1 v2.
  Definition wf_prod := wf_lexprod _ _ _ _ WA (fun _ => WB).
  *)
  Definition lt_prod v1 v2 := RA (fst v1) (fst v2)
       \/ (fst v1 = fst v2 /\ RB (snd v1) (snd v2)).

  Lemma wf_prod : well_founded lt_prod.
  Proof.
  intros [a b]; revert b.
  induction a using (well_founded_induction WA);
    induction b using (well_founded_induction WB).
  constructor.
  intros [a' b'] [Ho | [L R]].
  - now apply H.
  - now simpl in L; subst; apply H0.
  Qed.

End Product.


(** * Well founded order on pairs of [nat] *)

(*
Definition lt_nat_nat := lexprod _ _ lt (fun _ => lt).
Definition wf_nat_nat := wf_lexprod _ _ _ _ lt_wf (fun _ => lt_wf).
*)
Definition lt_nat_nat := lt_prod lt lt.
Definition wf_nat_nat := wf_prod lt_wf lt_wf.

Ltac lt_nat_nat_solve :=
  match goal with
  | |- lt_nat_nat ?v1 ?v2 => try (left; simpl; lia);
                             try (right; split; simpl; lia);
                             fail
  | |- lt_prod lt lt ?v1 ?v2 => try (left; simpl; lia);
                                try (right; split; simpl; lia);
                                fail
  end.

(** * Well founded order on triples of [nat] *)

Definition lt_nat_nat_nat := lt_prod lt lt_nat_nat.
Definition wf_nat_nat_nat := wf_prod lt_wf wf_nat_nat.

Ltac lt_nat_nat_nat_solve :=
  match goal with 
  | |- lt_nat_nat_nat ?v1 ?v2 =>
     try (left; simpl; lia);
     try (right; split; [ | left ]; simpl; lia);
     try (right; split; [ | right; split ]; simpl; lia);
     fail
  | |- lt_prod lt lt_nat_nat ?v1 ?v2 =>
     try (left; simpl; lia);
     try (right; split; [ | left ]; simpl; lia);
     try (right; split; [ | right; split ]; simpl; lia);
     fail
  | |- lt_prod lt (lt_prod lt lt) ?v1 ?v2 =>
     try (left; simpl; lia);
     try (right; split; [ | left ]; simpl; lia);
     try (right; split; [ | right; split ]; simpl; lia);
     fail
  end.
