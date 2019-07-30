(* Wf_nat_more Library *)

(** * Add-ons for Wf_nat library
Usefull properties apparently missing in the Wf_nat library. *)

Require Import Wf_nat.

Lemma lt_wf_rect :
  forall n (P:nat -> Type), (forall n, (forall m, m < n -> P m) -> P n) -> P n.
Proof.
intros n P Hw.
apply well_founded_induction_type with lt.
- apply lt_wf.
- assumption.
Qed.

Lemma lt_wf_double_rect :
 forall P:nat -> nat -> Type,
   (forall n m,
     (forall p q, p < n -> P p q) ->
     (forall p, p < m -> P n p) -> P n m) -> forall n m, P n m.
Proof.
  intros P Hrec p; pattern p; apply lt_wf_rect.
  intros n H q; pattern q; apply lt_wf_rect; auto with arith.
Defined.

