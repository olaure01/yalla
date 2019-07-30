(* wf_nat_more Library *)

(** * Add-ons for wf_nat library
Usefull properties apparently missing in the wf_nat library. *)

Require Import Lt.

Lemma lt_wf_rect :
  forall n (P:nat -> Type), (forall n, (forall m, m < n -> P m) -> P n) -> P n.
Proof.
intros n P Hw.
enough (forall m, m < S n -> P m) as HwS by (apply HwS ; unfold lt ; reflexivity).
induction n ; intros m Hm ; apply Hw ; intros m' Hm'.
- exfalso.
  inversion Hm ; subst.
  + clear - Hm' ; inversion Hm'.
  + clear - H0 ; inversion H0.
- apply IHn.
  apply Lt.lt_le_trans with m ; [ | apply le_S_n ] ; assumption.
Defined.

Lemma lt_wf_double_rect :
 forall P:nat -> nat -> Type,
   (forall n m,
     (forall p q, p < n -> P p q) ->
     (forall p, p < m -> P n p) -> P n m) -> forall n m, P n m.
Proof.
  intros P Hrec p; pattern p; apply lt_wf_rect.
  intros n H q; pattern q; apply lt_wf_rect; auto with arith.
Defined.

