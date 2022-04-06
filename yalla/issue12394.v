From Coq Require Import Eqdep_dec.
From OLlibs Require Import List_more.

Set Implicit Arguments.

Lemma injection_list A P :
  (forall x y : A, { x = y } + { x <> y }) ->
  forall (a : A) l p p' (F F' : Forall_inf P l),
  Forall_inf_cons a p F = Forall_inf_cons a p' F' -> p = p' /\ F = F'.
Proof.
intros Hdec a l p p' F F' [= Heq Heql]; split.
- apply (inj_pair2_eq_dec _ Hdec _ _ _ _ Heq).
- apply (inj_pair2_eq_dec _ (list_eq_dec Hdec) _ _ _ _ Heql).
Qed.
