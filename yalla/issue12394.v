From Coq Require Import Eqdep_dec.
From OLlibs Require Import List_more.

Lemma injection_list : forall A P,
  (forall x y : A, { x = y } + { x <> y }) ->
  forall (a : A) l (p p' : P a) (F F' : Forall_inf P l),
  Forall_inf_cons a p F = Forall_inf_cons a p' F' -> p = p' /\ F = F'.
Proof.
intros A P Hdec a l p p' F F' Heq.
injection Heq as Heq'.
apply inj_pair2_eq_dec in Heq'; auto.
split; auto.
apply inj_pair2_eq_dec in H; auto.
now intros x y; apply list_eq_dec.
Qed.
