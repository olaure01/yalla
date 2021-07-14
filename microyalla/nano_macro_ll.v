From Coq Require Import List.
From OLlibs Require Import dectype Permutation_Type.
From Yalla Require Import ll_def nanoll.

Fixpoint nll2ll A :=
match A with
| var x     => @formulas.var nat_dectype x
| covar x   => @formulas.covar nat_dectype x
| tens A B  => formulas.tens (nll2ll A) (nll2ll B)
| parr A B  => formulas.parr (nll2ll A) (nll2ll B)
| one       => formulas.one
| bot       => formulas.bot
| awith A B => formulas.awith (nll2ll A) (nll2ll B)
| aplus A B => formulas.aplus (nll2ll A) (nll2ll B)
| top       => formulas.top
| zero      => formulas.zero
| oc A      => formulas.oc (nll2ll A)
| wn A      => formulas.wn (nll2ll A)
end.

Lemma nll2ll_map_wn : forall l,
  map nll2ll (map wn l) = map formulas.wn (map nll2ll l).
Proof. now induction l; [| cbn; rewrite IHl]. Qed.

Definition pfrag_ll := @mk_pfrag nat_dectype false NoAxioms pmix_none true.
(*                               atoms       cut   axioms   mix       perm  *)

Theorem nll2ll_proof : forall l, ll l -> ll_def.ll pfrag_ll (map nll2ll l).
Proof.
intros l pi; induction pi ; cbn; try (now constructor).
- eapply ex_r; [ eassumption | cbn ].
  apply Permutation_Type_map.
  apply Permutation_Type_app_head.
  apply Permutation_Type_swap.
- rewrite map_app.
  apply (ex_r (formulas.tens (nll2ll A) (nll2ll B) :: map nll2ll l2 ++ map nll2ll l1)).
  + now constructor.
  + cbn; apply Permutation_Type_cons; try reflexivity.
    apply Permutation_Type_app_comm.
- rewrite nll2ll_map_wn.
  constructor.
  rewrite <- nll2ll_map_wn; assumption.
Qed.
