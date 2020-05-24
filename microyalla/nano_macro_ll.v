From Coq Require Import List.
From OLlibs Require Import dectype Permutation_Type.
Require Import ll_def nanoll.

Fixpoint ll2ll A :=
match A with
| var x     => @formulas.var nat_dectype x
| covar x   => @formulas.covar nat_dectype x
| tens A B  => formulas.tens (ll2ll A) (ll2ll B)
| parr A B  => formulas.parr (ll2ll A) (ll2ll B)
| one       => formulas.one
| bot       => formulas.bot
| awith A B => formulas.awith (ll2ll A) (ll2ll B)
| aplus A B => formulas.aplus (ll2ll A) (ll2ll B)
| top       => formulas.top
| zero      => formulas.zero
| oc A      => formulas.oc (ll2ll A)
| wn A      => formulas.wn (ll2ll A)
end.

Lemma ll2ll_map_wn : forall l,
  map ll2ll (map wn l) = map formulas.wn (map ll2ll l).
Proof with try reflexivity.
induction l...
simpl ; rewrite IHl...
Qed.

Definition pfrag_ll := @mk_pfrag nat_dectype false NoAxioms pmix_none true.
(*                               atoms       cut   axioms   mix       perm  *)

Theorem ll2ll_proof : forall l, ll l -> ll_def.ll pfrag_ll (map ll2ll l).
Proof.
intros l pi; induction pi ; simpl; try (now constructor).
- eapply ex_r; [ eassumption | simpl ].
  apply Permutation_Type_map.
  apply Permutation_Type_app_head.
  apply Permutation_Type_swap.
- rewrite map_app.
  apply (ex_r _ (formulas.tens (ll2ll A) (ll2ll B) :: map ll2ll l2 ++ map ll2ll l1)).
  + now constructor.
  + simpl; apply Permutation_Type_cons; try reflexivity.
    apply Permutation_Type_app_comm.
- rewrite ll2ll_map_wn.
  constructor.
  rewrite <- ll2ll_map_wn; assumption.
Qed.
