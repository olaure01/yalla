From Coq Require Import List Lia.
(*
From OLlibs Require Import funtheory.
*)
From OLlibs Require Import dectype Permutation_Type.
Require Import ill_def microill.

Fixpoint ill2ill A :=
match A with
| ivar x    => @iformulas.ivar nat_dectype (Some x)
| itens A B => iformulas.itens (ill2ill A) (ill2ill B)
| ilmap A B => iformulas.ilmap (ill2ill A) (ill2ill B)
| ione      => iformulas.ione
| iwith A B => iformulas.iwith (ill2ill A) (ill2ill B)
| iplus A B => iformulas.iplus (ill2ill A) (ill2ill B)
| itop      => iformulas.itop
| izero     => iformulas.izero
| ioc A     => iformulas.ioc (ill2ill A)
end.

(*
Lemma ill2ill_inj : injective ill2ill.
Proof.
intros A.
induction A ; intros B Heq ;
  destruct B ; inversion Heq ;
  try apply IHA in H0 ;
  try apply IHA1 in H0 ;
  try apply IHA2 in H1 ; subst ;
  reflexivity.
Qed.
*)

Lemma ill2ill_map_ioc : forall l,
  map ill2ill (map ioc l) = map iformulas.ioc (map ill2ill l).
Proof with try reflexivity.
induction l...
simpl ; rewrite IHl...
Qed.

(*
Lemma ill2ill_map_ioc_inv : forall l1 l2,
  map iformulas.ioc l1 = map ill2ill l2 ->
    { l2' | l2 = map ioc l2' /\ l1 = map ill2ill l2' }.
Proof with try assumption ; try reflexivity.
induction l1 ; intros l2 Heq ;
  destruct l2 ; inversion Heq...
- exists nil ; split...
- apply IHl1 in H1.
  destruct i ; inversion H0 ; subst.
  destruct H1 as (l2' & Heq1 & H1) ; subst.
  exists (i :: l2') ; split...
Qed.
*)

Lemma transp_perm {A} : forall n (l : list A),
  Permutation_Type l (transp n l).
Proof with try reflexivity.
induction n; intros l; simpl; destruct l...
- destruct l...
  apply Permutation_Type_swap.
- apply Permutation_Type_cons...
  apply IHn.
Qed.

Lemma transp_map {A B} (f : A -> B) : forall n l,
  transp n (map f l) = map f (transp n l).
Proof with try reflexivity.
induction n; destruct l...
- destruct l; simpl...
- simpl; f_equal.
  apply IHn.
Qed.

Definition ipfrag_ill := @ill_def.mk_ipfrag nat_dectype false ill_def.NoIAxioms true.
(*                                          atoms       cut   axioms            perm  *)

Theorem ill2ill_proof : forall l A, ill l A -> ill_def.ill ipfrag_ill (map ill2ill l) (ill2ill A).
Proof.
intros l A pi.
induction pi; rewrite <- (app_nil_l _) ; try (now constructor).
- apply (ex_ir _ (map ill2ill l)); try assumption.
  simpl; rewrite <- transp_map.
  apply transp_perm.
- now rewrite map_app; rewrite app_nil_l ; constructor.
- apply (ex_ir _ (nil ++ map ill2ill l1 ++ iformulas.ilmap (ill2ill A) (ill2ill B) :: map ill2ill l2)).
  + now constructor.
  + simpl; rewrite map_app.
    etransitivity; [ apply Permutation_Type_app_comm | ].
    apply Permutation_Type_cons; try reflexivity.
    apply Permutation_Type_app_comm.
- rewrite ill2ill_map_ioc.
  constructor.
  rewrite <- ill2ill_map_ioc; assumption.
Qed.