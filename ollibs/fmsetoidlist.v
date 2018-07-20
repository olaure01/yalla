(* fmsetoidlist Library *)
(* v0   Olivier Laurent *)

(** * Finite Multiset over Lists
   We define an axiomatization of finite multiset through their relation with lists.
   Equality is an equivalence relation.
   An implementation of the axioms is provided for every type 
   by lists up to permutation. *)

Require Import Relations.
Require Import Morphisms.
Require Import List.
Require Import Permutation.


(** * Axiomatization *)

(** A finite multiset with elements in [A] is a type [M]
    related with [list A] as follows: *)
Class FinMultisetoid M A :=
{
  meq : relation M;
  mequiv : Equivalence meq;
  empty : M;
  add : A -> M -> M;
  add_meq : Proper (eq ==> meq ==> meq) add;
  elts : M -> list A;
  elts_empty : elts empty = @nil A;
  elts_add : forall a m, Permutation (elts (add a m)) (a :: elts m);
  perm_meq : forall l1 l2, Permutation l1 l2 ->
               meq (fold_right add empty l1) (fold_right add empty l2);
  meq_perm : forall m1 m2, meq m1 m2 -> Permutation (elts m1) (elts m2);
  retract_meq : forall m, meq (fold_right add empty (elts m)) m
}.

(** [Mst] and [Elt] define a finite multiset construction over a type [K]
    if for any [A] in [K], [Mst A] is a finite multiset with elements [Elt A]. *)
Definition FMoidConstructor K Mst Elt :=
  forall A : K, FinMultisetoid (Mst A) (Elt A).


(** * Constructions and properties over finite multisets *)

Section FMSet2List.

Context {M A : Type}.
Context {fm : FinMultisetoid M A}.

Global Instance mequivalence : Equivalence meq := mequiv.

Definition list2fm l := fold_right add empty l.

Global Instance list2fm_perm : Proper (@Permutation A ==> meq) list2fm := perm_meq.

Global Instance elts_perm' : Proper (meq ==> @Permutation A) elts := meq_perm.

Lemma list2fm_retract : forall m, meq (list2fm (elts m)) m.
Proof.
apply retract_meq.
Qed.

Lemma list2fm_nil : list2fm nil = empty.
Proof.
reflexivity.
Qed.

Lemma list2fm_elt : forall l1 l2 a,
  meq (list2fm (l1 ++ a :: l2)) (add a (list2fm (l1 ++ l2))).
Proof.
intros l1 l2 a.
change (add a (list2fm (l1 ++ l2)))
  with (list2fm (a :: l1 ++ l2)).
apply perm_meq.
symmetry.
apply Permutation_middle.
Qed.

Lemma list2fm_cons : forall l a, meq (list2fm (a :: l)) (add a (list2fm l)).
Proof.
intros l a.
rewrite <- (app_nil_l (a :: l)).
rewrite list2fm_elt.
reflexivity.
Qed.

Lemma elts_perm : forall l, Permutation (elts (list2fm l)) l.
Proof.
induction l.
- simpl ; rewrite elts_empty.
  reflexivity.
- simpl ; rewrite elts_add.
  rewrite IHl.
  reflexivity.
Qed.

Lemma add_swap : forall m a b, meq (add a (add b m)) (add b (add a m)).
Proof.
intros m a b.
rewrite <- list2fm_retract.
rewrite ? elts_add.
rewrite perm_swap.
rewrite <- 2 elts_add.
rewrite list2fm_retract.
reflexivity.
Qed.

Definition sum m1 m2 := list2fm (elts m1 ++ elts m2).

Lemma elts_sum : forall m1 m2,
  Permutation (elts (sum m1 m2)) (elts m1 ++ elts m2).
Proof.
intros.
apply elts_perm.
Qed.

Lemma sum_empty_left : forall m, meq (sum empty m) m.
Proof.
intros m.
unfold sum.
rewrite elts_empty.
apply retract_meq.
Qed.

Lemma sum_empty_right : forall m, meq (sum m empty) m.
Proof.
intros m.
unfold sum.
rewrite elts_empty.
rewrite app_nil_r.
apply retract_meq.
Qed.

Lemma sum_comm : forall m1 m2, meq (sum m1 m2) (sum m2 m1).
Proof.
intros m1 m2.
unfold sum.
rewrite Permutation_app_comm.
reflexivity.
Qed.

Lemma sum_ass : forall m1 m2 m3, meq (sum (sum m1 m2) m3) (sum m1 (sum m2 m3)).
Proof.
intros m1 m2 m3.
unfold sum.
apply perm_meq.
etransitivity.
- apply Permutation_app_tail.
  apply elts_perm.
- rewrite <- app_assoc.
  apply Permutation_app_head.
  symmetry.
  apply elts_perm.
Qed.

Lemma list2fm_app : forall l1 l2,
  meq (list2fm (l1 ++ l2)) (sum (list2fm l1) (list2fm l2)).
Proof.
intros l1 l2.
unfold sum.
apply perm_meq.
etransitivity.
- apply Permutation_app_tail.
  symmetry.
  apply elts_perm.
- apply Permutation_app_head.
  symmetry.
  apply elts_perm.
Qed.

Global Instance sum_meq : Proper (meq ==> meq ==> meq) sum.
Proof.
intros m1 m2 Heq m1' m2' Heq'.
unfold sum.
apply meq_perm in Heq.
apply meq_perm in Heq'.
apply perm_meq.
apply Permutation_app ; assumption.
Qed.

End FMSet2List.


Section Fmmap.

Context {M A N B: Type}.
Context {fm : FinMultisetoid M A}.
Context {fm' : FinMultisetoid N B}.
Variable f : A -> B.

Definition fmmap (m : M) := list2fm (map f (elts m)).

Global Instance fmmap_meq : Proper (meq ==> meq) fmmap.
Proof.
intros l1 l2 Heq.
apply perm_meq.
apply Permutation_map.
apply meq_perm.
assumption.
Qed.

Lemma list2fm_map : forall l, meq (list2fm (map f l)) (fmmap (list2fm l)).
Proof.
intros l.
apply perm_meq.
apply Permutation_map.
symmetry.
apply elts_perm.
Qed.

Lemma elts_fmmap : forall m, Permutation (elts (fmmap m)) (map f (elts m)).
Proof.
intros m.
rewrite <- (list2fm_retract m) at 1.
remember (elts m) as l.
clear m Heql.
induction l.
- simpl.
  unfold fmmap.
  rewrite elts_empty.
  simpl.
  rewrite elts_empty.
  reflexivity.
- etransitivity.
  + apply elts_perm.
  + apply Permutation_map.
    apply elts_perm.
Qed.

End Fmmap.



(** * Lists up to permutation as finite multisets *)

Lemma fold_id {A} : forall l, fold_right (@cons A) nil l = l.
Proof.
induction l.
- reflexivity.
- simpl.
  f_equal.
  assumption.
Qed.

Fact FMoidConstr_list : FMoidConstructor _ list id.
Proof with try reflexivity.
intros A.
split with (@Permutation A) (@nil A) (@cons A) id...
- apply Permutation_Equivalence.
- intros a1 a2 Heq l1 l2 HP ; subst.
  apply Permutation_cons...
  assumption.
- intros l1 l2 HP.
  rewrite 2 fold_id.
  assumption.
- intros l1 l2 HP.
  assumption.
- intros m.
  rewrite fold_id...
Defined.




