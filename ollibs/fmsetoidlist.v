(** Finite Multiset over Lists

We define an axiomatization of finite multiset through their relation with lists.
Equality is an equivalence relation.
An implementation of the axioms is provided for every type
by lists up to permutation. *)

From Stdlib Require Import Relation_Definitions Morphisms Permutation.
From Yalla.OLlibs Require Import List_more.

Set Implicit Arguments.
Set Default Proof Using "Type".


(** * Axiomatization *)

(** A finite multiset with elements in [A] is a type [M]
    related with [list A] as follows: *)
Class FinMultisetoid M A := {
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
  retract_meq : forall m, meq (fold_right add empty (elts m)) m }.

(** [Mst] and [Elt] define a finite multiset construction over a type [K]
    if for any [A] in [K], [Mst A] is a finite multiset with elements [Elt A]. *)
Definition FMoidConstructor K Mst Elt := forall A : K, FinMultisetoid (Mst A) (Elt A).


(** * Constructions and properties over finite multisets *)

Section FMSet2List.

  Variable M A : Type.
  Variable fm : FinMultisetoid M A.

  #[export] Instance mequivalence : Equivalence meq := mequiv.

  Definition list2fm l := fold_right add empty l.

  #[export] Instance list2fm_perm : Proper (@Permutation A ==> meq) list2fm := perm_meq.

  #[export] Instance elts_perm' : Proper (meq ==> @Permutation A) elts := meq_perm.

  Lemma list2fm_retract m : meq (list2fm (elts m)) m.
  Proof. apply retract_meq. Qed.

  Lemma list2fm_nil : list2fm nil = empty.
  Proof. reflexivity. Qed.

  Lemma list2fm_elt l1 l2 a :
    meq (list2fm (l1 ++ a :: l2)) (add a (list2fm (l1 ++ l2))).
  Proof.
  symmetry.
  change (add a (list2fm (l1 ++ l2)))
    with (list2fm (a :: l1 ++ l2)).
  apply perm_meq, Permutation_middle.
  Qed.

  Lemma list2fm_cons l a : meq (list2fm (a :: l)) (add a (list2fm l)).
  Proof. now rewrite <- (app_nil_l (a :: l)), list2fm_elt. Qed.

  Lemma elts_perm l : Permutation (elts (list2fm l)) l.
  Proof. induction l as [|a l IHl]; cbn; [ rewrite elts_empty | rewrite elts_add, IHl ]; reflexivity. Qed.

  Lemma elts_eq_nil m : elts m = nil -> meq m empty.
  Proof. intro Heq. rewrite <- (retract_meq m), Heq. reflexivity. Qed.

  Lemma add_swap m a b : meq (add a (add b m)) (add b (add a m)).
  Proof. rewrite <- list2fm_retract, ? elts_add, perm_swap, <- 2 elts_add, list2fm_retract. reflexivity. Qed.

  Definition sum m1 m2 := list2fm (elts m1 ++ elts m2).

  Lemma elts_sum m1 m2 : Permutation (elts (sum m1 m2)) (elts m1 ++ elts m2).
  Proof. apply elts_perm. Qed.

  Lemma sum_empty_left m : meq (sum empty m) m.
  Proof. unfold sum. rewrite elts_empty. apply retract_meq. Qed.

  Lemma sum_empty_right m : meq (sum m empty) m.
  Proof. unfold sum. rewrite elts_empty, app_nil_r. apply retract_meq. Qed.

  Lemma sum_comm m1 m2 : meq (sum m1 m2) (sum m2 m1).
  Proof. unfold sum. rewrite Permutation_app_comm. reflexivity. Qed.

  Lemma sum_ass m1 m2 m3 : meq (sum (sum m1 m2) m3) (sum m1 (sum m2 m3)).
  Proof.
  unfold sum. apply perm_meq.
  transitivity ((elts m1 ++ elts m2) ++ elts m3).
  - apply Permutation_app_tail, elts_perm.
  - rewrite <- app_assoc. symmetry. apply Permutation_app_head, elts_perm.
  Qed.

  Lemma list2fm_app l1 l2 : meq (list2fm (l1 ++ l2)) (sum (list2fm l1) (list2fm l2)).
  Proof.
  unfold sum. apply perm_meq.
  transitivity (elts (list2fm l1) ++ l2); symmetry.
  - apply Permutation_app_tail, elts_perm.
  - apply Permutation_app_head, elts_perm.
  Qed.

  #[export] Instance sum_meq : Proper (meq ==> meq ==> meq) sum.
  Proof.
  intros m1 m2 Heq%meq_perm m1' m2' Heq'%meq_perm.
  apply perm_meq, Permutation_app; assumption.
  Qed.

End FMSet2List.

Arguments list2fm {_ _ _}  _.
Arguments list2fm_retract {_ _ _} _.
Arguments sum {_ _ _} _ _.


Section Fmmap.

  Variable M A N B: Type.
  Variable fm : FinMultisetoid M A.
  Variable fm' : FinMultisetoid N B.
  Variable f : A -> B.

  Definition fmmap (m : M) := list2fm (map f (elts m)).

  #[export] Instance fmmap_meq : Proper (meq ==> meq) fmmap.
  Proof. intro; intros. apply perm_meq, Permutation_map, meq_perm. assumption. Qed.

  Lemma list2fm_map l : meq (list2fm (map f l)) (fmmap (list2fm l)).
  Proof. symmetry. apply perm_meq, Permutation_map, elts_perm. Qed.

  Lemma elts_fmmap m : Permutation (elts (fmmap m)) (map f (elts m)).
  Proof.
  rewrite <- (list2fm_retract m) at 1.
  remember (elts m) as l eqn:Heql. clear m Heql. induction l as [|a l IHl].
  - cbn. unfold fmmap. rewrite elts_empty. cbn. rewrite elts_empty. reflexivity.
  - transitivity (map f (elts (list2fm (a :: l)))).
    + apply elts_perm.
    + apply Permutation_map, elts_perm.
  Qed.

End Fmmap.

Arguments fmmap {_ _ _ _ _ _} _ _.


(** * Lists up to permutation as finite multisets *)

Fact FMoidConstr_list : FMoidConstructor list id.
Proof.
intro A.
split with (@Permutation A) (@nil A) (@cons A) id; auto.
- apply Permutation_Equivalence.
- intros a1 a2 <- l1 l2 HP.
  apply Permutation_cons, HP. reflexivity.
- intros. rewrite 2 fold_id. assumption.
- intro. rewrite fold_id. reflexivity.
Defined.
