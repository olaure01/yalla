(** Finite Multiset over Lists

We define an axiomatization of finite multisets through their relation with lists.
Equality is required to be Coq equality.
An implementation of the axioms is provided by sorted lists
for every type equiped with a Boolean-valued total order relation. *)

From Coq Require Import Bool List Permutation Morphisms.
From Yalla.OLlibs Require Import BOrders.

Set Implicit Arguments.
Set Default Proof Using "Type".


(** * Axiomatization *)

(** A finite multiset with elements in [A] is a type [M]
    related with [list A] as follows: *)
Class FinMultiset M A := {
  empty : M;
  add : A -> M -> M;
  elts : M -> list A;
  elts_empty : elts empty = @nil A;
  elts_add : forall a m, Permutation (elts (add a m)) (a :: elts m);
  elts_retract : forall m, fold_right add empty (elts m) = m;
  perm_eq : forall l1 l2, Permutation l1 l2 ->
                  fold_right add empty l1 = fold_right add empty l2 }.

(** [Mst] and [Elt] define a finite multiset construction over a type [K]
    if for any [A] in [K], [Mst A] is a finite multiset with elements [Elt A]. *)
Definition FMConstructor K Mst Elt := forall A : K, FinMultiset (Mst A) (Elt A).


(** * Constructions and properties over finite multisets *)

Section FMSet2List.

  Variable M A : Type.
  Variable fm : FinMultiset M A.

  Definition list2fm l := fold_right add empty l.

  #[export] Instance list2fm_perm : Proper (@Permutation A ==> eq) list2fm := perm_eq.

  Lemma list2fm_retract m : list2fm (elts m) = m.
  Proof. apply elts_retract. Qed.

  Lemma list2fm_nil : list2fm nil = empty.
  Proof. reflexivity. Qed.

  Lemma list2fm_elt l1 l2 a : list2fm (l1 ++ a :: l2) = add a (list2fm (l1 ++ l2)).
  Proof.
  symmetry.
  change (add a (list2fm (l1 ++ l2))) with (list2fm (a :: l1 ++ l2)).
  apply perm_eq, Permutation_middle.
  Qed.

  Lemma list2fm_cons l a : list2fm (a :: l) = add a (list2fm l).
  Proof. now rewrite <- (app_nil_l (a :: l)), list2fm_elt. Qed.

  Lemma elts_perm l : Permutation (elts (list2fm l)) l.
  Proof.
  induction l as [|a l IHl]; cbn.
  - rewrite elts_empty. reflexivity.
  - rewrite elts_add, IHl. reflexivity.
  Qed.

  #[export] Instance elts_perm' : Proper (eq ==> @Permutation A) elts.
  Proof. intros m1 m2 ->. reflexivity. Qed.

  Lemma elts_eq_nil m : elts m = nil -> m = empty.
  Proof. intros Heq. assert (Hr := elts_retract m). rewrite Heq in Hr. simpl in Hr. symmetry. assumption. Qed.

  Lemma add_swap m a b : add a (add b m) = add b (add a m).
  Proof.
  rewrite <- list2fm_retract. rewrite <- list2fm_retract at 1. rewrite 4 elts_add, perm_swap. reflexivity.
  Qed.

  Definition sum m1 m2 := list2fm (elts m1 ++ elts m2).

  Lemma elts_sum m1 m2 : Permutation (elts (sum m1 m2)) (elts m1 ++ elts m2).
  Proof. apply elts_perm. Qed.

  Lemma sum_empty_left m : sum empty m = m.
  Proof. unfold sum. rewrite elts_empty. apply elts_retract. Qed.

  Lemma sum_empty_right m : sum m empty = m.
  Proof. unfold sum. rewrite elts_empty, app_nil_r. apply elts_retract. Qed.

  Lemma sum_comm m1 m2 : sum m1 m2 = sum m2 m1.
  Proof. unfold sum. rewrite Permutation_app_comm. reflexivity. Qed.

  Lemma sum_ass m1 m2 m3 : sum (sum m1 m2) m3 = sum m1 (sum m2 m3).
  Proof.
  unfold sum. apply perm_eq.
  transitivity ((elts m1 ++ elts m2) ++ elts m3).
  - apply Permutation_app_tail, elts_perm.
  - rewrite <- app_assoc. symmetry. apply Permutation_app_head, elts_perm.
  Qed.

  Lemma list2fm_app l1 l2 : list2fm (l1 ++ l2) = sum (list2fm l1) (list2fm l2).
  Proof.
  unfold sum. apply perm_eq.
  transitivity (elts (list2fm l1) ++ l2); symmetry.
  - apply Permutation_app_tail, elts_perm.
  - apply Permutation_app_head, elts_perm.
  Qed.

End FMSet2List.

Arguments list2fm {_ _ _} _.
Arguments sum {_ _ _} _ _.


Section Fmmap.

  Variable M A N B : Type.
  Variable fm : FinMultiset M A.
  Variable fm' : FinMultiset N B.
  Variable f : A -> B.

  Definition fmmap (m : M) := list2fm (map f (elts m)).

  Lemma list2fm_map l : list2fm (map f l) = fmmap (list2fm l).
  Proof. symmetry. apply perm_eq, Permutation_map, elts_perm. Qed.

  Lemma elts_fmmap m : Permutation (elts (fmmap m)) (map f (elts m)).
  Proof.
  rewrite <- (elts_retract m).
  remember (elts m) as l eqn:Heql. clear m Heql. induction l; cbn.
  - unfold fmmap. rewrite elts_empty. cbn. rewrite elts_empty. reflexivity.
  - apply elts_perm.
  Qed.

End Fmmap.

Arguments fmmap {_ _ _ _ _ _} _ _.


Section Induction.

  Variable M A : Type.
  Variable fm : FinMultiset M A.

  Lemma fm_rect (P : M -> Type) : P empty -> (forall a m, P m -> P (add a m)) -> forall m, P m.
  Proof.
  intros He Ha m.
  remember (elts m) as l eqn:Heql.
  assert (HP := Permutation_refl l).
  rewrite Heql in HP at 2. clear Heql.
  induction l as [|a l IHl] in m, HP |- *.
  - apply Permutation_nil in HP.
    apply elts_eq_nil in HP as ->. assumption.
  - assert (Hr := elts_retract m).
    symmetry in HP. rewrite (perm_eq HP) in Hr. cbn in Hr. subst.
    apply Ha, IHl.
    change (fold_right add empty l) with (list2fm l).
    symmetry. apply elts_perm.
  Defined.

  Lemma fm_ind (P : M -> Prop) : P empty -> (forall a m, P m -> P (add a m)) -> forall m, P m.
  Proof. intros. apply fm_rect; assumption. Defined.

  Lemma fm_rec (P : M -> Set) : P empty -> (forall a m, P m -> P (add a m)) -> forall m, P m.
  Proof. intros. apply fm_rect; assumption. Defined.

End Induction.


(** * Notations *)

Module FMSetNotations.
  Infix ":::" := add (at level 60, right associativity).
  Infix "+++" := sum (right associativity, at level 60).
  Notation " [[ ]] " := empty.
  Notation " [[ x ]] " := (add x empty).
  Notation " [[ x ; .. ; y ]] " := (add x .. (add y empty) ..).
End FMSetNotations.


(** ** Sorted lists as finite multisets
  Sorted lists provide a finite multisets construction for [BOrder]. *)

Definition fmslist_empty B : SortedList B := exist _ (nil) eq_refl.

Lemma fmslist_add B : @car B -> SortedList B -> SortedList B.
Proof. intros a m. exists (insert a (proj1_sig m)). apply (insert_sorted a m). Defined.

Lemma insert_add B (a : @car B) l : proj1_sig (fmslist_add a l) = insert a (proj1_sig l).
Proof. reflexivity. Qed.

Theorem FMConstr_slist : FMConstructor SortedList (@car).
Proof.
intros A.
split with (@fmslist_empty A) (@fmslist_add A) (fun m => proj1_sig m); auto.
- intros a [l Hsort].
  induction l as [| a0 l IHl] in Hsort |- *; [ reflexivity | ].
  cbn. destruct (leb a a0); [ reflexivity | ].
  change (a :: a0 :: l) with ((a :: nil) ++ a0 :: l).
  apply is_sorted_tail in Hsort.
  apply Permutation_cons_app, (IHl Hsort).
- intros [l Hsort].
  induction l as [| a l IHl] in Hsort |- *.
  + apply sortedlist_equality. reflexivity.
  + destruct l as [|c l]; apply sortedlist_equality; [ reflexivity | ].
    cbn. cbn in Hsort. apply andb_true_iff in Hsort as [Ha Hsort].
    assert (H' := IHl Hsort).
    apply (f_equal (fun m => proj1_sig m)) in H'.
    simpl in H'. rewrite H'. cbn.
    destruct (leb a c); [ reflexivity | discriminate Ha ].
- intros l1 l2 HP. induction HP as [| ? ? ? ? IHP | | ? ? ? ? IHP ]; [ reflexivity | | | ]; cbn.
  + rewrite IHP. reflexivity.
  + apply sortedlist_equality, insert_insert.
  + rewrite IHP. assumption.
Defined.
