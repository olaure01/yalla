(** Finite Multiset over Lists

We define an axiomatization of finite multisets through their relation with lists.
Equality is required to be Coq equality.
Permutation are with output in [Type].
An implementation of the axioms is provided by sorted lists
for every type equiped with a Boolean-valued total order relation. *)

From Coq Require Import Bool List CMorphisms.
From OLlibs Require Import BOrders Permutation_Type_more.

Set Implicit Arguments.


(** * Axiomatization *)

(** A finite multiset with elements in [A] is a type [M]
    related with [list A] as follows: *)
Class FinMultiset M A := {
  empty : M;
  add : A -> M -> M;
  elts : M -> list A;
  elts_empty : elts empty = @nil A;
  elts_add : forall a m, Permutation_Type (elts (add a m)) (a :: elts m);
  elts_retract : forall m, fold_right add empty (elts m) = m;
  perm_eq : forall l1 l2, Permutation_Type l1 l2 ->
                  fold_right add empty l1 = fold_right add empty l2
}.

(** [Mst] and [Elt] define a finite multiset construction over a type [K]
    if for any [A] in [K], [Mst A] is a finite multiset with elements [Elt A]. *)
Definition FMConstructor K Mst Elt := forall A : K, FinMultiset (Mst A) (Elt A).


(** * Constructions and properties over finite multisets *)

Section FMSet2List.

  Variable M A : Type.
  Variable fm : FinMultiset M A.

  Definition list2fm l := fold_right add empty l.

  Global Instance list2fm_perm : Proper (@Permutation_Type A ==> eq) list2fm
    := perm_eq.

  Lemma list2fm_retract : forall m, list2fm (elts m) = m.
  Proof. apply elts_retract. Qed.

  Lemma list2fm_nil : list2fm nil = empty.
  Proof. reflexivity. Qed.

  Lemma list2fm_elt : forall l1 l2 a,
    list2fm (l1 ++ a :: l2) = add a (list2fm (l1 ++ l2)).
  Proof.
  intros l1 l2 a; symmetry.
  change (add a (list2fm (l1 ++ l2)))
    with (list2fm (a :: l1 ++ l2)).
  apply perm_eq, Permutation_Type_middle.
  Qed.

  Lemma list2fm_cons : forall l a, list2fm (a :: l) = add a (list2fm l).
  Proof.
  now intros l a; rewrite <- (app_nil_l (a :: l)), list2fm_elt.
  Qed.

  Lemma elts_perm : forall l, Permutation_Type (elts (list2fm l)) l.
  Proof.
  induction l ; simpl.
  - now rewrite elts_empty.
  - transitivity (a :: elts (list2fm l)).
    + apply elts_add.
    + now apply Permutation_Type_cons.
  Qed.

  Global Instance elts_perm' : Proper (eq ==> @Permutation_Type A) elts.
  Proof. now intros m1 m2 Heq ; subst. Qed.

  Lemma elts_eq_nil : forall m, elts m = nil -> m = empty.
  Proof.
  intros m Heq.
  now assert (Hr := elts_retract m); rewrite Heq in Hr; simpl in Hr; subst.
  Qed.

  Lemma add_swap : forall m a b, add a (add b m) = add b (add a m).
  Proof.
  intros m a b.
  rewrite <- list2fm_retract.
  rewrite <- list2fm_retract at 1.
  apply list2fm_perm.
  etransitivity ; [ apply elts_add | ].
  etransitivity ; [ apply Permutation_Type_cons ;
                      [ reflexivity | apply elts_add ] | ].
  symmetry.
  etransitivity ; [ apply elts_add | ].
  etransitivity ; [ apply Permutation_Type_cons ;
                      [ reflexivity | apply elts_add ] | ].
  apply Permutation_Type_swap.
  Qed.

  Definition sum m1 m2 := list2fm (elts m1 ++ elts m2).

  Lemma elts_sum : forall m1 m2,
    Permutation_Type (elts (sum m1 m2)) (elts m1 ++ elts m2).
  Proof. intros; apply elts_perm. Qed.

  Lemma sum_empty_left : forall m, sum empty m = m.
  Proof.
  intros m; unfold sum.
  rewrite elts_empty.
  apply elts_retract.
  Qed.

  Lemma sum_empty_right : forall m, sum m empty = m.
  Proof.
  intros m; unfold sum.
  rewrite elts_empty, app_nil_r.
  apply elts_retract.
  Qed.

  Lemma sum_comm : forall m1 m2, sum m1 m2 = sum m2 m1.
  Proof.
  intros m1 m2; unfold sum.
  apply list2fm_perm, Permutation_Type_app_comm.
  Qed.

  Lemma sum_ass : forall m1 m2 m3, sum (sum m1 m2) m3 = sum m1 (sum m2 m3).
  Proof.
  intros m1 m2 m3; unfold sum.
  apply perm_eq.
  transitivity ((elts m1 ++ elts m2) ++ elts m3).
  - apply Permutation_Type_app_tail, elts_perm.
  - rewrite <- app_assoc; symmetry.
    apply Permutation_Type_app_head, elts_perm.
  Qed.

  Lemma list2fm_app : forall l1 l2,
    list2fm (l1 ++ l2) = sum (list2fm l1) (list2fm l2).
  Proof.
  intros l1 l2; unfold sum.
  apply perm_eq.
  transitivity (elts (list2fm l1) ++ l2); symmetry.
  - apply Permutation_Type_app_tail, elts_perm.
  - apply Permutation_Type_app_head, elts_perm.
  Qed.

End FMSet2List.

Arguments list2fm {_} {_} {_} _.
Arguments sum {_} {_} {_} _ _.


Section Fmmap.

 Variable M A N B : Type.
 Variable fm : FinMultiset M A.
 Variable fm' : FinMultiset N B.
 Variable f : A -> B.

  Definition fmmap (m : M) := list2fm (map f (elts m)).

  Lemma list2fm_map : forall l, list2fm (map f l) = fmmap (list2fm l).
  Proof.
  intros l; symmetry.
  apply perm_eq, Permutation_Type_map, elts_perm.
  Qed.

  Lemma elts_fmmap : forall m, Permutation_Type (elts (fmmap m)) (map f (elts m)).
  Proof.
  intros m.
  rewrite <- (elts_retract m).
  remember (elts m) as l; clear m Heql; induction l; simpl.
  - unfold fmmap; rewrite elts_empty; simpl.
    now rewrite elts_empty.
  - apply elts_perm.
  Qed.

End Fmmap.

Arguments fmmap {_} {_} {_} {_} {_} {_} _ _.


Section Induction.

  Variable M A : Type.
  Variable fm : FinMultiset M A.

  Lemma fm_rect : forall (P : M -> Type),
    P empty -> (forall a m, P m -> P (add a m)) -> forall m, P m.
  Proof.
  intros P He Ha m.
  remember (elts m) as l.
  apply Permutation_Type_refl' in Heql; unfold id in Heql.
  revert m Heql; induction l; intros m Heql.
  - apply Permutation_Type_nil in Heql.
    now apply elts_eq_nil in Heql; subst.
  - assert (Hr := elts_retract m).
    symmetry in Heql; rewrite (perm_eq Heql) in Hr; simpl in Hr; subst.
    apply Ha, IHl.
    symmetry.
    change (fold_right add empty l) with (list2fm l).
    apply elts_perm.
  Defined.

  Lemma fm_ind : forall (P : M -> Prop),
    P empty -> (forall a m, P m -> P (add a m)) -> forall m, P m.
  Proof. intros; apply fm_rect; assumption. Defined.

  Lemma fm_rec : forall (P : M -> Set),
    P empty -> (forall a m, P m -> P (add a m)) -> forall m, P m.
  Proof. intros; apply fm_rect; assumption. Defined.

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
Proof.
intros a m.
exists (insert a (proj1_sig m)).
apply (insert_sorted a m); reflexivity.
Defined.

Lemma insert_add B : forall (a : @car B) l,
  proj1_sig (fmslist_add a l) = insert a (proj1_sig l).
Proof. reflexivity. Qed.

Theorem FMConstr_slist : FMConstructor SortedList (@car).
Proof.
intros A.
split with (@fmslist_empty A) (@fmslist_add A) (fun m => proj1_sig m); intros; auto.
- destruct m as [l Hsort].
  revert Hsort; induction l; simpl; intros Hsort; auto.
  destruct (leb a a0); auto.
  change (a :: a0 :: l) with ((a :: nil) ++ a0 :: l).
  apply Permutation_Type_cons_app.
  apply is_sorted_tail in Hsort.
  apply (IHl Hsort).
- destruct m as [l Hsort].
  revert Hsort; induction l; intros Hsort.
  + now apply sortedlist_equality.
  + destruct l; apply sortedlist_equality; simpl; auto.
    apply andb_true_iff in Hsort as [Ha Hsort].
    assert (H' := IHl Hsort).
    apply (f_equal (fun m => proj1_sig m)) in H'.
    simpl in H'; rewrite H'; simpl.
    destruct (leb a c); [ reflexivity | discriminate Ha ].
- induction X; simpl; auto.
  + now rewrite IHX.
  + apply sortedlist_equality, insert_insert.
  + now rewrite IHX1.
Defined.
