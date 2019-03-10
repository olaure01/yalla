(* concat_more Library *)

(** * Add-ons for List library
Properties of concat. *)

Require Import List_Type_more.

Require Export basic_misc.

Lemma concat_elt {A} : forall (a : A) L l1 l2,
    concat L = l1 ++ a :: l2 ->
    {L1 & {L2 & {l1' & {l2' & prod (l1 = concat L1 ++ l1') (prod (l2 = l2' ++ concat L2) (L = L1 ++ (l1' ++ a :: l2') :: L2))}}}}.
Proof.
  intros a L.
  induction L; intros l1 l2 eq.
  - destruct l1; inversion eq.
  - simpl in eq.
    dichot_Type_elt_app_exec eq.
    + split with nil.
      split with L.
      split with l1.
      split with l.
      subst.
      nsplit 3; reflexivity.
    + destruct IHL with l0 l2 as (L1 & L2 & l1' & l2' & eqb & eqt & eq) ; [symmetry ; apply eq1 |].
      split with (a0 :: L1).
      split with L2.
      split with l1'.
      split with l2'.
      subst.
      nsplit 3; try reflexivity.
      apply app_assoc.
Qed.  

Lemma concat_Forall2_Type {A} {B} : forall (L : list (list A)) (l : list B) R,
    Forall2_Type R (concat L) l ->
    {L' & prod (concat L' = l) (Forall2_Type (fun (x : list A) (y : list B) => Forall2_Type R x y) L L')}.
Proof with try assumption.
  induction L; intros l R F2R.
  - inversion F2R; subst.
    split with nil.
    split.
    + reflexivity.
    + apply Forall2_Type_nil.
  - simpl in F2R.
    destruct Forall2_Type_app_inv_l with A B R a (concat L) l...
    destruct x.
    destruct x.
    simpl in *.
    destruct IHL with l1 R as (L' & p)...
    destruct p.
    split with (l0 :: L').
    split.
    + simpl; rewrite e0...
      symmetry...
    + apply Forall2_Type_cons...
Qed.

(* NEED MOVING*)
Lemma Forall2_Type_length {A} {B} : forall l1 l2 (R : A -> B -> Type),
    Forall2_Type R l1 l2 -> length l1 = length l2.
Proof with try assumption ; try reflexivity.
  intros l1 l2 R HF.
  induction HF...
  simpl; rewrite IHHF...
Qed.

Lemma Forall2_Type_in_l {A} {B} : forall l1 l2 a (R : A -> B -> Type),
    Forall2_Type R l1 l2 -> In_Type a l1 ->
    {b & prod (In_Type b l2) (R a b)}.
Proof with try assumption ; try reflexivity.
  intros l1 l2 a R HF.
  induction HF ; intro Hin; inversion Hin.
  - subst.
    split with y.
    split...
    left...
  - destruct IHHF as (b & Hinb & HRab)...
    split with b.
    split...
    right...
Qed.

Lemma Forall2_Type_in_r {A} {B} : forall l1 l2 b (R : A -> B -> Type),
    Forall2_Type R l1 l2 -> In_Type b l2 ->
    {a & prod (In_Type a l1) (R a b)}.
Proof with try assumption ; try reflexivity.
  intros l1 l2 b R HF.
  induction HF ; intro Hin; inversion Hin.
  - subst.
    split with x.
    split...
    left...
  - destruct IHHF as (a & Hina & HRab)...
    split with a.
    split...
    right...
Qed.