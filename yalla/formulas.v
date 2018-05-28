(* formulas library for yalla *)
(* v 1.0   Olivier Laurent *)


(** * Linear Logic formulas *)

Require Import RelationClasses.
Require Import List.
Require Import Omega.

Require Import Injective.

Require yalla_ax.

(** ** Definition and main properties of formulas *)

(** A set of atoms for building formulas *)
Definition Atom := yalla_ax.Atom.

(** Formulas *)
Inductive formula : Set :=
| var : Atom -> formula
| covar : Atom -> formula
| one : formula
| bot : formula
| tens : formula -> formula -> formula
| parr : formula -> formula -> formula
| zero : formula
| top : formula
| aplus : formula -> formula -> formula
| awith : formula -> formula -> formula
| oc : formula -> formula
| wn : formula -> formula.

(** Orthogonal / dual of a [formula] *)

(** (the dual of [tens] and [parr] is the one compatible with non-commutative systems) *)
Fixpoint dual A :=
match A with
| var x     => covar x
| covar x   => var x
| one       => bot
| bot       => one
| tens A B  => parr (dual B) (dual A)
| parr A B  => tens (dual B) (dual A)
| zero      => top
| top       => zero
| aplus A B => awith (dual A) (dual B)
| awith A B => aplus (dual A) (dual B)
| oc A      => wn (dual A)
| wn A      => oc (dual A)
end.

Lemma bidual : forall A, dual (dual A) = A.
Proof.
induction A ; simpl ;
  try (rewrite IHA1 ; rewrite IHA2) ;
  try rewrite IHA ;
  try reflexivity.
Qed.

Lemma codual : forall A B, dual A = B <-> A = dual B.
Proof.
intros A B ; split ; intro H.
- rewrite <- bidual at 1.
  rewrite H.
  reflexivity.
- rewrite <- bidual.
  rewrite H.
  reflexivity.
Qed.

Lemma dual_inj : injective dual.
Proof.
intros A B H.
rewrite <- (bidual A).
rewrite <- (bidual B).
rewrite H.
reflexivity.
Qed.

(** Size of a [formula] as its number of symbols *)
Fixpoint fsize A :=
match A with
| var X     => 1
| covar X   => 1
| one       => 1
| bot       => 1
| tens A B  => S (fsize A + fsize B)
| parr A B  => S (fsize A + fsize B)
| zero      => 1
| top       => 1
| aplus A B => S (fsize A + fsize B)
| awith A B => S (fsize A + fsize B)
| oc A      => S (fsize A)
| wn A      => S (fsize A)
end.

Lemma fsize_pos : forall A, 0 < fsize A.
Proof.
induction A ; simpl ; omega.
Qed.

Lemma fsize_dual : forall A, fsize (dual A) = fsize A.
Proof.
induction A ; simpl ;
  try (rewrite IHA1 ; rewrite IHA2) ;
  try rewrite IHA ;
  try reflexivity ;
  try omega.
Qed.

Ltac fsize_auto :=
  simpl ;
  repeat rewrite fsize_dual ;
  simpl ;
  match goal with
  | H: fsize _ < _ |- _ => simpl in H
  | H: fsize _ <= _ |- _ => simpl in H
  | H: fsize _ = _ |- _ => simpl in H
  end ;
  omega.

(** Atomic [formula] *)
Inductive atomic : formula -> Prop :=
| atomic_var : forall x, atomic (var x)
| atomic_covar : forall x, atomic (covar x).


(** ** Sub-formulas *)

(** First argument is a sub-formula of the second: *)
Inductive subform : formula -> formula -> Prop :=
| sub_id : forall A, subform A A
| sub_tens_l : forall A B C, subform A B -> subform A (tens B C)
| sub_tens_r : forall A B C, subform A B -> subform A (tens C B)
| sub_parr_l : forall A B C, subform A B -> subform A (parr B C)
| sub_parr_r : forall A B C, subform A B -> subform A (parr C B)
| sub_plus_l : forall A B C, subform A B -> subform A (aplus B C)
| sub_plus_r : forall A B C, subform A B -> subform A (aplus C B)
| sub_with_l : forall A B C, subform A B -> subform A (awith B C)
| sub_with_r : forall A B C, subform A B -> subform A (awith C B)
| sub_oc : forall A B, subform A B -> subform A (oc B)
| sub_wn : forall A B, subform A B -> subform A (wn B).

Lemma sub_trans : forall A B C, subform A B -> subform B C -> subform A C.
Proof with try assumption.
intros A B C Hl Hr ; revert A Hl ; induction Hr ; intros A' Hl ;
  try (constructor ; apply IHHr)...
Qed.

Instance sub_po : PreOrder subform.
Proof.
split.
- intros l.
  apply sub_id.
- intros l1 l2 l3.
  apply sub_trans.
Qed.

(** Each element of the first list is a sub-formula of some element of the second. *)
Definition subform_list l1 l2 := Forall (fun A => Exists (subform A) l2) l1.

Lemma sub_id_list : forall l l0, subform_list l (l0 ++ l).
Proof.
induction l ; intros l0 ; constructor.
- induction l0.
  + constructor.
    apply sub_id.
  + apply Exists_cons_tl ; assumption.
- replace (l0 ++ a :: l) with ((l0 ++ a :: nil) ++ l).
  + apply IHl.
  + rewrite <- app_assoc ; reflexivity.
Qed.

Lemma sub_trans_list : forall l1 l2 l3,
  subform_list l1 l2 -> subform_list l2 l3 -> subform_list l1 l3.
Proof with try eassumption.
induction l1 ; intros l2 l3 Hl Hr ; constructor.
- inversion Hl ; subst.
  revert Hr H1 ; clear ; induction l2 ; intros Hr Hl ; inversion Hl ; subst.
  + inversion Hr ; subst.
    inversion H2 ; subst.
    * apply Exists_cons_hd.
      etransitivity...
    * apply Exists_cons_tl.
      revert H ; clear - H0 ; induction l ; intro H ; inversion H ; subst.
      apply Exists_cons_hd.
      etransitivity...
      apply Exists_cons_tl.
      apply IHl...
  + inversion Hr ; subst.
    apply IHl2...
- inversion Hl ; subst.
  eapply IHl1...
Qed.

Instance sub_list_po : PreOrder subform_list.
Proof.
split.
- intros l.
  rewrite <- app_nil_l.
  apply sub_id_list.
- intros l1 l2 l3.
  apply sub_trans_list.
Qed.

(* unused

Require Import genperm.

Lemma sub_perm_list :
  forall b l l1 l2, subform_list l l1 -> PCperm b l1 l2 -> subform_list l l2
.
Proof with try eassumption.
intros b l l1 l2 H1 HP ; revert H1 ; induction l ; intro H1.
- constructor.
- inversion H1 ; subst.
  constructor.
  + eapply PCperm_Exists...
  + apply IHl...
Qed.
*)


