(* iformulas library for yalla *)
(* Coq 8.6 *)
(* v 1.0   Olivier Laurent *)


(** * Intuitionistic Linear Logic formulas *)

Require Import RelationClasses.
Require Import List.
Require Import Omega.

Require Import Bool_more.

(** ** Definition and main properties of formulas *)

(** A set of atoms for building formulas *)
Parameter IAtom : Set.
(** Boolean parameter deciding whether [izero] is a formula or not *)
Parameter ifzer : bool.
(** Boolean parameter deciding whether [itop] is a formula or not *)
Parameter iftop : bool.

(** Intuitionistic formulas

(with implication in both directions for non-commutative systems) *)
Inductive iformula : Set :=
| ivar  : IAtom -> iformula
| ione  : iformula
| itens : iformula -> iformula -> iformula
| ilmap : iformula -> iformula -> iformula
| ilpam : iformula -> iformula -> iformula
| itop {ft : iftop = true} : iformula
| iwith : iformula -> iformula -> iformula
| izero {fz : ifzer = true} : iformula
| iplus : iformula -> iformula -> iformula
| ioc   : iformula -> iformula.

(** Technical lemma : indepence of Boolean proof for validity of [itop]. *)
Lemma uniq_itop : forall ft1 ft2, @itop ft1 = @itop ft2.
Proof.
intros.
assert (ft1 = ft2) by (apply UIP_bool) ; subst.
reflexivity.
Qed.

(** Technical lemma : indepence of Boolean proof for validity of [izero]. *)
Lemma uniq_izero : forall fz1 fz2, @izero fz1 = @izero fz2.
Proof.
intros.
assert (fz1 = fz2) by (apply UIP_bool) ; subst.
reflexivity.
Qed.

(** Size of a [iformula] as its number of symbols *)
Fixpoint ifsize A :=
match A with
| ivar X     => 1
| ione       => 1
| itens A B  => S ((ifsize A) + (ifsize B))
| ilmap A B  => S ((ifsize A) + (ifsize B))
| ilpam A B  => S ((ifsize A) + (ifsize B))
| itop       => 1
| iwith A B  => S ((ifsize A) + (ifsize B))
| izero      => 1
| iplus A B  => S ((ifsize A) + (ifsize B))
| ioc A      => S (ifsize A)
end.

Ltac ifsize_auto :=
  simpl ;
  match goal with
  | H: ifsize _ < _ |- _ => simpl in H
  | H: ifsize _ <= _ |- _ => simpl in H
  | H: ifsize _ = _ |- _ => simpl in H
  end ;
  omega.

(** Atomic [iformula] *)
Inductive iatomic : iformula -> Prop :=
| iatomic_var : forall x, iatomic (ivar x).

(** ** Sub-formulas *)

(** First argument is a sub-formula of the second: *)
Inductive isubform : iformula -> iformula -> Prop :=
| isub_id : forall A, isubform A A
| isub_tens_l : forall A B C, isubform A B -> isubform A (itens B C)
| isub_tens_r : forall A B C, isubform A B -> isubform A (itens C B)
| isub_lmap_l : forall A B C, isubform A B -> isubform A (ilmap B C)
| isub_lmap_r : forall A B C, isubform A B -> isubform A (ilmap C B)
| isub_lpam_l : forall A B C, isubform A B -> isubform A (ilpam B C)
| isub_lpam_r : forall A B C, isubform A B -> isubform A (ilpam C B)
| isub_plus_l : forall A B C, isubform A B -> isubform A (iplus B C)
| isub_plus_r : forall A B C, isubform A B -> isubform A (iplus C B)
| isub_with_l : forall A B C, isubform A B -> isubform A (iwith B C)
| isub_with_r : forall A B C, isubform A B -> isubform A (iwith C B)
| isub_oc : forall A B, isubform A B -> isubform A (ioc B).

Lemma isub_trans : forall A B C, isubform A B -> isubform B C -> isubform A C.
Proof with try assumption.
intros A B C Hl Hr ; revert A Hl ; induction Hr ; intros A' Hl ;
  try (constructor ; apply IHHr)...
Qed.

Instance isub_po : PreOrder isubform.
Proof.
split.
- intros l.
  apply isub_id.
- intros l1 l2 l3.
  apply isub_trans.
Qed.

(** Each element of the first list is a sub-formula of some element of the second. *)
Definition isubform_list l1 l2 := Forall (fun A => Exists (isubform A) l2) l1.

Lemma isub_id_list : forall l l0, isubform_list l (l0 ++ l).
Proof.
induction l ; intros l0 ; constructor.
- induction l0.
  + constructor.
    apply isub_id.
  + apply Exists_cons_tl ; assumption.
- replace (l0 ++ a :: l) with ((l0 ++ a :: nil) ++ l).
  + apply IHl.
  + rewrite <- app_assoc ; reflexivity.
Qed.

Lemma isub_trans_list : forall l1 l2 l3,
  isubform_list l1 l2 -> isubform_list l2 l3 -> isubform_list l1 l3.
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

Instance isub_list_po : PreOrder isubform_list.
Proof.
split.
- intros l.
  rewrite <- app_nil_l.
  apply isub_id_list.
- intros l1 l2 l3.
  apply isub_trans_list.
Qed.

(* unused

Require Import genperm.

Lemma isub_perm_list :
  forall b l l1 l2,
    isubform_list l l1 -> PCperm b l1 l2 ->
    isubform_list l l2
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

