(* Bool_more Library *)
(* v0   Olivier Laurent *)


(** * Add-ons for Bool library
Usefull properties apparently missing in the Bool library. *)

Require Export Bool.
Require Import RelationClasses.

(** * Some basic properties of [leb] *)

Lemma leb_refl : forall b, leb b b.
Proof.
intro b ; destruct b ; reflexivity.
Qed.

Lemma leb_trans : forall b1 b2 b3,
  leb b1 b2 -> leb b2 b3 -> leb b1 b3.
Proof.
intros b1 b2 b3 ; destruct b1 ; destruct b2 ; destruct b3 ;
  simpl ; intros Ht Hf ; try reflexivity.
- inversion Hf.
- inversion Ht.
Qed.

Instance leb_preorder : PreOrder leb.
Proof.
split.
- intros b ; apply leb_refl.
- intros b1 b2 b3 ; apply leb_trans.
Qed.

Lemma leb_true : forall b, leb b true.
Proof.
destruct b ; constructor.
Qed.

Lemma false_leb : forall b, leb false b.
Proof.
intros ; constructor.
Qed.

(** * Uniqueness of Identity Proofs at [bool] type *)
(* begin hide *)
Lemma eq_refl_bool_ext : forall b1 b2 : bool, b1 = b2 -> b1 = b2.
Proof.
intros b1 b2 Heq.
destruct b1 ; destruct b2 ; intros ;
  try (apply eq_refl) ;
  subst ; rewrite Heq ; apply eq_refl.
Defined.
(* end hide *)

Lemma UIP_bool : forall (b1 b2 : bool) (f1 f2 : b1 = b2), f1 = f2.
Proof.
intros b1 b2 f1 f2.
assert (forall f, f = eq_refl_bool_ext b1 b2 f1) as Heq.
{ destruct f.
  revert f1.
  destruct b1 ; reflexivity.
}
rewrite (Heq f2).
apply Heq.
Qed.


(** * Forall on lists with [bool] output *)
Require Import List.
Require Import List_Type.

Fixpoint Forallb {A} P (l : list A) :=
match l with
| nil => true
| cons h t => andb (P h) (Forallb P t)
end.

Lemma Forallb_Forall {A} : forall P (l : list A),
  is_true (Forallb P l) <-> Forall (fun x => is_true (P x)) l.
Proof.
induction l ; split ; intros H ; try (now constructor).
- constructor.
  + simpl in H ; destruct (P a).
    * constructor.
    * inversion H.
  + apply IHl.
    simpl in H ; destruct (Forallb P l).
    * constructor.
    * rewrite andb_false_r in H.
      inversion H.
- inversion H ; subst.
  apply IHl in H3.
  simpl.
  destruct (P a) ; destruct (Forallb P l) ; now inversion H2.
Qed.

Lemma Forallb_Forall_Type {A} : forall P (l : list A),
  is_true (Forallb P l) -> Forall_Type (fun x => is_true (P x)) l.
Proof.
induction l ; intros H ; try (now constructor).
constructor.
- simpl in H ; destruct (P a).
  + constructor.
  + inversion H.
- apply IHl.
  simpl in H ; destruct (Forallb P l).
  + constructor.
  + rewrite andb_false_r in H.
    inversion H.
Qed.


(** * Exists on lists with [bool] output *)
Fixpoint Existsb {A} P (l : list A) :=
match l with
| nil => false
| cons h t => orb (P h) (Existsb P t)
end.

Lemma Existsb_Exists {A} : forall P (l : list A),
  is_true (Existsb P l) <-> Exists (fun x => is_true (P x)) l.
Proof with try assumption.
induction l ; split ; intros H ; try (now inversion H).
- inversion H.
  apply orb_true_iff in H1.
  destruct H1 as [H1 | H1].
  + constructor...
  + apply Exists_cons_tl.
    apply IHl...
- inversion H ; subst.
  + simpl ; rewrite H1.
    reflexivity.
  + apply IHl in H1.
    simpl ; rewrite H1.
    rewrite orb_true_r.
    reflexivity.
Qed.





