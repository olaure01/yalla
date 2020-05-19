(** Generalization of [Forall_inf] to dependent product *)

From Coq Require Export Eqdep_dec.
From Coq Require Import PeanoNat List.
From OLlibs Require Import List_Type.

Set Implicit Arguments.


(** * [In_Forall_inf] *)

Section In_Forall_inf.
  Variable A : Type.
  Variable P : A -> Type.

  Fixpoint In_Forall_inf l (a : A) (Pa : P a) (Fl : Forall_inf P l) : Type :=
    match Fl with
    | Forall_inf_nil _ => False
    | Forall_inf_cons b Pb Fl => ((existT P a Pa) = (existT P b Pb)) + In_Forall_inf Pa Fl
    end.

  Lemma In_Forall_inf_elt: forall l1 l2 a (Fl : Forall_inf P (l1 ++ a :: l2)),
      { Pa : P a & In_Forall_inf Pa Fl }.
  Proof.
  induction l1; intros l2 a' Fl.
  - simpl in Fl.
    remember (a' :: l2).
    destruct Fl; inversion Heql.
    subst.
    split with p.
    now left.
  - remember ((a :: l1) ++ a' :: l2).
    destruct Fl; inversion Heql.
    subst.
    destruct IHl1 with l2 a' Fl as (Pa , Hin); auto.
    split with Pa.
    now right.
  Qed.

  Lemma In_Forall_inf_in : forall l a (Fl : Forall_inf P l),
    In_inf a l -> { Pa : P a & In_Forall_inf Pa Fl }.
  Proof.
  intros l.
  induction l; intros a' Fl Hin; inversion Hin.
  - subst.
    remember (a' :: l) as l'.
    destruct Fl; inversion Heql'.
    subst.
    split with p.
    now left.
  - remember (a :: l) as l'.
    destruct Fl; inversion Heql'.
    subst.
    destruct IHl with a' Fl as (Pa & Hin'); auto.
    split with Pa.
    now right.
  Qed.

  Fixpoint Forall_inf_sum (f : forall a, P a -> nat) (l : list A) (Pl : Forall_inf P l) :=
    match Pl with
    | Forall_inf_nil _ => 0
    | @Forall_inf_cons _ _ x l Px Pl => (f x Px) + (Forall_inf_sum f Pl)
    end.

  Fixpoint Forall_inf_App l1 l2 Pl1 Pl2 :=
    match Pl1 with
    | Forall_inf_nil _ => Pl2
    | @Forall_inf_cons _ _ x l Px Pl => @Forall_inf_cons _ P x (l ++ l2) Px
                                                         (Forall_inf_App l l2 Pl Pl2)
    end.

  Lemma Forall_inf_sum_app : forall f l1 l2 (Pl1 : Forall_inf P l1) (Pl2 : Forall_inf P l2),
      Forall_inf_sum f (Forall_inf_App Pl1 Pl2)
    = Forall_inf_sum f Pl1 + Forall_inf_sum f Pl2.
  Proof.
  intros f l1 l2 Pl1 Pl2.
  induction Pl1.
  - reflexivity.
  - simpl; rewrite IHPl1.
    apply Nat.add_assoc.
  Qed.

  Lemma In_Forall_inf_to_In_inf : forall l (L : list A) (p : P l) (PL : Forall_inf P L),
    In_Forall_inf p PL -> In_inf l L.
  Proof.
  intros l L p PL Hin; induction PL; inversion Hin.
  - now left; inversion H; subst.
  - now right; apply IHPL.
  Qed.

End In_Forall_inf.


(** * [Dependent_Forall_inf] *)

Inductive Dependent_Forall_inf A (P : A -> Type) (Pred : forall a, P a -> Type) :
   forall l, Forall_inf P l -> Type :=
| Dependent_Forall_inf_nil : Dependent_Forall_inf Pred (Forall_inf_nil P)
| Dependent_Forall_inf_cons : forall a l Pa (Fl : Forall_inf P l), (Pred a Pa) ->
           Dependent_Forall_inf Pred Fl -> Dependent_Forall_inf Pred (Forall_inf_cons a Pa Fl).

Section Eq_Dec.

  Variable A : Type.
  Hypothesis eq_dec : forall (x y : A), {x = y} + {x <> y}.

  Lemma Dependent_Forall_inf_forall : forall (P : A -> Type) Pred,
    forall l a Pa (Fl : Forall_inf P l),
      Dependent_Forall_inf Pred Fl -> In_Forall_inf a Pa Fl -> Pred a Pa.
  Proof.
  intros P Pred l a Pa Fl DFl; revert a Pa;
    induction DFl; intros a' Pa' Hin; inversion Hin.
  - inversion H; subst.
    apply inj_pair2_eq_dec in H2; auto.
    now rewrite H2.
  - now apply IHDFl.
  Qed.

  Lemma forall_Dependent_Forall_inf : forall (P : A -> Type) Pred,
    forall l (Fl : Forall_inf P l),
      (forall a Pa, In_Forall_inf a Pa Fl -> Pred a Pa) ->
      Dependent_Forall_inf Pred Fl.
  Proof.
  intros P Pred l Fl; induction Fl; intros f.
  - apply Dependent_Forall_inf_nil.
  - apply Dependent_Forall_inf_cons.
    + now apply f; left.
    + apply IHFl.
      intros a Pa Hin.
      now apply f; right.
  Qed.

  Lemma Dependent_Forall_inf_inv : forall (P : A -> Type) Pred a l Pa (Pl : Forall_inf P l),
    Dependent_Forall_inf Pred (Forall_inf_cons a Pa Pl) -> Pred a Pa.
  Proof.
  intros P Pred a l Pa Pl DPl.
  inversion DPl; subst.
  replace Pa with Pa0; auto.
  now apply inj_pair2_eq_dec.
  Qed.

  Lemma Dependent_Forall_inf_dec : forall (P :A -> Type) Pred,
    (forall a Pa, Pred a Pa + (Pred a Pa -> False)) ->
      forall l (Fl : Forall_inf P l),
        Dependent_Forall_inf Pred Fl + (Dependent_Forall_inf Pred Fl -> False).
  Proof.
  intros P Pred dec_Pred l Fl; induction Fl.
  - left.
    apply Dependent_Forall_inf_nil.
  - destruct IHFl as [HFl | HFl].
    + destruct dec_Pred with x p as [HPa | HnPa].
      * left.
        now apply Dependent_Forall_inf_cons.
      * right.
        intro DFl; inversion DFl.
        apply HnPa.
        replace p with Pa; auto.
        now apply inj_pair2_eq_dec.
    + right.
      intro DFl; inversion DFl.
      apply inj_pair2_eq_dec in H3; [ | now apply list_eq_dec ].
      now apply HFl; subst.
  Qed.

  Lemma Dependent_Forall_inf_arrow : forall (P : A -> Type) Pred1 Pred2,
    (forall a Pa, Pred1 a Pa -> Pred2 a Pa) ->
    forall l (Fl : Forall_inf P l), Dependent_Forall_inf Pred1 Fl -> Dependent_Forall_inf Pred2 Fl.
  Proof.
  intros P Pred1 Pred2 f l Fl DFl.
  induction DFl; constructor; auto.
  Qed.

  Lemma Dependent_Forall_inf_app : forall (P : A -> Type) Pred,
    forall l1 l2 (Fl1 : Forall_inf P l1) (Fl2 : Forall_inf P l2),
      Dependent_Forall_inf Pred Fl1 -> Dependent_Forall_inf Pred Fl2 ->
      { Fl : Forall_inf P (l1 ++ l2) & Dependent_Forall_inf Pred Fl }.
  Proof.
  intros P Pred l1 l2 Fl1 Fl2 DFl1; revert Fl2; induction DFl1; intros Fl2 DFl2.
  - now split with Fl2.
  - destruct IHDFl1 with Fl2 as (Fl0 & DFl); auto.
    split with (Forall_inf_cons a Pa Fl0).
    now apply Dependent_Forall_inf_cons.
  Qed.

  Lemma Dependent_Forall_inf_app_inv : forall (P : A -> Type) Pred,
    forall l1 l2 (Fl : Forall_inf P (l1 ++ l2)), Dependent_Forall_inf Pred Fl ->
       { Fl1 : Forall_inf P l1 & Dependent_Forall_inf Pred Fl1 }
     * { Fl2 : Forall_inf P l2 & Dependent_Forall_inf Pred Fl2 }.
  Proof.
  intros P Pred l1 l2 Fl; induction l1; intro DFl.
  - split.
    + split with (Forall_inf_nil P).
      apply Dependent_Forall_inf_nil.
    + now split with Fl.
  - inversion DFl.
    destruct IHl1 with Fl0 as ((Fl1 & DFl1) & (Fl2 & DFl2)); auto.
    split.
    + split with (Forall_inf_cons a Pa Fl1).
      now apply Dependent_Forall_inf_cons.
    + now split with Fl2.
  Qed.

  Lemma Dependent_Forall_inf_elt_inv : forall (P : A -> Type) Pred,
    forall l1 l2 a (Fl : Forall_inf P (l1 ++ a :: l2)),
      Dependent_Forall_inf Pred Fl -> { Pa : P a & Pred a Pa }.
  Proof.
  intros P Pred l1 l2 a Fl DFl.
  apply Dependent_Forall_inf_app_inv in DFl.
  destruct DFl as [_ [Fl2 DFl2]].
  inversion DFl2; subst.
  now exists Pa.
  Qed.

End Eq_Dec.
