(** Generalization of [Forall_inf] to dependent product *)

Require Export Eqdep_dec.
Require Import PeanoNat List.
Require Import List_Type.

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

  Lemma In_Forall_inf_elt l1 l2 a : forall Fl : Forall_inf P (l1 ++ a :: l2),
      { Pa : P a & In_Forall_inf Pa Fl }.
  Proof.
  revert l2 a; induction l1 as [|a l1 IHl1]; intros l2 a' Fl.
  - simpl in Fl.
    remember (a' :: l2) eqn:Heql.
    destruct Fl as [|? ? p Fl]; inversion Heql; subst.
    now split with p; left.
  - remember ((a :: l1) ++ a' :: l2) eqn:Heql.
    destruct Fl as [|? ? p Fl]; inversion Heql; subst.
    destruct IHl1 with l2 a' Fl as [Pa Hin]; auto.
    now split with Pa; right.
  Qed.

  Lemma In_Forall_inf_in l a  : forall Fl : Forall_inf P l,
    In_inf a l -> { Pa : P a & In_Forall_inf Pa Fl }.
  Proof.
  revert a; induction l as [|a l IHl]; intros a' Fl Hin; inversion Hin; subst.
  - remember (a' :: l) as l' eqn:Heql'.
    destruct Fl as [|? ? p Fl]; inversion Heql'; subst.
    now split with p; left.
  - remember (a :: l) as l' eqn:Heql'.
    destruct Fl as [|? ? p Fl]; inversion Heql'; subst.
    destruct IHl with a' Fl as [Pa Hin']; auto.
    now split with Pa; right.
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

  Lemma Forall_inf_sum_app f l1 l2 : forall (Pl1 : Forall_inf P l1) (Pl2 : Forall_inf P l2),
      Forall_inf_sum f (Forall_inf_App Pl1 Pl2)
    = Forall_inf_sum f Pl1 + Forall_inf_sum f Pl2.
  Proof.
  intros Pl1; induction Pl1 as [| ? ? ? ? IHPl1]; auto.
  simpl; intros; rewrite IHPl1.
  apply Nat.add_assoc.
  Qed.

  Lemma In_Forall_inf_to_In_inf l (L : list A) (p : P l) : forall (PL : Forall_inf P L),
    In_Forall_inf p PL -> In_inf l L.
  Proof.
  intros PL Hin; induction PL; [ inversion Hin | inversion Hin as [He|]]; intuition.
  now left; inversion He.
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

  Lemma Dependent_Forall_inf_forall (P : A -> Type) Pred l a Pa : forall (Fl : Forall_inf P l),
    Dependent_Forall_inf Pred Fl -> In_Forall_inf a Pa Fl -> Pred a Pa.
  Proof.
  intros Fl DFl; revert a Pa;
    induction DFl as [|? ? ? ? ? ? IH]; intros a' Pa' Hin;
    [ inversion Hin | inversion Hin as [He|Heq] ].
  - inversion He as [[Heq He]]; subst.
    apply inj_pair2_eq_dec in He; auto.
    now rewrite He.
  - now apply IH.
  Qed.

  Lemma forall_Dependent_Forall_inf (P : A -> Type) Pred l : forall (Fl : Forall_inf P l),
    (forall a Pa, In_Forall_inf a Pa Fl -> Pred a Pa) ->
    Dependent_Forall_inf Pred Fl.
  Proof.
  intros Fl; induction Fl as [|? ? ? ? IH]; intros f.
  - apply Dependent_Forall_inf_nil.
  - apply Dependent_Forall_inf_cons.
    + now apply f; left.
    + apply IH; intros a Pa Hin.
      now apply f; right.
  Qed.

  Lemma Dependent_Forall_inf_inv (P : A -> Type) Pred a l Pa : forall (Pl : Forall_inf P l),
    Dependent_Forall_inf Pred (Forall_inf_cons a Pa Pl) -> Pred a Pa.
  Proof.
  intros Pl DPl; inversion DPl as [| ? ? Pb] ; subst.
  replace Pa with Pb; auto.
  now apply inj_pair2_eq_dec.
  Qed.

  Lemma Dependent_Forall_inf_dec (P :A -> Type) Pred :
    (forall a Pa, Pred a Pa + (Pred a Pa -> False)) ->
    forall l (Fl : Forall_inf P l),
    Dependent_Forall_inf Pred Fl + (Dependent_Forall_inf Pred Fl -> False).
  Proof.
  intros dec_Pred l Fl; induction Fl as [|x l p ? [HFl|HFl]].
  - left.
    apply Dependent_Forall_inf_nil.
  - destruct dec_Pred with x p as [HPa | HnPa].
    + now left; apply Dependent_Forall_inf_cons.
    + right; intro DFl; inversion DFl as [|? ? Pb].
      apply HnPa.
      replace p with Pb; auto.
      now apply inj_pair2_eq_dec.
  - right; intro DFl; inversion DFl as [|? ? ? ? ? ? Heq [He1 He2]].
    apply inj_pair2_eq_dec in He2; [ | now apply list_eq_dec ].
    now apply HFl; subst.
  Qed.

  Lemma Dependent_Forall_inf_arrow (P : A -> Type) Pred1 Pred2 :
    (forall a Pa, Pred1 a Pa -> Pred2 a Pa) ->
    forall l (Fl : Forall_inf P l), Dependent_Forall_inf Pred1 Fl -> Dependent_Forall_inf Pred2 Fl.
  Proof. intros f l Fl DFl; induction DFl; constructor; auto. Qed.

  Lemma Dependent_Forall_inf_app (P : A -> Type) Pred l1 l2 :
    forall (Fl1 : Forall_inf P l1) (Fl2 : Forall_inf P l2),
    Dependent_Forall_inf Pred Fl1 -> Dependent_Forall_inf Pred Fl2 ->
    { Fl : Forall_inf P (l1 ++ l2) & Dependent_Forall_inf Pred Fl }.
  Proof.
  intros Fl1 Fl2 DFl1; revert Fl2; induction DFl1 as [|a l Pa ? ? ? IH]; intros Fl2 DFl2.
  - now split with Fl2.
  - destruct IH with Fl2 as [Fl0 DFl]; auto.
    split with (Forall_inf_cons a Pa Fl0).
    now apply Dependent_Forall_inf_cons.
  Qed.

  Lemma Dependent_Forall_inf_app_inv (P : A -> Type) Pred l1 l2 : forall (Fl : Forall_inf P (l1 ++ l2)),
     Dependent_Forall_inf Pred Fl ->
       { Fl1 : Forall_inf P l1 & Dependent_Forall_inf Pred Fl1 }
     * { Fl2 : Forall_inf P l2 & Dependent_Forall_inf Pred Fl2 }.
  Proof.
  intros Fl; induction l1 as [|a l1 IHl1]; intro DFl.
  - split.
    + split with (Forall_inf_nil P).
      apply Dependent_Forall_inf_nil.
    + now split with Fl.
  - inversion DFl as [|b lb Pa Fl0].
    destruct IHl1 with Fl0 as [[Fl1 DFl1] [Fl2 DFl2]]; auto.
    split.
    + split with (Forall_inf_cons a Pa Fl1).
      now apply Dependent_Forall_inf_cons.
    + now split with Fl2.
  Qed.

  Lemma Dependent_Forall_inf_elt_inv (P : A -> Type) Pred l1 l2 a :
    forall (Fl : Forall_inf P (l1 ++ a :: l2)),
    Dependent_Forall_inf Pred Fl -> { Pa : P a & Pred a Pa }.
  Proof.
  intros Fl DFl; apply Dependent_Forall_inf_app_inv in DFl as [_ [Fl2 DFl2]].
  inversion_clear DFl2 as [|b l Pa].
  now exists Pa.
  Qed.

End Eq_Dec.
