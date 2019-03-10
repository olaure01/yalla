Require Import List_Type_more.

Section One_predicate.
  Context {A : Type}.
  Variable P : A -> Type.

  Fixpoint In_Forall_Type {l} (a : A) (Pa : P a) (Fl : Forall_Type P l) : Type :=
    match Fl with
    | Forall_Type_nil _ => False
    | Forall_Type_cons b Pb Fl => ((existT P a Pa) = (existT P b Pb)) + In_Forall_Type a Pa Fl
    end.

  Lemma In_Forall_Type_elt: forall l1 l2 a (Fl : Forall_Type P (l1 ++ a :: l2)),
      {Pa & In_Forall_Type a Pa Fl}.
  Proof with try assumption.
    intros l1.
    induction l1; intros l2 a' Fl.
    - simpl in Fl.
      remember (a' :: l2).
      destruct Fl; inversion Heql.
      subst.
      split with p.
      left.
      reflexivity.
    - remember ((a :: l1) ++ a' :: l2).
      destruct Fl; inversion Heql.
      subst.
      destruct IHl1 with l2 a' Fl as (Pa , Hin)...
      split with Pa.
      right...
  Qed.

  Lemma In_Forall_Type_in : forall l a (Fl : Forall_Type P l),
      In_Type a l ->
      {Pa & In_Forall_Type a Pa Fl}.
  Proof with try assumption.
    intros l.
    induction l; intros a' Fl Hin; inversion Hin.
    - subst.
      remember (a' :: l) as l'.
      destruct Fl; inversion Heql'.
      subst.
      split with p.
      left.
      reflexivity.
    - remember (a :: l) as l'.
      destruct Fl; inversion Heql'.
      subst.
      destruct IHl with a' Fl as (Pa & Hin')...
      split with Pa.
      right...
  Qed.
   
  Fixpoint Forall_Type_sum (f : forall a, P a -> nat) (l : list A) (Pl : Forall_Type P l) :=
    match Pl with
    | Forall_Type_nil _ => 0
    | @Forall_Type_cons _ _ x l Px Pl => (f x Px) + (Forall_Type_sum f l Pl)
    end.

  Lemma Forall_Type_sum_cons : forall f a Pa l Pl, Forall_Type_sum f (a :: l) (@Forall_Type_cons _ _ a l Pa Pl) = (f a Pa) + Forall_Type_sum f l Pl.
  Proof.
    intros f a Pa l Pl.
    reflexivity.
  Qed.

  Fixpoint Forall_Type_App l1 l2 Pl1 Pl2 :=
    match Pl1 with
    | Forall_Type_nil _ => Pl2
    | @Forall_Type_cons _ _ x l Px Pl => @Forall_Type_cons _ P x (l ++ l2) Px (Forall_Type_App l l2 Pl Pl2)
    end.

  Lemma Forall_Type_sum_app : forall f l1 l2 Pl1 Pl2, Forall_Type_sum f (l1 ++ l2) (Forall_Type_App l1 l2 Pl1 Pl2) = Forall_Type_sum f l1 Pl1 + Forall_Type_sum f l2 Pl2.
  Proof.
    intros f l1 l2 Pl1 Pl2.
    induction Pl1.
    - reflexivity.
    - simpl; rewrite IHPl1.
      apply Plus.plus_assoc.
  Qed.

End One_predicate.

Fixpoint list_to_Forall {T} {P} (l : list (sigT P)) : Forall_Type P (map (@projT1 T P) l) :=
  match l with
  | nil => Forall_Type_nil _
  | p :: l => Forall_Type_cons (projT1 p) (projT2 p) (list_to_Forall l)
  end.

Fixpoint Forall_to_list {T} {P} {l : list T} (Fl : Forall_Type P l) : list (sigT P) :=
  match Fl with
  | Forall_Type_nil _ => nil
  | Forall_Type_cons x Px Fl => (existT P x Px) :: (Forall_to_list Fl)
  end.

Lemma Forall_to_list_support {T} {P} L FL :
   map (@projT1 _ _) (@Forall_to_list T P L FL) = L.
Proof.
induction FL ; simpl ; try rewrite IHFL ; reflexivity.
Defined.

Lemma Forall_to_list_length {T} {P} (l : list T) (Fl : Forall_Type P l) :
  length (Forall_to_list Fl) = length l.
Proof.
  induction Fl.
  - reflexivity.
  - simpl; rewrite IHFl; reflexivity.
Qed.


Import EqNotations.

Lemma Forall_to_list_to_Forall {T} {P} :
   forall L FL, rew (Forall_to_list_support _ _) in list_to_Forall 
(@Forall_to_list T P L FL) = FL.
Proof.
induction FL ; simpl.
- reflexivity.
- transitivity (Forall_Type_cons x p
                (rew [Forall_Type P] Forall_to_list_support l FL in 
                    list_to_Forall (Forall_to_list FL))).
   + clear.
     destruct (Forall_to_list_support l FL) ; reflexivity.
   + rewrite IHFL ; reflexivity.
Qed.