(** Generalization of [Forall_inf] to dependent product *)

From Coq Require Export Eqdep_dec.
From Coq Require Import PeanoNat List.
From Yalla.OLlibs Require Import List_Type.

Set Implicit Arguments.
Set Default Proof Using "Type".


(** * [In_Forall_inf] *)

Section In_Forall_inf.
  Variable A : Type.
  Variable P : A -> Type.

  Fixpoint In_Forall_inf l (a : A) (Pa : P a) (Fl : Forall_inf P l) : Type :=
    match Fl with
    | Forall_inf_nil _ => False
    | Forall_inf_cons b Pb Fl => ((existT P a Pa) = (existT P b Pb)) + In_Forall_inf Pa Fl
    end.

  Lemma In_Forall_inf_elt l1 l2 a (Fl : Forall_inf P (l1 ++ a :: l2)) : { Pa : P a & In_Forall_inf Pa Fl }.
  Proof.
  induction l1 as [|b l1 IHl1] in l2, a, Fl |- *.
  - simpl in Fl.
    remember (a :: l2) eqn:Heql.
    destruct Fl as [|? ? p Fl]; inversion Heql; subst.
    exists p. left. reflexivity.
  - remember ((b :: l1) ++ a :: l2) eqn:Heql.
    destruct Fl as [|? ? p Fl]; inversion Heql; subst.
    destruct IHl1 with l2 a Fl as [Pa Hin].
    exists Pa. right. assumption.
  Qed.

  Lemma In_Forall_inf_in l a (Fl : Forall_inf P l) : In_inf a l -> { Pa : P a & In_Forall_inf Pa Fl }.
  Proof.
  induction l as [|b l IHl] in a, Fl |- *; intros Hin; inversion Hin; subst.
  - remember (a :: l) as l' eqn:Heql'.
    destruct Fl as [|? ? p Fl]; inversion Heql'; subst.
    exists p. left. reflexivity.
  - remember (b :: l) as l' eqn:Heql'.
    destruct Fl as [|? ? p Fl]; inversion Heql'; subst.
    destruct IHl with a Fl as [Pa Hin']; [ assumption | ].
    exists Pa. right. assumption.
  Qed.

  Fixpoint Forall_inf_sum (f : forall a, P a -> nat) (l : list A) (Pl : Forall_inf P l) :=
    match Pl with
    | Forall_inf_nil _ => 0
    | Forall_inf_cons x Px Pl => (f x Px) + (Forall_inf_sum f Pl)
    end.

  Fixpoint Forall_inf_App l1 l2 Pl1 Pl2 :=
    match Pl1 with
    | Forall_inf_nil _ => Pl2
    | @Forall_inf_cons _ _ x l Px Pl => @Forall_inf_cons _ P x (l ++ l2) Px
                                                         (Forall_inf_App l l2 Pl Pl2)
    end.

  Lemma Forall_inf_sum_app f l1 l2 (Pl1 : Forall_inf P l1) (Pl2 : Forall_inf P l2) :
      Forall_inf_sum f (Forall_inf_App Pl1 Pl2)
    = Forall_inf_sum f Pl1 + Forall_inf_sum f Pl2.
  Proof. induction Pl1 as [| ? ? ? ? IHPl1]; [ reflexivity | ]. simpl. rewrite IHPl1. apply Nat.add_assoc. Qed.

  Lemma In_Forall_inf_to_In_inf l (L : list A) (p : P l) (PL : Forall_inf P L) : In_Forall_inf p PL -> In_inf l L.
  Proof.
  intros Hin. induction PL; [ inversion Hin | inversion Hin as [He|]]; [ left | right; auto ].
  injection He as [= ->]. reflexivity.
  Qed.

End In_Forall_inf.


(** * [Dependent_Forall_inf] *)

Inductive Dependent_Forall_inf A (P : A -> Type) (Pred : forall a, P a -> Type) :
   forall l, Forall_inf P l -> Type :=
| Dependent_Forall_inf_nil : Dependent_Forall_inf Pred (Forall_inf_nil P)
| Dependent_Forall_inf_cons a l Pa (Fl : Forall_inf P l) : (Pred a Pa) ->
           Dependent_Forall_inf Pred Fl -> Dependent_Forall_inf Pred (Forall_inf_cons a Pa Fl).

Section Eq_Dec.

  Variable A : Type.
  Hypothesis eq_dec : forall (x y : A), {x = y} + {x <> y}.

  Lemma Dependent_Forall_inf_forall (P : A -> Type) Pred l a Pa (Fl : Forall_inf P l) :
    Dependent_Forall_inf Pred Fl -> In_Forall_inf a Pa Fl -> Pred a Pa.
  Proof using eq_dec.
  intros DFl. revert a Pa; induction DFl as [|? ? ? ? ? ? IH]; intros a' Pa' Hin;
    [ inversion Hin | inversion Hin as [He|Heq] ].
  - injection He as [= -> He].
    apply inj_pair2_eq_dec in He as ->; assumption.
  - apply IH. assumption.
  Qed.

  Lemma forall_Dependent_Forall_inf (P : A -> Type) Pred l (Fl : Forall_inf P l) :
    (forall a Pa, In_Forall_inf a Pa Fl -> Pred a Pa) ->
    Dependent_Forall_inf Pred Fl.
  Proof.
  induction Fl as [|? ? ? ? IH]; intros f; constructor.
  - apply f. left. reflexivity.
  - apply IH. intros a Pa Hin.
    apply f. right. assumption.
  Qed.

  Lemma Dependent_Forall_inf_inv (P : A -> Type) Pred a l Pa : forall (Pl : Forall_inf P l),
    Dependent_Forall_inf Pred (Forall_inf_cons a Pa Pl) -> Pred a Pa.
  Proof using eq_dec.
  intros Pl DPl. inversion DPl as [| ? ? Pb]. subst.
  replace Pa with Pb; [ assumption | ].
  apply inj_pair2_eq_dec; assumption.
  Qed.

  Lemma Dependent_Forall_inf_dec (P :A -> Type) Pred (dec_Pred : forall a Pa, Pred a Pa + notT (Pred a Pa)) l
    (Fl : Forall_inf P l) : Dependent_Forall_inf Pred Fl + (Dependent_Forall_inf Pred Fl -> False).
  Proof using eq_dec.
  induction Fl as [|x l p ? [HFl|HFl]].
  - left. apply Dependent_Forall_inf_nil.
  - destruct dec_Pred with x p as [HPa | HnPa].
    + left. apply Dependent_Forall_inf_cons; assumption.
    + right. intro DFl. inversion DFl as [|? ? Pb].
      apply HnPa.
      replace p with Pb; [ assumption | ].
      apply inj_pair2_eq_dec; assumption.
  - right. intro DFl. inversion DFl as [|? ? ? ? ? ? Heq [He1 He2]].
    apply inj_pair2_eq_dec in He2; [ subst | apply list_eq_dec, eq_dec ].
    apply HFl. assumption.
  Qed.

  Lemma Dependent_Forall_inf_arrow (P : A -> Type) Pred1 Pred2 :
    (forall a Pa, Pred1 a Pa -> Pred2 a Pa) ->
    forall l (Fl : Forall_inf P l), Dependent_Forall_inf Pred1 Fl -> Dependent_Forall_inf Pred2 Fl.
  Proof. intros f l Fl DFl. induction DFl; constructor; auto. Qed.

  Lemma Dependent_Forall_inf_app (P : A -> Type) Pred l1 l2 (Fl1 : Forall_inf P l1) (Fl2 : Forall_inf P l2) :
    Dependent_Forall_inf Pred Fl1 -> Dependent_Forall_inf Pred Fl2 ->
    { Fl : Forall_inf P (l1 ++ l2) & Dependent_Forall_inf Pred Fl }.
  Proof.
  intros DFl1. induction DFl1 as [|a l Pa ? ? ? IH] in Fl2 |- *; intros DFl2.
  - exists Fl2. assumption.
  - destruct IH with Fl2 as [Fl0 DFl]; [ assumption | ].
    exists (Forall_inf_cons a Pa Fl0).
    apply Dependent_Forall_inf_cons; assumption.
  Qed.

  Lemma Dependent_Forall_inf_app_inv (P : A -> Type) Pred l1 l2 (Fl : Forall_inf P (l1 ++ l2)) :
     Dependent_Forall_inf Pred Fl ->
       { Fl1 : Forall_inf P l1 & Dependent_Forall_inf Pred Fl1 }
     * { Fl2 : Forall_inf P l2 & Dependent_Forall_inf Pred Fl2 }.
  Proof.
  induction l1 as [|a l1 IHl1]; intro DFl.
  - split.
    + exists (Forall_inf_nil P). apply Dependent_Forall_inf_nil.
    + exists Fl. assumption.
  - inversion DFl as [|b lb Pa Fl0].
    destruct IHl1 with Fl0 as [[Fl1 DFl1] [Fl2 DFl2]]; [ assumption | ].
    split.
    + exists (Forall_inf_cons a Pa Fl1).
      apply Dependent_Forall_inf_cons; assumption.
    + exists Fl2. assumption.
  Qed.

  Lemma Dependent_Forall_inf_elt_inv (P : A -> Type) Pred l1 l2 a (Fl : Forall_inf P (l1 ++ a :: l2)) :
    Dependent_Forall_inf Pred Fl -> { Pa : P a & Pred a Pa }.
  Proof.
  intros DFl. apply Dependent_Forall_inf_app_inv in DFl as [_ [Fl2 DFl2]].
  inversion_clear DFl2 as [|b l Pa]. exists Pa. assumption.
  Qed.

End Eq_Dec.


From Yalla.OLlibs Require Import dectype.
From Yalla.OLlibs Require issue12394. (* TODO remove when issue #12394 solved *)

(* TODO dealing with issue coq/coq#12394 *)
(* Example:
  [ old code
         apply inj_pair2_eq_dec in H2; [ | apply list_eq_dec, (@eq_dt_dec Hdec)].
         apply inj_pair2_eq_dec in H3; [ | apply list_eq_dec, list_eq_dec (@eq_dt_dec Hdec)].
         subst.
    new code should be cbnified or old code back once coq/coq#12394 solved
         apply inj_pair2_eq_dec in H2;
           [ | apply (@list_eq_dec _ (@eqb (list_dectype Hdec))); apply eqb_eq ].
         assert (Pa = p) as Heq; subst.
         { apply issue12394.injection_list_Forall_inf_cons in H2 as [-> _]; [ reflexivity | ].
           apply (@list_eq_dec _ (@eqb Hdec)); apply eqb_eq. } *)
Ltac Dependent_Forall_inversion Hdec H :=
  match type of H with
  | Dependent_Forall_inf _ _ =>
    let a := fresh in
    let b := fresh in
    let L := fresh "L" in
    let H1 := fresh H in
    let H2 := fresh H in
    let H3 := fresh H in
    let Heq1 := fresh in
    let Heq2 := fresh in
    let Heq := fresh "HeqD" in
    inversion H as [|a b L H1 H2 H3 [Heq1 Heq2] Heq]; subst a; subst b;
    apply inj_pair2_eq_dec in Heq;
      [ | apply (@list_eq_dec _ (@eqb (list_dectype Hdec))); apply eqb_eq ];
    apply issue12394.injection_list_Forall_inf_cons in Heq as [-> ->];
      [ | apply (@list_eq_dec _ (@eqb Hdec)); apply eqb_eq ]
  end.
