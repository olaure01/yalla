(** Some results on association lists *)

(* see https://www.cis.upenn.edu/~plclub/metalib/current/html/AssocList.html
   and https://caml.inria.fr/pub/docs/manual-ocaml/libref/List.html#1_Associationlists
   for more global approaches *)

From Coq Require Import Bool.
From Coq Require Export List.
From Yalla.OLlibs Require Export dectype.

Set Implicit Arguments.
Set Default Proof Using "Type".


(** [remove_assoc] *)

Section RemoveAssoc.

  Variable T1 : DecType.
  Variable T2 : Type.
  Variable x : T1.
  Implicit Type L : list (T1 * T2).

  Definition remove_assoc L := filter (fun '(y, _) => negb (eqb x y)) L.

  Lemma remove_assoc_remove L :
    remove eq_dt_dec x (map fst L) = map fst (remove_assoc L).
  Proof.
  induction L as [|a L IHL]; simpl; [ reflexivity | rewrite IHL ]; destruct a; simpl.
  now repeat case_analysis; [ | exfalso | ].
  Qed.

  Lemma remove_assoc_notin L y a:
    x <> y -> In (y, a) L -> In (y, a) (remove_assoc L).
  Proof.
  intros; apply filter_In; split; [ assumption | ].
  now apply negb_true_iff, eqb_neq.
  Qed.

  Lemma snd_remove_assoc L :
    incl (map snd (remove_assoc L)) (map snd L).
  Proof. apply incl_map, incl_filter. Qed.

  Lemma NoDup_remove_assoc_snd L :
    NoDup (map snd L) -> NoDup (map snd (remove_assoc L)).
  Proof.
  induction L as [|a L IHL]; simpl; intros Hnd; [ constructor | destruct a ].
  inversion_clear Hnd as [| ? ? Hnin Hnd2 ].
  case_analysis; [ auto | ].
  constructor; try intros Hin; [ | auto ].
  apply snd_remove_assoc in Hin.
  apply Hnin, Hin.
  Qed.

  Lemma NoDup_remove_assoc_in L y i :
    NoDup (map snd L) -> In (y, i) L -> In i (map snd (remove_assoc L)) ->
    In (y, i) (remove_assoc L).
  Proof.
  intros Hnd Hin1 Hin2.
  apply remove_assoc_notin; [ | apply snd_remove_assoc in Hin2; exact Hin1 ].
  intros <-.
  revert Hnd Hin1 Hin2. clear. induction L as [|(t1, t2) L IHL]; simpl; [ trivial | ].
  intros Hnd Hin1. inversion Hnd as [| ? ? Hnin Hnd2]; case_analysis; intros Hin2.
  - subst.
    apply IHL; [ assumption | | assumption ].
    destruct Hin1 as [[= ->]|]; [ | assumption ].
    contradiction Hnin.
    apply snd_remove_assoc in Hin2. exact Hin2.
  - destruct Hin2 as [ Heq' | Hin2 ]; subst.
    + destruct Hin1 as [ [= ->] | Hin1 ].
      * contradiction.
      * apply Hnin. apply in_map with (f:= snd) in Hin1. exact Hin1.
    + apply IHL in Hin2; destruct Hin1 as [[= ->]|Hin1]; auto; exfalso; auto.
  Qed.

End RemoveAssoc.

Arguments remove_assoc {_ _} _ _.
