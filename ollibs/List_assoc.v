(** Some results on association lists *)

(* see https://www.cis.upenn.edu/~plclub/metalib/current/html/AssocList.html
   and https://caml.inria.fr/pub/docs/manual-ocaml/libref/List.html#1_Associationlists
   for more global approaches *)

From Coq Require Import Bool.
From Coq Require Export List.
From OLlibs Require Export dectype.

Set Implicit Arguments.


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
  induction L; simpl; [ reflexivity | rewrite IHL ]; destruct a; simpl.
  repeat case_analysis; intuition.
  exfalso; intuition.
  Qed.

  Lemma remove_assoc_notin L :
    forall y a, x <> y -> In (y, a) L -> In (y, a) (remove_assoc L).
  Proof.
  intros; apply filter_In; split; auto.
  now apply negb_true_iff, eqb_neq.
  Qed.

  Lemma snd_remove_assoc L :
    incl (map snd (remove_assoc L)) (map snd L).
  Proof. apply incl_map, incl_filter. Qed.

  Lemma NoDup_remove_assoc_snd L :
    NoDup (map snd L) -> NoDup (map snd (remove_assoc L)).
  Proof.
  induction L; simpl; intros Hnd; [ constructor | destruct a ].
  inversion_clear Hnd.
  case_analysis; intuition.
  constructor; intuition.
  apply snd_remove_assoc in H2.
  now apply H.
  Qed.

  Lemma NoDup_remove_assoc_in L y i :
    NoDup (map snd L) -> In (y, i) L -> In i (map snd (remove_assoc L)) ->
    In (y, i) (remove_assoc L).
  Proof.
  intros Hnd Hin1 Hin2.
  apply remove_assoc_notin; [ | apply snd_remove_assoc in Hin2; intuition ].
  intros Heq; symmetry in Heq; subst.
  revert Hnd Hin1 Hin2; clear; induction L; [ intuition | ].
  destruct a; simpl.
  intros Hnd Hin1; inversion_clear Hnd; case_analysis; intros Hin2.
  - symmetry in Heq; subst.
    apply IHL; intuition.
    exfalso; inversion H1; subst.
    apply H.
    now apply snd_remove_assoc in Hin2.
  - destruct Hin2 as [ Heq' | Hin2 ]; subst.
    + destruct Hin1 as [ Hin1 | Hin1 ].
      * inversion Hin1; subst; intuition.
      * apply H; now apply in_map with (f:= snd) in Hin1.
    + apply IHL in Hin2; intuition.
      exfalso; apply Heq; now inversion H1.
  Qed.

End RemoveAssoc.

Arguments remove_assoc {_} {_} _ _.
