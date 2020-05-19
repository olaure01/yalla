(** Turn goals involving [Permutation_Type] into similar ones with [Permutation]
this requires a type with decidable equality
this allows to solve the goal through the use of rewrite *)
(* it is not possible directly because of Issue #7675 *)
(* Issue#7675 is not a problem for PCPermutation_Type, see Issue#12240 *)

(* similarly with CPermutation_Type and CPermutation *)
(* and then  with PCEPermutation_Type and PCEPermutation *)
(* and then  with PCPermutation_Type and PCPermutation *)
(* and then  with PEPermutation_Type and PEPermutation *)


From Coq Require Import List PeanoNat Compare_dec.
From Coq Require Export Permutation CPermutation.
From OLlibs Require Import List_Type.
From OLlibs Require Export Permutation_Type CPermutation_Type GPermutation GPermutation_Type.

Set Implicit Arguments.


(** * [Permutation] case *)

Section Permutation.

  Variable A : Type.

  Lemma notF_Permutation_Type_notF_Permutation (l1 l2 : list A) (F : Prop):
    (Permutation_Type l1 l2 -> F) -> Permutation l1 l2 -> F.
  Proof.
  intros HnP HP; revert HnP; induction HP; intros HnP; intuition.
  - apply HnP; constructor.
  - apply IHHP1; intros IHHP1'.
    apply IHHP2; intros IHHP2'.
    apply HnP; etransitivity; eassumption.
  Qed.

  Lemma not_Permutation_Type_not_Permutation (l1 l2 : list A):
    (Permutation_Type l1 l2 -> False) -> ~ Permutation l1 l2.
  Proof. intros HnP HP; now apply (notF_Permutation_Type_notF_Permutation HnP). Qed.

  Section Dec.

    Hypothesis EqDec : forall x y : A, {x = y} + {x <> y}.

    Lemma Permutation_Type_dec (l1 l2 : list A):
      Permutation_Type l1 l2 + (Permutation_Type l1 l2 -> False).
    Proof.
    revert l2; induction l1; intros l2.
    - destruct l2.
      + left; constructor.
      + right; apply Permutation_Type_nil_cons.
    - destruct (in_inf_dec EqDec a l2) as [Hin | Hnin].
      + destruct (in_inf_split _ _ Hin) as [(l2', l2'') ->].
        destruct (IHl1 (l2' ++ l2'')) as [HP | HnP]; [left|right].
        * now apply Permutation_Type_cons_app.
        * intros HP; apply HnP.
          now apply Permutation_Type_cons_app_inv in HP.
      + right; intros HP; apply Hnin.
        apply (Permutation_Type_in_inf _ HP).
        now constructor.
    Qed.

    Lemma Permutation_Permutation_Type (l1 l2 : list A):
      Permutation l1 l2 -> Permutation_Type l1 l2.
    Proof.
    intros HP; destruct (Permutation_Type_dec l1 l2); [ assumption | ].
    exfalso; revert HP; now apply not_Permutation_Type_not_Permutation.
    Qed.

  End Dec.

End Permutation.


(** * [CPermutation] case *)

Section CPermutation.

  Variable A : Type.

  Lemma notF_CPermutation_Type_notF_CPermutation (l1 l2 : list A) (F : Prop):
    (CPermutation_Type l1 l2 -> F) -> CPermutation l1 l2 -> F.
  Proof. intros HnP HP; revert HnP; induction HP; intros HnP; apply HnP; constructor. Qed.

  Lemma not_CPermutation_Type_not_CPermutation (l1 l2 : list A):
    (CPermutation_Type l1 l2 -> False) -> ~ CPermutation l1 l2.
  Proof. intros HnP HP; now apply (notF_CPermutation_Type_notF_CPermutation HnP). Qed.

  Section Dec.

    Hypothesis EqDec : forall x y : A, {x = y} + {x <> y}.

    Lemma CPermutation_Type_dec (l1 l2 : list A):
      CPermutation_Type l1 l2 + (CPermutation_Type l1 l2 -> False).
    Proof.
    assert (forall k, { n | l2 = skipn n l1 ++ firstn n l1 }
                    + (forall n, n < k -> l2 <> skipn n l1 ++ firstn n l1)) as Hk.
    { induction k.
      - right; intros n Hn; inversion Hn.
      - destruct IHk as [[n Hn]|Hnn].
        + left; now exists n.
        + destruct (list_eq_dec EqDec l2 (skipn k l1 ++ firstn k l1)) as [Hk|Hnk]; [left|right].
          * now exists k.
          * intros n Hn; inversion Hn; auto. }
    assert ({ n | l2 = skipn n l1 ++ firstn n l1 }
         + ({ n | l2 = skipn n l1 ++ firstn n l1 } -> False)) as [[n ->] | Hns].
    { destruct (Hk (S (length l1))) as [Hn|Hnn]; [left|right]; auto.
      intros [n ->].
      destruct (lt_dec n (length l1)) as [Hlt|Hle].
      - apply (Hnn n); auto.
      - apply Nat.nlt_ge in Hle.
        apply (Hnn (length l1)); auto.
        now rewrite skipn_all, skipn_all2, firstn_all, firstn_all2. }
    - left; apply CPermutation_Type_skipn_firstn.
    - right; intros HP; now apply Hns, CPermutation_Type_split.
    Qed.

    Lemma CPermutation_CPermutation_Type (l1 l2 : list A):
      CPermutation l1 l2 -> CPermutation_Type l1 l2.
    Proof.
    intros HP; destruct (CPermutation_Type_dec l1 l2); [ assumption | ].
    exfalso; revert HP; now apply not_CPermutation_Type_not_CPermutation.
    Qed.

  End Dec.

End CPermutation.


(** * [PCEPermutation] case *)

Section PCEPermutation.

  Variable A : Type.

  Lemma not_PCEPermutation_Type_not_PCEPermutation c (l1 l2 : list A):
    (PCEPermutation_Type c l1 l2 -> False) -> ~ PCEPermutation c l1 l2.
  Proof.
  now destruct c; [ apply not_CPermutation_Type_not_CPermutation |
                  | apply not_Permutation_Type_not_Permutation ].
  Qed.

  Section Dec.

    Hypothesis EqDec : forall x y : A, {x = y} + {x <> y}.

    Lemma PCEPermutation_Type_dec c (l1 l2 : list A):
      PCEPermutation_Type c l1 l2 + (PCEPermutation_Type c l1 l2 -> False).
    Proof.
    destruct c; [ apply CPermutation_Type_dec | | apply Permutation_Type_dec ]; auto.
    destruct (list_eq_dec EqDec l1 l2); intuition.
    Qed.

    Lemma PCEPermutation_PCEPermutation_Type c (l1 l2 : list A):
      PCEPermutation c l1 l2 -> PCEPermutation_Type c l1 l2.
    Proof.
    now destruct c; [ apply CPermutation_CPermutation_Type | | apply Permutation_Permutation_Type ].
    Qed.

  End Dec.

End PCEPermutation.


(** * [PCPermutation] case *)

Section PCPermutation.

  Variable A : Type.

  Lemma not_PCPermutation_Type_not_PCPermutation b (l1 l2 : list A):
    (PCPermutation_Type b l1 l2 -> False) -> ~ PCPermutation b l1 l2.
  Proof.
  destruct b; [ apply not_Permutation_Type_not_Permutation
              | apply not_CPermutation_Type_not_CPermutation ].
  Qed.

  Section Dec.

    Hypothesis EqDec : forall x y : A, {x = y} + {x <> y}.

    Lemma PCPermutation_Type_dec b (l1 l2 : list A):
      PCPermutation_Type b l1 l2 + (PCPermutation_Type b l1 l2 -> False).
    Proof. now destruct b; [ apply Permutation_Type_dec | apply CPermutation_Type_dec ]. Qed.

    Lemma PCPermutation_PCPermutation_Type b (l1 l2 : list A):
      PCPermutation b l1 l2 -> PCPermutation_Type b l1 l2.
    Proof.
    now destruct b; [ apply Permutation_Permutation_Type | apply CPermutation_CPermutation_Type ].
    Qed.

  End Dec.

End PCPermutation.


(** * [PEPermutation] case *)

Section PEPermutation.

  Variable A : Type.

  Lemma not_PEPermutation_Type_not_PEPermutation b (l1 l2 : list A):
    (PEPermutation_Type b l1 l2 -> False) -> ~ PEPermutation b l1 l2.
  Proof. destruct b; [ apply not_Permutation_Type_not_Permutation | intuition ]. Qed.

  Section Dec.

    Hypothesis EqDec : forall x y : A, {x = y} + {x <> y}.

    Lemma PEPermutation_Type_dec b (l1 l2 : list A):
      PEPermutation_Type b l1 l2 + (PEPermutation_Type b l1 l2 -> False).
    Proof.
    destruct b; [ apply Permutation_Type_dec | ]; auto.
    destruct (list_eq_dec EqDec l1 l2); intuition.
    Qed.

    Lemma PEPermutation_PEPermutation_Type b (l1 l2 : list A):
      PEPermutation b l1 l2 -> PEPermutation_Type b l1 l2.
    Proof. now destruct b; [ apply Permutation_Permutation_Type | ]. Qed.

  End Dec.

End PEPermutation.


(** * Transformation tactics *)

(** transforms [Permutation_Type] into [Permutation] *)
Ltac PermutationPropify Hdec :=
  match goal with
  | |- Permutation_Type _ _ =>
    apply (Permutation_Permutation_Type Hdec);
    repeat match goal with
    | H : Permutation_Type _ _ |- _ => apply Permutation_Type_Permutation in H
    end
  | _ => fail "Not a Permutation_Type conclusion"
  end.

(** transforms [CPermutation_Type] into [CPermutation] *)
Ltac CPermutationPropify Hdec :=
  match goal with
  | |- CPermutation_Type _ _ =>
    apply (CPermutation_CPermutation_Type Hdec);
    repeat match goal with
    | H : CPermutation_Type _ _ |- _ => apply CPermutation_Type_CPermutation in H
    end
  | _ => fail "Not a CPermutation_Type conclusion"
  end.

(** transforms [PCEPermutation_Type] into [PCEPermutation] *)
Ltac PCEPermutationPropify Hdec :=
  match goal with
  | |- PCEPermutation_Type _ _ _ =>
    apply (PCEPermutation_PCEPermutation_Type Hdec);
    repeat match goal with
    | H : PCEPermutation_Type _ _ _ |- _ => apply PCEPermutation_Type_PCEPermutation in H
    end
  | _ => fail "Not a PCEPermutation_Type conclusion"
  end.

(** transforms [PCPermutation_Type] into [PCPermutation] *)
Ltac PCPermutationPropify Hdec :=
  match goal with
  | |- PCPermutation_Type _ _ _ =>
    apply (PCPermutation_PCPermutation_Type Hdec);
    repeat match goal with
    | H : PCPermutation_Type _ _ _ |- _ => apply PCPermutation_Type_PCPermutation in H
    end
  | _ => fail "Not a PCPermutation_Type conclusion"
  end.

(** transforms [PEPermutation_Type] into [PEPermutation] *)
Ltac PEPermutationPropify Hdec :=
  match goal with
  | |- PEPermutation_Type _ _ _ =>
    apply (PEPermutation_PEPermutation_Type Hdec);
    repeat match goal with
    | H : PEPermutation_Type _ _ _ |- _ => apply PEPermutation_Type_PEPermutation in H
    end
  | _ => fail "Not a PEPermutation_Type conclusion"
  end.
