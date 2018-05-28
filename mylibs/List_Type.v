(* List_Type_ Library *)

(** * Copy of some List library with parameters with Type output *)


Require Export List.

Set Implicit Arguments.

Section Exists_Forall.

  (** * Existential and universal predicates over lists *)

  Variable A:Type.

  Section One_predicate.

    Variable P:A->Type.

    Inductive Exists_Type : list A -> Type :=
      | Exists_Type_cons_hd : forall x l, P x -> Exists_Type (x::l)
      | Exists_Type_cons_tl : forall x l, Exists_Type l -> Exists_Type (x::l).

    Hint Constructors Exists_Type.

    Lemma Exists_Type_nil : Exists_Type nil -> False.
    Proof. inversion 1. Qed.

    Lemma Exists_Type_cons x l:
      Exists_Type (x::l) -> P x + Exists_Type l.
    Proof. inversion 1; auto. Qed.

    Lemma Exists_dec l:
      (forall x:A, P x + (P x -> False)) ->
      Exists_Type l + (Exists_Type l -> False).
    Proof.
      intro Pdec. induction l as [|a l' Hrec].
      - right. now apply Exists_Type_nil.
      - destruct Hrec as [Hl'|Hl'].
        * left. now apply Exists_Type_cons_tl.
        * destruct (Pdec a) as [Ha|Ha].
          + left. now apply Exists_Type_cons_hd.
          + right. now inversion_clear 1.
    Qed.

    Inductive Forall_Type : list A -> Type :=
      | Forall_Type_nil : Forall_Type nil
      | Forall_Type_cons : forall x l, P x -> Forall_Type l -> Forall_Type (x::l).

    Hint Constructors Forall_Type.

    Lemma Forall_Type_inv : forall (a:A) l, Forall_Type (a :: l) -> P a.
    Proof.
      intros ? ? H ; inversion H ; trivial.
    Qed.

  End One_predicate.

  Lemma Forall_impl : forall (P Q : A -> Type), (forall a, P a -> Q a) ->
    forall l, Forall_Type P l -> Forall_Type Q l.
  Proof.
    induction l ; intros H ; inversion H ; constructor ; auto.
  Qed.

End Exists_Forall.

Hint Constructors Exists_Type.
Hint Constructors Forall_Type.

Section Forall2.

  (** [Forall2]: stating that elements of two lists are pairwise related. *)

  Variables A B : Type.
  Variable R : A -> B -> Type.

  Inductive Forall2_Type : list A -> list B -> Type :=
    | Forall2_Type_nil : Forall2_Type nil nil
    | Forall2_Type_cons : forall x y l l',
      R x y -> Forall2_Type l l' -> Forall2_Type (x::l) (y::l').

  Hint Constructors Forall2_Type.

  Theorem Forall2_Type_refl : Forall2_Type nil nil.
  Proof. intros; apply Forall2_Type_nil. Qed.

  Theorem Forall2_Type_app_inv_l : forall l1 l2 l0,
    Forall2_Type (l1 ++ l2) l0 ->
    { l'' : { l' : _ & Forall2_Type l1 (fst l') & Forall2_Type l2 (snd l') }
          | l0 = fst (projT1 (sigT_of_sigT2 l'')) ++ snd (projT1 (sigT_of_sigT2 l'')) }.
  Proof.
    induction l1; intros.
    - assert (Forall2_Type nil nil) as H1 by auto.
      assert (Forall2_Type l2 l0) as H2 by auto.
      exists (existT2 _ _ (nil,l0) H1 H2).
      reflexivity.
    - simpl in X; inversion X; subst; clear X.
      apply IHl1 in X1 as (l0' & Hl).
      destruct l0' as [ l'' H1 H2 ].
      simpl in Hl.
      assert (Forall2_Type (a :: l1) (y :: fst l'')) as H3 by auto.
      exists (existT2 _ _ (y :: fst l'', snd l'') H3 H2).
      simpl ; rewrite Hl ; auto.
  Qed.

  Theorem Forall2_Type_app_inv_r : forall l1 l2 l0,
    Forall2_Type l0 (l1 ++ l2) ->
    { l'' : { l' : _ & Forall2_Type (fst l') l1 & Forall2_Type (snd l') l2 }
          | l0 = fst (projT1 (sigT_of_sigT2 l'')) ++ snd (projT1 (sigT_of_sigT2 l'')) }.
  Proof.
    induction l1; intros.
    - assert (Forall2_Type nil nil) as H1 by auto.
      assert (Forall2_Type l0 l2) as H2 by auto.
      exists (existT2 _ _ (nil,l0) H1 H2).
      reflexivity.
    - simpl in X; inversion X; subst; clear X.
      apply IHl1 in X1 as (l0' & Hl).
      destruct l0' as [ l'' H1 H2 ].
      simpl in Hl.
      assert (Forall2_Type (x :: fst l'') (a :: l1)) as H3 by auto.
      exists (existT2 _ _ (x :: fst l'', snd l'') H3 H2).
      simpl ; rewrite Hl ; auto.
  Qed.

  Theorem Forall2_Type_app : forall l1 l2 l1' l2',
    Forall2_Type l1 l1' -> Forall2_Type l2 l2' -> Forall2_Type (l1 ++ l2) (l1' ++ l2').
  Proof.
    intros. induction l1 in l1', X, X0 |- *; inversion X; subst; simpl; auto.
  Qed.
End Forall2.

Hint Constructors Forall2.
