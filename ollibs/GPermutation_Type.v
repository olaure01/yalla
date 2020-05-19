(** Factorized statements for different notions of permutation *)

From Coq Require Import List CMorphisms.
From OLlibs Require Import funtheory ComparisonOrder List_more
                           Permutation_Type_more Permutation_Type_solve
                           CPermutation_Type CPermutation_Type_solve.
From OLlibs Require GPermutation.

Set Implicit Arguments.


Section GPermutationType.

  Variable A : Type.
  Variable c : comparison.
  Variable b : bool.

  (** * Definitions
   parametrized by a trilean or a boolean. *)

  (** Permutation or cyclic permutation or equality *)

  Definition PCEPermutation_Type :=
  match c with
  | Lt => @eq (list A)
  | Eq => @CPermutation_Type A
  | Gt => @Permutation_Type A
  end.

  (** Permutation or cyclic permutation *)
  Definition PCPermutation_Type := if b then @Permutation_Type A else @CPermutation_Type A.

  (** Permutation or equality *)
  Definition PEPermutation_Type := if b then @Permutation_Type A else @eq (list A).

  Ltac case_perm_tri := unfold PCEPermutation_Type; destruct c.
  Ltac case_perm := unfold PCPermutation_Type, PEPermutation_Type; destruct b.

  Lemma PCEPermutation_Type_PCEPermutation : forall l1 l2,
    PCEPermutation_Type l1 l2 -> GPermutation.PCEPermutation c l1 l2.
  Proof.
  now case_perm_tri; [ apply CPermutation_Type_CPermutation | | apply Permutation_Type_Permutation ].
  Qed.

  Lemma PCPermutation_Type_PCPermutation : forall l1 l2,
    PCPermutation_Type l1 l2 -> GPermutation.PCPermutation b l1 l2.
  Proof.
  case_perm; [ apply Permutation_Type_Permutation | apply CPermutation_Type_CPermutation ].
  Qed.

  Lemma PEPermutation_Type_PEPermutation : forall l1 l2,
    PEPermutation_Type l1 l2 -> GPermutation.PEPermutation b l1 l2.
  Proof. now case_perm; [ apply Permutation_Type_Permutation | ]. Qed.

  Global Instance PEPermutation_PCPermutation_Type :
    Proper (PEPermutation_Type ==> PCPermutation_Type) id.
  Proof.  now case_perm; simpl; intros l l' HP; [ | subst ]. Qed.

  Global Instance PCEPermutation_Permutation_Type :
    Proper (PCEPermutation_Type ==> (@Permutation_Type A)) id.
  Proof.
  case_perm_tri; intros l1 l2 HP; [ apply CPermutation_Permutation_Type | subst | ]; auto.
  Qed.

  Global Instance PCPermutation_Permutation_Type :
    Proper (PCPermutation_Type ==> (@Permutation_Type A)) id.
  Proof. now case_perm; [ | apply CPermutation_Permutation_Type ]. Qed.

  Global Instance PEPermutation_Permutation_Type :
    Proper (PEPermutation_Type ==> (@Permutation_Type A)) id.
  Proof. case_perm; simpl; intros l l' HP; now subst. Qed.

  Global Instance CPermutation_Type_PCPermutation_Type :
    Proper (@CPermutation_Type A ==> PCPermutation_Type) id.
  Proof. now case_perm; [ apply CPermutation_Permutation_Type | ]. Qed.

  Global Instance eq_PCEPermutation_Type : Proper (eq ==> PCEPermutation_Type) id.
  Proof. case_perm_tri; intuition. Qed.

  Global Instance eq_PEPermutation_Type : Proper (eq ==> PEPermutation_Type) id.
  Proof. case_perm; intuition. Qed.


  (** ** Properties of [PCEPermutation_Type] *)

  Global Instance PCEPermutation_Type_refl : Reflexive PCEPermutation_Type.
  Proof. case_perm_tri; intros l; reflexivity. Qed.

  Global Instance PCEPermutation_Type_sym : Symmetric PCEPermutation_Type.
  Proof. case_perm_tri; intros l l'; now symmetry. Qed.

  Global Instance PCEPermutation_Type_trans : Transitive PCEPermutation_Type.
  Proof. case_perm_tri; intros l l' l''; now transitivity l'. Qed.

  Global Instance PCEPermutation_Type_equiv : Equivalence PCEPermutation_Type.
  Proof.
  split;
  [ apply PCEPermutation_Type_refl
  | apply PCEPermutation_Type_sym
  | apply PCEPermutation_Type_trans ].
  Qed.

  Lemma PCEPermutation_Type_nil : forall l, PCEPermutation_Type nil l -> l = nil.
  Proof.
  now case_perm_tri; [ apply CPermutation_Type_nil | intros; subst | apply Permutation_Type_nil ].
  Qed.

  Lemma PCEPermutation_Type_nil_cons : forall l a, PCEPermutation_Type nil (a :: l) -> False.
  Proof.
  case_perm_tri;
    [ apply CPermutation_Type_nil_cons
    | intros l a Heq; inversion Heq | apply Permutation_Type_nil_cons ].
  Qed.

  Lemma PCEPermutation_Type_length_1_inv : forall a l,
    PCEPermutation_Type (a :: nil) l -> l = a :: nil.
  Proof.
  now case_perm_tri;
    [ apply CPermutation_Type_length_1_inv | intros; subst | apply Permutation_Type_length_1_inv ].
  Qed.

  Global Instance PCEPermutation_Type_in a : Proper (PCEPermutation_Type ==> Basics.impl) (In a).
  Proof.
  now case_perm_tri; intros l l' HP Hin;
    [ apply CPermutation_Type_in with l | subst | apply Permutation_Type_in with l ].
  Qed.

  Global Instance PCEPermutation_Type_Forall (P : A -> Prop) :
    Proper (PCEPermutation_Type ==> Basics.impl) (Forall P).
  Proof.
  now case_perm_tri;
    [ apply CPermutation_Type_Forall | intros ? ? -> | apply Permutation_Type_Forall ].
  Qed.

  Global Instance PCEPermutation_Type_Exists (P : A -> Prop) :
    Proper (PCEPermutation_Type ==> Basics.impl) (Exists P).
  Proof.
  now case_perm_tri;
    [ apply CPermutation_Type_Exists | intros ? ? -> | apply Permutation_Type_Exists ].
  Qed.

  Global Instance PCEPermutation_Type_Forall_inf (P : A -> Type) :
    Proper (PCEPermutation_Type ==> Basics.arrow) (Forall_inf P).
  Proof.
  now case_perm_tri;
    [ apply CPermutation_Type_Forall_inf | intros ? ? -> | apply Permutation_Type_Forall_inf ].
  Qed.

  Global Instance PCEPermutation_Type_Exists_inf (P : A -> Type) :
    Proper (PCEPermutation_Type ==> Basics.arrow) (Exists_inf P).
  Proof.
  now case_perm_tri;
    [ apply CPermutation_Type_Exists_inf | intros ? ? -> | apply Permutation_Type_Exists_inf ].
  Qed.


  (** ** Properties of [PCPermutation_Type] *)

  Global Instance PCPermutation_Type_refl : Reflexive PCPermutation_Type.
  Proof. case_perm; intros l; reflexivity. Qed.

  Global Instance PCPermutation_Type_sym : Symmetric PCPermutation_Type.
  Proof. case_perm; intros l l'; now symmetry. Qed.

  Global Instance PCPermutation_Type_trans : Transitive PCPermutation_Type.
  Proof. case_perm; intros l l' l''; now transitivity l'. Qed.

  Global Instance PCPermutation_Type_equiv : Equivalence PCPermutation_Type.
  Proof.
  split;
  [ apply PCPermutation_Type_refl | apply PCPermutation_Type_sym | apply PCPermutation_Type_trans ].
  Qed.


  Lemma PCPermutation_Type_swap : forall a1 a2,
    PCPermutation_Type (a1 :: a2 :: nil) (a2 :: a1 :: nil).
  Proof. case_perm; [ intros; apply Permutation_Type_swap | apply CPermutation_Type_swap ]. Qed.

  Lemma PCPermutation_Type_cons_append : forall a l, PCPermutation_Type (a :: l) (l ++ a :: nil).
  Proof.
  case_perm; intros; rewrite <- (app_nil_l l), app_comm_cons;
    [ apply Permutation_Type_cons_append | apply CPermutation_Type_cons_append ].
  Qed.

  Lemma PCPermutation_Type_app_comm : forall l l', PCPermutation_Type (l ++ l') (l' ++ l).
  Proof. case_perm; [ apply Permutation_Type_app_comm | apply cperm_Type ]. Qed.

  Lemma PCPermutation_Type_app_rot : forall l1 l2 l3,
    PCPermutation_Type (l1 ++ l2 ++ l3) (l2 ++ l3 ++ l1).
  Proof. case_perm; [ apply Permutation_Type_app_rot | apply CPermutation_Type_app_rot ]. Qed.

  Lemma PCPermutation_Type_nil : forall l, PCPermutation_Type nil l -> l = nil.
  Proof. now case_perm; [ apply Permutation_Type_nil | apply CPermutation_Type_nil ]. Qed.

  Lemma PCPermutation_Type_nil_cons : forall l a, PCPermutation_Type nil (a :: l) -> False.
  Proof. now case_perm; [ apply Permutation_Type_nil_cons | apply CPermutation_Type_nil_cons ]. Qed.

  Lemma PCPermutation_Type_length_1_inv : forall a l,
    PCPermutation_Type (a :: nil) l -> l = a :: nil.
  Proof.
  now case_perm; [ apply Permutation_Type_length_1_inv | apply CPermutation_Type_length_1_inv ].
  Qed.

  Lemma PCPermutation_Type_length_2_inv : forall a1 a2 l,
    PCPermutation_Type (a1 :: a2 :: nil) l -> {l = a1 :: a2 :: nil} + {l = a2 :: a1 :: nil}.
  Proof.
  now case_perm; [ apply Permutation_Type_length_2_inv | apply CPermutation_Type_length_2_inv ].
  Qed.

  Global Instance PCPermutation_Type_in a : Proper (PCPermutation_Type ==> Basics.impl) (In a).
  Proof.
  now case_perm; intros l l' HP Hin;
    [ apply Permutation_Type_in with l | apply CPermutation_Type_in with l ].
  Qed.

  Global Instance PCPermutation_Type_Forall (P : A -> Prop) :
    Proper (PCPermutation_Type ==> Basics.impl) (Forall P).
  Proof. case_perm; [ apply Permutation_Type_Forall | apply CPermutation_Type_Forall ]. Qed.

  Global Instance PCPermutation_Type_Exists (P : A -> Prop) :
    Proper (PCPermutation_Type ==> Basics.impl) (Exists P).
  Proof. now case_perm; [ apply Permutation_Type_Exists | apply CPermutation_Type_Exists ]. Qed.

  Global Instance PCPermutation_Type_Forall_inf (P : A -> Type) :
    Proper (PCPermutation_Type ==> Basics.arrow) (Forall_inf P).
  Proof. case_perm; [ apply Permutation_Type_Forall_inf | apply CPermutation_Type_Forall_inf ]. Qed.

  Global Instance PCPermutation_Type_Exists_inf (P : A -> Type) :
    Proper (PCPermutation_Type ==> Basics.arrow) (Exists_inf P).
  Proof.
  now case_perm; [ apply Permutation_Type_Exists_inf | apply CPermutation_Type_Exists_inf ].
  Qed.


  (** ** Properties of [PEPermutation] *)

  Global Instance PEPermutation_Type_refl : Reflexive PEPermutation_Type.
  Proof. now case_perm. Qed.

  Global Instance PEPermutation_Type_sym : Symmetric PEPermutation_Type.
  Proof. now case_perm. Qed.

  Global Instance PEPermutation_Type_trans : Transitive PEPermutation_Type.
  Proof. now case_perm; intros l l' l''; transitivity l'. Qed.

  Global Instance PEPermutation_Type_equiv : Equivalence PEPermutation_Type.
  Proof.
  split;
  [ apply PEPermutation_Type_refl | apply PEPermutation_Type_sym | apply PEPermutation_Type_trans ].
  Qed.

  Global Instance PEPermutation_Type_cons :
    Proper (eq ==> PEPermutation_Type ==> PEPermutation_Type) cons.
  Proof. now case_perm; intros x y -> l1 l2 HP; [ apply Permutation_Type_cons | rewrite HP ]. Qed.

  Global Instance PEPermutation_Type_app :
    Proper (PEPermutation_Type ==> PEPermutation_Type ==> PEPermutation_Type) (@app A).
  Proof. now case_perm; simpl; intros l m HP1 l' m' HP2; [ apply Permutation_Type_app | subst ]. Qed.

  Lemma PEPermutation_Type_app_tail : forall l l' tl,
    PEPermutation_Type l l' -> PEPermutation_Type (l ++ tl) (l' ++ tl).
  Proof. now case_perm; simpl; intros l l' tl HP; [ apply Permutation_Type_app_tail | subst ]. Qed.

  Lemma PEPermutation_Type_app_head : forall l tl tl',
    PEPermutation_Type tl tl' -> PEPermutation_Type (l ++ tl) (l ++ tl').
  Proof. now case_perm; simpl; intros l l' tl HP; [ apply Permutation_Type_app_head | subst ]. Qed.

  Lemma PEPermutation_Type_add_inside : forall a l l' tl tl',
    PEPermutation_Type l l' -> PEPermutation_Type tl tl' ->
    PEPermutation_Type (l ++ a :: tl) (l' ++ a :: tl').
  Proof.
  now case_perm; simpl; intros a l l' tl tl' HP1 HP2; [ apply Permutation_Type_add_inside | subst ].
  Qed.

  Lemma PEPermutation_Type_nil : forall l, PEPermutation_Type nil l -> l = nil.
  Proof. now case_perm; intros; [ apply Permutation_Type_nil | symmetry ]. Qed.

  Lemma PEPermutation_Type_nil_cons : forall l a, PEPermutation_Type nil (a :: l) -> False.
  Proof. case_perm; intros l a HP; [ apply (Permutation_Type_nil_cons HP) | inversion HP ]. Qed.

  Lemma PEPermutation_Type_length_1_inv : forall a l,
    PEPermutation_Type (a :: nil) l -> l = a :: nil.
  Proof. now case_perm; intros; [ apply Permutation_Type_length_1_inv | symmetry ]. Qed.

  Lemma PEPermutation_Type_length_2_inv : forall a1 a2 l,
    PEPermutation_Type (a1 :: a2 :: nil) l -> {l = a1 :: a2 :: nil} + {l = a2 :: a1 :: nil}.
  Proof. now case_perm; intros; [ apply Permutation_Type_length_2_inv | left; symmetry ]. Qed.

  Lemma PEPermutation_Type_vs_elt_inv : forall a l l1 l2,
    PEPermutation_Type l (l1 ++ a :: l2) ->
      {'(l3, l4) & PEPermutation_Type (l1 ++ l2) (l3 ++ l4) & l = l3 ++ a :: l4 }.
  Proof.
  case_perm; intros a l l1 l2 HP.
  - destruct (Permutation_Type_vs_elt_inv _ _ _ HP) as ((l', l'') & ->).
    apply Permutation_Type_app_inv in HP; symmetry in HP.
    exists (l', l''); auto.
  - exists (l1, l2); intuition.
  Qed.

  Lemma PEPermutation_Type_vs_cons_inv : forall a l l1,
    PEPermutation_Type l (a :: l1) ->
      {'(l2, l3) & PEPermutation_Type l1 (l2 ++ l3) & l = l2 ++ a :: l3 }.
  Proof.
  intros a l l1 HP.
  rewrite <- (app_nil_l l1).
  now apply PEPermutation_Type_vs_elt_inv.
  Qed.

  Global Instance PEPermtutation_Type_in a : Proper (PEPermutation_Type ==> Basics.impl) (In a).
  Proof.
  now case_perm; simpl; intros l l' HP HIn; subst; [ apply Permutation_Type_in with l | ].
  Qed.

  Global Instance PEPermutation_Type_Forall (P : A -> Prop) :
    Proper (PEPermutation_Type ==> Basics.impl) (Forall P).
  Proof.
  now case_perm; simpl; intros l1 l2 HP HF; subst; [ apply Permutation_Type_Forall with l1 | ].
  Qed.

  Global Instance PEPermutation_Type_Exists (P : A -> Prop) :
    Proper (PEPermutation_Type ==> Basics.impl) (Exists P).
  Proof.
  now case_perm; simpl; intros l1 l2 HP HF; subst; [ apply Permutation_Type_Exists with l1 | ].
  Qed.

  Global Instance PEPermutation_Type_Forall_inf (P : A -> Type) :
    Proper (PEPermutation_Type ==> Basics.arrow) (Forall_inf P).
  Proof.
  now case_perm; simpl; intros l1 l2 HP HF; subst; [ apply Permutation_Type_Forall_inf with l1 | ].
  Qed.

  Global Instance PEPermutation_Type_Exists_inf (P : A -> Type) :
    Proper (PEPermutation_Type ==> Basics.arrow) (Exists_inf P).
  Proof.
  now case_perm; simpl; intros l1 l2 HP HF; subst; [ apply Permutation_Type_Exists_inf with l1 | ].
  Qed.

  Global Instance PEPermutation_Type_rev :
    Proper (PEPermutation_Type ==> PEPermutation_Type) (@rev A).
  Proof. now case_perm; intros l1 l2 HP; [ apply Permutation_Type_rev' | subst ].  Qed.


  (** * From [PEPermutation_Type] to [PCPermutation_Type] *)

  Global Instance PEPermutation_PCPermutation_Type_cons :
    Proper (eq ==> PEPermutation_Type ==> PCPermutation_Type) cons.
  Proof.
  intros x y -> l1 l2 HP.
  apply PEPermutation_PCPermutation_Type.
  now rewrite HP.
  Qed.

  Global Instance PEPermutation_PCPermutation_Type_app :
  Proper (PEPermutation_Type ==> PEPermutation_Type ==> PCPermutation_Type) (@app A).
  Proof.
  intros l1 l1' HPhd l2 l2' HPtl.
  apply PEPermutation_PCPermutation_Type.
  now rewrite HPhd, HPtl.
  Qed.

  Lemma PCPermutation_Type_vs_elt_inv : forall a l l1 l2,
    PCPermutation_Type l (l1 ++ a :: l2) ->
      {'(l', l'') & PEPermutation_Type (l2 ++ l1) (l'' ++ l') & l = l' ++ a :: l'' }.
  Proof.
  case_perm; intros a l l1 l2 HP.
  - destruct (Permutation_Type_vs_elt_inv _ _ _ HP) as ((l',l'') & ->).
    exists (l', l''); auto.
    apply Permutation_Type_app_inv in HP.
    symmetry in HP.
    etransitivity ; [ eapply Permutation_Type_app_comm | ].
    etransitivity ; [ eassumption | apply Permutation_Type_app_comm ].
  - destruct (CPermutation_Type_vs_elt_inv _ _ _ HP) as [(l',l'') Heq ->].
    exists (l', l''); auto.
  Qed.

  Lemma PCPermutation_Type_vs_cons_inv : forall a l l1,
    PCPermutation_Type l (a :: l1) ->
      {'(l', l'') & PEPermutation_Type l1 (l'' ++ l') & l = l' ++ a :: l'' }.
  Proof.
  intros a l l1 HP.
  rewrite <- app_nil_l in HP.
  apply PCPermutation_Type_vs_elt_inv in HP as [(l', l'') HP ->].
  exists (l', l''); auto.
  now rewrite app_nil_r in HP.
  Qed.

  Lemma PCPermutation_Type_cons_cons_inv : forall a1 a2 l1 l2,
    PCPermutation_Type (a1 :: l1) (a2 :: l2) ->
      (a1 = a2) * PEPermutation_Type l1 l2
    + {'(l3, l4) & PEPermutation_Type l1 (l4 ++ a2 :: l3) & l2 = l3 ++ a1 :: l4 }.
  Proof.
  intros a1 a2 l1 l2 HP; symmetry in HP.
  apply PCPermutation_Type_vs_cons_inv in HP.
  destruct HP as [(l1',l2') HP' Heq].
  destruct l1'; inversion Heq; subst.
  - left; split; auto.
    now rewrite app_nil_r in HP'.
  - right; exists (l1', l2'); auto.
  Qed.

  Lemma PCPermutation_Type_cons_cons_notin_inv : forall a l l1, ~ In a l ->
    PCPermutation_Type (a :: l) (a :: l1) -> PEPermutation_Type l l1.
  Proof.
  intros a l l1 Hin HP.
  apply PCPermutation_Type_cons_cons_inv in HP as [[Heq HP] | [(l3, l4) HP Heq]]; auto.
  exfalso.
  apply Hin, Permutation_Type_in with (l4 ++ a :: l3), in_elt.
  now symmetry in HP; apply PEPermutation_Permutation_Type.
  Qed.

End GPermutationType.

Section MultiGPermutationType.

  Variable A B : Type.
  Variable c : comparison.
  Variable b : bool.

  Lemma PCEPermutation_Type_Forall2_inf (P : A -> B -> Type) : forall l1 l1' l2,
    PCEPermutation_Type c l1 l1' -> Forall2_inf P l1 l2 -> 
      { l2' & PCEPermutation_Type c l2 l2' & Forall2_inf P l1' l2' }.
  Proof.
  destruct c; [ apply CPermutation_Type_Forall2_inf | | apply Permutation_Type_Forall2_inf ].
  now simpl; intros l1 l1' l2 -> HF; exists l2.
  Qed.

  Lemma PCPermutation_Type_Forall2_inf (P : A -> B -> Type) : forall l1 l1' l2,
    PCPermutation_Type b l1 l1' -> Forall2_inf P l1 l2 -> 
      { l2' & PCPermutation_Type b l2 l2' & Forall2_inf P l1' l2' }.
  Proof.
  destruct b; [ apply Permutation_Type_Forall2_inf | apply CPermutation_Type_Forall2_inf ].
  Qed.

  Lemma PEPermutation_Type_Forall2_inf (P : A -> B -> Type) : forall l1 l1' l2,
    PEPermutation_Type b l1 l1' -> Forall2_inf P l1 l2 ->
      { l2' & PEPermutation_Type b l2 l2' & Forall2_inf P l1' l2' }.
  Proof.
  destruct b; [ apply Permutation_Type_Forall2_inf | simpl; intros; subst; now exists l2 ].
  Qed.

  Variable f : A -> B.

  Global Instance PCEPermutation_Type_map :
    Proper (PCEPermutation_Type c ==> PCEPermutation_Type c) (map f).
  Proof. now destruct c; intros l1 l2 ->. Qed.

  Global Instance PCPermutation_Type_map :
    Proper (PCPermutation_Type b ==> PCPermutation_Type b) (map f).
  Proof. now destruct b; intros l1 l2 ->. Qed.

  Global Instance PEPermutation_Type_map :
    Proper (PEPermutation_Type b ==> PEPermutation_Type b) (map f).
  Proof. now destruct b; simpl; intros l1 l2 HP; [ apply Permutation_Type_map | subst ]. Qed.

  Lemma PCEPermutation_Type_map_inv : forall l1 l2,
    PCEPermutation_Type c l1 (map f l2) -> { l3 & l1 = map f l3 & PCEPermutation_Type c l2 l3 }.
  Proof.
  destruct c; [ apply CPermutation_Type_map_inv | | apply Permutation_Type_map_inv ].
  now simpl; intros l1 l2 ->; exists l2.
  Qed.

  Lemma PCPermutation_Type_map_inv : forall l1 l2,
    PCPermutation_Type b l1 (map f l2) -> { l3 & l1 = map f l3 & PCPermutation_Type b l2 l3 }.
  Proof. destruct b; [ apply Permutation_Type_map_inv | apply CPermutation_Type_map_inv ]. Qed.

  Lemma PEPermutation_Type_map_inv : forall l1 l2,
    PEPermutation_Type b l1 (map f l2) -> { l3 & l1 = map f l3 & PEPermutation_Type b l2 l3 }.
  Proof. now destruct b; [ apply Permutation_Type_map_inv | intros l1 l2; exists l2 ]. Qed.

  Lemma PCEPermutation_Type_map_inv_inj : injective f -> forall l1 l2,
    PCEPermutation_Type c (map f l1) (map f l2) -> PCEPermutation_Type c l1 l2.
  Proof.
  destruct c;
  [ apply CPermutation_Type_map_inv_inj | apply map_injective | apply Permutation_Type_map_inv_inj ].
  Qed.

  Lemma PCPermutation_Type_map_inv_inj : injective f -> forall l1 l2,
    PCPermutation_Type b (map f l1) (map f l2) -> PCPermutation_Type b l1 l2.
  Proof.
  now destruct b; [ apply Permutation_Type_map_inv_inj | apply CPermutation_Type_map_inv_inj ].
  Qed.

  Lemma PEPermutation_Type_map_inv_inj : injective f -> forall l1 l2,
    PEPermutation_Type b (map f l1) (map f l2) -> PEPermutation_Type b l1 l2.
  Proof. now destruct b; [ apply Permutation_Type_map_inv_inj | apply map_injective ]. Qed.

  Lemma PCEPermutation_Type_image : forall a l l',
    PCEPermutation_Type c (a :: l) (map f l') -> { a' | a = f a' }.
  Proof.
  destruct c; [ apply CPermutation_Type_image | | apply Permutation_Type_image ].
  now simpl; intros a l l' Heq; destruct l' as [|a' l']; inversion Heq; subst; exists a'.
  Qed.

  Lemma PCPermutation_Type_image : forall a l l',
    PCPermutation_Type b (a :: l) (map f l') -> { a' | a = f a' }.
  Proof. destruct b; [ apply Permutation_Type_image | apply CPermutation_Type_image ]. Qed.

  Lemma PEPermutation_Type_image : forall a l l',
    PEPermutation_Type b (a :: l) (map f l') -> { a' | a = f a' }.
  Proof.
  destruct b ; [ apply Permutation_Type_image | ].
  now simpl; intros a l l' HP; destruct l' as [|a' l']; inversion HP; subst; exists a'.
  Qed.

  Variable c' : comparison.
  Variable b' : bool.

  Lemma PCEPermutation_Type_monot : ComparisonOrder.le c c' ->
    forall l1 l2 : list A, PCEPermutation_Type c l1 l2 -> PCEPermutation_Type c' l1 l2.
  Proof.
  intros Hle l1 l2; destruct c, c'; simpl; try (now inversion Hle); try (now intros; subst).
  apply CPermutation_Permutation_Type.
  Qed.

  Lemma PCPermutation_Type_monot : Bool.le b b' ->
    forall l1 l2 : list A, PCPermutation_Type b l1 l2 -> PCPermutation_Type b' l1 l2.
  Proof.
  intros Hle l1 l2; destruct b, b'; try (now inversion Hle).
  apply CPermutation_Permutation_Type.
  Qed.

  Lemma PEPermutation_Type_monot : Bool.le b b' ->
    forall l1 l2 : list A, PEPermutation_Type b l1 l2 -> PEPermutation_Type b' l1 l2.
  Proof.
  intros Hle l1 l2; destruct b, b'; try (now inversion Hle).
  now simpl; intros ->.
  Qed.

End MultiGPermutationType.


(** * Solvinc tactics *)

(** unfolding into [Permutation_Type], [CPermutation_Type] or [eq] *)
Ltac hyps_GPermutation_Type_unfold :=
  match goal with
  | H : PCEPermutation_Type _ _ _ |- _ => unfold PCEPermutation_Type in H;
                                          hyps_GPermutation_Type_unfold
  | H : PCPermutation_Type _ _ _ |- _ => unfold PCPermutation_Type in H;
                                         hyps_GPermutation_Type_unfold
  | H : PEPermutation_Type _ _ _ |- _ => unfold PEPermutation_Type in H;
                                         hyps_GPermutation_Type_unfold
  | _ => idtac
  end.

(** automatic solving *)
Ltac GPermutation_Type_solve :=
  hyps_GPermutation_Type_unfold; simpl;
  match goal with
  | |- PCEPermutation_Type ?c _ _ => unfold PCEPermutation_Type; destruct c; simpl;
                                     GPermutation_Type_solve
  | |- PCPermutation_Type ?b _ _ => unfold PCPermutation_Type; destruct b; simpl;
                                    GPermutation_Type_solve
  | |- PEPermutation_Type ?b _ _ => unfold PEPermutation_Type; destruct b; simpl;
                                    GPermutation_Type_solve
  | |- Permutation_Type _ _  => Permutation_Type_solve
  | |- CPermutation_Type _ _  => CPermutation_Type_solve
  | |- eq _ _  => reflexivity
  end.
