(** Factorized statements for different notions of permutation *)

From Stdlib Require Import List Morphisms Permutation.
From Yalla.OLlibs Require Import funtheory ComparisonOrder
                           Permutation_more Permutation_solve
                           CPermutation_more CPermutation_solve.

Set Implicit Arguments.


Section GPermutation.

  Variable A : Type.
  Variable c : comparison.
  Variable b : bool.

  (** * Definitions
   parametrized by a trilean or a boolean. *)

  (** Permutation or cyclic permutation or equality *)

  Definition PCEPermutation :=
  match c with
  | Lt => @eq (list A)
  | Eq => @CPermutation A
  | Gt => @Permutation A
  end.

  (** Permutation or cyclic permutation *)
  Definition PCPermutation := if b then @Permutation A else @CPermutation A.

  (** Permutation or equality *)
  Definition PEPermutation := if b then @Permutation A else @eq (list A).

  Ltac case_perm_tri := unfold PCEPermutation; destruct c.
  Ltac case_perm := unfold PCPermutation, PEPermutation; destruct b.


  #[export] Instance PEPermutation_PCPermutation : Proper (PEPermutation ==> PCPermutation) id.
  Proof. now case_perm; simpl; intros l l' ->. Qed.

  #[export] Instance PCEPermutation_Permutation : Proper (PCEPermutation ==> (@Permutation A)) id.
  Proof. case_perm_tri; intros l1 l2 HP; [ apply CPermutation_Permutation | subst | ]; auto. Qed.

  #[export] Instance PCPermutation_Permutation : Proper (PCPermutation ==> (@Permutation A)) id.
  Proof. now case_perm; [ | apply CPermutation_Permutation ]. Qed.

  #[export] Instance PEPermutation_Permutation : Proper (PEPermutation ==> (@Permutation A)) id.
  Proof. case_perm; simpl; intros l l' HP; now subst. Qed.

  #[export] Instance CPermutation_PCPermutation :
    Proper (@CPermutation A ==> PCPermutation) id.
  Proof. now case_perm; [ apply CPermutation_Permutation | ]. Qed.

  #[export] Instance eq_PCEPermutation : Proper (eq ==> PCEPermutation) id.
  Proof. case_perm_tri; repeat intro; subst; reflexivity. Qed.

  #[export] Instance eq_PEPermutation : Proper (eq ==> PEPermutation) id.
  Proof. case_perm; repeat intro; subst; reflexivity. Qed.


  (** ** Properties of [PCEPermutation] *)

  #[export] Instance PCEPermutation_refl : Reflexive PCEPermutation.
  Proof. case_perm_tri; intros l; reflexivity. Qed.

  #[export] Instance PCEPermutation_sym : Symmetric PCEPermutation.
  Proof. case_perm_tri; intros l l'; now symmetry. Qed.

  #[export] Instance PCEPermutation_trans : Transitive PCEPermutation.
  Proof. case_perm_tri; intros l l' l''; now transitivity l'. Qed.

  #[export] Instance PCEPermutation_equiv : Equivalence PCEPermutation.
  Proof.
  split; [ apply PCEPermutation_refl | apply PCEPermutation_sym | apply PCEPermutation_trans ].
  Qed.

  Lemma PCEPermutation_nil l : PCEPermutation nil l -> l = nil.
  Proof.
  now case_perm_tri; [ apply CPermutation_nil | subst | apply Permutation_nil ].
  Qed.

  Lemma PCEPermutation_nil_cons l a : ~ PCEPermutation nil (a :: l).
  Proof.
  case_perm_tri;
    [ apply CPermutation_nil_cons | intros Heq; inversion Heq | apply Permutation_nil_cons ].
  Qed.

  Lemma PCEPermutation_length_1_inv a l : PCEPermutation (a :: nil) l -> l = a :: nil.
  Proof.
  now case_perm_tri;
    [ apply CPermutation_length_1_inv | subst | apply Permutation_length_1_inv ].
  Qed.

  Lemma PCEPermutation_vs_elt_subst a l l1 l2 :
    PCEPermutation l (l1 ++ a :: l2) -> exists l3 l4,
      (forall l0, PCEPermutation (l1 ++ l0 ++ l2) (l3 ++ l0 ++ l4)) /\ l = l3 ++ a :: l4.
  Proof.
  case_perm_tri; intros HP.
  - apply CPermutation_vs_elt_subst, HP.
  - exists l1, l2; split; [ reflexivity | exact HP ].
  - apply Permutation_vs_elt_subst, HP.
  Qed.

  #[export] Instance PCEPermutation_in a : Proper (PCEPermutation ==> Basics.impl) (In a).
  Proof.
  now case_perm_tri; intros l l' HP Hin;
    [ apply CPermutation_in with l | subst | apply Permutation_in with l ].
  Qed.

  #[export] Instance PCEPermutation_Forall (P : A -> Prop) :
    Proper (PCEPermutation ==> Basics.impl) (Forall P).
  Proof.
  now case_perm_tri; [ apply CPermutation_Forall | intros ? ? -> | apply Permutation_Forall ].
  Qed.

  #[export] Instance PCEPermutation_Exists (P : A -> Prop) :
    Proper (PCEPermutation ==> Basics.impl) (Exists P).
  Proof.
  now case_perm_tri; [ apply CPermutation_Exists | intros ? ? -> | apply Permutation_Exists ].
  Qed.


  (** ** Properties of [PCPermutation] *)

  #[export] Instance PCPermutation_refl : Reflexive PCPermutation.
  Proof. case_perm; intros l; reflexivity. Qed.

  #[export] Instance PCPermutation_sym : Symmetric PCPermutation.
  Proof. case_perm; intros l l'; now symmetry. Qed.

  #[export] Instance PCPermutation_trans : Transitive PCPermutation.
  Proof. case_perm; intros l l' l''; now transitivity l'. Qed.

  #[export] Instance PCPermutation_equiv : Equivalence PCPermutation.
  Proof.
  split; [ apply PCPermutation_refl | apply PCPermutation_sym | apply PCPermutation_trans ].
  Qed.

  Lemma PCPermutation_swap a1 a2 : PCPermutation (a1 :: a2 :: nil) (a2 :: a1 :: nil).
  Proof. case_perm; [ apply perm_swap | apply CPermutation_swap ]. Qed.

  Lemma PCPermutation_cons_append a l : PCPermutation (a :: l) (l ++ a :: nil).
  Proof.
  case_perm; rewrite <- (app_nil_l l), app_comm_cons;
    [ apply Permutation_cons_append | apply CPermutation_cons_append ].
  Qed.

  Lemma PCPermutation_app_comm l l' : PCPermutation (l ++ l') (l' ++ l).
  Proof. case_perm; [ apply Permutation_app_comm | apply cperm ]. Qed.

  Lemma PCPermutation_app_rot l1 l2 l3 : PCPermutation (l1 ++ l2 ++ l3) (l2 ++ l3 ++ l1).
  Proof. case_perm; [ apply Permutation_app_rot | apply CPermutation_app_rot ]. Qed.

  Lemma PCPermutation_nil l : PCPermutation nil l -> l = nil.
  Proof. now case_perm; [ apply Permutation_nil | apply CPermutation_nil ]. Qed.

  Lemma PCPermutation_nil_cons l a : ~ PCPermutation nil (a :: l).
  Proof. now case_perm; [ apply Permutation_nil_cons | apply CPermutation_nil_cons ]. Qed.

  Lemma PCPermutation_length_1_inv a l : PCPermutation (a :: nil) l -> l = a :: nil.
  Proof.
  now case_perm; [ apply Permutation_length_1_inv | apply CPermutation_length_1_inv ].
  Qed.

  Lemma PCPermutation_length_2_inv a1 a2 l :
    PCPermutation (a1 :: a2 :: nil) l -> l = a1 :: a2 :: nil \/ l = a2 :: a1 :: nil.
  Proof.
  now case_perm; [ apply Permutation_length_2_inv | apply CPermutation_length_2_inv ].
  Qed.

  Lemma PCPermutation_vs_elt_subst a l l1 l2 :
    PCPermutation l (l1 ++ a :: l2) -> exists l3 l4,
      (forall l0, PCPermutation (l1 ++ l0 ++ l2) (l3 ++ l0 ++ l4)) /\ l = l3 ++ a :: l4.
  Proof.
  case_perm; intros HP;
    [ apply Permutation_vs_elt_subst | apply CPermutation_vs_elt_subst ]; assumption.
  Qed.

  #[export] Instance PCPermutation_in a : Proper (PCPermutation ==> Basics.impl) (In a).
  Proof.
  now case_perm; intros l l' HP Hin; [ apply Permutation_in with l | apply CPermutation_in with l ].
  Qed.

  #[export] Instance PCPermutation_Forall (P : A -> Prop) :
    Proper (PCPermutation ==> Basics.impl) (Forall P).
  Proof. case_perm; [ apply Permutation_Forall | apply CPermutation_Forall ]. Qed.

  #[export] Instance PCPermutation_Exists (P : A -> Prop) :
    Proper (PCPermutation ==> Basics.impl) (Exists P).
  Proof. now case_perm; [ apply Permutation_Exists | apply CPermutation_Exists ]. Qed.


  (** ** Properties of [PEPermutation] *)

  #[export] Instance PEPermutation_refl : Reflexive PEPermutation.
  Proof. now case_perm. Qed.

  #[export] Instance PEPermutation_sym : Symmetric PEPermutation.
  Proof. now case_perm. Qed.

  #[export] Instance PEPermutation_trans : Transitive PEPermutation.
  Proof. now case_perm; intros l l' l''; transitivity l'. Qed.

  #[export] Instance PEPermutation_equiv : Equivalence PEPermutation.
  Proof.
  split; [ apply PEPermutation_refl | apply PEPermutation_sym | apply PEPermutation_trans ].
  Qed.

  #[export] Instance PEPermutation_cons : Proper (eq ==> PEPermutation ==> PEPermutation) cons.
  Proof. now case_perm; intros x y -> l1 l2 HP; [ apply Permutation_cons | rewrite HP ]. Qed.

  #[export] Instance PEPermutation_app :
    Proper (PEPermutation ==> PEPermutation ==> PEPermutation) (@app A).
  Proof. now case_perm; simpl; intros l m HP1 l' m' HP2; [ apply Permutation_app | subst ]. Qed.

  Lemma PEPermutation_app_tail l l' tl :
    PEPermutation l l' -> PEPermutation (l ++ tl) (l' ++ tl).
  Proof. now case_perm; simpl; intros HP; [ apply Permutation_app_tail | subst ]. Qed.

  Lemma PEPermutation_app_head l tl tl' :
    PEPermutation tl tl' -> PEPermutation (l ++ tl) (l ++ tl').
  Proof. now case_perm; simpl; intros HP; [ apply Permutation_app_head | subst ]. Qed.

  Lemma PEPermtuation_add_inside a l l' tl tl' :
    PEPermutation l l' -> PEPermutation tl tl' -> PEPermutation (l ++ a :: tl) (l' ++ a :: tl').
  Proof. now case_perm; simpl; intros HP1 HP2; [ apply Permutation_add_inside | subst ]. Qed.

  Lemma PEPermutation_nil l : PEPermutation nil l -> l = nil.
  Proof. now case_perm; [ apply Permutation_nil | symmetry ]. Qed.

  Lemma PEPermutation_nil_cons l a : ~ PEPermutation nil (a :: l).
  Proof. case_perm; [ apply Permutation_nil_cons | intro Heq; inversion Heq ]. Qed.

  Lemma PEPermutation_length_1_inv a l : PEPermutation (a :: nil) l -> l = a :: nil.
  Proof. now case_perm; [ apply Permutation_length_1_inv | symmetry ]. Qed.

  Lemma PEPermutation_length_2_inv a1 a2 l :
    PEPermutation (a1 :: a2 :: nil) l -> l = a1 :: a2 :: nil \/ l = a2 :: a1 :: nil.
  Proof. now case_perm; [ apply Permutation_length_2_inv | left; symmetry ]. Qed.

  Lemma PEPermutation_vs_elt_subst a l l1 l2 :
    PEPermutation l (l1 ++ a :: l2) -> exists l3 l4,
      (forall l0, PEPermutation (l1 ++ l0 ++ l2) (l3 ++ l0 ++ l4)) /\ l = l3 ++ a :: l4.
  Proof.
  case_perm; intros HP.
  - apply Permutation_vs_elt_subst; assumption.
  - exists l1, l2; split; [ reflexivity | assumption ].
  Qed.

  Lemma PEPermutation_vs_elt_inv a l l1 l2 :
    PEPermutation l (l1 ++ a :: l2) -> exists l3 l4,
      PEPermutation (l1 ++ l2) (l3 ++ l4) /\ l = l3 ++ a :: l4.
  Proof.
  intros HP; apply PEPermutation_vs_elt_subst in HP as [l3 [l4 [HP ->]]].
  exists l3, l4; split; [ apply (HP nil) | reflexivity ].
  Qed.

  Lemma PEPermutation_vs_cons_inv a l l1 :
    PEPermutation l (a :: l1) -> exists l2 l3, PEPermutation l1 (l2 ++ l3) /\ l = l2 ++ a :: l3.
  Proof. now intro HP; rewrite <- (app_nil_l l1); apply PEPermutation_vs_elt_inv. Qed.

  #[export] Instance PEPermtutation_in a : Proper (PEPermutation ==> Basics.impl) (In a).
  Proof. now case_perm; simpl; intros l l' HP HIn; subst; [ apply Permutation_in with l | ]. Qed.

  #[export] Instance PEPermutation_Forall (P : A -> Prop) :
    Proper (PEPermutation ==> Basics.impl) (Forall P).
  Proof.
  now case_perm; simpl; intros l1 l2 HP HF; subst; [ apply Permutation_Forall with l1 | ].
  Qed.

  #[export] Instance PEPermutation_Exists (P : A -> Prop) :
    Proper (PEPermutation ==> Basics.impl) (Exists P).
  Proof.
  now case_perm; simpl; intros l1 l2 HP HF; subst; [ apply Permutation_Exists with l1 | ].
  Qed.

  #[export] Instance PEPermutation_rev : Proper (PEPermutation ==> PEPermutation) (@rev A).
  Proof. now case_perm; intros l1 l2 ->. Qed.


  (** * From [PEPermutation] to [PCPermutation] *)

  #[export] Instance PEPermutation_PCPermutation_cons :
    Proper (eq ==> PEPermutation ==> PCPermutation) cons.
  Proof.
  intros x y -> l1 l2 HP.
  apply PEPermutation_PCPermutation.
  now rewrite HP.
  Qed.

  #[export] Instance PEPermutation_PCPermutation_app :
    Proper (PEPermutation ==> PEPermutation ==> PCPermutation) (@app A).
  Proof.
  intros l1 l1' HPhd l2 l2' HPtl.
  apply PEPermutation_PCPermutation.
  now rewrite HPhd, HPtl.
  Qed.

  Lemma PCPermutation_vs_elt_inv a l l1 l2 :
    PCPermutation l (l1 ++ a :: l2) ->  exists l' l'',
      PEPermutation (l2 ++ l1) (l'' ++ l') /\ l = l' ++ a :: l''.
  Proof.
  case_perm; intro HP.
  - destruct (Permutation_vs_elt_inv _ _ _ HP) as (l' & l'' & ->).
    exists l', l''; split; auto.
    apply Permutation_app_inv in HP.
    symmetry in HP.
    etransitivity; [ eapply Permutation_app_comm | ].
    etransitivity; [ eassumption | apply Permutation_app_comm ].
  - destruct (CPermutation_vs_elt_inv _ _ _ HP) as (l' & l'' & Heq & ->).
    exists l', l''; auto.
  Qed.

  Lemma PCPermutation_vs_cons_inv a l l1 :
    PCPermutation l (a :: l1) -> exists l' l'', PEPermutation l1 (l'' ++ l') /\ l = l' ++ a :: l''.
  Proof.
  intro HP.
  rewrite <- app_nil_l in HP.
  apply PCPermutation_vs_elt_inv in HP as (l' & l'' & HP & ->).
  exists l', l''; split; auto.
  now rewrite app_nil_r in HP.
  Qed.

  Lemma PCPermutation_cons_cons_inv a1 a2 l1 l2 :
    PCPermutation (a1 :: l1) (a2 :: l2) ->
       a1 = a2 /\ PEPermutation l1 l2
    \/ exists l3 l4, PEPermutation l1 (l4 ++ a2 :: l3) /\ l2 = l3 ++ a1 :: l4.
  Proof.
  intros HP; symmetry in HP.
  apply PCPermutation_vs_cons_inv in HP.
  destruct HP as [l1' [l2' [HP' Heq]]].
  destruct l1' as [|a' l1']; inversion Heq; subst.
  - left; split; auto.
    now rewrite app_nil_r in HP'.
  - right; exists l1', l2'; auto.
  Qed.

  Lemma PCPermutation_cons_cons_notin_inv a l l1 :
    ~ In a l -> PCPermutation (a :: l) (a :: l1) -> PEPermutation l l1.
  Proof.
  intros Hin HP.
  apply PCPermutation_cons_cons_inv in HP as [[Heq HP] | [l3 [l4 [HP Heq]]]]; auto.
  exfalso.
  apply Hin; rewrite HP; apply in_elt.
  Qed.

End GPermutation.

Section MultiGPermutation.

  Variable A B : Type.
  Variable c : comparison.
  Variable b : bool.

  Lemma PCEPermutation_Forall2 (P : A -> B -> Prop) l1 l1' l2 :
    PCEPermutation c l1 l1' -> Forall2 P l1 l2 -> exists l2',
      PCEPermutation c l2 l2' /\ Forall2 P l1' l2'.
  Proof.
  destruct c; [ apply CPermutation_Forall2 | | apply Permutation_Forall2 ].
  now simpl; intros -> HF; exists l2.
  Qed.

  Lemma PCPermutation_Forall2 (P : A -> B -> Prop) l1 l1' l2 :
    PCPermutation b l1 l1' -> Forall2 P l1 l2 -> exists l2',
      PCPermutation b l2 l2' /\ Forall2 P l1' l2'.
  Proof. destruct b; [ apply Permutation_Forall2 | apply CPermutation_Forall2 ]. Qed.

  Lemma PEPermutation_Forall2 (P : A -> B -> Prop) l1 l1' l2 :
    PEPermutation b l1 l1' -> Forall2 P l1 l2 -> exists l2',
      PEPermutation b l2 l2' /\ Forall2 P l1' l2'.
  Proof. destruct b; [ apply Permutation_Forall2 | simpl; intros; subst; now exists l2 ]. Qed.

  Variable f : A -> B.

  #[export] Instance PCEPermutation_map : Proper (PCEPermutation c ==> PCEPermutation c) (map f).
  Proof. now destruct c; intros l1 l2 ->. Qed.

  #[export] Instance PCPermutation_map : Proper (PCPermutation b ==> PCPermutation b) (map f).
  Proof. now destruct b; intros l1 l2 ->. Qed.

  #[export] Instance PEPermutation_map : Proper (PEPermutation b ==> PEPermutation b) (map f).
  Proof. now destruct b; simpl; intros l1 l2 ->. Qed.

  Lemma PCEPermutation_map_inv l1 l2 :
    PCEPermutation c l1 (map f l2) -> exists l3, l1 = map f l3 /\ PCEPermutation c l2 l3.
  Proof.
  destruct c; [ apply CPermutation_map_inv | | apply Permutation_map_inv ].
  now simpl; intros ->; exists l2.
  Qed.

  Lemma PCPermutation_map_inv l1 l2 :
    PCPermutation b l1 (map f l2) -> exists l3, l1 = map f l3 /\ PCPermutation b l2 l3.
  Proof. destruct b; [ apply Permutation_map_inv | apply CPermutation_map_inv ]. Qed.

  Lemma PEPermutation_map_inv l1 l2 :
    PEPermutation b l1 (map f l2) -> exists l3, l1 = map f l3 /\ PEPermutation b l2 l3.
  Proof. now destruct b; [ apply Permutation_map_inv | exists l2 ]. Qed.

  Lemma PCEPermutation_map_inv_inj (Hinj : injective f) l1 l2 :
    PCEPermutation c (map f l1) (map f l2) -> PCEPermutation c l1 l2.
  Proof.
  now destruct c;
    [ apply CPermutation_map_inv_inj | apply map_injective | apply Permutation_map_inv_inj ].
  Qed.

  Lemma PCPermutation_map_inv_inj (Hinj : injective f) l1 l2 :
    PCPermutation b (map f l1) (map f l2) -> PCPermutation b l1 l2.
  Proof. now destruct b; [ apply Permutation_map_inv_inj | apply CPermutation_map_inv_inj ]. Qed.

  Lemma PEPermutation_map_inv_inj (Hinj : injective f) l1 l2 :
    PEPermutation b (map f l1) (map f l2) -> PEPermutation b l1 l2.
  Proof. now destruct b; [ apply Permutation_map_inv_inj | apply map_injective ]. Qed.

  Lemma PCEPermutation_image a l l' :
    PCEPermutation c (a :: l) (map f l') -> exists a', a = f a'.
  Proof.
  destruct c; [ apply CPermutation_image | | apply Permutation_image ].
  now simpl; intros Heq; destruct l' as [|a' l']; inversion Heq; subst; exists a'.
  Qed.

  Lemma PCPermutation_image a l l' :
    PCPermutation b (a :: l) (map f l') -> exists a', a = f a'.
  Proof. destruct b; [ apply Permutation_image | apply CPermutation_image ]. Qed.

  Lemma PEPermutation_image a l l' :
    PEPermutation b (a :: l) (map f l') -> exists a', a = f a'.
  Proof.
  destruct b ; [ apply Permutation_image | ].
  now simpl; intros Heq; destruct l' as [|a' l']; inversion Heq; subst; exists a'.
  Qed.

  Variable c' : comparison.
  Variable b' : bool.

  Lemma PCEPermutation_monot (Hle : ComparisonOrder.le c c') (l1 l2 : list A) :
    PCEPermutation c l1 l2 -> PCEPermutation c' l1 l2.
  Proof.
  destruct c, c'; simpl; try (now inversion Hle); try (now intros; subst).
  apply CPermutation_Permutation.
  Qed.

  Lemma PCPermutation_monot (Hle : Bool.le b b') (l1 l2 : list A) :
    PCPermutation b l1 l2 -> PCPermutation b' l1 l2.
  Proof. destruct b, b'; try (now inversion Hle); apply CPermutation_Permutation. Qed.

  Lemma PEPermutation_monot (Hle : Bool.le b b') (l1 l2 : list A) :
    PEPermutation b l1 l2 -> PEPermutation b' l1 l2.
  Proof. now destruct b, b'; try (now inversion Hle); simpl; intros ->. Qed.

End MultiGPermutation.


(** * Solvinc tactics *)

(** unfolding into [Permutation], [CPermutation] or [eq] *)
Ltac hyps_GPermutation_unfold :=
  match goal with
  | H : PCEPermutation _ _ _ |- _ => unfold PCEPermutation in H; hyps_GPermutation_unfold
  | H : PCPermutation _ _ _ |- _ => unfold PCPermutation in H; hyps_GPermutation_unfold
  | H : PEPermutation _ _ _ |- _ => unfold PEPermutation in H; hyps_GPermutation_unfold
  | _ => idtac
  end.

(** automatic solving *)
Ltac GPermutation_solve :=
  hyps_GPermutation_unfold; simpl;
  match goal with
  | |- PCEPermutation ?c _ _ => unfold PCEPermutation; destruct c; simpl; GPermutation_solve
  | |- PCPermutation ?b _ _ => unfold PCPermutation; destruct b; simpl; GPermutation_solve
  | |- PEPermutation ?b _ _ => unfold PEPermutation; destruct b; simpl; GPermutation_solve
  | |- Permutation _ _  => Permutation_solve
  | |- CPermutation _ _  => CPermutation_solve
  | |- eq _ _  => reflexivity
  end.
