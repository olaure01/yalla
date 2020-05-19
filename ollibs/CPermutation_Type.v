(** Cyclic Permutations
Definition and basic properties of cyclic permutations in [Type]. *)

From Coq Require Import CMorphisms PeanoNat.
From Coq Require CPermutation.
From OLlibs Require Import List_more Permutation_Type_more funtheory.

Set Implicit Arguments.


(** * Definition *)
Inductive CPermutation_Type A : list A -> list A -> Type :=
| cperm_Type : forall l1 l2, CPermutation_Type (l1 ++ l2) (l2 ++ l1).

Instance CPermutation_Permutation_Type A : Proper (@CPermutation_Type A ==> @Permutation_Type A) id.
Proof.
intros l1 l2 HC.
inversion HC.
apply Permutation_Type_app_comm.
Qed.

Lemma CPermutation_Type_CPermutation A : forall l1 l2 : list A,
  CPermutation_Type l1 l2 -> CPermutation.CPermutation l1 l2.
Proof. intros l1 l2 HP; inversion HP; constructor. Qed.


(** * Properties *)

Instance CPermutation_Type_refl A : Reflexive (@CPermutation_Type A).
Proof.
intros l.
assert (CPermutation_Type (nil ++ l) (l ++ nil))
  as HC by (eapply cperm_Type).
simpl in HC.
now rewrite app_nil_r in HC.
Qed.

Instance CPermutation_Type_sym A : Symmetric (@CPermutation_Type A).
Proof.
intros l1 l2 HC.
inversion HC.
apply cperm_Type.
Qed.

Instance CPermutation_Type_trans A : Transitive (@CPermutation_Type A).
Proof.
intros l1 l2 l3 HC1 HC2.
inversion HC1 ; inversion HC2 ; subst.
apply dichot_app_inf in H1.
destruct H1 as [[l2' [Hl1 Hl2]] | [l4' [Hr1 Hr2]]] ; subst.
- rewrite <- app_assoc, app_assoc.
  apply cperm_Type.
- rewrite <- app_assoc, (app_assoc l6).
  apply cperm_Type.
Qed.

Instance CPermutation_Type_equiv A : Equivalence (@CPermutation_Type A).
Proof.
split.
- apply CPermutation_Type_refl.
- apply CPermutation_Type_sym.
- apply CPermutation_Type_trans.
Qed.

Lemma CPermutation_Type_split A : forall l1 l2 : list A,
  CPermutation_Type l1 l2 -> { n | l2 = skipn n l1 ++ firstn n l1 }.
Proof.
intros l1 l2 [l1' l2'].
exists (length l1').
rewrite skipn_app, skipn_all, Nat.sub_diag; simpl; f_equal.
now rewrite firstn_app, firstn_all, Nat.sub_diag; simpl; rewrite app_nil_r.
Qed.

Lemma CPermutation_Type_skipn_firstn A : forall (l : list A) n,
  CPermutation_Type l (skipn n l ++ firstn n l).
Proof.
intros l n.
transitivity (firstn n l ++ skipn n l); [ | constructor ].
now rewrite (firstn_skipn n).
Qed.

Lemma CPermutation_Type_app A : forall l1 l2 l3 : list A,
  CPermutation_Type (l1 ++ l2) l3 -> CPermutation_Type (l2 ++ l1) l3.
Proof.
intros l1 l2 l3 HC.
refine (CPermutation_Type_trans _ HC).
apply cperm_Type.
Qed.

Lemma CPermutation_Type_app_rot A : forall (l1 : list A) l2 l3,
   CPermutation_Type (l1 ++ l2 ++ l3) (l2 ++ l3 ++ l1).
Proof.
intros l1 l2 l3.
rewrite (app_assoc l2).
apply cperm_Type.
Qed.

Lemma CPermutation_Type_cons_append A : forall (a : A) l,
  CPermutation_Type (a :: l) (l ++ a :: nil).
Proof.
intros.
rewrite <- (app_nil_l l), app_comm_cons.
apply cperm_Type.
Qed.

Lemma CPermutation_Type_swap A : forall a b : A,
  CPermutation_Type (a :: b :: nil) (b :: a :: nil).
Proof.
intros.
change (a :: b :: nil) with ((a :: nil) ++ (b :: nil)).
change (b :: a :: nil) with ((b :: nil) ++ (a :: nil)).
apply cperm_Type.
Qed.

Lemma CPermutation_Type_cons A : forall l1 (a : A) l2,
  CPermutation_Type (l1 ++ a :: nil) l2 -> CPermutation_Type (a :: l1) l2.
Proof.
intros l1 a l2 HC.
now apply (CPermutation_Type_app l1 (a :: nil)).
Qed.

Lemma CPermutation_Type_morph_cons A : forall P : list A -> Prop,
  (forall a l, P (l ++ a :: nil) -> P (a :: l)) ->
  Proper (@CPermutation_Type A ==> Basics.impl) P.
Proof.
assert (forall P : list A -> Prop,
         (forall a l, P (l ++ a :: nil) -> P (a :: l)) ->
         forall l1 l2, CPermutation_Type l1 l2 -> P l1 -> P l2)
  as Himp.
{ intros P HP l1 l2 HC.
  inversion HC ; subst ; clear HC.
  revert l0 ; induction l3 using rev_ind ; intros l0 HPl.
  - now rewrite app_nil_r in HPl.
  - rewrite app_assoc in HPl.
    apply HP in HPl.
    rewrite <- app_assoc, <- app_comm_cons, app_nil_l; auto. }
intros P HP l1 l2 HC H.
now apply Himp with l1.
Qed.

Lemma CPermutation_Type_nil A : forall l : list A,
  CPermutation_Type nil l -> l = nil.
Proof. now intros; apply Permutation_Type_nil, CPermutation_Permutation_Type. Qed.

Lemma CPermutation_Type_nil_cons A : forall l (a : A),
  CPermutation_Type nil (a :: l) -> False.
Proof.
intros l a HC.
apply CPermutation_Type_nil in HC.
inversion HC.
Qed.

Lemma CPermutation_Type_length_1 A : forall a b : A,
  CPermutation_Type (a :: nil) (b :: nil) -> a = b.
Proof. now intros; apply Permutation_Type_length_1, CPermutation_Permutation_Type. Qed.

Lemma CPermutation_Type_length_2 A : forall a1 a2 b1 b2 : A,
  CPermutation_Type (a1 :: a2 :: nil) (b1 :: b2 :: nil) ->
    { a1 = b1 /\ a2 = b2 } + { a1 = b2 /\ a2 = b1 }.
Proof. now intros; apply Permutation_Type_length_2, CPermutation_Permutation_Type. Qed.

Lemma CPermutation_Type_length_1_inv A : forall (a : A) l,
  CPermutation_Type (a :: nil) l -> l = a :: nil.
Proof. now intros; apply Permutation_Type_length_1_inv, CPermutation_Permutation_Type. Qed.

Lemma CPermutation_Type_length_2_inv A : forall (a : A) b l,
  CPermutation_Type (a :: b :: nil) l ->
  { l = a :: b :: nil } + { l = b :: a :: nil }.
Proof. now intros; apply Permutation_Type_length_2_inv, CPermutation_Permutation_Type. Qed.

Lemma CPermutation_Type_vs_elt_inv A : forall (a : A) l l1 l2,
  CPermutation_Type l (l1 ++ a :: l2) ->
    {'(l1',l2') | l2 ++ l1 = l2' ++ l1' & l = l1' ++ a :: l2' }.
Proof.
intros a l l1 l2 HC.
inversion HC; subst.
symmetry in H1.
dichot_elt_app_inf_exec H1; subst.
- now exists (l0 ++ l1, l); simpl; rewrite <- app_assoc.
- now exists (l4, l2 ++ l3); simpl; rewrite <- app_assoc.
Qed.

Lemma CPermutation_Type_vs_cons_inv A : forall (a : A) l l1,
  CPermutation_Type l (a :: l1) ->
    {'(l1',l2') | l1 = l2' ++ l1' & l = l1' ++ a :: l2' }.
Proof.
intros a l l1 HC.
rewrite <- (app_nil_l (a::_)) in HC.
apply CPermutation_Type_vs_elt_inv in HC.
destruct HC as [(l1',l2') H1 H2].
rewrite app_nil_r in H1 ; subst.
now exists (l1', l2').
Qed.

Lemma CPermutation_Type_app_app_inv A : forall l1 l2 l3 l4 : list A,
  CPermutation_Type (l1 ++ l2) (l3 ++ l4) ->
     {'(l1',l2',l3',l4') : _ & prod
        (prod  (CPermutation_Type l1 (l1' ++ l3'))
               (CPermutation_Type l2 (l2' ++ l4')))
        (prod  (CPermutation_Type l3 (l1' ++ l2'))
               (CPermutation_Type l4 (l3' ++ l4'))) }
   + {'(l1',l2') : _ & prod (prod
        (CPermutation_Type l1 (l4 ++ l1'))
        (CPermutation_Type l3 (l2 ++ l2')))
        (CPermutation_Type l1' l2') }
   + {'(l1',l2') : _ & prod (prod
        (CPermutation_Type l2 (l4 ++ l1'))
        (CPermutation_Type l3 (l1 ++ l2')))
        (CPermutation_Type l1' l2') }
   + {'(l1',l2') : _ & prod (prod
        (CPermutation_Type l1 (l3 ++ l1'))
        (CPermutation_Type l4 (l2 ++ l2')))
        (CPermutation_Type l1' l2') }
   + {'(l1',l2') : _ & prod (prod
        (CPermutation_Type l2 (l3 ++ l1'))
        (CPermutation_Type l4 (l1 ++ l2')))
        (CPermutation_Type l1' l2') }.
Proof.
intros l1 l2 l3 l4 HC.
inversion HC as [lx ly Hx Hy].
dichot_app_inf_exec Hx; dichot_app_inf_exec Hy; subst.
- left; left; left; right; exists (l ++ l0, l0 ++ l); repeat split;
    rewrite <- ? app_assoc; apply CPermutation_Type_app_rot.
- dichot_app_inf_exec Hy0; subst.
  + left; left; left; left; exists (l, l0, lx, l5); repeat split;
      apply CPermutation_Type_refl.
  + left; right; exists (l1 ++ lx , lx ++ l1); repeat split;
      rewrite <- ? app_assoc ; apply CPermutation_Type_app_rot.
- dichot_app_inf_exec Hy1 ; subst.
  + left; left; right; exists (ly ++ l2, l2 ++ ly); repeat split;
      rewrite <- ? app_assoc; apply CPermutation_Type_app_rot.
  + left; left; left; left; exists (l, ly, l3, l0); repeat split;
      apply CPermutation_Type_refl.
- right; exists (l5 ++ l0, l0 ++ l5); repeat split;
    rewrite <- ? app_assoc; apply CPermutation_Type_app_rot.
Qed.

(** [rev], [in], [map], [Forall], [Exists], etc. *)
Instance CPermutation_Type_rev A : Proper (@CPermutation_Type A ==> @CPermutation_Type A) (@rev A).
Proof.
intros l; induction l; intros l' HC.
- apply CPermutation_Type_nil in HC; subst; apply CPermutation_Type_refl.
- apply CPermutation_Type_sym in HC.
  apply CPermutation_Type_vs_cons_inv in HC.
  destruct HC as [(l1 & l2) -> ->].
  now simpl; rewrite ? rev_app_distr; simpl; rewrite <- app_assoc.
Qed.

Instance CPermutation_Type_in A (a : A) : Proper (@CPermutation_Type A ==> Basics.impl) (In a).
Proof.
intros l l' HC Hin.
apply Permutation_Type_in with l; auto.
now apply CPermutation_Permutation_Type.
Qed.

Instance CPermutation_Type_map A B (f : A -> B) :
   Proper (@CPermutation_Type A ==> @CPermutation_Type B) (map f).
Proof.
intros l l' HC.
now inversion HC; subst; rewrite ? map_app.
Qed.

Lemma CPermutation_Type_map_inv A B : forall(f : A -> B) l1 l2,
  CPermutation_Type l1 (map f l2) ->
    { l & l1 = map f l & (CPermutation_Type l2 l) }.
Proof.
induction l1; intros l2 HP.
- exists nil; auto.
  simpl; destruct l2; auto.
  + apply CPermutation_Type_refl.
  + apply CPermutation_Type_nil in HP.
    inversion HP.
- apply CPermutation_Type_sym in HP.
  destruct (CPermutation_Type_vs_cons_inv HP) as [(l3 & l4) -> Heq2].
  decomp_map_inf Heq2; subst; simpl.
  exists (x :: l5 ++ l0).
  + now simpl; rewrite ? map_app.
  + constructor.
Qed.

Instance CPermutation_Type_Forall A (P : A -> Prop) :
  Proper (@CPermutation_Type A ==> Basics.impl) (Forall P).
Proof.
intros l1 l2 HC HF.
apply Permutation_Type_Forall with l1; auto.
now apply CPermutation_Permutation_Type.
Qed.

Instance CPermutation_Type_Exists A (P : A -> Prop) :
  Proper (@CPermutation_Type A ==> Basics.impl) (Exists P).
Proof.
intros l1 l2 HC HE.
apply Permutation_Type_Exists with l1; auto.
now apply CPermutation_Permutation_Type.
Qed.

Instance CPermutation_Type_Forall_inf A (P : A -> Type) :
  Proper (@CPermutation_Type A ==> Basics.arrow) (Forall_inf P).
Proof.
intros l1 l2 HC HF.
apply Permutation_Type_Forall_inf with l1; auto.
now apply CPermutation_Permutation_Type.
Qed.

Instance CPermutation_Type_Exists_inf A (P : A -> Type) :
  Proper (@CPermutation_Type A ==> Basics.arrow) (Exists_inf P).
Proof.
intros l1 l2 HC HE.
apply Permutation_Type_Exists_inf with l1; auto.
now apply CPermutation_Permutation_Type.
Qed.

Lemma CPermutation_Type_Forall2_inf A B (P : A -> B -> Type) :
  forall l1 l1' l2, CPermutation_Type l1 l1' -> Forall2_inf P l1 l2 ->
    { l2' & CPermutation_Type l2 l2' & Forall2_inf P l1' l2' }.
Proof.
intros l1 l1' l2 HP.
revert l2; induction HP; intros l2' HF; inversion HF; subst.
- exists nil; auto.
  + reflexivity.
  + now symmetry in H0; apply app_eq_nil in H0 as [Heq1 Heq2]; subst.
- destruct l1 ; inversion H0; subst.
  + rewrite app_nil_l in H0; subst.
    exists (y :: l').
    * reflexivity.
    * now rewrite app_nil_l in HF; simpl; rewrite app_nil_r.
  + apply Forall2_inf_app_inv_l in X0 as [(la, lb) [HF1 HF2] ->].
    exists (lb ++ y :: la).
    * rewrite app_comm_cons; constructor.
    * apply Forall2_inf_app; auto.
Qed.

Lemma CPermutation_Type_image A B : forall (f : A -> B) a l l',
  CPermutation_Type (a :: l) (map f l') -> { a' | a = f a' }.
Proof.
intros f a l l' HP.
apply Permutation_Type_image with l l'.
now apply CPermutation_Permutation_Type.
Qed.

Lemma CPermutation_Type_map_inv_inj A B : forall f : A -> B, injective f ->
  forall l1 l2, CPermutation_Type (map f l1) (map f l2) -> CPermutation_Type l1 l2.
Proof.
intros f Hi l1 l2 HP; inversion HP as [l3 l4 Heq1 Heq2].
symmetry in Heq1; symmetry in Heq2.
decomp_map_inf Heq1; decomp_map_inf Heq2; subst.
apply map_injective in Heq5; auto.
apply map_injective in Heq6; auto.
subst; constructor.
Qed.

Lemma CPermutation_Type_map_inv_inj_local A B : forall (f : A -> B) l1 l2,
  (forall x y, In x l1 -> In y l2 -> f x = f y -> x = y) ->
    CPermutation_Type (map f l1) (map f l2) -> CPermutation_Type l1 l2.
Proof.
intros f l1 l2 Hi HP; inversion HP as [l3 l4 Heq1 Heq2].
symmetry in Heq1; symmetry in Heq2.
decomp_map_inf Heq1; decomp_map_inf Heq2; subst.
symmetry in Heq5; symmetry in Heq6.
apply map_injective_in in Heq5.
2:{ intros x y Hin1 Hin2 Heq; apply Hi; auto; apply in_or_app; auto. }
apply map_injective_in in Heq6.
2:{ intros x y Hin1 Hin2 Heq; apply Hi; auto; apply in_or_app; auto. }
subst; constructor.
Qed.
