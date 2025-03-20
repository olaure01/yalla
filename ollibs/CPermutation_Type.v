(** Cyclic Permutations
Definition and basic properties of cyclic permutations in [Type]. *)

Set Implicit Arguments.

From Stdlib Require Import CMorphisms PeanoNat.
From Stdlib Require CPermutation.
From Yalla.OLlibs Require Import List_more Permutation_Type_more funtheory.


(** * Definition *)
Inductive CPermutation_Type A : list A -> list A -> Type :=
| cperm_Type : forall l1 l2, CPermutation_Type (l1 ++ l2) (l2 ++ l1).

#[export] Instance CPermutation_Permutation_Type A :
   Proper (@CPermutation_Type A ==> @Permutation_Type A) id.
Proof. intros ? ? []. apply Permutation_Type_app_comm. Qed.

Lemma CPermutation_Type_CPermutation A (l1 l2 : list A) :
  CPermutation_Type l1 l2 -> CPermutation.CPermutation l1 l2.
Proof. intros []. constructor. Qed.


(** * Properties *)

#[export] Instance CPermutation_Type_refl A : Reflexive (@CPermutation_Type A).
Proof.
intro l.
assert (CPermutation_Type (nil ++ l) (l ++ nil))
  as HC by (eapply cperm_Type).
simpl in HC.
now rewrite app_nil_r in HC.
Qed.

#[export] Instance CPermutation_Type_sym A : Symmetric (@CPermutation_Type A).
Proof. intros ? ? []. apply cperm_Type. Qed.

#[export] Instance CPermutation_Type_trans A : Transitive (@CPermutation_Type A).
Proof.
intros l1 l2 l3 [l4 l5] HC2. inversion HC2 as [l6 l7 H1 H2]. subst.
dichot_app_inf_exec H1 as [[l2' <- ->] | [l4' -> <-]].
- rewrite <- app_assoc, app_assoc. apply cperm_Type.
- rewrite <- app_assoc, (app_assoc l7). apply cperm_Type.
Qed.

#[export] Instance CPermutation_Type_equiv A : Equivalence (@CPermutation_Type A).
Proof.
split.
- apply CPermutation_Type_refl.
- apply CPermutation_Type_sym.
- apply CPermutation_Type_trans.
Qed.

Lemma CPermutation_Type_split A (l1 l2 : list A) :
  CPermutation_Type l1 l2 -> { n | l2 = skipn n l1 ++ firstn n l1 }.
Proof.
intros [l1' l2'].
exists (length l1').
rewrite skipn_app, skipn_all, Nat.sub_diag. cbn. f_equal.
now rewrite firstn_app, firstn_all, Nat.sub_diag; cbn; rewrite app_nil_r.
Qed.

Lemma CPermutation_Type_skipn_firstn A (l : list A) n : CPermutation_Type l (skipn n l ++ firstn n l).
Proof.
transitivity (firstn n l ++ skipn n l); [ | constructor ].
now rewrite (firstn_skipn n).
Qed.

Lemma CPermutation_Type_app A (l1 l2 l3 : list A) :
  CPermutation_Type (l1 ++ l2) l3 -> CPermutation_Type (l2 ++ l1) l3.
Proof. intro HC. exact (CPermutation_Type_trans (cperm_Type _ _) HC). Qed.

Theorem CPermutation_Type_app_comm A (l1 l2 : list A) :
  CPermutation_Type (l1 ++ l2) (l2 ++ l1).
Proof. apply cperm_Type. Qed.

Lemma CPermutation_Type_app_rot A (l1 l2 l3 : list A) :
  CPermutation_Type (l1 ++ l2 ++ l3) (l2 ++ l3 ++ l1).
Proof. rewrite (app_assoc l2). apply cperm_Type. Qed.

Lemma CPermutation_Type_cons_append A (a : A) l :
  CPermutation_Type (a :: l) (l ++ a :: nil).
Proof. intros. rewrite <- (app_nil_l l), app_comm_cons. apply cperm_Type. Qed.

Lemma CPermutation_Type_swap A (a b : A) : CPermutation_Type (a :: b :: nil) (b :: a :: nil).
Proof.
intros.
change (a :: b :: nil) with ((a :: nil) ++ (b :: nil)).
change (b :: a :: nil) with ((b :: nil) ++ (a :: nil)).
apply cperm_Type.
Qed.

Lemma CPermutation_Type_cons A l1 (a : A) l2 :
  CPermutation_Type (l1 ++ a :: nil) l2 -> CPermutation_Type (a :: l1) l2.
Proof. intro. now apply (CPermutation_Type_app l1 (a :: nil)). Qed.

Lemma CPermutation_Type_morph_cons A (P : list A -> Prop) :
  (forall a l, P (l ++ a :: nil) -> P (a :: l)) ->
  Proper (@CPermutation_Type A ==> Basics.impl) P.
Proof.
intros HP l1 l2 [l3 l4] HPl.
induction l4 as [|a l4 IHl4] in l3, HPl |- * using rev_ind.
- now rewrite app_nil_r in HPl.
- rewrite app_assoc in HPl. rewrite <- app_assoc, <- app_comm_cons, app_nil_l.
  apply IHl4, HP, HPl.
Qed.

Lemma CPermutation_Type_nil A (l : list A) : CPermutation_Type nil l -> l = nil.
Proof. now intro; apply Permutation_Type_nil, CPermutation_Permutation_Type. Qed.

Lemma CPermutation_Type_nil_cons A l (a : A) : notT (CPermutation_Type nil (a :: l)).
Proof. intros [=]%CPermutation_Type_nil. Qed.

Lemma CPermutation_Type_length_1 A (a b : A) :
  CPermutation_Type (a :: nil) (b :: nil) -> a = b.
Proof. now intro; apply Permutation_Type_length_1, CPermutation_Permutation_Type. Qed.

Lemma CPermutation_Type_length_2 A (a1 a2 b1 b2 : A) :
  CPermutation_Type (a1 :: a2 :: nil) (b1 :: b2 :: nil) -> { a1 = b1 /\ a2 = b2 } + { a1 = b2 /\ a2 = b1 }.
Proof. now intro; apply Permutation_Type_length_2, CPermutation_Permutation_Type. Qed.

Lemma CPermutation_Type_length_1_inv A (a : A) l : CPermutation_Type (a :: nil) l -> l = a :: nil.
Proof. now intro; apply Permutation_Type_length_1_inv, CPermutation_Permutation_Type. Qed.

Lemma CPermutation_Type_length_2_inv A (a : A) b l :
  CPermutation_Type (a :: b :: nil) l -> { l = a :: b :: nil } + { l = b :: a :: nil }.
Proof. now intro; apply Permutation_Type_length_2_inv, CPermutation_Permutation_Type. Qed.

Lemma CPermutation_Type_vs_elt_inv A (a : A) l l1 l2 :
  CPermutation_Type l (l1 ++ a :: l2) -> {'(l1',l2') | l2 ++ l1 = l2' ++ l1' & l = l1' ++ a :: l2' }.
Proof.
intro HC. inversion HC as [l3 l4 H1 H2]. subst.
dichot_elt_app_inf_exec H2; subst.
- now exists (l3 ++ l1, l); cbn; rewrite <- app_assoc.
- now exists (l, l2 ++ l4); cbn; rewrite <- app_assoc.
Qed.

Lemma CPermutation_Type_vs_cons_inv A (a : A) l l1 :
  CPermutation_Type l (a :: l1) -> {'(l1',l2') | l1 = l2' ++ l1' & l = l1' ++ a :: l2' }.
Proof.
intro HC. rewrite <- (app_nil_l (a::_)) in HC. apply CPermutation_Type_vs_elt_inv in HC as [(l1',l2') H1 ->].
rewrite app_nil_r in H1. now exists (l1', l2').
Qed.

Lemma CPermutation_Type_vs_elt_subst A (a : A) l l1 l2 :
  CPermutation_Type l (l1 ++ a :: l2) ->
  {'(l3, l4) & forall l0, CPermutation_Type (l1 ++ l0 ++ l2) (l3 ++ l0 ++ l4) & l = l3 ++ a :: l4 }.
Proof.
intros [(l', l'') Heq ->]%CPermutation_Type_vs_elt_inv.
exists (l', l''); [ | reflexivity ].
intro l0.
etransitivity; [ apply CPermutation_Type_app_comm | ].
list_simpl. rewrite Heq, app_assoc. constructor.
Qed.

Lemma CPermutation_Type_app_app_inv A (l1 l2 l3 l4 : list A) :
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
intro HC. inversion HC as [lx ly Hx Hy].
dichot_app_inf_exec Hx; dichot_app_inf_exec Hy; subst.
- left; left; left; right; exists (l ++ l0, l0 ++ l); repeat split;
    rewrite <- ? app_assoc; apply CPermutation_Type_app_rot.
- dichot_app_inf_exec Hy0; subst.
  + left; left; left; left; exists (l, l1, lx, l0); repeat split;
      apply CPermutation_Type_refl.
  + left; right; exists (l1 ++ lx , lx ++ l1); repeat split;
      rewrite <- ? app_assoc ; apply CPermutation_Type_app_rot.
- dichot_app_inf_exec Hy1 ; subst.
  + left; left; right; exists (ly ++ l2, l2 ++ ly); repeat split;
      rewrite <- ? app_assoc; apply CPermutation_Type_app_rot.
  + left; left; left; left; exists (l0, ly, l2, l); repeat split;
      apply CPermutation_Type_refl.
- right; exists (l0 ++ l, l ++ l0); repeat split;
    rewrite <- ? app_assoc; apply CPermutation_Type_app_rot.
Qed.

(** [rev], [in], [map], [Forall], [Exists], etc. *)
#[export] Instance CPermutation_Type_rev A :
  Proper (@CPermutation_Type A ==> @CPermutation_Type A) (@rev A).
Proof.
intros l; induction l; intros l' HC.
- apply CPermutation_Type_nil in HC; subst; apply CPermutation_Type_refl.
- apply CPermutation_Type_sym in HC.
  apply CPermutation_Type_vs_cons_inv in HC.
  destruct HC as [(l1 & l2) -> ->].
  now simpl; rewrite ? rev_app_distr; simpl; rewrite <- app_assoc.
Qed.

#[export] Instance CPermutation_Type_in A (a : A) :
  Proper (@CPermutation_Type A ==> Basics.impl) (In a).
Proof.
intros l l' HC Hin.
apply Permutation_Type_in with l; auto.
now apply CPermutation_Permutation_Type.
Qed.

#[export] Instance CPermutation_Type_map A B (f : A -> B) :
  Proper (@CPermutation_Type A ==> @CPermutation_Type B) (map f).
Proof.
intros l l' HC.
now inversion HC; subst; rewrite ? map_app.
Qed.

Lemma CPermutation_Type_map_inv A B (f : A -> B) l1 l2 :
  CPermutation_Type l1 (map f l2) -> { l & l1 = map f l & CPermutation_Type l2 l }.
Proof.
induction l1 as [|a l1 IHl1] in l2 |- *; intro HP.
- exists nil; [ reflexivity | ].
  destruct l2.
  + apply CPermutation_Type_refl.
  + apply CPermutation_Type_nil in HP as [=].
- apply CPermutation_Type_sym in HP.
  destruct (CPermutation_Type_vs_cons_inv HP) as [(l3, l4) -> Heq2].
  decomp_map Heq2. subst l2.
  exists (a :: l4 ++ l3).
  + rewrite <- map_app. reflexivity.
  + constructor.
Qed.

#[export] Instance CPermutation_Type_Forall A (P : A -> Prop) :
  Proper (@CPermutation_Type A ==> Basics.impl) (Forall P).
Proof.
intros l1 l2 HC HF.
apply Permutation_Type_Forall with l1, HF.
apply CPermutation_Permutation_Type, HC.
Qed.

#[export] Instance CPermutation_Type_Exists A (P : A -> Prop) :
  Proper (@CPermutation_Type A ==> Basics.impl) (Exists P).
Proof.
intros l1 l2 HC HE.
apply Permutation_Type_Exists with l1, HE.
apply CPermutation_Permutation_Type, HC.
Qed.

#[export] Instance CPermutation_Type_Forall_inf A (P : A -> Type) :
  Proper (@CPermutation_Type A ==> arrow) (Forall_inf P).
Proof.
intros l1 l2 HC HF.
apply Permutation_Type_Forall_inf with l1, HF.
apply CPermutation_Permutation_Type, HC.
Qed.

#[export] Instance CPermutation_Type_Exists_inf A (P : A -> Type) :
  Proper (@CPermutation_Type A ==> arrow) (Exists_inf P).
Proof.
intros l1 l2 HC HE.
apply Permutation_Type_Exists_inf with l1, HE.
apply CPermutation_Permutation_Type, HC.
Qed.

Lemma CPermutation_Type_Forall2_inf A B (P : A -> B -> Type) l1 l1' l2 :
  CPermutation_Type l1 l1' -> Forall2_inf P l1 l2 -> { l2' & CPermutation_Type l2 l2' & Forall2_inf P l1' l2' }.
Proof.
intro HP. induction HP in l2 |- *; intro HF; inversion HF; subst.
- exists nil.
  + reflexivity.
  + now symmetry in H0; apply app_eq_nil in H0 as [Heq1 Heq2]; subst.
- destruct l1; inversion H0; subst.
  + rewrite app_nil_l in H0. subst.
    exists (y :: l').
    * reflexivity.
    * rewrite app_nil_r. assumption.
  + apply Forall2_inf_app_inv_l in X0 as [(la, lb) [HF1 HF2] ->].
    exists (lb ++ y :: la).
    * rewrite app_comm_cons. constructor.
    * apply Forall2_inf_app; [ | constructor ]; assumption.
Qed.

Lemma CPermutation_Type_image A B (f : A -> B) a l l' :
  CPermutation_Type (a :: l) (map f l') -> { a' | a = f a' }.
Proof. intro HP. apply Permutation_Type_image with l l', CPermutation_Permutation_Type, HP. Qed.

Lemma CPermutation_Type_map_inv_inj A B (f : A -> B) (Hi : injective f) l1 l2 :
  CPermutation_Type (map f l1) (map f l2) -> CPermutation_Type l1 l2.
Proof.
intro HP. inversion HP as [l3 l4 Heq1 Heq2].
decomp_map Heq1. decomp_map Heq2 eqn:Heq. subst l1 l2.
destruct Heq as [->%(map_injective Hi) ->%(map_injective Hi)]. constructor.
Qed.

Lemma CPermutation_Type_map_inv_inj_local A B (f : A -> B) l1 l2 :
  (forall x y, In x l1 -> In y l2 -> f x = f y -> x = y) ->
    CPermutation_Type (map f l1) (map f l2) -> CPermutation_Type l1 l2.
Proof.
intros Hi HP. inversion HP as [l3 l4 Heq1 Heq2].
decomp_map Heq1. decomp_map Heq2 eqn:Heq. subst l1 l2.
destruct Heq as [Heq1%eq_sym Heq2%eq_sym].
apply map_injective_in in Heq1 as ->; [ apply map_injective_in in Heq2 as -> | ]; [ constructor | | ].
- intros x y Hin1 Hin2 Heq. apply Hi; [ apply in_or_app .. | ]; [left | right | ]; assumption.
- intros x y Hin1 Hin2 Hf. apply Hi; [ apply in_or_app .. | ]; [right | left | ]; assumption.
Qed.
