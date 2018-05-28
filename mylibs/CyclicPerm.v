(* CyclicPerm library *)
(* Coq 8.6 *)
(* v0.1  2017/02/17   Olivier Laurent *)


(** * Cyclic Permutations
Definition and basic properties of cyclic permutations. *)

Require Import Morphisms.

Require Import List_more.
Require Import Permutation_more.

(** Definition *)
Inductive CPermutation {A} : list A -> list A -> Prop :=
| cperm : forall l1 l2, CPermutation (l1 ++ l2) (l2 ++ l1).

Instance cperm_perm {A} : Proper (CPermutation ==> (@Permutation A)) id.
Proof.
intros l1 l2 HC.
inversion HC.
apply Permutation_app_comm.
Qed.

Instance cperm_refl {A} : Reflexive (@CPermutation A).
Proof.
intros l.
rewrite <- (app_nil_l l) at 2.
rewrite <- (app_nil_r l) at 1.
eapply cperm.
Qed.

Instance cperm_sym {A} : Symmetric (@CPermutation A).
Proof.
intros l1 l2 HC.
inversion HC.
eapply cperm.
Qed.

Instance cperm_trans {A} : Transitive (@CPermutation A).
Proof.
intros l1 l2 l3 HC1 HC2.
inversion HC1 ; inversion HC2 ; subst.
apply dichot_app in H1.
destruct H1 as [[l2' [Hl1 Hl2]] | [l4' [Hr1 Hr2]]] ; subst.
- rewrite <- app_assoc.
  rewrite app_assoc at 1.
  eapply cperm.
- rewrite app_assoc.
  rewrite <- app_assoc at 1.
  eapply cperm.
Qed.

Instance cperm_equiv {A} : Equivalence (@CPermutation A).
Proof.
split.
- apply cperm_refl.
- apply cperm_sym.
- apply cperm_trans.
Qed.

Lemma cperm_app {A} : forall l1 l2 l3 : list A,
  CPermutation (l1 ++ l2) l3 -> CPermutation (l2 ++ l1) l3.
Proof.
intros l1 l2 l3 HC.
transitivity (l1 ++ l2) ; try assumption.
eapply cperm.
Qed.

Lemma cperm_app_rot {A} : forall (l1 : list A) l2 l3,
   CPermutation (l1 ++ l2 ++ l3) (l2 ++ l3 ++ l1).
Proof.
intros l1 l2 l3.
rewrite (app_assoc l2).
apply cperm.
Qed.

Lemma cperm_last {A} : forall (a : A) l, CPermutation (a :: l) (l ++ a :: nil).
Proof.
intros.
rewrite <- (app_nil_l l).
rewrite app_comm_cons.
apply cperm.
Qed.

Lemma cperm_swap {A} : forall a b : A, CPermutation (a :: b :: nil) (b :: a :: nil).
Proof.
intros.
change (a :: b :: nil) with ((a :: nil) ++ (b :: nil)).
change (b :: a :: nil) with ((b :: nil) ++ (a :: nil)).
apply cperm.
Qed.

Lemma cperm_cons {A} : forall l1 (a : A) l2,
  CPermutation (l1 ++ (a :: nil)) l2 -> CPermutation (a :: l1) l2.
Proof.
intros l1 a l2 HC.
apply (cperm_app l1 (a :: nil)) ; assumption.
Qed.

Lemma cperm_morph_cons {A} : forall P : list A -> Prop,
  (forall a l, P (l ++ a :: nil) -> P (a :: l)) -> Proper (CPermutation ==> iff) P.
Proof with try assumption.
assert (forall P : list A -> Prop,
         (forall a l, P (l ++ a :: nil) -> P (a :: l)) ->
         forall l1 l2, CPermutation l1 l2 -> P l1 -> P l2)
  as Himp.
{
intros P HP l1 l2 HC.
inversion HC ; subst ; clear HC.
revert l0 ; induction l3 using rev_ind ; intros l0 HPl.
- rewrite app_nil_r in HPl...
- rewrite app_assoc in HPl.
  apply HP in HPl.
  rewrite <- app_assoc.
  rewrite <- app_comm_cons.
  rewrite app_nil_l...
  apply IHl3...
}
intros P HP l1 l2 HC.
split ; [ | symmetry in HC ] ; apply Himp...
Qed.

Lemma cperm_nil {A} : forall l : list A, CPermutation nil l -> l = nil.
Proof.
intros.
apply Permutation_nil.
apply cperm_perm.
assumption.
Qed.

Lemma cperm_nil_cons {A} : forall l (a : A), ~ CPermutation nil (a :: l).
Proof.
intros l a HC.
apply cperm_nil in HC.
inversion HC.
Qed.

Lemma cperm_one {A} : forall a b : A, CPermutation (a :: nil) (b :: nil) -> a = b.
Proof.
intros.
apply Permutation_length_1.
apply cperm_perm.
assumption.
Qed.

Lemma cperm_two {A} : forall a1 a2 b1 b2 : A,
  CPermutation (a1 :: a2 :: nil) (b1 :: b2 :: nil) ->
    a1 = b1 /\ a2 = b2 \/ a1 = b2 /\ a2 = b1.
Proof.
intros.
apply Permutation_length_2.
apply cperm_perm.
assumption.
Qed.

Lemma cperm_one_inv {A} : forall l (a : A), CPermutation (a :: nil) l -> l = a :: nil.
Proof.
intros.
apply Permutation_length_1_inv.
apply cperm_perm.
assumption.
Qed.

Lemma cperm_two_inv {A} : forall (a : A) b l,
  CPermutation (a :: b :: nil) l -> l = a :: b :: nil \/ l = b :: a :: nil.
Proof.
intros.
apply Permutation_length_2_inv.
apply cperm_perm.
assumption.
Qed.

Lemma cperm_vs_elt_inv {A} : forall (a : A) l l1 l2,
  CPermutation l (l1 ++ a :: l2) ->
    exists l' l'', l2 ++ l1 = l'' ++ l' /\ l = l' ++ a :: l''.
Proof.
intros a l l1 l2 HC.
inversion HC ; subst.
symmetry in H1.
dichot_elt_app_exec H1 ; subst.
- exists (l0 ++ l1) ; exists l ; split ;
    rewrite <- app_assoc ; reflexivity.
- exists l4 ; exists (l2 ++ l3) ; split ;
    rewrite <- app_assoc ; reflexivity.
Qed.

Lemma cperm_vs_cons_inv {A} : forall (a : A) l l1,
  CPermutation l (a :: l1) -> exists l2 l3, l1 = l3 ++ l2 /\ l = l2 ++ a :: l3.
Proof.
intros.
rewrite <- (app_nil_l (a::_)) in H.
apply cperm_vs_elt_inv in H.
destruct H as (l' & l'' & H1 & H2).
rewrite app_nil_r in H1 ; subst.
exists l' ; exists l'' ; split ; reflexivity.
Qed.

Lemma cperm_app_app_inv {A} : forall (l1 : list A) l2 l3 l4,
  CPermutation (l1 ++ l2) (l3 ++ l4) ->
     (exists l3' l3'' l4' l4'',
        CPermutation l1 (l3' ++ l4')  /\ CPermutation l2 (l3'' ++ l4'')
     /\
        CPermutation l3 (l3' ++ l3'') /\ CPermutation l4 (l4' ++ l4''))
  \/ (exists l l',
        CPermutation l1 (l4 ++ l) /\ CPermutation l3 (l2 ++ l')
          /\ CPermutation l l')
  \/ (exists l l',
        CPermutation l2 (l4 ++ l) /\ CPermutation l3 (l1 ++ l')
          /\ CPermutation l l')
  \/ (exists l l',
        CPermutation l1 (l3 ++ l) /\ CPermutation l4 (l2 ++ l')
          /\ CPermutation l l')
  \/ (exists l l',
        CPermutation l2 (l3 ++ l) /\ CPermutation l4 (l1 ++ l')
          /\ CPermutation l l').
Proof with try assumption ; try reflexivity.
intros l1 l2 l3 l4 HC.
inversion HC as [lx ly Hx Hy].
dichot_app_exec Hx ; dichot_app_exec Hy ; subst.
- right ; left.
  exists (l ++ l0) ; exists (l0 ++ l).
  split ; [ | split ] ; 
    try (rewrite <- ? app_assoc ; apply cperm_app_rot)...
  apply cperm.
- dichot_app_exec Hy0 ; subst.
  + left.
    exists l ; exists l0 ; exists lx ; exists l5.
    split ; [ | split ; [ | split ]] ; try apply cperm...
  + right ; right ; right ; left.
    exists (l1 ++ lx) ; exists (lx ++ l1).
    split ; [ | split ] ; 
      try (rewrite <- ? app_assoc ; apply cperm_app_rot)...
    apply cperm.
- dichot_app_exec Hy1 ; subst.
  + right ; right ; left.
    exists (ly ++ l2) ; exists (l2 ++ ly).
    split ; [ | split ] ; 
      try (rewrite <- ? app_assoc ; apply cperm_app_rot)...
    apply cperm.
  + left.
    exists l ; exists ly ; exists l3 ; exists l0.
    split ; [ | split ; [ | split ]] ; try apply cperm...
- right ; right ; right ; right.
  exists (l5 ++ l0) ; exists (l0 ++ l5).
  split ; [ | split ] ; 
    try (rewrite <- ? app_assoc ; apply cperm_app_rot)...
  apply cperm.
Qed.

(** [rev], [in], [map], [Forall], [Exists], etc. *)
Instance cperm_rev {A} : Proper (CPermutation ==> CPermutation) (@rev A).
Proof.
intro l ; induction l ; intros l' HC.
- apply cperm_nil in HC ; subst ; reflexivity.
- symmetry in HC.
  apply cperm_vs_cons_inv in HC.
  destruct HC as (l1 & l2 & Heq1 & Heq2) ; subst.
  simpl ; rewrite ? rev_app_distr ; simpl.
  rewrite <- app_assoc.
  apply cperm.
Qed.

Instance cperm_in {A} (a : A) : Proper (CPermutation ==> Basics.impl) (In a).
Proof with try eassumption.
intros l l' HC Hin.
eapply Permutation_in...
apply cperm_perm...
Qed.

Instance cperm_map {A B} (f : A -> B) :
   Proper (CPermutation ==> CPermutation) (map f).
Proof.
intros l l' HC.
inversion HC ; subst ; rewrite ? map_app.
apply cperm.
Qed.

Lemma cperm_map_inv {A B} : forall (f : A -> B) l1 l2,
  CPermutation l1 (map f l2) -> exists l3, l1 = map f l3.
Proof.
intros f l1 l2 HC.
inversion HC ; subst.
decomp_map H1 ; subst.
exists (l4 ++ l1).
rewrite map_app.
reflexivity.
Qed.

Instance cperm_Forall {A} (P : A -> Prop) :
  Proper (CPermutation ==> Basics.impl) (Forall P).
Proof with try eassumption.
intros l1 l2 HC HF.
eapply Permutation_Forall...
apply cperm_perm...
Qed.

Instance cperm_Exists {A} (P : A -> Prop) :
  Proper (CPermutation ==> Basics.impl) (Exists P).
Proof with try eassumption.
intros l1 l2 HC HE.
eapply Permutation_Exists...
apply cperm_perm...
Qed.

Lemma cperm_image {A B} :
  forall (f : A -> B) a l l',
    CPermutation (a :: l) (map f l') -> exists a', a = f a'
.
Proof.
intros f a l l' HP.
eapply Permutation_image.
apply cperm_perm ; eassumption.
Qed.


