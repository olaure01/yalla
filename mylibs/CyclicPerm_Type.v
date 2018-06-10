(* CyclicPerm_Type library *)


(** * Cyclic Permutations
Definition and basic properties of cyclic permutations in Type. *)

Require Import CMorphisms.

Require Import List_Type.
Require Import List_Type_more.
Require Import Permutation_Type_more.

(** Definition *)
Inductive CPermutation_Type {A} : list A -> list A -> Type :=
| cperm_Type : forall l1 l2, CPermutation_Type (l1 ++ l2) (l2 ++ l1).

Instance cperm_perm_Type {A} : Proper (CPermutation_Type ==> (@Permutation_Type A)) id.
Proof.
intros l1 l2 HC.
inversion HC.
apply Permutation_Type_app_comm.
Qed.

Instance cperm_Type_refl {A} : Reflexive (@CPermutation_Type A).
Proof.
intros l.
assert (CPermutation_Type (nil ++ l) (l ++ nil))
  as HC by (eapply cperm_Type).
simpl in HC.
rewrite app_nil_r in HC.
assumption.
Qed.

Instance cperm_Type_sym {A} : Symmetric (@CPermutation_Type A).
Proof.
intros l1 l2 HC.
inversion HC.
eapply cperm_Type.
Qed.

Instance cperm_Type_trans {A} : Transitive (@CPermutation_Type A).
Proof.
intros l1 l2 l3 HC1 HC2.
inversion HC1 ; inversion HC2 ; subst.
apply dichot_Type_app in H1.
destruct H1 as [[l2' [Hl1 Hl2]] | [l4' [Hr1 Hr2]]] ; subst.
- rewrite <- app_assoc.
  rewrite app_assoc.
  eapply cperm_Type.
- rewrite <- app_assoc.
  rewrite (app_assoc l6).
  eapply cperm_Type.
Qed.

Instance cperm_Type_equiv {A} : Equivalence (@CPermutation_Type A).
Proof.
split.
- apply cperm_Type_refl.
- apply cperm_Type_sym.
- apply cperm_Type_trans.
Qed.

Lemma cperm_Type_app {A} : forall l1 l2 l3 : list A,
  CPermutation_Type (l1 ++ l2) l3 -> CPermutation_Type (l2 ++ l1) l3.
Proof.
intros l1 l2 l3 HC.
apply (cperm_Type_trans _ (l1 ++ l2)) ; try assumption.
eapply cperm_Type.
Qed.

Lemma cperm_Type_app_rot {A} : forall (l1 : list A) l2 l3,
   CPermutation_Type (l1 ++ l2 ++ l3) (l2 ++ l3 ++ l1).
Proof.
intros l1 l2 l3.
rewrite (app_assoc l2).
apply cperm_Type.
Qed.

Lemma cperm_Type_last {A} : forall (a : A) l,
  CPermutation_Type (a :: l) (l ++ a :: nil).
Proof.
intros.
rewrite <- (app_nil_l l).
rewrite app_comm_cons.
apply cperm_Type.
Qed.

Lemma cperm_Type_swap {A} : forall a b : A,
  CPermutation_Type (a :: b :: nil) (b :: a :: nil).
Proof.
intros.
change (a :: b :: nil) with ((a :: nil) ++ (b :: nil)).
change (b :: a :: nil) with ((b :: nil) ++ (a :: nil)).
apply cperm_Type.
Qed.

Lemma cperm_Type_cons {A} : forall l1 (a : A) l2,
  CPermutation_Type (l1 ++ (a :: nil)) l2 -> CPermutation_Type (a :: l1) l2.
Proof.
intros l1 a l2 HC.
apply (cperm_Type_app l1 (a :: nil)) ; assumption.
Qed.

Lemma cperm_Type_morph_cons {A} : forall P : list A -> Prop,
  (forall a l, P (l ++ a :: nil) -> P (a :: l)) ->
  Proper (CPermutation_Type ==> Basics.impl) P.
Proof with try eassumption.
assert (forall P : list A -> Prop,
         (forall a l, P (l ++ a :: nil) -> P (a :: l)) ->
         forall l1 l2, CPermutation_Type l1 l2 -> P l1 -> P l2)
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
intros P HP l1 l2 HC H.
eapply Himp...
Qed.

Lemma cperm_Type_nil {A} : forall l : list A,
  CPermutation_Type nil l -> l = nil.
Proof.
intros.
apply Permutation_Type_nil.
apply cperm_perm_Type.
assumption.
Qed.

Lemma cperm_Type_nil_cons {A} : forall l (a : A),
  CPermutation_Type nil (a :: l) -> False.
Proof.
intros l a HC.
apply cperm_Type_nil in HC.
inversion HC.
Qed.

Lemma cperm_Type_one {A} : forall a b : A,
  CPermutation_Type (a :: nil) (b :: nil) -> a = b.
Proof.
intros.
apply Permutation_Type_length_1.
apply cperm_perm_Type.
assumption.
Qed.

Lemma cperm_Type_two {A} : forall a1 a2 b1 b2 : A,
  CPermutation_Type (a1 :: a2 :: nil) (b1 :: b2 :: nil) ->
    { a1 = b1 /\ a2 = b2 } +  { a1 = b2 /\ a2 = b1 }.
Proof.
intros.
apply Permutation_Type_length_2.
apply cperm_perm_Type.
assumption.
Qed.

Lemma cperm_Type_one_inv {A} : forall l (a : A),
  CPermutation_Type (a :: nil) l -> l = a :: nil.
Proof.
intros.
apply Permutation_Type_length_1_inv.
apply cperm_perm_Type.
assumption.
Qed.

Lemma cperm_Type_two_inv {A} : forall (a : A) b l,
  CPermutation_Type (a :: b :: nil) l ->
  { l = a :: b :: nil } + { l = b :: a :: nil }.
Proof.
intros.
apply Permutation_Type_length_2_inv.
apply cperm_perm_Type.
assumption.
Qed.

Lemma cperm_Type_vs_elt_inv {A} : forall (a : A) l l1 l2,
  CPermutation_Type l (l1 ++ a :: l2) ->
    { pl | l2 ++ l1 = snd pl ++ fst pl & l = fst pl ++ a :: snd pl }.
Proof.
intros a l l1 l2 HC.
inversion HC ; subst.
symmetry in H1.
dichot_Type_elt_app_exec H1 ; subst.
- exists (l0 ++ l1, l) ; simpl ;
    rewrite <- app_assoc ; reflexivity.
- exists (l4, l2 ++ l3) ; simpl ;
    rewrite <- app_assoc ; reflexivity.
Qed.

Lemma cperm_Type_vs_cons_inv {A} : forall (a : A) l l1,
  CPermutation_Type l (a :: l1) ->
    { pl | l1 = snd pl ++ fst pl & l = fst pl ++ a :: snd pl }.
Proof.
intros a l l1 HC.
rewrite <- (app_nil_l (a::_)) in HC.
apply cperm_Type_vs_elt_inv in HC.
destruct HC as [(l' & l'') H1 H2].
rewrite app_nil_r in H1 ; subst.
exists (l', l'') ; split ; reflexivity.
Qed.

Lemma cperm_Type_app_app_inv {A} : forall l1 l2 l3 l4 : list A,
  CPermutation_Type (l1 ++ l2) (l3 ++ l4) ->
     { ql : _ & prod (prod 
        (CPermutation_Type l1 (fst (fst ql) ++ fst (snd ql)))
        (CPermutation_Type l2 (snd (fst ql) ++ snd (snd ql))))
        (prod
        (CPermutation_Type l3 (fst (fst ql) ++ snd (fst ql)))
        (CPermutation_Type l4 (fst (snd ql) ++ snd (snd ql)))) }
   + { pl : _ & prod (prod
        (CPermutation_Type l1 (l4 ++ fst pl))
        (CPermutation_Type l3 (l2 ++ snd pl)))
        (CPermutation_Type (fst pl) (snd pl)) }
   + { pl : _ & prod (prod
        (CPermutation_Type l2 (l4 ++ fst pl))
        (CPermutation_Type l3 (l1 ++ snd pl)))
        (CPermutation_Type (fst pl) (snd pl)) }
   + { pl : _ & prod (prod
        (CPermutation_Type l1 (l3 ++ fst pl))
        (CPermutation_Type l4 (l2 ++ snd pl)))
        (CPermutation_Type (fst pl) (snd pl)) }
   + { pl : _ & prod (prod
        (CPermutation_Type l2 (l3 ++ fst pl))
        (CPermutation_Type l4 (l1 ++ snd pl)))
        (CPermutation_Type (fst pl) (snd pl)) }.
Proof with try assumption.
intros l1 l2 l3 l4 HC.
inversion HC as [lx ly Hx Hy].
dichot_Type_app_exec Hx ; dichot_Type_app_exec Hy ; subst.
- left ; left ; left ; right.
  exists (l ++ l0, l0 ++ l).
  simpl ; split ; [ split | ] ; 
    try (rewrite <- ? app_assoc ; apply cperm_Type_app_rot).
  apply cperm_Type.
- dichot_Type_app_exec Hy0 ; subst.
  + left ; left ; left ; left.
    exists (l, l0, (lx, l5)).
    simpl ; split ; [ split | split ] ; try apply cperm_Type...
    * apply cperm_Type_refl.
    * apply cperm_Type_refl.
  + left ; right.
    exists (l1 ++ lx , lx ++ l1).
    split ; [ split | ] ; 
      try (rewrite <- ? app_assoc ; apply cperm_Type_app_rot)...
    apply cperm_Type.
- dichot_Type_app_exec Hy1 ; subst.
  + left ; left ; right.
    exists (ly ++ l2, l2 ++ ly).
    split ; [ split | ] ; 
      try (rewrite <- ? app_assoc ; apply cperm_Type_app_rot)...
    apply cperm_Type.
  + left ; left ; left ; left.
    exists (l, ly, (l3, l0)).
    simpl ; split ; [ split | split ] ; try apply cperm_Type...
    * apply cperm_Type_refl.
    * apply cperm_Type_refl.
- right.
  exists (l5 ++ l0, l0 ++ l5).
  split ; [ split | ] ; 
    try (rewrite <- ? app_assoc ; apply cperm_Type_app_rot)...
  apply cperm_Type.
Qed.

(** [rev], [in], [map], [Forall], [Exists], etc. *)
Instance cperm_Type_rev {A} : Proper (CPermutation_Type ==> CPermutation_Type) (@rev A).
Proof.
intro l ; induction l ; intros l' HC.
- apply cperm_Type_nil in HC ; subst ; apply cperm_Type_refl.
- apply cperm_Type_sym in HC.
  apply cperm_Type_vs_cons_inv in HC.
  destruct HC as [(l1 & l2) Heq1 Heq2] ; subst.
  simpl ; rewrite ? rev_app_distr ; simpl.
  rewrite <- app_assoc.
  apply cperm_Type.
Qed.

Instance cperm_Type_in {A} (a : A) : Proper (CPermutation_Type ==> Basics.impl) (In a).
Proof with try eassumption.
intros l l' HC Hin.
eapply Permutation_Type_in...
apply cperm_perm_Type...
Qed.

Instance cperm_Type_map {A B} (f : A -> B) :
   Proper (CPermutation_Type ==> CPermutation_Type) (map f).
Proof.
intros l l' HC.
inversion HC ; subst ; rewrite ? map_app.
apply cperm_Type.
Qed.

Lemma cperm_Type_map_inv {A B} : forall(f : A -> B) l1 l2,
  CPermutation_Type l1 (map f l2) ->
    { l : _ & l1 = map f l & (CPermutation_Type l2 l) }.
Proof with try assumption.
induction l1 ; intros l2 HP.
- exists nil ; try reflexivity.
  simpl ; destruct l2...
  + apply cperm_Type_refl.
  + apply cperm_Type_nil in HP.
    inversion HP.
- apply cperm_Type_sym in HP.
  assert (Heq := HP).
  apply cperm_Type_vs_cons_inv in Heq.
  destruct Heq as [(l3 & l4) Heq1 Heq2].
  simpl in Heq1 ; simpl in Heq2 ; symmetry in Heq2.
  decomp_map_Type Heq2 ; subst ; simpl.
  exists (x :: l6 ++ l0).
  + simpl ; rewrite ? map_app ; reflexivity.
  + constructor.
Qed.

Instance cperm_Type_Forall {A} (P : A -> Prop) :
  Proper (CPermutation_Type ==> Basics.impl) (Forall P).
Proof with try eassumption.
intros l1 l2 HC HF.
eapply Permutation_Type_Forall...
apply cperm_perm_Type...
Qed.

Instance cperm_Type_Exists {A} (P : A -> Prop) :
  Proper (CPermutation_Type ==> Basics.impl) (Exists P).
Proof with try eassumption.
intros l1 l2 HC HE.
eapply Permutation_Type_Exists...
apply cperm_perm_Type...
Qed.

Instance cperm_Type_Forall_Type {A} (P : A -> Type) :
  Proper (CPermutation_Type ==> Basics.arrow) (Forall_Type P).
Proof with try eassumption.
intros l1 l2 HC HF.
eapply Permutation_Type_Forall_Type...
apply cperm_perm_Type...
Qed.

Instance cperm_Type_Exists_Type {A} (P : A -> Type) :
  Proper (CPermutation_Type ==> Basics.arrow) (Exists_Type P).
Proof with try eassumption.
intros l1 l2 HC HE.
eapply Permutation_Type_Exists_Type...
apply cperm_perm_Type...
Qed.

Lemma cperm_Type_Forall2 {A B} (P : A -> B -> Type) :
  forall l1 l1' l2, CPermutation_Type l1 l1' -> Forall2_Type P l1 l2 ->
    { l2' : _ & CPermutation_Type l2 l2' & Forall2_Type P l1' l2' }.
Proof.
intros l1 l1' l2 HP.
revert l2 ; induction HP ; intros l2' HF ; inversion HF ; subst.
- exists nil ; auto.
  + reflexivity.
  + symmetry in H0 ; apply app_eq_nil in H0 as [Heq1 Heq2] ; subst.
    constructor.
- destruct l1 ; inversion H0 ; subst.
  + rewrite app_nil_l in H0 ; subst.
    exists (y :: l').
    * reflexivity.
    * rewrite app_nil_l in HF ; simpl ; rewrite app_nil_r ; assumption.
  + apply Forall2_Type_app_inv_l in X0 as ([(la & lb) H1 H2] & Heq).
    simpl in Heq ; rewrite Heq.
    exists (lb ++ y :: la).
    * rewrite app_comm_cons ; constructor.
    * apply Forall2_Type_app ; auto.
      constructor ; auto.
Qed.

Lemma cperm_Type_image {A B} : forall (f : A -> B) a l l',
  CPermutation_Type (a :: l) (map f l') -> { a' | a = f a' }.
Proof.
intros f a l l' HP.
eapply Permutation_Type_image.
apply cperm_perm_Type ; eassumption.
Qed.

