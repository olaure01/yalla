(* Permutation_Type_more Library *)

(** * Add-ons for Permutation_Type library
Usefull properties apparently missing in the Permutation_Type library. *)

Require Import Plus.
Require Import CMorphisms.

Require Import Injective.
Require Import List_more.
Require Import Permutation_more.
Require Export Permutation_Type.
Require Import List_Type.
Require Import List_Type_more.


Instance Permutation_Type_refl' {A} : Proper (Logic.eq ==> @Permutation_Type A) id.
Proof.
intros x y Heq.
rewrite Heq.
reflexivity.
Qed.

Lemma Permutation_Type_morph_transp {A} : forall P : list A -> Prop,
  (forall a b l1 l2, P (l1 ++ a :: b :: l2) -> P (l1 ++ b :: a :: l2)) ->
    Proper ((@Permutation_Type A) ==> iff) P.
Proof with try eassumption.
assert (forall P : list A -> Prop,
         (forall a b l1 l2, P (l1 ++ a :: b :: l2) ->
                            P (l1 ++ b :: a :: l2)) ->
         forall l1 l2, Permutation_Type l1 l2 ->
         forall l0, P (l0 ++ l1) -> P (l0 ++ l2))
  as Himp.
{ intros P HP l1 l2 H.
  induction H ; intros...
  - rewrite <- (app_nil_l l').
    rewrite app_comm_cons.
    rewrite app_assoc.
    apply IHPermutation_Type.
    list_simpl...
  - apply HP...
  - apply IHPermutation_Type2.
    apply IHPermutation_Type1... }
intros P HP l1 l2 H.
split ; intro H'.
- rewrite <- (app_nil_l l2).
  rewrite <- (app_nil_l l1) in H'.
  eapply Himp...
- symmetry in H.
  rewrite <- (app_nil_l l1).
  rewrite <- (app_nil_l l2) in H'.
  eapply Himp...
Qed.

Lemma Permutation_Type_elt {A} : forall (a : A) l1 l2 l1' l2',
  Permutation_Type (l1 ++ l2) (l1' ++ l2') ->
    Permutation_Type (l1 ++ a :: l2) (l1' ++ a :: l2').
Proof.
intros a l1 l2 l1' l2' HP.
eapply Permutation_Type_trans.
- apply Permutation_Type_sym.
  apply Permutation_Type_middle.
- apply Permutation_Type_cons_app.
  assumption.
Qed.

Lemma Permutation_Type_vs_elt_inv {A} : forall (a : A) l l1 l2,
  Permutation_Type l (l1 ++ a :: l2) -> { pl | l = fst pl ++ a :: snd pl}.
Proof with try assumption ; try reflexivity.
intros a l l1 l2 HP.
remember (l1 ++ a :: l2) as l0.
revert l1 l2 Heql0 ; induction HP ; intros l1 l2 Heql.
- destruct l1 ; inversion Heql.
- destruct l1 ; inversion Heql.
  + exists (@nil A, l)...
  + apply IHHP in H1.
    destruct H1 as (pl & Heq) ; subst.
    exists (a0 :: fst pl, snd pl)...
- destruct l1 ; inversion Heql ; subst.
  + exists (y :: nil, l)...
  + destruct l1 ; inversion H1 ; subst.
    * exists (@nil A, a0 :: l2)...
    * exists (a1 :: a0 :: l1, l2)...
- destruct (IHHP2 _ _ Heql) as (pl & Heq) ; subst.
  assert (Heq := IHHP1 (fst pl) (snd pl) eq_refl).
  destruct Heq as (pl' & Heq) ; subst.
  exists pl'...
Qed.

Lemma Permutation_Type_vs_cons_inv {A} : forall (a : A) l l1,
  Permutation_Type l (a :: l1) -> {pl | l = fst pl ++ a :: snd pl}.
Proof.
intros a l l1 HP.
rewrite <- (app_nil_l (a :: l1)) in HP.
eapply Permutation_Type_vs_elt_inv ; eassumption.
Qed.

Lemma Permutation_Type_vs_2elts {A} : forall (s : A) t l1 l2 l3,
  Permutation_Type (l1 ++ s :: l2 ++ t :: l3) (s :: t :: l1 ++ l2 ++ l3).
Proof.
intros.
apply Permutation_Type_sym.
apply Permutation_Type_cons_app.
rewrite 2 app_assoc.
apply Permutation_Type_cons_app.
apply Permutation_Type_refl.
Qed.

Lemma Permutation_Type_vs_2elts_inv : forall A D (s : A) t G,
  Permutation_Type D (s :: t :: G) -> { tG |
    D = fst tG ++ s :: fst (snd tG) ++ t :: snd (snd tG)
 \/ D = fst tG ++ t :: fst (snd tG) ++ s :: snd (snd tG)}.
Proof.
intros A D s t G HP.
assert (HP' := HP).
apply Permutation_Type_vs_cons_inv in HP'.
destruct HP' as (pl & HP') ; subst.
apply Permutation_Type_sym in HP.
apply Permutation_Type_cons_app_inv in HP.
apply Permutation_Type_sym in HP.
apply Permutation_Type_vs_cons_inv in HP.
destruct HP as (pl' & HP).
symmetry in HP.
dichot_Type_elt_app_exec HP ; subst ;
rewrite <- ? app_assoc ;
rewrite <- ? app_comm_cons.
- exists (fst pl', (l, snd pl)).
  right.
  rewrite <- HP0.
  simpl.
  rewrite <- app_assoc.
  rewrite <- app_comm_cons.
  reflexivity.
- exists (fst pl, (l0, snd pl')).
  left.
  simpl.
  rewrite HP1.
  reflexivity.
Qed.

Lemma Permutation_Type_app_rot {A} : forall (l1 : list A) l2 l3,
  Permutation_Type (l1 ++ l2 ++ l3) (l2 ++ l3 ++ l1).
Proof.
intros l1 l2 l3.
rewrite (app_assoc l2).
apply Permutation_Type_app_comm.
Qed.

Lemma Permutation_Type_app_swap_app {A} : forall (l1 : list A) l2 l3,
  Permutation_Type (l1 ++ l2 ++ l3) (l2 ++ l1 ++ l3).
Proof.
intros.
repeat rewrite app_assoc.
apply Permutation_Type_app_tail.
apply Permutation_Type_app_comm.
Qed.

Lemma Permutation_Type_app_middle {A} : forall (l : list A) l1 l2 l3 l4,
  Permutation_Type (l1 ++ l2) (l3 ++ l4) ->
    Permutation_Type (l1 ++ l ++ l2) (l3 ++ l ++ l4).
Proof.
intros.
eapply Permutation_Type_trans.
apply Permutation_Type_app_swap_app.
eapply Permutation_Type_trans.
apply Permutation_Type_app_head.
- eassumption.
- apply Permutation_Type_app_swap_app.
Qed.

Lemma Permutation_Type_app_middle_inv {A} : forall (l : list A) l1 l2 l3 l4,
  Permutation_Type (l1 ++ l ++ l2) (l3 ++ l ++ l4) ->
    Permutation_Type (l1 ++ l2) (l3 ++ l4).
Proof.
intros.
apply (Permutation_Type_app_inv_l l).
eapply Permutation_Type_trans.
apply Permutation_Type_app_swap_app.
eapply Permutation_Type_trans.
- eassumption.
- apply Permutation_Type_app_swap_app.
Qed.

Lemma Permutation_Type_app_app_inv {A} : forall (l1 l2 l3 l4 : list A),
  Permutation_Type (l1 ++ l2) (l3 ++ l4) -> { ql : _ & prod (prod
    (Permutation_Type l1 (fst (fst ql) ++ fst (snd ql)))
    (Permutation_Type l2 (snd (fst ql) ++ snd (snd ql)))) (prod
    (Permutation_Type l3 (fst (fst ql) ++ snd (fst ql)))
    (Permutation_Type l4 (fst (snd ql) ++ snd (snd ql)))) }.
Proof with try assumption.
induction l1 ; intros l2 l3 l4 HP.
- exists (@nil A, l3, (@nil A, l4)).
  split ; try split ; try split ; try apply Permutation_Type_refl...
- assert (Heq := HP).
  apply Permutation_Type_sym in Heq.
  apply Permutation_Type_vs_cons_inv in Heq.
  destruct Heq as [pl Heq].
  dichot_Type_elt_app_exec Heq ; subst.
  + rewrite <- ?app_comm_cons in HP.
    rewrite <- app_assoc in HP.
    rewrite <- app_comm_cons in HP.
    apply Permutation_Type_cons_app_inv in HP.
    rewrite app_assoc in HP.
    apply IHl1 in HP.
    destruct HP as (ql & (H1 & H2) & H3 & H4).
    exists (a :: fst (fst ql), snd (fst ql), (fst (snd ql), snd (snd ql))).
    simpl ; split ; try split ; try split...
    * apply Permutation_Type_skip...
    * apply Permutation_Type_sym.
      apply Permutation_Type_cons_app.
      apply Permutation_Type_sym...
  + rewrite <- ?app_comm_cons in HP.
    rewrite app_assoc in HP.
    apply Permutation_Type_cons_app_inv in HP.
    rewrite <- app_assoc in HP.
    apply IHl1 in HP.
    destruct HP as (ql & (H1 & H2) & H3 & H4).
    exists (fst (fst ql), snd (fst ql), (a :: fst (snd ql), snd (snd ql))).
    simpl ; split ; try split ; try split...
    * apply Permutation_Type_cons_app...
    * apply Permutation_Type_sym.
      apply Permutation_Type_cons_app.
      apply Permutation_Type_sym...
Qed.

Instance Permutation_Type_Forall {A} (P : A -> Prop) :
  Proper ((@Permutation_Type A) ==> Basics.impl) (Forall P).
Proof.
intros l1 l2 H.
apply Permutation_Type_Permutation in H.
rewrite H ; reflexivity.
Qed.

Instance Permutation_Type_Exists {A} (P : A -> Prop) :
  Proper ((@Permutation_Type A) ==> Basics.impl) (Exists P).
Proof.
intros l1 l2 H.
apply Permutation_Type_Permutation in H.
rewrite H ; reflexivity.
Qed.

Instance Permutation_Type_Forall_Type {A} (P : A -> Type) :
  Proper ((@Permutation_Type A) ==> Basics.arrow) (Forall_Type P).
Proof with try assumption.
intros l1 l2 H.
induction H ; intro H1...
- inversion H1 ; subst.
  apply IHPermutation_Type in X0.
  constructor...
- inversion H1.
  inversion X0.
  constructor...
  constructor...
- apply IHPermutation_Type2.
  apply IHPermutation_Type1...
Qed.

Instance Permutation_Type_Exists_Type {A} (P : A -> Type) :
  Proper ((@Permutation_Type A) ==> Basics.arrow) (Exists_Type P).
Proof with try assumption.
intros l1 l2 H.
induction H ; intro H1...
- inversion H1 ; subst.
  + apply Exists_Type_cons_hd...
  + apply IHPermutation_Type in X.
    apply Exists_Type_cons_tl...
- inversion H1 ; [ | inversion X ] ; subst.
  + apply Exists_Type_cons_tl.
    apply Exists_Type_cons_hd...
  + apply Exists_Type_cons_hd...
  + apply Exists_Type_cons_tl.
    apply Exists_Type_cons_tl...
- apply IHPermutation_Type2.
  apply IHPermutation_Type1...
Qed.

Lemma Permutation_Type_Forall2 {A B} (P : A -> B -> Type) :
  forall l1 l1' l2, Permutation_Type l1 l1' -> Forall2_Type P l1 l2 ->
    { l2' : _ & Permutation_Type l2 l2' & Forall2_Type P l1' l2' }.
Proof.
intros l1 l1' l2 HP.
revert l2 ; induction HP ; intros l2 HF ; inversion HF ; subst.
- exists nil ; auto.
- apply IHHP in X0 as [ l2' HP2 HF2 ].
  exists (y :: l2') ; auto.
  constructor ; assumption.
- inversion X0 ; subst.
  exists (y1 :: y0 :: l'0) ; auto.
  + constructor.
  + constructor ; [ | constructor ] ; assumption.
- apply Permutation_Type_nil in HP1 ; subst.
  apply Permutation_Type_nil in HP2 ; subst.
  exists nil ; auto.
- apply IHHP1 in HF as [ l2' HP2' HF2' ].
  apply IHHP2 in HF2' as [ l2'' HP2'' HF2'' ].
  exists l2'' ; auto.
  transitivity l2' ; assumption.
Qed.

Lemma Permutation_Type_map_inv {A B} : forall(f : A -> B) l1 l2,
  Permutation_Type l1 (map f l2) -> { l : _ & l1 = map f l & (Permutation_Type l2 l) }.
(*
Lemma Permutation_Type_map_inv {A B} : forall(f : A -> B) l1 l2,
  Permutation_Type l1 (map f l2) -> { pl : { l : _ & Permutation_Type l2 l} | l1 = map f (projT1 pl) }.
*)
Proof with try assumption.
induction l1 ; intros l2 HP.
- apply Permutation_Type_nil in HP.
  destruct l2 ; inversion HP.
  exists nil ; reflexivity.
- apply Permutation_Type_sym in HP.
  assert (Heq := HP).
  apply Permutation_Type_vs_cons_inv in Heq.
  destruct Heq as (pl & Heq).
  symmetry in Heq.
  decomp_map_Type Heq ; subst.
  apply Permutation_Type_sym in HP.
  rewrite map_app in HP.
  apply Permutation_Type_cons_app_inv in HP.
  specialize IHl1 with (l0 ++ l4).
  rewrite map_app in IHl1.
  apply IHl1 in HP.
  destruct HP as [l' Heq HP'] ; subst.
  exists (x :: l') ; simpl ; try reflexivity.
  apply Permutation_Type_sym.
  apply Permutation_Type_cons_app.
  apply Permutation_Type_sym...
Qed.

Lemma Permutation_Type_map_inv_inj {A B} : forall f : A -> B, injective f ->
  forall l1 l2, Permutation_Type (map f l1) (map f l2) -> Permutation_Type l1 l2.
Proof with try assumption.
intros f Hi l1 ; induction l1 ; intros l2 HP.
- apply Permutation_Type_nil in HP.
  destruct l2 ; inversion HP.
  apply Permutation_Type_refl.
- assert (Heq := HP).
  apply Permutation_Type_sym in Heq.
  apply Permutation_Type_vs_cons_inv in Heq.
  destruct Heq as ((l3 & l4) & Heq).
  symmetry in Heq.
  decomp_map_Type Heq ; subst.
  rewrite map_app in HP.
  simpl in HP.
  rewrite Heq3 in HP.
  apply Permutation_Type_cons_app_inv in HP.
  specialize IHl1 with (l0 ++ l6).
  rewrite map_app in IHl1.
  apply IHl1 in HP.
  apply Hi in Heq3 ; subst.
  apply Permutation_Type_cons_app...
Qed.

Lemma Permutation_Type_image {A B} : forall (f : A -> B) a l l',
  Permutation_Type (a :: l) (map f l') -> { a' | a = f a' }.
Proof.
intros f a l l' HP.
apply Permutation_Type_map_inv in HP.
destruct HP as [l'' Heq _].
destruct l'' ; inversion Heq.
eexists ; reflexivity.
Qed.

Lemma Permutation_Type_elt_map_inv {A B} : forall (f : A -> B) a l1 l2 l3 l4,
  Permutation_Type (l1 ++ a :: l2) (l3 ++ map f l4) ->
  (forall b, a <> f b) -> { pl | l3 = fst pl ++ a :: snd pl }.
Proof.
intros a l1 l2 l3 l4 f HP Hf.
apply Permutation_Type_sym in HP.
apply Permutation_Type_vs_elt_inv in HP.
destruct HP as ((l' & l'') & Heq).
dichot_Type_elt_app_exec Heq.
- subst.
  exists (l', l) ; reflexivity.
- exfalso.
  decomp_map_Type Heq1.
  apply Hf in Heq1.
  inversion Heq1.
Qed.

Instance Permutation_Type_flat_map {A B} f :
  Proper ((@Permutation_Type A) ==> (@Permutation_Type B)) (flat_map f).
Proof with try eassumption.
intros l1.
induction l1 ; intros l2 HP.
- destruct l2...
  + apply Permutation_Type_refl.
  + apply Permutation_Type_nil in HP.
    inversion HP.
- apply Permutation_Type_sym in HP.
  assert (Heq := HP).
  apply Permutation_Type_vs_cons_inv in Heq.
  destruct Heq as ((l' & l'') & Heq) ; subst.
  destruct l' ; apply Permutation_Type_sym in HP.
  + simpl in HP ; simpl ; apply Permutation_Type_app_head.
    apply IHl1.
    eapply Permutation_Type_cons_inv...
  + apply Permutation_Type_cons_app_inv in HP.
    apply IHl1 in HP.
    rewrite flat_map_app in HP ; simpl in HP.
    rewrite flat_map_app ; simpl.
    apply (Permutation_Type_app_head (f a)) in HP.
    apply (Permutation_Type_trans HP).
    rewrite ? app_assoc.
    apply Permutation_Type_app_tail.
    rewrite <- ? app_assoc.
    apply Permutation_Type_app_rot.
Qed.

Instance list_sum_perm_Type : Proper (@Permutation_Type nat ==> eq) list_sum.
Proof with try reflexivity.
intros l1 ; induction l1 ; intros l2 HP.
- apply Permutation_Type_nil in HP ; subst...
- assert (HP' := HP).
  apply Permutation_Type_sym in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as ((l3 & l4) & Heq) ; subst.
  apply Permutation_Type_cons_app_inv in HP.
  simpl ; erewrite IHl1 ; [ | apply HP ].
  rewrite 2 list_sum_app.
  simpl.
  rewrite 2 (plus_comm a).
  rewrite plus_assoc...
Qed.

