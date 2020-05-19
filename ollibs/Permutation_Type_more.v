(** Add-ons for Permutation_Type library
Usefull properties apparently missing in the Permutation_Type library. *)

From Coq Require Import PeanoNat Permutation CMorphisms.
From OLlibs Require Import List_more funtheory.
From OLlibs Require Export Permutation_Type.

Set Implicit Arguments.


(** * Additional Properties *)

Instance Permutation_Type_refl' A : Proper (Logic.eq ==> @Permutation_Type A) id.
Proof. now intros x y ->. Qed.

Lemma Permutation_Type_morph_transp A : forall P : list A -> Type,
  (forall a b l1 l2, P (l1 ++ a :: b :: l2) -> P (l1 ++ b :: a :: l2)) ->
    Proper ((@Permutation_Type A) ==> arrow) P.
Proof.
assert (forall P : list A -> Type,
         (forall a b l1 l2, P (l1 ++ a :: b :: l2) ->
                            P (l1 ++ b :: a :: l2)) ->
         forall l1 l2, Permutation_Type l1 l2 ->
         forall l0, P (l0 ++ l1) -> P (l0 ++ l2))
  as Himp.
{ intros P HP l1 l2 H.
  induction H; intros; auto.
  rewrite <- (app_nil_l l'), app_comm_cons, app_assoc.
  now apply IHPermutation_Type; list_simpl. }
intros P HP l1 l2 H H'.
rewrite <- (app_nil_l l2); rewrite <- (app_nil_l l1) in H'.
now apply Himp with l1.
Qed.

Lemma Permutation_Type_elt A : forall (a : A) l1 l2 l1' l2',
  Permutation_Type (l1 ++ l2) (l1' ++ l2') ->
    Permutation_Type (l1 ++ a :: l2) (l1' ++ a :: l2').
Proof.
intros a l1 l2 l1' l2' HP.
apply Permutation_Type_trans with (a :: l1 ++ l2).
- apply Permutation_Type_sym, Permutation_Type_middle.
- now apply Permutation_Type_cons_app.
Qed.

Lemma Permutation_Type_vs_elt_inv A : forall (a : A) l l1 l2,
  Permutation_Type l (l1 ++ a :: l2) -> {'(l1', l2') | l = l1' ++ a :: l2' }.
Proof.
intros a l l1 l2 HP.
remember (l1 ++ a :: l2) as l0; revert l1 l2 Heql0; induction HP; intros l1 l2 Heql;
  destruct l1; inversion Heql; subst.
- now exists (@nil A, l).
- destruct (IHHP l1 l2 eq_refl) as ((l1', l2') & ->).
  now exists (a0 :: l1', l2').
- now exists (y :: nil, l).
- destruct l1; inversion H1; subst.
  + now exists (@nil A, a0 :: l2).
  + now exists (a1 :: a0 :: l1, l2).
- destruct (IHHP2 nil l2 eq_refl) as ((l1', l2') & ->).
  destruct (IHHP1 l1' l2' eq_refl) as ((l1'', l2'') & ->).
  now exists (l1'', l2'').
- destruct (IHHP2 (a0 :: l1) l2 eq_refl) as ((l1', l2') & ->).
  destruct (IHHP1 l1' l2' eq_refl) as ((l1'', l2'') & ->).
  now exists (l1'', l2'').
Qed.

Lemma Permutation_Type_vs_cons_inv A : forall (a : A) l l1,
  Permutation_Type l (a :: l1) -> {'(l1', l2') | l = l1' ++ a :: l2' }.
Proof.
intros a l l1 HP.
rewrite <- (app_nil_l (a :: l1)) in HP.
eapply Permutation_Type_vs_elt_inv; eassumption.
Qed.

Lemma Permutation_Type_vs_2elts A : forall (s : A) t l1 l2 l3,
  Permutation_Type (l1 ++ s :: l2 ++ t :: l3) (s :: t :: l1 ++ l2 ++ l3).
Proof.
intros.
apply Permutation_Type_sym, Permutation_Type_cons_app.
rewrite 2 app_assoc.
apply Permutation_Type_cons_app, Permutation_Type_refl.
Qed.

Lemma Permutation_Type_vs_2elts_inv : forall A D (s : A) t G,
  Permutation_Type D (s :: t :: G) -> {'(D1, D2, D3) |
    D = D1 ++ s :: D2 ++ t :: D3
 \/ D = D1 ++ t :: D2 ++ s :: D3 }.
Proof.
intros A D s t G HP.
assert (HP' := HP).
apply Permutation_Type_vs_cons_inv in HP'.
destruct HP' as ((l1', l2') & HP') ; subst.
apply Permutation_Type_sym in HP.
apply Permutation_Type_cons_app_inv in HP.
apply Permutation_Type_sym in HP.
apply Permutation_Type_vs_cons_inv in HP.
destruct HP as ((l1'', l2'') & HP); symmetry in HP.
dichot_elt_app_inf_exec HP; subst ; rewrite <- ? app_assoc, <- ? app_comm_cons.
- now exists (l1'', l, l2'); right.
- now exists (l1', l0, l2''); left.
Qed.

Lemma Permutation_Type_app_rot A : forall (l1 : list A) l2 l3,
  Permutation_Type (l1 ++ l2 ++ l3) (l2 ++ l3 ++ l1).
Proof.
intros l1 l2 l3.
rewrite (app_assoc l2).
apply Permutation_Type_app_comm.
Qed.

Lemma Permutation_Type_app_swap_app A : forall (l1 : list A) l2 l3,
  Permutation_Type (l1 ++ l2 ++ l3) (l2 ++ l1 ++ l3).
Proof.
intros; rewrite ? app_assoc.
apply Permutation_Type_app_tail, Permutation_Type_app_comm.
Qed.

Lemma Permutation_Type_app_middle A : forall (l : list A) l1 l2 l3 l4,
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

Lemma Permutation_Type_app_middle_inv A : forall (l : list A) l1 l2 l3 l4,
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

Lemma Permutation_Type_app_app_inv A : forall (l1 l2 l3 l4 : list A),
  Permutation_Type (l1 ++ l2) (l3 ++ l4) -> {'(l1', l2', l3', l4') & prod (prod
    (Permutation_Type l1 (l1' ++ l3'))
    (Permutation_Type l2 (l2' ++ l4'))) (prod
    (Permutation_Type l3 (l1' ++ l2'))
    (Permutation_Type l4 (l3' ++ l4'))) }.
Proof.
induction l1 ; intros l2 l3 l4 HP.
- now exists (@nil A, l3, @nil A, l4); repeat split; try apply Permutation_Type_refl.
- assert (Heq := HP).
  apply Permutation_Type_sym, Permutation_Type_vs_cons_inv in Heq.
  destruct Heq as [(l1', l2') Heq].
  dichot_elt_app_inf_exec Heq; subst.
  + rewrite <- ?app_comm_cons, <- app_assoc, <- app_comm_cons in HP.
    apply Permutation_Type_cons_app_inv in HP.
    rewrite app_assoc in HP.
    apply IHl1 in HP.
    destruct HP as [[[[l1'' l2''] l3''] l4''] [[H1 H2] [H3 H4]]].
    exists (a :: l1'', l2'', l3'', l4''); simpl; repeat split; auto.
    now apply Permutation_Type_sym, Permutation_Type_cons_app, Permutation_Type_sym.
  + rewrite <- ?app_comm_cons, app_assoc in HP.
    apply Permutation_Type_cons_app_inv in HP.
    rewrite <- app_assoc in HP.
    apply IHl1 in HP.
    destruct HP as [[[[l1'' l2''] l3''] l4''] [[H1 H2] [H3 H4]]].
    exists (l1'', l2'', a :: l3'', l4''); simpl; repeat split; auto.
    * now apply Permutation_Type_cons_app.
    * now apply Permutation_Type_sym, Permutation_Type_cons_app, Permutation_Type_sym.
Qed.

Instance Permutation_Type_Forall A (P : A -> Prop) :
  Proper ((@Permutation_Type A) ==> Basics.impl) (Forall P).
Proof.
intros l1 l2 H.
apply Permutation_Type_Permutation in H.
rewrite H; reflexivity.
Qed.

Instance Permutation_Type_Exists A (P : A -> Prop) :
  Proper ((@Permutation_Type A) ==> Basics.impl) (Exists P).
Proof.
intros l1 l2 H.
apply Permutation_Type_Permutation in H.
rewrite H; reflexivity.
Qed.

Instance Permutation_Type_Forall_inf A (P : A -> Type) :
  Proper ((@Permutation_Type A) ==> Basics.arrow) (Forall_inf P).
Proof.
intros l1 l2 H.
induction H; intro H1; auto.
- inversion_clear H1 as [|? ? Hx HF].
  now apply IHPermutation_Type in HF; constructor.
- inversion_clear H1 as [|? ? Hx HF]; inversion HF.
  now repeat constructor.
Qed.

Instance Permutation_Type_Exists_inf A (P : A -> Type) :
  Proper ((@Permutation_Type A) ==> Basics.arrow) (Exists_inf P).
Proof.
intros l1 l2 H.
induction H; intro H1; auto.
- inversion_clear H1 as [ | ? ? HE ].
  + now apply Exists_inf_cons_hd.
  + apply IHPermutation_Type in HE.
    now apply Exists_inf_cons_tl.
- inversion_clear H1 as [ | ? ? HE ]; [ | inversion_clear HE ].
  + now apply Exists_inf_cons_tl, Exists_inf_cons_hd.
  + now apply Exists_inf_cons_hd.
  + now apply Exists_inf_cons_tl, Exists_inf_cons_tl.
Qed.

Lemma Permutation_Type_Forall2_inf A B (P : A -> B -> Type) :
  forall l1 l1' l2, Permutation_Type l1 l1' -> Forall2_inf P l1 l2 ->
    { l2' & Permutation_Type l2 l2' & Forall2_inf P l1' l2' }.
Proof.
intros l1 l1' l2 HP.
revert l2 ; induction HP ; intros l2 HF ; inversion HF ; subst.
- exists nil ; auto.
- apply IHHP in X0 as [ l2' HP2 HF2 ].
  exists (y :: l2') ; auto.
- inversion X0 ; subst.
  exists (y1 :: y0 :: l'0) ; auto.
  constructor.
- apply Permutation_Type_nil in HP1 ; subst.
  apply Permutation_Type_nil in HP2 ; subst.
  exists nil ; auto.
- apply IHHP1 in HF as [ l2' HP2' HF2' ].
  apply IHHP2 in HF2' as [ l2'' HP2'' HF2'' ].
  exists l2'' ; auto.
  transitivity l2' ; assumption.
Qed.

Lemma Permutation_Type_map_inv A B : forall(f : A -> B) l1 l2,
  Permutation_Type l1 (map f l2) -> { l & l1 = map f l & (Permutation_Type l2 l) }.
Proof.
induction l1; intros l2 HP.
- apply Permutation_Type_nil in HP.
  destruct l2; inversion HP.
  now exists nil.
- apply Permutation_Type_sym in HP.
  destruct (Permutation_Type_vs_cons_inv HP) as ((l1', l2') & Heq).
  decomp_map_inf Heq; subst.
  apply Permutation_Type_sym in HP.
  rewrite map_app in HP.
  apply Permutation_Type_cons_app_inv in HP.
  specialize IHl1 with (l0 ++ l4).
  rewrite map_app in IHl1.
  apply IHl1 in HP.
  destruct HP as [l' Heq HP']; subst.
  exists (x :: l'); auto.
  now apply Permutation_Type_sym, Permutation_Type_cons_app, Permutation_Type_sym.
Qed.

Lemma Permutation_Type_map_inv_inj A B : forall f : A -> B, injective f ->
  forall l1 l2, Permutation_Type (map f l1) (map f l2) -> Permutation_Type l1 l2.
Proof.
intros f Hi l1; induction l1; intros l2 HP.
- apply Permutation_Type_nil in HP.
  destruct l2; inversion HP.
  apply Permutation_Type_refl.
- assert (Heq := HP).
  apply Permutation_Type_sym in Heq.
  apply Permutation_Type_vs_cons_inv in Heq.
  destruct Heq as [(l3, l4) Heq].
  decomp_map_inf Heq; subst.
  rewrite map_app in HP; simpl in HP.
  rewrite Heq3 in HP.
  apply Permutation_Type_cons_app_inv in HP.
  specialize IHl1 with (l0 ++ l6).
  rewrite map_app in IHl1.
  apply IHl1 in HP.
  apply Hi in Heq3; subst.
  now apply Permutation_Type_cons_app.
Qed.

Lemma Permutation_Type_image A B : forall (f : A -> B) a l l',
  Permutation_Type (a :: l) (map f l') -> { a' | a = f a' }.
Proof.
intros f a l l' HP.
apply Permutation_Type_map_inv in HP.
destruct HP as [l'' Heq _].
destruct l'' as [ | b l'']; inversion Heq.
now exists b.
Qed.

Lemma Permutation_Type_elt_map_inv A B : forall (f : A -> B) a l1 l2 l3 l4,
  Permutation_Type (l1 ++ a :: l2) (l3 ++ map f l4) ->
  (forall b, a <> f b) -> {'(l1', l2') | l3 = l1' ++ a :: l2' }.
Proof.
intros a l1 l2 l3 l4 f HP Hf.
apply Permutation_Type_sym in HP.
apply Permutation_Type_vs_elt_inv in HP.
destruct HP as ((l', l'') & Heq).
dichot_elt_app_inf_exec Heq.
- subst.
  exists (l', l) ; reflexivity.
- exfalso.
  symmetry in Heq1; decomp_map_inf Heq1; symmetry in Heq1.
  apply Hf in Heq1.
  inversion Heq1.
Qed.

Instance Permutation_Type_flat_map A B f :
  Proper ((@Permutation_Type A) ==> (@Permutation_Type B)) (flat_map f).
Proof.
intros l1; induction l1; intros l2 HP.
- destruct l2; auto.
  apply Permutation_Type_nil in HP; inversion HP.
- apply Permutation_Type_sym in HP.
  destruct (Permutation_Type_vs_cons_inv HP) as ((l' & l'') & ->).
  destruct l'; apply Permutation_Type_sym in HP.
  + simpl in HP; simpl; apply Permutation_Type_app_head.
    apply IHl1.
    now apply Permutation_Type_cons_inv with a.
  + apply Permutation_Type_cons_app_inv in HP.
    apply IHl1 in HP.
    rewrite flat_map_app in HP; simpl in HP.
    rewrite flat_map_app; simpl.
    apply (Permutation_Type_app_head (f a)) in HP.
    apply (Permutation_Type_trans HP).
    rewrite ? app_assoc.
    apply Permutation_Type_app_tail.
    rewrite <- ? app_assoc.
    apply Permutation_Type_app_rot.
Qed.

Instance list_sum_perm_Type : Proper (@Permutation_Type nat ==> eq) list_sum.
Proof.
intros l1; induction l1; intros l2 HP.
- now apply Permutation_Type_nil in HP; subst.
- assert (HP' := HP).
  apply Permutation_Type_sym in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as ((l3 & l4) & ->).
  apply Permutation_Type_cons_app_inv in HP.
  simpl; erewrite IHl1; [ | apply HP ].
  rewrite 2 list_sum_app; simpl.
  now rewrite 2 (Nat.add_comm a), Nat.add_assoc.
Qed.


(** * Permutation definition based on transpositions for induction with fixed length *)
Inductive Permutation_Type_transp A : list A -> list A -> Type :=
| Permutation_Type_t_refl : forall l, Permutation_Type_transp l l
| Permutation_Type_t_swap : forall x y l1 l2,
                              Permutation_Type_transp (l1 ++ y :: x :: l2) (l1 ++ x :: y :: l2)
| Permutation_Type_t_trans l l' l'' :
    Permutation_Type_transp l l' -> Permutation_Type_transp l' l'' -> Permutation_Type_transp l l''.

Instance Permutation_Type_transp_sym A : Symmetric (@Permutation_Type_transp A).
Proof.
intros l1 l2 HC.
induction HC ; subst ; try (now constructor).
eapply Permutation_Type_t_trans ; eassumption.
Qed.

Instance Permutation_Type_transp_equiv A : Equivalence (@Permutation_Type_transp A).
Proof.
split.
- intros l ; apply Permutation_Type_t_refl.
- apply Permutation_Type_transp_sym.
- intros l1 l2 l3 ; apply Permutation_Type_t_trans.
Qed.

Lemma Permutation_Type_transp_cons A : forall (x : A) l1 l2,
  Permutation_Type_transp l1 l2 -> Permutation_Type_transp (x :: l1) (x :: l2).
Proof.
intros x l1 l2 HP.
induction HP ; try reflexivity.
- rewrite 2 app_comm_cons.
  apply Permutation_Type_t_swap.
- etransitivity ; eassumption.
Qed.

Lemma perm_perm_t_Type A : forall l1 l2 : list A,
  Permutation_Type l1 l2 -> Permutation_Type_transp l1 l2.
Proof.
intros l1 l2 HP; induction HP.
- constructor.
- now apply Permutation_Type_transp_cons.
- rewrite <- (app_nil_l (y :: _)), <- (app_nil_l (x :: y :: _)).
  now apply Permutation_Type_t_swap.
- now transitivity l'.
Qed.

Lemma perm_t_perm_Type A : forall l1 l2 : list A,
  Permutation_Type_transp l1 l2 -> Permutation_Type l1 l2.
Proof.
intros l1 l2 HP; induction HP; auto.
- now apply Permutation_Type_app_head, Permutation_Type_swap.
- now transitivity l'.
Qed.

Lemma Permutation_Type_ind_transp A : forall P : list A -> list A -> Prop,
  (forall l, P l l) ->
  (forall x y l1 l2, P (l1 ++ y :: x :: l2) (l1 ++ x :: y :: l2)) ->
  (forall l l' l'',
     Permutation_Type l l' -> P l l' -> Permutation_Type l' l'' -> P l' l'' -> P l l'') ->
  forall l1 l2, Permutation_Type l1 l2 -> P l1 l2.
Proof.
intros P Hr Ht Htr l1 l2 HP; apply perm_perm_t_Type in HP.
revert Hr Ht Htr; induction HP; intros Hr Ht Htr; auto.
apply (Htr _ l'); auto; now apply perm_t_perm_Type.
Qed.

Lemma Permutation_Type_rect_transp A : forall P : list A -> list A -> Type,
  (forall l, P l l) ->
  (forall x y l1 l2, P (l1 ++ y :: x :: l2) (l1 ++ x :: y :: l2)) ->
  (forall l l' l'',
     Permutation_Type l l' -> P l l' -> Permutation_Type l' l'' -> P l' l'' -> P l l'') ->
  forall l1 l2, Permutation_Type l1 l2 -> P l1 l2.
Proof.
intros P Hr Ht Htr l1 l2 HP; apply perm_perm_t_Type in HP.
revert Hr Ht Htr; induction HP; intros Hr Ht Htr; auto.
apply (Htr _ l'); auto; now apply perm_t_perm_Type.
Qed.


Lemma Permutation_Type_list_sum : forall l1 l2,
  Permutation_Type l1 l2 -> list_sum l1 = list_sum l2.
Proof.
unfold list_sum; intros l1 l2 HP; induction HP; simpl; intuition.
- apply Nat.add_shuffle3.
- now rewrite IHHP1.
Qed.

Lemma Permutation_Type_list_max : forall l1 l2,
  Permutation_Type l1 l2 -> list_max l1 = list_max l2.
Proof.
unfold list_max; intros l1 l2 HP; induction HP; simpl; intuition.
- now rewrite ? Nat.max_assoc, (Nat.max_comm x y).
- now rewrite IHHP1.
Qed.
