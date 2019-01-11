(* Permutation_more Library *)

(** * Add-ons for Permutation library
Usefull properties apparently missing in the Permutation library. *)

Require Import Psatz.
Require Import Plus.
Require Import Morphisms.
Require Export Permutation.

Require Import Injective.
Require Import List_more.


Instance Permutation_refl' {A} : Proper (Logic.eq ==> @Permutation A) id.
Proof.
intros x y Heq.
rewrite Heq.
reflexivity.
Qed.

Lemma Permutation_morph_transp {A} : forall P : list A -> Prop,
  (forall a b l1 l2, P (l1 ++ a :: b :: l2) -> P (l1 ++ b :: a :: l2)) ->
    Proper ((@Permutation A) ==> Basics.impl) P.
Proof with try eassumption.
assert (forall P : list A -> Prop,
         (forall a b l1 l2, P (l1 ++ a :: b :: l2) ->
                            P (l1 ++ b :: a :: l2)) ->
         forall l1 l2, Permutation l1 l2 ->
         forall l0, P (l0 ++ l1) -> P (l0 ++ l2))
  as Himp.
{ intros P HP l1 l2 H.
  induction H ; intros...
  - rewrite <- (app_nil_l l').
    rewrite app_comm_cons.
    rewrite app_assoc.
    apply IHPermutation.
    list_simpl...
  - apply HP...
  - apply IHPermutation2.
    apply IHPermutation1... }
intros P HP l1 l2 H H'.
rewrite <- (app_nil_l l2).
rewrite <- (app_nil_l l1) in H'.
eapply Himp...
Qed.

Lemma Permutation_elt {A} : forall (a : A) l1 l2 l1' l2',
  Permutation (l1 ++ l2) (l1' ++ l2') ->
    Permutation (l1 ++ a :: l2) (l1' ++ a :: l2').
Proof.
intros a l1 l2 l1' l2' HP.
etransitivity.
- symmetry.
  apply Permutation_middle.
- apply Permutation_cons_app.
  assumption.
Qed.

Lemma Permutation_vs_elt_inv {A} : forall (a : A) l l1 l2,
  Permutation l (l1 ++ a :: l2) -> exists l' l'', l = l' ++ a :: l''.
Proof with try assumption ; try reflexivity.
intros.
remember (l1 ++ a :: l2) as l0.
revert l1 l2 Heql0 ; induction H ; intros l1 l2 Heql.
- exists l1 ; exists l2...
- destruct l1 ; inversion Heql.
  + exists (@nil A) ; exists l...
  + apply IHPermutation in H2.
    destruct H2 as (l1' & l2' & Heq) ; subst.
    exists (a0 :: l1') ;  exists l2'...
- destruct l1 ; inversion Heql ; subst.
  + exists (y :: nil) ;  exists l...
  + destruct l1 ; inversion H1 ; subst.
    * exists (@nil A) ; exists (a0 :: l2)...
    * exists (a1 :: a0 :: l1) ; exists l2...
- destruct (IHPermutation2 _ _ Heql) as (ll' & ll'' & Heq) ; subst.
  assert (Heq := IHPermutation1 ll' ll'' eq_refl).
  destruct Heq as (l' & l'' & Heq) ; subst.
  exists l' ; exists l''...
Qed.

Lemma Permutation_vs_cons_inv {A} : forall (a : A) l l1,
  Permutation l (a :: l1) -> exists l2 l3, l = l2 ++ a :: l3.
Proof.
intros a l l1 HP.
rewrite <- (app_nil_l (a :: l1)) in HP.
eapply Permutation_vs_elt_inv ; eassumption.
Qed.

Lemma Permutation_vs_2elts {A} : forall (s : A) t l1 l2 l3,
  Permutation (l1 ++ s :: l2 ++ t :: l3) (s :: t :: l1 ++ l2 ++ l3).
Proof.
intros ; symmetry.
apply Permutation_cons_app.
rewrite 2 app_assoc.
apply Permutation_cons_app ; reflexivity.
Qed.

Lemma Permutation_vs_2elts_inv : forall A D (s : A) t G,
  Permutation D (s :: t :: G) -> exists G1 G2 G3, 
    D = G1 ++ s :: G2 ++ t :: G3 \/ D = G1 ++ t :: G2 ++ s :: G3.
Proof with try reflexivity.
intros.
assert (H' := H).
apply Permutation_vs_cons_inv in H'.
destruct H' as (D1 & D2 & H') ; subst.
symmetry in H.
apply Permutation_cons_app_inv in H.
symmetry in H.
apply Permutation_vs_cons_inv in H.
destruct H as (D3 & D4 & H).
symmetry in H.
dichot_elt_app_exec H ; subst ;
rewrite <- ? app_assoc ;
rewrite <- ? app_comm_cons.
- exists D3 ; exists l ; exists D2.
  right...
- exists D1 ; exists l0 ; exists D4.
  left...
Qed.

Lemma Permutation_app_rot {A} : forall (l1 : list A) l2 l3,
  Permutation (l1 ++ l2 ++ l3) (l2 ++ l3 ++ l1).
Proof.
intros l1 l2 l3.
rewrite (app_assoc l2).
apply Permutation_app_comm.
Qed.

Lemma Permutation_app_swap {A} : forall (l1 : list A) l2 l3,
  Permutation (l1 ++ l2 ++ l3) (l2 ++ l1 ++ l3).
Proof.
intros.
repeat rewrite app_assoc.
apply Permutation_app_tail.
apply Permutation_app_comm.
Qed.

Lemma Permutation_app_middle {A} : forall (l : list A) l1 l2 l3 l4,
  Permutation (l1 ++ l2) (l3 ++ l4) ->
    Permutation (l1 ++ l ++ l2) (l3 ++ l ++ l4).
Proof.
intros.
eapply Permutation_trans.
apply Permutation_app_swap.
eapply Permutation_trans.
apply Permutation_app_head.
- eassumption.
- apply Permutation_app_swap.
Qed.

Lemma Permutation_app_middle_inv {A} : forall (l : list A) l1 l2 l3 l4,
  Permutation (l1 ++ l ++ l2) (l3 ++ l ++ l4) ->
    Permutation (l1 ++ l2) (l3 ++ l4).
Proof.
intros.
apply (Permutation_app_inv_l l).
eapply Permutation_trans.
apply Permutation_app_swap.
eapply Permutation_trans.
- eassumption.
- apply Permutation_app_swap.
Qed.

Lemma Permutation_app_app_inv {A} : forall (l1 l2 l3 l4 : list A),
  Permutation (l1 ++ l2) (l3 ++ l4) -> exists l3' l3'' l4' l4'',
    Permutation l1 (l3' ++ l4')  /\ Permutation l2 (l3'' ++ l4'') /\
    Permutation l3 (l3' ++ l3'') /\ Permutation l4 (l4' ++ l4'').
Proof with try assumption ; try reflexivity.
induction l1 ; intros.
- exists (@nil A) ; exists l3 ; exists (@nil A) ; exists l4.
  split ; try split ; try split...
- assert (Heq := H).
  apply (Permutation_in a) in Heq.
  + apply in_app_or in Heq.
    destruct Heq as [Heq | Heq] ; apply in_split in Heq ;
    destruct Heq as (l' & l'' & Heq) ; subst.
    * rewrite <- ?app_comm_cons in H.
      rewrite <- app_assoc in H.
      rewrite <- app_comm_cons in H.
      apply Permutation_cons_app_inv in H.
      rewrite app_assoc in H.
      apply IHl1 in H.
      destruct H as (l3' & l3'' & l4' & l4'' & H1 & H2 & H3 & H4).
      exists (a::l3') ; exists l3'' ; exists l4' ; exists l4''.
      split ; try split ; try split...
      -- rewrite <- app_comm_cons.
         apply Permutation_cons...
      -- apply Permutation_sym.
         rewrite <- app_comm_cons.
         apply Permutation_cons_app.
         apply Permutation_sym...
    * rewrite <- ?app_comm_cons in H.
      rewrite app_assoc in H.
      apply Permutation_cons_app_inv in H.
      rewrite <- app_assoc in H.
      apply IHl1 in H.
      destruct H as (l3' & l3'' & l4' & l4'' & H1 & H2 & H3 & H4).
      exists l3' ; exists l3'' ; exists (a::l4') ; exists l4''.
      split ; try split ; try split...
      -- apply Permutation_cons_app...
      -- apply Permutation_sym.
         rewrite <- app_comm_cons.
         apply Permutation_cons_app.
         apply Permutation_sym...
  + constructor...
Qed.

Instance Permutation_Forall {A} (P : A -> Prop) :
  Proper ((@Permutation A) ==> Basics.impl) (Forall P).
Proof with try assumption.
intros l1 l2 H.
induction H ; intro H1...
- inversion H1 ; subst.
  apply IHPermutation in H4.
  constructor...
- inversion H1.
  inversion H3.
  constructor...
  constructor...
- apply IHPermutation2.
  apply IHPermutation1...
Qed.

Instance Permutation_Exists {A} (P : A -> Prop) :
  Proper ((@Permutation A) ==> Basics.impl) (Exists P).
Proof with try assumption.
intros l1 l2 H.
induction H ; intro H1...
- inversion H1 ; subst.
  + apply Exists_cons_hd...
  + apply IHPermutation in H2.
    apply Exists_cons_tl...
- inversion H1 ; [ | inversion H0 ] ; subst.
  + apply Exists_cons_tl.
    apply Exists_cons_hd...
  + apply Exists_cons_hd...
  + apply Exists_cons_tl.
    apply Exists_cons_tl...
- apply IHPermutation2.
  apply IHPermutation1...
Qed.

Lemma Permutation_Forall2 {A B} (P : A -> B -> Prop) :
  forall l1 l1' l2, Permutation l1 l1' -> Forall2 P l1 l2 -> exists l2',
    Permutation l2 l2' /\ Forall2 P l1' l2'.
Proof.
intros l1 l1' l2 HP.
revert l2 ; induction HP ; intros l2 HF ; inversion HF ; subst.
- exists nil ; auto.
- apply IHHP in H3 as (l2' & HP2 & HF2).
  exists (y :: l2') ; auto.
- inversion H3 ; subst.
  exists (y1 :: y0 :: l'0) ; split ; auto.
  constructor.
- apply Permutation_nil in HP1 ; subst.
  apply Permutation_nil in HP2 ; subst.
  exists nil ; auto.
- apply IHHP1 in HF as (l2' & HP2' & HF2').
  apply IHHP2 in HF2' as (l2'' & HP2'' & HF2'').
  exists l2'' ; split ; auto.
  transitivity l2' ; assumption.
Qed.

Lemma Permutation_map_inv {A B} : forall(f : A -> B) l1 l2,
  Permutation l1 (map f l2) -> exists l3, l1 = map f l3 /\ Permutation l2 l3.
Proof with try reflexivity ; try assumption.
induction l1 ; intros l2 HP.
- exists nil ; split...
  destruct l2...
  apply Permutation_nil in HP.
  inversion HP.
- symmetry in HP.
  assert (Heq := HP).
  apply Permutation_vs_cons_inv in Heq.
  destruct Heq as (l3 & l4 & Heq).
  symmetry in Heq.
  decomp_map Heq ; subst.
  symmetry in HP.
  rewrite map_app in HP.
  apply Permutation_cons_app_inv in HP.
  specialize IHl1 with (l0 ++ l6).
  rewrite map_app in IHl1.
  apply IHl1 in HP.
  destruct HP as (l3 & Heq & HP') ; subst.
  exists (x :: l3) ; split...
  symmetry.
  apply Permutation_cons_app.
  symmetry...
Qed.

Lemma Permutation_map_inv_inj {A B} : forall f : A -> B, injective f ->
  forall l1 l2, Permutation (map f l1) (map f l2) -> Permutation l1 l2.
Proof with try assumption ; try reflexivity.
intros f Hi l1 ; induction l1 ; intros l2 HP.
- apply Permutation_nil in HP.
  destruct l2 ; inversion HP...
- assert (Heq := HP).
  symmetry in Heq.
  apply Permutation_vs_cons_inv in Heq.
  destruct Heq as (l3 & l4 & Heq).
  symmetry in Heq.
  decomp_map Heq ; subst.
  rewrite map_app in HP.
  simpl in HP.
  rewrite Heq3 in HP.
  apply Permutation_cons_app_inv in HP.
  specialize IHl1 with (l0 ++ l6).
  rewrite map_app in IHl1.
  apply IHl1 in HP.
  apply Hi in Heq3 ; subst.
  apply Permutation_cons_app...
Qed.

Lemma Permutation_map_inv_inj_local {A B} : forall (f : A -> B) l1 l2,
  (forall x y, In x l1 -> In y l2 -> f x = f y -> x = y) ->
    Permutation (map f l1) (map f l2) -> Permutation l1 l2.
Proof with try assumption ; try reflexivity.
induction l1 ; intros l2 Hi HP.
- apply Permutation_nil in HP.
  destruct l2 ; inversion HP...
- assert (Heq := HP).
  symmetry in Heq.
  apply Permutation_vs_cons_inv in Heq.
  destruct Heq as (l3 & l4 & Heq).
  symmetry in Heq.
  decomp_map Heq ; subst.
  rewrite map_app in HP.
  simpl in HP.
  rewrite Heq3 in HP.
  apply Permutation_cons_app_inv in HP.
  specialize IHl1 with (l0 ++ l6).
  rewrite map_app in IHl1.
  apply IHl1 in HP...
  + apply Hi in Heq3 ; subst.
    * apply Permutation_cons_app...
    * apply in_eq.
    * apply in_elt.
  + intros x' y' Hx' Hy' Hf.
    apply Hi...
    * apply in_cons...
    * apply in_app_or in Hy'.
      destruct Hy' as [ Hy' | Hy' ] ; apply in_or_app.
      left...
      right ; apply in_cons...
Qed.

Lemma Permutation_image {A B} : forall (f : A -> B) a l l',
  Permutation (a :: l) (map f l') -> exists a', a = f a'.
Proof.
intros f a l l' HP.
apply Permutation_map_inv in HP.
destruct HP as (l'' & Heq & _).
destruct l'' ; inversion Heq.
eexists ; reflexivity.
Qed.

Lemma Permutation_elt_map_inv {A B} : forall (f : A -> B) a l1 l2 l3 l4,
  Permutation (l1 ++ a :: l2) (l3 ++ map f l4) ->
  (forall b, a <> f b) -> exists l1' l2', l3 = l1' ++ a :: l2'.
Proof.
intros a l1 l2 l3 l4 f HP Hf.
symmetry in HP.
apply Permutation_vs_elt_inv in HP.
destruct HP as (l' & l'' & Heq).
dichot_elt_app_exec Heq.
- subst.
  eexists ; eexists ; reflexivity.
- exfalso.
  decomp_map Heq1.
  apply Hf in Heq1.
  inversion Heq1.
Qed.

Instance Permutation_flat_map {A B} f :
  Proper ((@Permutation A) ==> (@Permutation B)) (flat_map f).
Proof with try reflexivity ; try eassumption.
intros l1.
induction l1 ; intros l2 HP.
- destruct l2...
  apply Permutation_nil in HP.
  inversion HP.
- symmetry in HP.
  assert (Heq := HP).
  apply Permutation_vs_cons_inv in Heq.
  destruct Heq as (l' & l'' & Heq) ; subst.
  destruct l'.
  + simpl in HP ; symmetry in HP.
    simpl ; apply Permutation_app_head.
    apply IHl1.
    eapply Permutation_cons_inv...
  + symmetry in HP.
    apply Permutation_cons_app_inv in HP.
    apply IHl1 in HP.
    rewrite flat_map_app in HP ; simpl in HP.
    rewrite flat_map_app ; simpl.
    apply (Permutation_app_head (f a)) in HP.
    apply (Permutation_trans HP).
    rewrite ? app_assoc.
    apply Permutation_app_tail.
    rewrite <- ? app_assoc.
    apply Permutation_app_rot.
Qed.

Instance list_sum_perm : Proper (@Permutation nat ==> eq) list_sum.
Proof with try reflexivity.
intros l1 ; induction l1 ; intros l2 HP.
- apply Permutation_nil in HP ; subst...
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_vs_cons_inv in HP'.
  destruct HP' as (l3 & l4 & Heq) ; subst.
  apply Permutation_cons_app_inv in HP.
  simpl ; erewrite IHl1 ; [ | apply HP ].
  rewrite 2 list_sum_app.
  simpl.
  rewrite 2 (plus_comm a).
  rewrite plus_assoc...
Qed.


(** ** Permutation definition based on transpositions for induction with fixed length *)
Inductive Permutation_transp {A} : list A -> list A -> Prop :=
| perm_t_refl : forall l, Permutation_transp l l
| perm_t_swap : forall x y l1 l2, Permutation_transp (l1 ++ y :: x :: l2) (l1 ++ x :: y :: l2)
| perm_t_trans l l' l'' :
    Permutation_transp l l' -> Permutation_transp l' l'' -> Permutation_transp l l''.

Instance Permutation_transp_sym {A} : Symmetric (@Permutation_transp A).
Proof.
intros l1 l2 HC.
induction HC ; subst ; try (now constructor).
eapply perm_t_trans ; eassumption.
Qed.

Instance Permutation_transp_equiv A : Equivalence (@Permutation_transp A).
Proof.
split.
- intros l ; apply perm_t_refl.
- apply Permutation_transp_sym.
- intros l1 l2 l3 ; apply perm_t_trans.
Qed.

Lemma Permutation_transp_cons {A} : forall (x : A) l1 l2,
  Permutation_transp l1 l2 -> Permutation_transp (x :: l1) (x :: l2).
Proof.
intros x l1 l2 HP.
induction HP ; try reflexivity.
- rewrite 2 app_comm_cons.
  apply perm_t_swap.
- etransitivity ; eassumption.
Qed.

Lemma perm_perm_t {A} : forall l1 l2 : list A,
  Permutation l1 l2 <-> Permutation_transp l1 l2.
Proof with try eassumption.
intros l1 l2 ; split ; intros HP.
- induction HP.
  + constructor.
  + apply Permutation_transp_cons...
  + rewrite <- (app_nil_l (y :: _)).
    rewrite <- (app_nil_l (x :: y :: _)).
    apply perm_t_swap.
  + etransitivity...
- induction HP.
  + reflexivity.
  + apply Permutation_app_head.
    apply perm_swap.
  + etransitivity...
Qed.

Lemma Permutation_ind_transp {A} : forall P : list A -> list A -> Prop,
  (forall l, P l l) ->
  (forall x y l1 l2, P (l1 ++ y :: x :: l2) (l1 ++ x :: y :: l2)) ->
  (forall l l' l'',
     Permutation l l' -> P l l' -> Permutation l' l'' -> P l' l'' -> P l l'') ->
  forall l1 l2, Permutation l1 l2 -> P l1 l2.
Proof with try assumption.
intros P Hr Ht Htr l1 l2 HP ; revert Hr Ht Htr.
apply perm_perm_t in HP.
induction HP ; intros Hr Ht Htr.
- apply Hr.
- apply Ht.
- apply (Htr _ l').
  + apply perm_perm_t...
  + apply IHHP1...
  + apply perm_perm_t...
  + apply IHHP2...
Qed.


Lemma Permutation_list_sum : forall l1 l2,
  Permutation l1 l2 -> list_sum l1 = list_sum l2.
Proof.
unfold list_sum.
intros l1 l2 HP.
induction HP ; simpl ; intuition ; try lia.
Qed.

Lemma Permutation_list_max : forall l1 l2,
  Permutation l1 l2 -> list_max l1 = list_max l2.
Proof.
unfold list_max.
intros l1 l2 HP.
induction HP ; simpl ; intuition ; try lia.
Qed.






