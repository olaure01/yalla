(* Permutation_more Library *)
(* Coq 8.6 *)

(* v0.1  2017/02/17   Olivier Laurent *)


(** * Add-ons for Permutation library
Usefull properties apparently missing in the Permutation library. *)

Require Import Morphisms.
Require Export Permutation.

Require Import List_more.



Lemma Permutation_morph_transp {A} : forall P : list A -> Prop,
  (forall a b l1 l2, P (l1 ++ a :: b :: l2) -> P (l1 ++ b :: a :: l2)) ->
    Proper ((@Permutation A) ==> iff) P.
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

Lemma Permutation_elt {A} : forall (a : A) l1 l2 l1' l2',
  Permutation (l1 ++ l2) (l1' ++ l2') ->
    Permutation (l1 ++ a :: l2) (l1' ++ a :: l2').
Proof.
intros a l1 l2 l1' l2' HP.
etransitivity.
- symmetry.
  apply Permutation_cons_app.
  reflexivity.
- apply Permutation_cons_app.
  assumption.
Qed.

Lemma Permutation_elt_inv {A} : forall (a : A) l1 l2 l1' l2',
  Permutation (l1 ++ a :: l2) (l1' ++ a :: l2') ->
    Permutation (l1 ++ l2) (l1' ++ l2').
Proof.
intros a l1 l2 l1' l2' HP.
eapply Permutation_cons_inv.
etransitivity.
- apply Permutation_middle.
- etransitivity.
  + eassumption.
  + symmetry.
    apply Permutation_middle.
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

Lemma Permutation_image {A B} : forall (f : A -> B) a l l',
  Permutation (a :: l) (map f l') -> exists a', a = f a'.
Proof.
intros f a l l' HP.
apply Permutation_map_inv in HP.
destruct HP as (l'' & Heq & _).
destruct l'' ; inversion Heq.
eexists ; reflexivity.
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


