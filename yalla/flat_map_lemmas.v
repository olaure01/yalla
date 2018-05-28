(* flat_map_lemmas library for yalla *)
(* v 1.0   Olivier Laurent *)


(** * Some substitution lemmas using [flat_map] *)

Require Import List_more.
Require Import Permutation_more.
Require Import CyclicPerm.
Require Import Permutation_solve.
Require Import CPermutation_solve.
Require Import genperm.

Require Import basic_tactics.


Lemma perm_subst_flat_map {T} : forall (A : T) l ls l0 B,
  Permutation (B :: l0) (flat_map (cons A) ls) ->
       (exists l1, forall lB, exists ls',
           Permutation (lB ++ l0) (flat_map (cons A) ls')
        /\ Permutation (flat_map (app l) ls') (lB ++ l1)
        /\ Permutation (B :: l1) (flat_map (app l) ls))
    \/ (B = A /\ exists x ls' ls'', ls = ls' ++ x :: ls''
        /\ forall lB, Permutation (lB ++ l0)
                                  (flat_map (cons A) ls' ++ lB ++ x
                                     ++ flat_map (cons A) ls'')).
Proof with myeeasy ; try perm_solve.
induction ls ; intros l0 B HP.
- left.
  symmetry in HP.
  apply Permutation_nil in HP.
  inversion HP.
- assert (Heq := HP).
  symmetry in HP.
  apply Permutation_vs_cons_inv in HP.
  destruct HP as (l2 & l3 & HP).
  apply eq_sym in HP.
  simpl in HP.
  rewrite app_comm_cons in HP.
  dichot_elt_app_exec HP ; subst.
  + destruct l2 ; inversion HP0 ; subst.
    * right.
      split...
      exists a ; exists nil ; exists ls ; split...
      intro lB...
    * left.
      exists (l ++ l1 ++ l2 ++ flat_map (app l) ls).
      intro lB.
      exists ((l2 ++ lB ++ l1) :: ls) ; nsplit 3...
  + assert (Permutation (B :: l4 ++ l3) (flat_map (cons A) ls))
      as HP by (rewrite <- HP1 ; perm_solve).
    apply IHls in HP...
    destruct HP as [ [l1 HP] | [HeqA HP] ]. 
    * left.
      exists (l ++ a ++ l1).
      intro lB.
      destruct (HP lB) as (ls' & HP1' & HP2' & HP3').
      exists (a :: ls') ; nsplit 3...
      apply (Permutation_app_head (A :: a)) in HP1'.
      assert (Permutation (lB ++ l0) (lB ++ (A :: a) ++ l4 ++ l3)) as HP4'.
      {
        apply Permutation_app_head.
        simpl in Heq.
        rewrite <- HP1 in Heq.
        rewrite ? app_assoc in Heq.
        rewrite app_comm_cons in Heq.
        apply Permutation_cons_app_inv in Heq...
      }
      apply (Permutation_trans HP4').
      apply (Permutation_trans (Permutation_app_swap _ _ _) HP1').
    * right.
      split...
      destruct HP as (x & ls' & ls'' & Heqls & HP).
      rewrite Heqls.
      exists x ; exists (a :: ls') ; exists ls'' ; split...
      intro lB.
      specialize HP with lB.
      simpl.
      simpl in Heq.
      rewrite <- HP1 in Heq.
      rewrite ? app_assoc in Heq.
      rewrite ? app_comm_cons in Heq.
      apply Permutation_cons_app_inv in Heq.
      apply (Permutation_app_head lB) in Heq.
      apply (Permutation_app_head (A:: a)) in HP.
      rewrite <- ? app_comm_cons in HP.
      rewrite <- ? app_assoc.
      eapply Permutation_trans...
      eapply Permutation_trans ; [ | apply HP ]...
Qed.

Lemma app_vs_app_flat_map {T} : forall (A : T) l0 ls l1 l2,
  l1 ++ l2 = l0 ++ flat_map (cons A) ls ->
      (exists l0',
           l0' <> nil
        /\ l0 = l1 ++ l0'
        /\ l2 = l0' ++ flat_map (cons A) ls)
   \/ (exists ls' ls'',
           ls = ls' ++ ls''
        /\ l1 = l0 ++ flat_map (cons A) ls'
        /\ l2 = flat_map (cons A) ls'')
   \/ (exists x l ls' ls'',
           l <> nil
        /\ ls = ls' ++ (x ++ l) :: ls''
        /\ l1 = l0 ++ flat_map (cons A) (ls' ++ x :: nil)
        /\ l2 = l ++ flat_map (cons A) ls'').
Proof with myeasy.
induction l0.
- induction ls ; intros l1 l2 HP.
  + right ; left...
    exists nil ; exists nil ; split...
    apply app_eq_nil in HP.
    destruct HP ; subst ; split...
  + simpl in HP.
    rewrite app_comm_cons in HP.
    dichot_app_exec HP ; subst.
    * destruct l1.
      -- right ; left.
         exists nil ; exists (a :: ls) ; nsplit 3...
         simpl in HP0 ; subst...
      -- destruct l.
         right ; left.
         inversion HP0 ; subst.
         exists (l1 :: nil) ; exists ls ; nsplit 3...
         rewrite app_nil_r...
         simpl ; rewrite app_nil_r...
         right ; right.
         inversion HP0.
         exists l1 ; exists (t0 :: l) ; exists nil ; exists ls ; nsplit 4...
         intro Hl ; inversion Hl...
         simpl ; rewrite app_nil_r...
    * apply IHls in HP1.
      destruct HP1 as [ (l0' & Heq1 & Heq2 & Heq3)
                      | [ (ls' & ls'' & Heq1 & Heq2 & Heq3)
                      | (x & l & ls' & ls'' & Heq1 & Heq2 & Heq3 & Heq4) ]] ;
        subst.
      -- exfalso.
         symmetry in Heq2.
         apply app_eq_nil in Heq2.
         destruct Heq2 ; subst.
         apply Heq1...
      -- right ; left.
         exists (a :: ls') ; exists ls'' ; nsplit 3...
      -- right ; right.
         exists x ; exists l ; exists (a :: ls') ; exists ls'' ; nsplit 4...
- intros ls l1 l2 HP.
  destruct l1.
  + simpl in HP.
    rewrite HP.
    left.
    exists (a :: l0) ; nsplit 3...
    intros Hnil ; inversion Hnil.
  + inversion HP ; subst.
    apply IHl0 in H1.
    destruct H1 as [ (l0' & Heq1 & Heq2 & Heq3)
                   | [ (ls' & ls'' & Heq1 & Heq2 & Heq3)
                   | (x & l & ls' & ls'' & Heq1 & Heq2 & Heq3 & Heq4) ]] ; subst.
    * left.
      exists l0' ; nsplit 3...
    * right ; left.
      exists ls' ; exists ls'' ; nsplit 3...
    * right ; right.
      exists x ; exists l ; exists ls' ; exists ls'' ; nsplit 4...
Qed.

Lemma app_app_vs_flat_map {T} : forall (A : T) ls l1 l2 l3,
  l1 ++ l2 ++ l3 = (flat_map (cons A) ls) ->
      (exists ls' ls'' ls''',
           ls = ls' ++ ls'' ++ ls'''
        /\ l1 = flat_map (cons A) ls'
        /\ l2 = flat_map (cons A) ls''
        /\ l3 = flat_map (cons A) ls''')
   \/ (exists x l ls' ls''',
           l <> nil
        /\ ls = ls' ++ (x ++ l2 ++ l) :: ls'''
        /\ l1 = flat_map (cons A) (ls' ++ x :: nil)
        /\ l3 = l ++ flat_map (cons A) ls''')
   \/ (exists x l ls' ls'' ls''',
           l <> nil
        /\ ls = ls' ++ (x ++ l) :: ls'' ++ ls'''
        /\ l1 = flat_map (cons A) (ls' ++ x :: nil)
        /\ l2 = l ++ flat_map (cons A) ls''
        /\ l3 = flat_map (cons A) ls''')
   \/ (exists x' l' ls' ls'' ls''',
           l' <> nil
        /\ ls = ls' ++ ls'' ++ (x' ++ l') :: ls'''
        /\ l1 = flat_map (cons A) ls'
        /\ l2 = flat_map (cons A) (ls'' ++ x' :: nil)
        /\ l3 = l' ++ flat_map (cons A) ls''')
   \/ (exists x l x' l' ls' ls'' ls''',
           l <> nil /\ l' <> nil 
        /\ ls = ls' ++ (x ++ l) :: ls'' ++ (x' ++ l') :: ls'''
        /\ l1 = flat_map (cons A) (ls' ++ x :: nil)
        /\ l2 = l ++ flat_map (cons A) (ls'' ++ x' :: nil)
        /\ l3 = l' ++ flat_map (cons A) ls''').
Proof with myeasy.
intros A ls l1 l2 l3 HP.
apply (app_vs_app_flat_map _ nil) in HP.
destruct HP as [ (l0' & Heq1 & Heq2 & Heq3)
               | [ (ls' & ls'' & Heq1 & Heq2 & Heq3)
               | (x & l & ls' & ls'' & Heq1 & Heq2 & Heq3 & Heq4) ]] ; subst.
- exfalso.
  symmetry in Heq2.
  apply app_eq_nil in Heq2.
  destruct Heq2 ; subst.
  apply Heq1...
- apply (app_vs_app_flat_map _ nil) in Heq3.
  destruct Heq3 as [ (l0' & Heq01 & Heq02 & Heq03)
                   | [ (ls0' & ls0'' & Heq01 & Heq02 & Heq03)
                   | (x0 & l0 & ls0' & ls0'' & Heq01 & Heq02 & Heq03 & Heq04) ]] ;
    subst.
  + exfalso.
    symmetry in Heq02.
    apply app_eq_nil in Heq02.
    destruct Heq02 ; subst.
    apply Heq01...
  + left.
    exists ls' ; exists ls0' ; exists ls0'' ; nsplit 4...
  + right ; right ; right ; left.
    exists x0 ; exists l0 ; exists ls' ; exists ls0' ; exists ls0'' ; nsplit 5... 
- apply app_vs_app_flat_map in Heq4.
  destruct Heq4 as [ (l0' & Heq01 & Heq02 & Heq03)
                   | [ (ls0' & ls0'' & Heq01 & Heq02 & Heq03)
                   | (x0 & l0 & ls0' & ls0'' & Heq01 & Heq02 & Heq03 & Heq04) ]] ;
    subst.
  + right ; left.
    exists x ; exists l0' ; exists ls' ; exists ls'' ; nsplit 4...
  + right ; right ; left.
    exists x ; exists l ; exists ls' ; exists ls0' ; exists ls0'' ; nsplit 5...
  + right ; right ; right ; right.
    exists x ; exists l ; exists x0 ; exists l0 ; exists ls' ;
      exists ls0' ; exists ls0'' ; nsplit 6...
Qed.

Lemma elt_subst_flat_map {T} : forall (A : T) l ls l0l l0r B,
  l0l ++ B :: l0r = flat_map (cons A) ls ->
     (exists l1l l1r, forall lB, exists ls',
         l0l ++ lB ++ l0r = flat_map (cons A) ls'
      /\ l1l ++ lB ++ l1r = flat_map (app l) ls'
      /\ l1l ++ B :: l1r = flat_map (app l) ls)
  \/ (B = A /\ exists x ls' ls'', ls = ls' ++ x :: ls''
      /\ forall lB, l0l ++ lB ++ l0r =
           (flat_map (cons A) ls' ++ lB ++ x ++ flat_map (cons A) ls'')).
Proof with myeeasy ; try cperm_solve.
induction ls ; intros l0l l0r B HP.
- left.
  destruct l0l ; inversion HP.
- simpl in HP.
  rewrite app_comm_cons in HP.
  dichot_elt_app_exec HP ; subst.
  + destruct l0l ; inversion HP0 ; subst.
    * right.
      split...
      exists a ; exists nil ; exists ls ; split...
    * left. 
      exists (l ++ l0l) ; exists (l0 ++ flat_map (app l) ls).
      intro lB ; exists((l0l ++ lB ++ l0) :: ls) ; 
        nsplit 3 ; simpl ; rewrite <- ? app_assoc...
  + apply IHls in HP1...
    destruct HP1 as [ (l1l & l1r & HP1) | (HeqA & x & ls' & ls'' & Heqls & HP1) ].
    * left.
      exists (l ++ a ++ l1l) ; exists l1r.
      intro lB.
      destruct (HP1 lB) as (ls' & HP1' & HP2' & HP3').
      exists (a :: ls') ; nsplit 3 ; simpl ; rewrite <- ? app_assoc...
      rewrite HP1'...
      rewrite HP2'...
      rewrite HP3'...
    * right.
      split...
      rewrite Heqls...
      exists x ; exists (a :: ls') ; exists ls'' ; split...
      intros lB.
      specialize HP1 with lB.
      simpl.
      rewrite <- ? app_assoc.
      rewrite HP1...
Qed.

Lemma PCperm_subst_flat_map {T} b : forall (A : T) l ls l0 B, 
  PCperm b (B :: l0) (flat_map (cons A) ls) ->
     (exists l1, forall lB, exists ls', PCperm b (lB ++ l0)
                                                 (flat_map (cons A) ls')
        /\ PCperm b (flat_map (app l) ls') (lB ++ l1)
        /\ PCperm b (B :: l1) (flat_map (app l) ls))
  \/ (B = A /\ exists x ls' ls'', ls = ls' ++ x :: ls''
        /\ forall lB, PCperm b (lB ++ l0)
                               (flat_map (cons A) ls' ++ lB ++ x
                                     ++ flat_map (cons A) ls'')).
Proof with myeeasy.
intros A l ls l0 B HP.
hyps_PCperm_unfold ; unfold PCperm ; destruct b.
- apply perm_subst_flat_map...
- symmetry in HP.
  apply cperm_vs_cons_inv in HP.
  destruct HP as (l0l & l0r & Heq & HP).
  symmetry in HP.
  apply (elt_subst_flat_map _ l) in HP...
  destruct HP as [ (l1l & l1r & HP) | (HeqA & x & ls' & ls'' & Heqls & HP1) ].
  + left.
    exists (l1r ++ l1l).
    intro lB.
    destruct (HP lB) as (ls' & HP1 & HP2 & HP3) ; subst.
    assert (CPermutation (lB ++ l0r ++ l0l) (l0l ++ lB ++ l0r))
      as HP1' by cperm_solve.
    rewrite HP1 in HP1'.
    assert (CPermutation (l1l ++ lB ++ l1r) (lB ++ l1r ++ l1l))
      as HP2' by cperm_solve.
    rewrite HP2 in HP2'.
    assert (CPermutation (B :: l1r ++ l1l) (l1l ++ B :: l1r))
      as HP3' by cperm_solve.
    rewrite HP3 in HP3'.
    exists ls' ; nsplit 3...
  + right.
    split...
    exists x ; exists ls' ; exists ls'' ; subst.
    split...
    intro lB.
    specialize HP1 with lB.
    rewrite <- HP1.
    rewrite app_assoc.
    apply cperm.
Qed.

Lemma flat_map_cons_is_flat_map_app {T} : forall (a : T) l,
  flat_map (cons a) l = flat_map (app (a :: nil)) l.
Proof.
intros.
apply flat_map_ext.
reflexivity.
Qed.

Lemma perm_flat_map_app {T} : forall (l : list T) ls,
  Permutation (flat_map (app l) ls) (flat_map (fun _ => l) ls ++ flat_map id ls).
Proof.
induction ls ; perm_solve.
Qed.

Lemma perm_flat_map_const_const {T} : forall (a : T) ls lp,
  Permutation (flat_map (fun _ : list T => a :: nil) ls) lp ->
    forall x, In x lp -> x = a.
Proof with try assumption.
induction ls ; intros lp HP x Hin.
- apply Permutation_nil in HP ; subst.
  inversion Hin.
- assert (HP0 := HP).
  simpl in HP ; symmetry in HP.
  apply Permutation_vs_cons_inv in HP.
  destruct HP as (l1 & l2 & HP) ; subst.
  simpl in HP0 ; apply Permutation_cons_app_inv in HP0.
  apply in_elt_inv in Hin.
  destruct Hin as [ Heq | Hin ]...
  apply (IHls (l1 ++ l2))...
Qed.

Lemma perm_flat_map_const {T} : forall (a : T) ls lp,
  Permutation (flat_map (fun _ : list T => a :: nil) ls) lp ->
    exists ls', lp = flat_map (fun _ : list T => a :: nil) ls'.
Proof with try reflexivity.
intros a ls lp ; revert ls ; induction lp ; intros ls HP.
- exists nil...
- destruct ls.
  + apply Permutation_nil in HP.
    inversion HP.
  + assert (Ha := perm_flat_map_const_const _ _ _ HP).
    assert (Ha0 := in_eq a0 lp).
    apply Ha in Ha0 ; subst.
    simpl in HP ; apply Permutation_cons_inv in HP.
    apply IHlp in HP.
    destruct HP as [ls' HP] ; subst.
    exists (l :: ls')...
Qed.

Lemma perm_flat_map_const_subst {T0 T1 T2} :
  forall (l1 : list T1) (l2 : list T2) (ls1 ls2 : list T0), l1 <> nil ->
    Permutation (flat_map (fun _ => l1) ls1) (flat_map (fun _ => l1) ls2) ->
    Permutation (flat_map (fun _ => l2) ls1) (flat_map (fun _ => l2) ls2).
Proof with try reflexivity ; try assumption.
induction ls1 ; intros ls2 Hnil HP.
- apply Permutation_nil in HP.
  destruct ls2...
  exfalso.
  simpl ; inversion HP.
  apply app_eq_nil in H0.
  apply Hnil.
  apply H0.
- destruct ls2.
  + exfalso.
    symmetry in HP.
    apply Permutation_nil in HP.
    apply app_eq_nil in HP.
    apply Hnil.
    apply HP.
  + simpl in HP ; apply Permutation_app_inv_l in HP.
    apply IHls1 in HP...
    eapply Permutation_app_head...
Qed.


