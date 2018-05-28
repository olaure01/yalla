(* mell_mset example file for yalla library *)
(* Coq 8.6 *)
(* v 1.0   Olivier Laurent *)


(** * Example of a concrete use of the yalla library: multi-set based MELL *)

Require Import Injective.
Require Import nattree.
Require Import fmsetlist.
Require Import List_more.
Require Import Permutation_more.

Import FMSetNotations.


(** ** 0. load the [ll] library *)

Require ll.
Require fmformulas.


(** ** 1. define formulas *)

Inductive formula : Set :=
| var : formulas.Atom -> formula
| covar : formulas.Atom -> formula
| one : formula
| bot : formula
| tens : formula -> formula -> formula
| parr : formula -> formula -> formula
| oc : formula -> formula
| wn : formula -> formula.

Fixpoint dual A :=
match A with
| var x     => covar x
| covar x   => var x
| one       => bot
| bot       => one
| tens A B  => parr (dual B) (dual A)
| parr A B  => tens (dual B) (dual A)
| oc A      => wn (dual A)
| wn A      => oc (dual A)
end.


(** ** 2. define embedding into [formulas.formula] *)

Fixpoint mell2ll A :=
match A with
| var x    => formulas.var x
| covar x  => formulas.covar x
| one      => formulas.one
| bot      => formulas.bot
| tens A B => formulas.tens (mell2ll A) (mell2ll B)
| parr A B => formulas.parr (mell2ll A) (mell2ll B)
| oc A     => formulas.oc (mell2ll A)
| wn A     => formulas.wn (mell2ll A)
end.

Lemma mell2ll_inj : injective mell2ll.
Proof with try reflexivity.
intros A.
induction A ; intros B Heq ;
  destruct B ; inversion Heq ;
  try apply IHA in H0 ;
  try apply IHA1 in H0 ;
  try apply IHA2 in H1 ; subst...
Qed.

Instance border_formula : BOrder.
Proof.
eapply (@border_inj _ border_nat).
eapply comp_inj ; [ eapply comp_inj | ].
- apply nattree2nat_inj.
- eapply section_inj.
  apply fmformulas.form_nattree_section.
- apply mell2ll_inj.
Defined.

Lemma mell2ll_dual : forall A,
  formulas.dual (mell2ll A) = mell2ll (dual A).
Proof.
induction A ; simpl ;
  rewrite ? IHA ;
  rewrite ? IHA1 ;
  rewrite ? IHA2 ;
  reflexivity.
Qed.

Lemma mell2ll_map_wn : forall l,
  map mell2ll (map wn l) = map formulas.wn (map mell2ll l).
Proof with try reflexivity.
induction l...
simpl ; rewrite IHl...
Qed.

Lemma mell2ll_map_wn_inv : forall l1 l2,
  Permutation (map formulas.wn l1) (map mell2ll l2) -> exists l1' l2',
    l1 = map mell2ll l1' /\ l2 = map wn l2' /\ Permutation l1' l2'.
Proof with try assumption ; try reflexivity.
induction l1 ; intros l2 Heq ;
  destruct l2.
- exists nil ; exists nil ; split ; [ | split]...
- apply Permutation_nil in Heq.
  inversion Heq.
- symmetry in Heq.
  apply Permutation_nil in Heq.
  inversion Heq.
- assert (HP := Heq).
  symmetry in Heq.
  apply Permutation_vs_cons_inv in Heq.
  destruct Heq as (l0 & l3 & Heq).
  destruct l0.
  + simpl in Heq ; inversion Heq ; subst.
    simpl in HP.
    rewrite H0 in HP.
    apply Permutation_cons_inv in HP.
    apply IHl1 in HP.
    destruct HP as (l1' & l2' & Heq1 & Heq2 & HP) ; subst.
    destruct f ; inversion H0.
    exists (f :: l1') ; exists (f :: l2') ; split ; [ | split ]...
    apply Permutation_cons...
  + inversion Heq.
    simpl in HP ; rewrite H1 in HP.
    rewrite app_comm_cons in HP.
    apply Permutation_cons_app_inv in HP.
    symmetry in H1.
    decomp_map H1 ; subst.
    replace ((mell2ll f :: map mell2ll l4) ++ map mell2ll l6)
      with (map mell2ll ((f :: l4) ++ l6))
      in HP by (list_simpl ; reflexivity).
    apply IHl1 in HP.
    destruct HP as (l1' & l2' & Heq1 & Heq2 & HP) ; subst.
    destruct x ; inversion H1.
    decomp_map Heq2 ; subst.
    exists (x :: l1') ; exists (x0 :: l2 ++ x :: l1) ; split ; [ | split ]...
    * list_simpl...
    * rewrite app_comm_cons.
      apply Permutation_cons_app...
Qed.


(** *** 2bis. sequents *)

Instance fmset_formula : FinMultiset (SortedList _) formula :=
  FMConstr_slist border_formula.


(** ** 3. define proofs *)

Inductive mell : SortedList border_formula -> Prop :=
| ax_r : forall X, mell (add (covar X) (add (var X) empty))
| one_r : mell (add one empty)
| bot_r : forall m, mell m -> mell (add bot m)
| tens_r : forall A B m1 m2,
              mell (add A m1) -> mell (add B m2) ->
              mell (add (tens A B) (sum m1 m2))
| parr_r : forall A B m,
              mell (add A (add B m)) ->
              mell (add (parr A B) m)
| oc_r : forall A m,
              mell (add A (fmmap wn m)) ->
              mell (add (oc A) (fmmap wn m))
| de_r : forall A m,
              mell (add A m) -> mell (add (wn A) m)
| wk_r : forall A m,
              mell m -> mell (add (wn A) m)
| co_r : forall A m,
              mell (add (wn A) (add (wn A) m)) ->
              mell (add (wn A) m).


(** ** 4. characterize corresponding [ll] fragment *)

(*
Definition mell_fragment A := exists B, A = mell2ll B.

Lemma mell_is_fragment : ll.fragment mell_fragment.
Proof.
intros A HfA B Hsf.
induction Hsf ; 
  try (apply IHHsf ;
       destruct HfA as [B0 HfA] ;
       destruct B0 ; inversion HfA ; subst ;
       eexists ; reflexivity).
assumption.
Qed.
*)

(** cut / axioms / mix0 / mix2 / permutation *)
Definition pfrag_mell := ll.mk_pfrag false (fun _ => False) false false true.
(*                                   cut   axioms           mix0  mix2  perm  *)


(** ** 5. prove equivalence of proof predicates *)

Lemma mell2mellfrag : forall m,
  mell m -> exists s, ll.ll pfrag_mell (map mell2ll (elts m)) s.
Proof with try reflexivity ; try eassumption.
intros m pi.
induction pi ;
  try destruct IHpi as [s' pi'] ;
  try destruct IHpi1 as [s1' pi1'] ;
  try destruct IHpi2 as [s2' pi2'] ;
  eexists ; simpl ; rewrite ? map_app.
- apply (ll.ex_r _ (map mell2ll (covar X :: var X :: nil))).
  + apply ll.ax_r.
  + symmetry.
    destruct (Compare_dec.leb
           (cpair 2 (pcpair (cpair (fmformulas.a2n X) (pcpair 0 0)) 0))
           (cpair 1 (pcpair (cpair (fmformulas.a2n X) (pcpair 0 0)) 0)))...
    apply perm_swap.
- apply ll.one_r.
- eapply ll.ex_r.
  + apply ll.bot_r...
  + change (formulas.bot :: map mell2ll (elts m))
      with (map mell2ll (bot :: elts m)).
    apply Permutation_map.
    rewrite <- (@insert_add border_formula).
    assert (proj1_sig (fmslist_add bot m) = elts (add bot m)) 
      as Helt by reflexivity.
    rewrite Helt.
    symmetry.
    apply elts_add.
- eapply ll.ex_r.
  + apply ll.tens_r.
    * assert (Helt := Permutation_map mell2ll (elts_add A m1)).
      apply (ll.ex_r _ _ _ _ pi1') in Helt.
      simpl in Helt...
    * assert (Helt := Permutation_map mell2ll (elts_add B m2)).
      apply (ll.ex_r _ _ _ _ pi2') in Helt.
      simpl in Helt...
  + rewrite <- map_app.
    change (formulas.tens (mell2ll A) (mell2ll B)
              :: map mell2ll (proj1_sig m2 ++ proj1_sig m1))
      with (map mell2ll (tens A B :: elts m2 ++ elts m1)).
    apply Permutation_map.
    rewrite <- (@insert_add border_formula).
    assert (proj1_sig (fmslist_add (tens A B) (sum m1 m2))
              = elts (add (tens A B) (sum m1 m2)))
      as Helt by reflexivity.
    rewrite Helt.
    etransitivity ; [ apply Permutation_cons ;
                      [ reflexivity | apply Permutation_app_comm ] | ].
    rewrite <- elts_sum.
    symmetry.
    apply elts_add.
- eapply ll.ex_r.
  + apply ll.parr_r.
    assert (Permutation (elts (add A (add B m))) (A :: B :: elts m))
      as Helt.
    { etransitivity ; [ apply elts_add | ].
      apply Permutation_cons...
      apply elts_add. }
    apply (Permutation_map mell2ll) in Helt.
    apply (ll.ex_r _ _ _ _ pi') in Helt.
    simpl in Helt...
  + change (formulas.parr (mell2ll A) (mell2ll B) :: map mell2ll (proj1_sig m))
      with (map mell2ll (parr A B :: elts m)).
    apply Permutation_map.
    rewrite <- (@insert_add border_formula).
    assert (proj1_sig (fmslist_add (parr A B) m) = elts (add (parr A B) m)) 
      as Helt by reflexivity.
    rewrite Helt.
    symmetry.
    apply elts_add.
- eapply ll.ex_r.
  + apply ll.oc_r.
    assert (Permutation (elts (add A (fmmap wn m))) (A :: map wn (elts m)))
      as Helt.
    { etransitivity ; [ apply elts_add | ].
      apply Permutation_cons...
      apply elts_fmmap. }
    apply (Permutation_map  mell2ll) in Helt.
    apply (ll.ex_r _ _ _ _ pi') in Helt.
    eapply ll.ex_r ; [ apply Helt | ].
    simpl.
    apply Permutation_cons...
    rewrite mell2ll_map_wn.
    apply Permutation_map.
    reflexivity.
  + rewrite <- mell2ll_map_wn.
    change (formulas.oc (mell2ll A) :: map mell2ll (map wn (proj1_sig m)))
      with (map mell2ll (oc A :: map wn (elts m))).
    apply Permutation_map.
    rewrite <- (@insert_add border_formula).
    assert (proj1_sig (fmslist_add (oc A) (fmmap wn m))
              = elts (add (oc A) (fmmap wn m)))
      as Helt by reflexivity.
    rewrite Helt.
    symmetry.
    rewrite <- elts_fmmap.
    apply elts_add.
- eapply ll.ex_r.
  + apply ll.de_r.
    assert (Helt := Permutation_map mell2ll (elts_add A m)).
    apply (ll.ex_r _ _ _ _ pi') in Helt.
    simpl in Helt...
  + change (formulas.wn (mell2ll A) :: map mell2ll (proj1_sig m))
      with (map mell2ll (wn A :: elts m)).
    apply Permutation_map.
    rewrite <- (@insert_add border_formula).
    assert (proj1_sig (fmslist_add (wn A) m) = elts (add (wn A) m)) 
      as Helt by reflexivity.
    rewrite Helt.
    symmetry.
    apply elts_add.
- eapply ll.ex_r.
  + apply (ll.wk_r _ (mell2ll A))...
  + change (formulas.wn (mell2ll A) :: map mell2ll (elts m))
      with (map mell2ll (wn A :: elts m)).
    apply Permutation_map.
    rewrite <- (@insert_add border_formula).
    assert (proj1_sig (fmslist_add (wn A) m) = elts (add (wn A) m)) 
      as Helt by reflexivity.
    rewrite Helt.
    symmetry.
    apply elts_add.
- eapply ll.ex_r.
  + apply (ll.co_r _ (mell2ll A) nil).
    simpl.
    assert (Permutation (elts (add (wn A) (add (wn A) m)))
                        (wn A :: wn A :: elts m))
      as Helt.
    { etransitivity ; [ apply elts_add | ].
      apply Permutation_cons...
      apply elts_add. }
    apply (Permutation_map mell2ll) in Helt.
    apply (ll.ex_r _ _ _ _ pi') in Helt.
    simpl in Helt...
  + change (formulas.wn (mell2ll A) :: map formulas.wn nil
              ++ map mell2ll (proj1_sig m))
      with (map mell2ll (wn A :: elts m)).
    apply Permutation_map.
    rewrite <- (@insert_add border_formula).
    assert (proj1_sig (fmslist_add (wn A) m) = elts (add (wn A) m)) 
      as Helt by reflexivity.
    rewrite Helt.
    symmetry.
    apply elts_add.
Qed.

Lemma mellfrag2mell : forall m s,
  ll.ll pfrag_mell (map mell2ll (elts m)) s -> mell m.
Proof with try eassumption ; try reflexivity.
intros m s pi.
remember (map mell2ll (elts m)) as l.
assert (HP := Permutation_refl l).
rewrite Heql in HP at 2 ; clear Heql.
revert m HP ; induction pi ; intros m HP ; subst ;
  try (now inversion f) ;
  try (now (apply Permutation_image in HP ;
            destruct HP as [Z Heq] ;
            destruct Z ; inversion Heq)).
- apply Permutation_length_2_inv in HP.
  destruct HP as [ HP | HP ] ; symmetry in HP ; decomp_map HP ; subst.
  + destruct l1 ; inversion HP4.
    destruct x ; inversion HP1 ; subst.
    destruct x0 ; inversion HP3 ; subst.
    apply (f_equal (fold_right add empty)) in HP.
    rewrite retract in HP ; subst.
    apply ax_r.
  + destruct l1 ; inversion HP4.
    destruct x ; inversion HP1 ; subst.
    destruct x0 ; inversion HP3 ; subst.
    apply (f_equal (fold_right add empty)) in HP.
    rewrite retract in HP ; subst.
    simpl.
    assert (add (var a0) (add (covar a0) empty)
          = add (covar a0) (add (var a0) empty))
      as Hswap by apply add_swap.
    unfold add in Hswap.
    simpl in Hswap.
    rewrite Hswap.
    apply ax_r.
- apply IHpi.
  etransitivity...
- apply Permutation_length_1_inv in HP.
  remember (elts m) as l.
  destruct l ; inversion HP.
  destruct l ; inversion H1.
  destruct f ; inversion H0 ; subst.
  apply (f_equal (fold_right add empty)) in Heql.
  rewrite retract in Heql ; subst.
  apply one_r.
- symmetry in HP.
  assert (HP2 := HP).
  apply Permutation_vs_cons_inv in HP.
  destruct HP as (l1 & l2 & HP).
  symmetry in HP.
  decomp_map HP ; subst.
  destruct x ; inversion HP4 ; subst.
  apply (f_equal list2fm) in HP.
  rewrite list2fm_retract in HP ; subst.
  rewrite list2fm_elt.
  apply bot_r.
  apply IHpi.
  eapply Permutation_trans ; [ | apply elts_fmmap ].
  unfold fmmap.
  eapply Permutation_trans ; [ | symmetry ; apply elts_perm ].
  eapply Permutation_trans ; [ | symmetry ; apply Permutation_map ;
                                            apply elts_perm ].
  eapply Permutation_trans in HP2 ; [ | apply elts_fmmap ].
  unfold fmmap in HP2.
  eapply Permutation_trans in HP2 ; [ | symmetry ; apply elts_perm ].
  eapply Permutation_trans in HP2 ; [ | symmetry ; apply Permutation_map ;
                                                   apply elts_perm ].
  list_simpl in HP2.
  symmetry in HP2.
  apply Permutation_cons_app_inv in HP2.
  rewrite map_app...
- symmetry in HP.
  assert (HP2 := HP).
  apply Permutation_vs_cons_inv in HP.
  destruct HP as (l3 & l4 & HP).
  symmetry in HP.
  decomp_map HP ; subst.
  destruct x ; inversion HP4 ; subst.
  apply (f_equal list2fm) in HP.
  rewrite list2fm_retract in HP ; subst.
  eapply Permutation_trans in HP2 ; [ | apply elts_fmmap ].
  unfold fmmap in HP2.
  eapply Permutation_trans in HP2 ; [ | symmetry ; apply elts_perm ].
  eapply Permutation_trans in HP2 ; [ | symmetry ; apply Permutation_map ;
                                                   apply elts_perm ].
  list_simpl in HP2.
  symmetry in HP2.
  apply Permutation_cons_app_inv in HP2.
  rewrite <- map_app in HP2.
  apply Permutation_map_inv in HP2.
  destruct HP2 as (l & Heq & HP).
  rewrite list2fm_elt.
  apply list2fm_perm in HP.
  rewrite HP.
  decomp_map Heq ; subst.
  rewrite list2fm_app.
  rewrite sum_comm.
  apply tens_r.
  + apply IHpi1.
    eapply Permutation_trans ; [ | apply elts_fmmap ].
    unfold fmmap.
    eapply Permutation_trans ; [ | symmetry ; apply elts_perm ].
    change (mell2ll x1 :: map mell2ll l7) with (map mell2ll (x1 :: l7)).
    apply Permutation_map.
    symmetry.
    etransitivity.
    * apply elts_add.
    * apply Permutation_cons...
      apply elts_perm.
  + apply IHpi2.
    eapply Permutation_trans ; [ | apply elts_fmmap ].
    unfold fmmap.
    eapply Permutation_trans ; [ | symmetry ; apply elts_perm ].
    change (mell2ll x2 :: map mell2ll l4) with (map mell2ll (x2 :: l4)).
    apply Permutation_map.
    symmetry.
    etransitivity.
    * apply elts_add.
    * apply Permutation_cons...
      apply elts_perm.
- symmetry in HP.
  assert (HP2 := HP).
  apply Permutation_vs_cons_inv in HP.
  destruct HP as (l1 & l2 & HP).
  symmetry in HP.
  decomp_map HP ; subst.
  destruct x ; inversion HP4 ; subst.
  apply (f_equal list2fm) in HP.
  rewrite list2fm_retract in HP ; subst.
  rewrite list2fm_elt.
  apply parr_r.
  apply IHpi.
  eapply Permutation_trans ; [ | apply elts_fmmap ].
  unfold fmmap.
  eapply Permutation_trans ; [ | symmetry ; apply elts_perm ].
  rewrite <- 2 list2fm_elt.
  eapply Permutation_trans ; [ | symmetry ; apply Permutation_map ;
                                            apply elts_perm ].
  eapply Permutation_trans in HP2 ; [ | apply elts_fmmap ].
  unfold fmmap in HP2.
  eapply Permutation_trans in HP2 ; [ | symmetry ; apply elts_perm ].
  eapply Permutation_trans in HP2 ; [ | symmetry ; apply Permutation_map ;
                                                   apply elts_perm ].
  list_simpl in HP2.
  symmetry in HP2.
  apply Permutation_cons_app_inv in HP2.
  list_simpl.
  apply Permutation_cons_app.
  apply Permutation_cons_app...
- symmetry in HP.
  assert (HP2 := HP).
  apply Permutation_vs_cons_inv in HP.
  destruct HP as (l1 & l2 & HP).
  symmetry in HP.
  decomp_map HP ; subst.
  destruct x ; inversion HP4 ; subst.
  apply (f_equal list2fm) in HP.
  rewrite list2fm_retract in HP ; subst.
  rewrite list2fm_elt.
  eapply Permutation_trans in HP2 ; [ | apply elts_fmmap ].
  unfold fmmap in HP2.
  eapply Permutation_trans in HP2 ; [ | symmetry ; apply elts_perm ].
  eapply Permutation_trans in HP2 ; [ | symmetry ; apply Permutation_map ;
                                                   apply elts_perm ].
  list_simpl in HP2.
  symmetry in HP2.
  apply Permutation_cons_app_inv in HP2.
  rewrite <- map_app in HP2.
  apply mell2ll_map_wn_inv in HP2.
  destruct HP2 as (l1 & l2 & Heq1 & Heq2 & HP) ; subst.
  rewrite Heq2.
  rewrite list2fm_map.
  apply oc_r.
  apply IHpi.
  eapply Permutation_trans ; [ | apply elts_fmmap ].
  unfold fmmap.
  eapply Permutation_trans ; [ | symmetry ; apply elts_perm ].
  eapply Permutation_trans ; [ | symmetry ; apply Permutation_map ;
                                            apply elts_add ].
  simpl ; apply Permutation_cons...
  rewrite <- mell2ll_map_wn.
  apply Permutation_map.
  change (proj1_sig (list2fm (map wn (proj1_sig (list2fm l2)))))
    with (elts (list2fm (map wn (elts (list2fm l2))))).
  eapply Permutation_trans ; [ | symmetry ; apply elts_perm ].
  apply Permutation_map.
  eapply Permutation_trans ; [ | symmetry ; apply elts_perm ]...
- symmetry in HP.
  assert (HP2 := HP).
  apply Permutation_vs_cons_inv in HP.
  destruct HP as (l1 & l2 & HP).
  symmetry in HP.
  decomp_map HP ; subst.
  destruct x ; inversion HP4 ; subst.
  apply (f_equal list2fm) in HP.
  rewrite list2fm_retract in HP ; subst.
  rewrite list2fm_elt.
  apply de_r.
  apply IHpi.
  eapply Permutation_trans ; [ | apply elts_fmmap ].
  unfold fmmap.
  eapply Permutation_trans ; [ | symmetry ; apply elts_perm ].
  rewrite <- list2fm_elt.
  eapply Permutation_trans ; [ | symmetry ; apply Permutation_map ;
                                            apply elts_perm ].
  eapply Permutation_trans in HP2 ; [ | apply elts_fmmap ].
  unfold fmmap in HP2.
  eapply Permutation_trans in HP2 ; [ | symmetry ; apply elts_perm ].
  eapply Permutation_trans in HP2 ; [ | symmetry ; apply Permutation_map ;
                                                   apply elts_perm ].
  list_simpl in HP2.
  symmetry in HP2.
  apply Permutation_cons_app_inv in HP2.
  list_simpl.
  apply Permutation_cons_app...
- symmetry in HP.
  assert (HP2 := HP).
  apply Permutation_vs_cons_inv in HP.
  destruct HP as (l1 & l2 & HP).
  symmetry in HP.
  decomp_map HP ; subst.
  destruct x ; inversion HP4 ; subst.
  apply (f_equal list2fm) in HP.
  rewrite list2fm_retract in HP ; subst.
  rewrite list2fm_elt.
  apply wk_r.
  apply IHpi.
  eapply Permutation_trans ; [ | apply elts_fmmap ].
  unfold fmmap.
  eapply Permutation_trans ; [ | symmetry ; apply elts_perm ].
  eapply Permutation_trans ; [ | symmetry ; apply Permutation_map ;
                                            apply elts_perm ].
  eapply Permutation_trans in HP2 ; [ | apply elts_fmmap ].
  unfold fmmap in HP2.
  eapply Permutation_trans in HP2 ; [ | symmetry ; apply elts_perm ].
  eapply Permutation_trans in HP2 ; [ | symmetry ; apply Permutation_map ;
                                                   apply elts_perm ].
  list_simpl in HP2.
  symmetry in HP2.
  apply Permutation_cons_app_inv in HP2.
  rewrite map_app...
- symmetry in HP.
  assert (HP2 := HP).
  apply Permutation_vs_cons_inv in HP.
  destruct HP as (l1 & l2 & HP).
  symmetry in HP.
  decomp_map HP ; subst.
  destruct x ; inversion HP4 ; subst.
  apply (f_equal list2fm) in HP.
  rewrite list2fm_retract in HP ; subst.
  rewrite list2fm_elt.
  apply co_r.
  apply IHpi.
  eapply Permutation_trans ; [ | apply elts_fmmap ].
  unfold fmmap.
  eapply Permutation_trans ; [ | symmetry ; apply elts_perm ].
  rewrite <- 2 list2fm_elt.
  eapply Permutation_trans ; [ | symmetry ; apply Permutation_map ;
                                            apply elts_perm ].
  eapply Permutation_trans in HP2 ; [ | apply elts_fmmap ].
  unfold fmmap in HP2.
  eapply Permutation_trans in HP2 ; [ | symmetry ; apply elts_perm ].
  eapply Permutation_trans in HP2 ; [ | symmetry ; apply Permutation_map ;
                                                   apply elts_perm ].
  list_simpl in HP2.
  list_simpl.
  apply Permutation_cons_app.
  symmetry.
  etransitivity ; [ apply HP2 | ].
  apply Permutation_middle.
- inversion H.
Qed.


(** ** 6. import properties *)

(** *** axiom expansion *)

Lemma ax_gen_r : forall A, mell (add (dual A) (add A empty)).
Proof.
intro A.
destruct (@ll.ax_exp pfrag_mell (formulas.dual (mell2ll A)))
  as [s Hax].
rewrite formulas.bidual in Hax.
rewrite mell2ll_dual in Hax.
eapply mellfrag2mell.
eapply ll.ex_r ; [ eassumption | ].
change (mell2ll (dual A) :: mell2ll A :: nil)
  with (map mell2ll (dual A :: A :: nil)).
apply Permutation_map.
etransitivity ; [ | symmetry ; apply elts_add ].
reflexivity.
Qed.

(** *** cut elimination *)

Lemma cut_r : forall A m1 m2, 
  mell (add A m1) -> mell (add (dual A) m2) -> mell (sum m1 m2).
Proof with try eassumption.
intros A m1 m2 pi1 pi2.
destruct (mell2mellfrag _ pi1) as [s1 pi1'] ; simpl in pi1'.
destruct (mell2mellfrag _ pi2) as [s2 pi2'] ; simpl in pi2'.
rewrite <- (@insert_add border_formula) in pi1'.
assert (proj1_sig (fmslist_add A m1) = elts (add A m1)) 
  as Helt by reflexivity.
rewrite Helt in pi1'.
clear Helt.
assert (Permutation (map mell2ll (elts (add A m1)))
                    (map mell2ll (A :: elts m1)))
  as Helt by (apply Permutation_map ; apply elts_add).
apply (ll.ex_r _ _ _ _ pi1') in Helt.
simpl in Helt.
rewrite <- (@insert_add border_formula) in pi2'.
assert (proj1_sig (fmslist_add (dual A) m2) = elts (add (dual A) m2)) 
  as Helt2 by reflexivity.
rewrite Helt2 in pi2' ; clear Helt2.
assert (Permutation (map mell2ll (elts (add (dual A) m2)))
                    (map mell2ll (dual A :: elts m2)))
  as Helt2 by (apply Permutation_map ; apply elts_add).
apply (ll.ex_r _ _ _ _ pi2') in Helt2.
list_simpl in Helt2.
eapply ll.cut_r_axfree in Helt ;
  [ | | rewrite mell2ll_dual ]...
- destruct Helt as [s Helt].
  rewrite <- map_app in Helt.
  eapply mellfrag2mell.
  eapply ll.ex_r ; [ apply Helt | ].
  apply Permutation_map.
  symmetry.
  etransitivity ; [ apply elts_sum | ].
  reflexivity.
- intros l Hax ; inversion Hax.
Qed.





