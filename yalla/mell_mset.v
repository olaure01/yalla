(* mell_mset example file for yalla library *)

(** * Example of a concrete use of the yalla library: multi-set based MELL *)

From OLlibs Require Import funtheory dectype List_more Permutation_more Permutation_Type_more
                           BOrders nattree fmsetlist_Type.
Import FMSetNotations.


(** ** 0. load the [ll] library *)

From Yalla Require Import atoms fmformulas.
From Yalla Require ll_cut.

Set Implicit Arguments.


Section Atoms.

Context { atom : DecType }.
Context { Atoms : AtomType_into_nat atom }.

(** ** 1. define formulas *)

Inductive formula :=
| var : atom -> formula
| covar : atom -> formula
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
Proof.
intros A; induction A; intros B Heq; destruct B; inversion Heq;
  try apply IHA in H0; try apply IHA1 in H0; try apply IHA2 in H1; subst; reflexivity.
Qed.

Instance border_formula : BOrder.
Proof.
eapply (@border_inj _ border_nat).
eapply compose_injective ; [ | eapply compose_injective ].
- apply mell2ll_inj.
- eapply section_injective.
  intros A; apply fmformulas.form_nattree_section.
- apply nattree2nat_inj.
Defined.

Lemma mell2ll_dual A : formulas.dual (mell2ll A) = mell2ll (dual A).
Proof. induction A; cbn; rewrite ? IHA, ? IHA1, ? IHA2; reflexivity. Qed.

Lemma mell2ll_map_wn l : map mell2ll (map wn l) = map formulas.wn (map mell2ll l).
Proof. induction l as [ | a l IHl ]; [ | cbn; rewrite IHl ]; reflexivity. Qed.

Lemma mell2ll_map_wn_inv l1 l2 : Permutation_Type (map formulas.wn l1) (map mell2ll l2) ->
  { pl & ((l1 = map mell2ll (fst pl)) * (l2 = map wn (snd pl))
        * (Permutation_Type (fst pl) (snd pl)))%type }.
Proof.
induction l1 in l2 |- *; intros Heq; destruct l2.
- exists (nil, nil); repeat split; reflexivity.
- apply Permutation_Type_nil in Heq.
  inversion Heq.
- symmetry in Heq.
  apply Permutation_Type_nil in Heq.
  inversion Heq.
- assert (HP := Heq).
  symmetry in Heq.
  apply Permutation_Type_vs_cons_inv in Heq.
  destruct Heq as ((l0 & l3) & Heq).
  destruct l0.
  + cbn in Heq, HP; inversion Heq; subst.
    rewrite H0 in HP.
    apply Permutation_Type_cons_inv in HP.
    apply IHl1 in HP.
    destruct HP as ((l1' & l2') & (-> & ->) & HP).
    destruct f; inversion H0.
    exists (f :: l1', f :: l2'); repeat split.
    apply Permutation_Type_cons; [ reflexivity | assumption ].
  + inversion Heq.
    cbn in HP; rewrite H1, app_comm_cons in HP.
    apply Permutation_Type_cons_app_inv in HP.
    decomp_map_inf H1; subst; cbn in HP.
    replace (mell2ll f :: map mell2ll l4 ++ map mell2ll l6)
      with (map mell2ll ((f :: l4) ++ l6))
      in HP by (list_simpl; reflexivity).
    apply IHl1 in HP.
    destruct HP as ((l1' & l2') & (Heq1 & Heq2) & HP).
    cbn in Heq1, Heq2, H1, HP; subst.
    destruct x; inversion H1.
    symmetry in Heq2; decomp_map_inf Heq2; subst.
    exists (x :: l1', x0 :: l1 ++ x :: l2); repeat split.
    * list_simpl; reflexivity.
    * rewrite app_comm_cons.
      apply Permutation_Type_cons_app; assumption.
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
From Yalla Require ll_prop.

Definition mell_fragment A := exists B, A = mell2ll B.

Lemma mell_is_fragment : ll_prop.fragment mell_fragment.
Proof.
intros A HfA B Hsf.
induction Hsf;
  try (apply IHHsf;
       destruct HfA as [B0 HfA] ;
       destruct B0; inversion HfA; subst;
       eexists; reflexivity).
assumption.
Qed.
*)

(** cut / axioms / pmix / permutation *)
Definition pfrag_mell := @ll_def.mk_pfrag atom  false ll_def.NoAxioms (fun n => false) true.
(*                                        atoms cut   axioms                           perm  *)


(** ** 5. prove equivalence of proof predicates *)

Lemma mell2mellfrag m : mell m -> inhabited (ll_def.ll pfrag_mell (map mell2ll (elts m))).
Proof.
intros pi; induction pi; simpl; rewrite ? map_app;
  try (destruct IHpi as [IHpi]); try (destruct IHpi1 as [IHpi1]); try (destruct IHpi2 as [IHpi2]);
  constructor.
- apply (ll_def.ex_r (map mell2ll (covar X :: var X :: nil))).
  + apply ll_def.ax_r.
  + symmetry.
    destruct (Nat.leb
         (compose (compose nattree2nat
                                         (fun A => fmformulas.form2nattree A)) mell2ll (covar X))
         (compose (compose nattree2nat
                                         (fun A => fmformulas.form2nattree A)) mell2ll (var X))).
    * reflexivity.
    * apply Permutation_Type_swap.
- apply ll_def.one_r.
- eapply ll_def.ex_r.
  + apply ll_def.bot_r; eassumption.
  + change (formulas.bot :: map mell2ll (elts m))
      with (map mell2ll (bot :: elts m)).
    apply Permutation_Type_map.
    rewrite <- (@insert_add border_formula).
    assert (proj1_sig (fmslist_add bot m) = elts (add bot m)) 
      as Helt by reflexivity.
    rewrite Helt.
    symmetry; apply elts_add.
- eapply ll_def.ex_r.
  + apply ll_def.tens_r.
    * assert (Helt := Permutation_Type_map mell2ll (elts_add A m1)).
      apply (ll_def.ex_r _ _ IHpi1) in Helt.
      cbn in Helt; eassumption.
    * assert (Helt := Permutation_Type_map mell2ll (elts_add B m2)).
      apply (ll_def.ex_r _ _ IHpi2) in Helt.
      cbn in Helt; eassumption.
  + rewrite <- map_app.
    change (formulas.tens (mell2ll A) (mell2ll B)
              :: map mell2ll (proj1_sig m2 ++ proj1_sig m1))
      with (map mell2ll (tens A B :: elts m2 ++ elts m1)).
    apply Permutation_Type_map.
    rewrite <- (@insert_add border_formula).
    assert (proj1_sig (fmslist_add (tens A B) (sum m1 m2))
              = elts (add (tens A B) (sum m1 m2)))
      as Helt by reflexivity.
    rewrite Helt.
    etransitivity; [ apply Permutation_Type_cons;
                      [ reflexivity | apply Permutation_Type_app_comm ] | ].
    etransitivity; [ apply Permutation_Type_cons;
                      [ reflexivity | symmetry; apply elts_sum ] | ].
    symmetry; apply elts_add.
- eapply ll_def.ex_r.
  + apply ll_def.parr_r.
    assert (Permutation_Type (elts (add A (add B m))) (A :: B :: elts m))
      as Helt.
    { etransitivity; [ apply elts_add | ].
      apply Permutation_Type_cons, elts_add; reflexivity. }
    apply (Permutation_Type_map mell2ll) in Helt.
    apply (ll_def.ex_r _ _ IHpi) in Helt.
    cbn in Helt; eassumption.
  + change (formulas.parr (mell2ll A) (mell2ll B) :: map mell2ll (proj1_sig m))
      with (map mell2ll (parr A B :: elts m)).
    apply Permutation_Type_map.
    rewrite <- (@insert_add border_formula).
    assert (proj1_sig (fmslist_add (parr A B) m) = elts (add (parr A B) m)) 
      as Helt by reflexivity.
    rewrite Helt.
    symmetry; apply elts_add.
- eapply ll_def.ex_r.
  + apply ll_def.oc_r.
    assert (Permutation_Type (elts (add A (fmmap wn m))) (A :: map wn (elts m)))
      as Helt.
    { etransitivity; [ apply elts_add | ].
      apply Permutation_Type_cons, elts_fmmap; reflexivity. }
    apply (Permutation_Type_map  mell2ll) in Helt.
    apply (ll_def.ex_r _ _ IHpi) in Helt.
    eapply ll_def.ex_r; [ apply Helt | ].
    cbn.
    apply Permutation_Type_cons; [ reflexivity | ].
    rewrite mell2ll_map_wn.
    apply Permutation_Type_map; reflexivity.
  + rewrite <- mell2ll_map_wn.
    change (formulas.oc (mell2ll A) :: map mell2ll (map wn (proj1_sig m)))
      with (map mell2ll (oc A :: map wn (elts m))).
    apply Permutation_Type_map.
    rewrite <- (@insert_add border_formula).
    assert (proj1_sig (fmslist_add (oc A) (fmmap wn m))
              = elts (add (oc A) (fmmap wn m)))
      as Helt by reflexivity.
    rewrite Helt.
    symmetry; etransitivity; [ apply elts_add | ].
    apply Permutation_Type_cons, elts_fmmap; reflexivity.
- eapply ll_def.ex_r.
  + apply ll_def.de_r.
    assert (Helt := Permutation_Type_map mell2ll (elts_add A m)).
    apply (ll_def.ex_r _ _ IHpi) in Helt.
    cbn in Helt; eassumption.
  + change (formulas.wn (mell2ll A) :: map mell2ll (proj1_sig m))
      with (map mell2ll (wn A :: elts m)).
    apply Permutation_Type_map.
    rewrite <- (@insert_add border_formula).
    assert (proj1_sig (fmslist_add (wn A) m) = elts (add (wn A) m)) 
      as Helt by reflexivity.
    rewrite Helt.
    symmetry; apply elts_add.
- eapply ll_def.ex_r.
  + apply (ll_def.wk_r (mell2ll A)); eassumption.
  + change (formulas.wn (mell2ll A) :: map mell2ll (elts m))
      with (map mell2ll (wn A :: elts m)).
    apply Permutation_Type_map.
    rewrite <- (@insert_add border_formula).
    assert (proj1_sig (fmslist_add (wn A) m) = elts (add (wn A) m)) 
      as Helt by reflexivity.
    rewrite Helt.
    symmetry; apply elts_add.
- eapply ll_def.ex_r.
  + apply ll_def.co_r.
    cbn.
    assert (Permutation_Type (elts (add (wn A) (add (wn A) m)))
                             (wn A :: wn A :: elts m))
      as Helt.
    { etransitivity; [ apply elts_add | ].
      apply Permutation_Type_cons, elts_add; reflexivity. }
    apply (Permutation_Type_map mell2ll) in Helt.
    apply (ll_def.ex_r _ _ IHpi) in Helt.
    cbn in Helt; eassumption.
  + change (formulas.wn (mell2ll A) :: map mell2ll (proj1_sig m))
      with (map mell2ll (wn A :: elts m)).
    apply Permutation_Type_map.
    rewrite <- (@insert_add border_formula).
    assert (proj1_sig (fmslist_add (wn A) m) = elts (add (wn A) m)) 
      as Helt by reflexivity.
    rewrite Helt.
    symmetry; apply elts_add.
Qed.

Lemma mellfrag2mell m : ll_def.ll pfrag_mell (map mell2ll (elts m)) -> mell m.
Proof.
intros pi.
remember (map mell2ll (elts m)) as l.
assert (Permutation_Type l (map mell2ll (elts m))) as HP by now subst.
clear Heql.
induction pi in m, HP |- *; subst;
  try (now inversion f);
  try (now (apply Permutation_Type_image in HP as [Z Heq];
            destruct Z; inversion Heq)).
- apply Permutation_Type_length_2_inv in HP as [HP | HP]; decomp_map HP; subst.
  + destruct l1; inversion HP4.
    destruct x; inversion HP1; subst.
    destruct x0; inversion HP3; subst.
    apply (f_equal (fold_right add empty)) in HP.
    rewrite elts_retract in HP; subst.
    apply ax_r.
  + destruct l1; inversion HP4.
    destruct x; inversion HP1; subst.
    destruct x0; inversion HP3; subst.
    apply (f_equal (fold_right add empty)) in HP.
    rewrite elts_retract in HP; subst.
    cbn.
    assert (add (var X) (add (covar X) empty)
          = add (covar X) (add (var X) empty))
      as Hswap by apply add_swap.
    unfold add in Hswap.
    cbn in Hswap.
    rewrite Hswap.
    apply ax_r.
- apply IHpi.
  cbn in p.
  etransitivity; eassumption.
- apply IHpi.
  etransitivity; [ | eassumption ].
  apply Permutation_Type_app_head,  Permutation_Type_app_tail, Permutation_Type_map; assumption.
- apply Permutation_Type_length_1_inv in HP.
  remember (elts m) as l.
  destruct l; inversion HP.
  destruct l; inversion H1.
  destruct f; inversion H0; subst.
  apply (f_equal (fold_right add empty)) in Heql.
  rewrite elts_retract in Heql; subst.
  apply one_r.
- symmetry in HP.
  assert (HP2 := HP).
  apply Permutation_Type_vs_cons_inv in HP.
  destruct HP as ((l1 & l2) & HP).
  decomp_map HP; subst.
  destruct x; inversion HP4; subst.
  apply (f_equal list2fm) in HP.
  rewrite list2fm_retract in HP; subst.
  rewrite list2fm_elt.
  apply bot_r, IHpi.
  etransitivity ; [ | apply elts_fmmap ].
  unfold fmmap.
  etransitivity; [ | symmetry; apply elts_perm ].
  etransitivity; [ | symmetry; apply Permutation_Type_map, elts_perm ].
  eapply Permutation_Type_trans in HP2; [ | apply elts_fmmap ].
  unfold fmmap in HP2.
  eapply Permutation_Type_trans in HP2; [ | symmetry; apply elts_perm ].
  eapply Permutation_Type_trans in HP2;
   [ | symmetry; apply Permutation_Type_map, elts_perm ].
  list_simpl in HP2.
  symmetry in HP2.
  apply Permutation_Type_cons_app_inv in HP2.
  rewrite map_app; assumption.
- symmetry in HP.
  assert (HP2 := HP).
  apply Permutation_Type_vs_cons_inv in HP.
  destruct HP as ((l3 & l4) & HP).
  decomp_map HP; subst.
  destruct x; inversion HP4; subst.
  apply (f_equal list2fm) in HP.
  rewrite list2fm_retract in HP; subst.
  eapply Permutation_Type_trans in HP2; [ | apply elts_fmmap ].
  unfold fmmap in HP2.
  eapply Permutation_Type_trans in HP2; [ | symmetry; apply elts_perm ].
  eapply Permutation_Type_trans in HP2;
    [ | symmetry ; apply Permutation_Type_map; apply elts_perm ].
  list_simpl in HP2.
  symmetry in HP2.
  apply Permutation_Type_cons_app_inv in HP2.
  rewrite <- map_app in HP2.
  apply Permutation_Type_map_inv in HP2.
  destruct HP2 as [l Heq HP].
  rewrite list2fm_elt.
  eapply list2fm_perm in HP; cbn in HP.
  rewrite HP.
  symmetry in Heq; decomp_map Heq; subst.
  rewrite list2fm_app, sum_comm.
  apply tens_r.
  + apply IHpi1.
    eapply Permutation_Type_trans; [ | apply elts_fmmap ].
    unfold fmmap.
    eapply Permutation_Type_trans; [ | symmetry ; apply elts_perm ].
    change (mell2ll x1 :: map mell2ll l7) with (map mell2ll (x1 :: l7)).
    apply Permutation_Type_map.
    symmetry; etransitivity.
    * apply elts_add.
    * apply Permutation_Type_cons, elts_perm; reflexivity.
  + apply IHpi2.
    eapply Permutation_Type_trans; [ | apply elts_fmmap ].
    unfold fmmap.
    eapply Permutation_Type_trans; [ | symmetry; apply elts_perm ].
    change (mell2ll x2 :: map mell2ll l4) with (map mell2ll (x2 :: l4)).
    apply Permutation_Type_map.
    symmetry; etransitivity.
    * apply elts_add.
    * apply Permutation_Type_cons, elts_perm; reflexivity.
- symmetry in HP.
  assert (HP2 := HP).
  apply Permutation_Type_vs_cons_inv in HP.
  destruct HP as ((l1 & l2) & HP).
  decomp_map HP; subst.
  destruct x; inversion HP4; subst.
  apply (f_equal list2fm) in HP.
  rewrite list2fm_retract in HP; subst.
  rewrite list2fm_elt.
  apply parr_r, IHpi.
  etransitivity; [ | apply elts_fmmap ].
  unfold fmmap.
  etransitivity; [ | symmetry; apply elts_perm ].
  rewrite <- 2 list2fm_elt.
  etransitivity; [ | symmetry; apply Permutation_Type_map, elts_perm ].
  eapply Permutation_Type_trans in HP2; [ | apply elts_fmmap ].
  unfold fmmap in HP2.
  eapply Permutation_Type_trans in HP2; [ | symmetry; apply elts_perm ].
  eapply Permutation_Type_trans in HP2; [ | symmetry; apply Permutation_Type_map, elts_perm ].
  list_simpl in HP2.
  symmetry in HP2.
  apply Permutation_Type_cons_app_inv in HP2.
  list_simpl.
  apply Permutation_Type_cons_app, Permutation_Type_cons_app; assumption.
- symmetry in HP.
  assert (HP2 := HP).
  apply Permutation_Type_vs_cons_inv in HP.
  destruct HP as ((l1 & l2) & HP).
  decomp_map HP; subst.
  destruct x; inversion HP4; subst.
  apply (f_equal list2fm) in HP.
  rewrite list2fm_retract in HP; subst.
  rewrite list2fm_elt.
  eapply Permutation_Type_trans in HP2; [ | apply elts_fmmap ].
  unfold fmmap in HP2.
  eapply Permutation_Type_trans in HP2; [ | symmetry; apply elts_perm ].
  eapply Permutation_Type_trans in HP2; [ | symmetry; apply Permutation_Type_map, elts_perm ].
  list_simpl in HP2.
  symmetry in HP2.
  apply Permutation_Type_cons_app_inv in HP2.
  rewrite <- map_app in HP2.
  apply mell2ll_map_wn_inv in HP2.
  destruct HP2 as ((l1' & l2') & (Heq1 & Heq2) & HP); subst.
  rewrite Heq2.
  erewrite list2fm_map.
  apply oc_r, IHpi.
  etransitivity; [ | apply elts_fmmap ].
  unfold fmmap.
  etransitivity; [ | symmetry; apply elts_perm ].
  etransitivity; [ | symmetry; apply Permutation_Type_map, elts_add ].
  simpl; apply Permutation_Type_cons; [ reflexivity | ].
  rewrite <- mell2ll_map_wn.
  apply Permutation_Type_map.
  change (proj1_sig (list2fm (map wn (proj1_sig (list2fm l2')))))
    with (elts (list2fm (map wn (elts (list2fm l2'))))).
  etransitivity; [ | symmetry; apply elts_perm ].
  apply Permutation_Type_map.
  etransitivity; [ | symmetry; apply elts_perm ]; assumption.
- symmetry in HP.
  assert (HP2 := HP).
  apply Permutation_Type_vs_cons_inv in HP.
  destruct HP as ((l1 & l2) & HP).
  decomp_map HP; subst.
  destruct x; inversion HP4; subst.
  apply (f_equal list2fm) in HP.
  rewrite list2fm_retract in HP; subst.
  rewrite list2fm_elt.
  apply de_r, IHpi.
  etransitivity; [ | apply elts_fmmap ].
  unfold fmmap.
  etransitivity; [ | symmetry; apply elts_perm ].
  rewrite <- list2fm_elt.
  etransitivity ; [ | symmetry; apply Permutation_Type_map, elts_perm ].
  eapply Permutation_Type_trans in HP2; [ | apply elts_fmmap ].
  unfold fmmap in HP2.
  eapply Permutation_Type_trans in HP2; [ | symmetry; apply elts_perm ].
  eapply Permutation_Type_trans in HP2; [ | symmetry; apply Permutation_Type_map, elts_perm ].
  list_simpl in HP2.
  symmetry in HP2.
  apply Permutation_Type_cons_app_inv in HP2.
  list_simpl.
  apply Permutation_Type_cons_app; assumption.
- symmetry in HP.
  assert (HP2 := HP).
  apply Permutation_Type_vs_cons_inv in HP.
  destruct HP as ((l1 & l2) & HP).
  decomp_map HP; subst.
  destruct x; inversion HP4; subst.
  apply (f_equal list2fm) in HP.
  rewrite list2fm_retract in HP; subst.
  rewrite list2fm_elt.
  apply wk_r, IHpi.
  etransitivity; [ | apply elts_fmmap ].
  unfold fmmap.
  etransitivity; [ | symmetry; apply elts_perm ].
  etransitivity; [ | symmetry; apply Permutation_Type_map, elts_perm ].
  eapply Permutation_Type_trans in HP2; [ | apply elts_fmmap ].
  unfold fmmap in HP2.
  eapply Permutation_Type_trans in HP2; [ | symmetry; apply elts_perm ].
  eapply Permutation_Type_trans in HP2; [ | symmetry; apply Permutation_Type_map, elts_perm ].
  list_simpl in HP2.
  symmetry in HP2.
  apply Permutation_Type_cons_app_inv in HP2.
  rewrite map_app; assumption.
- symmetry in HP.
  assert (HP2 := HP).
  apply Permutation_Type_vs_cons_inv in HP.
  destruct HP as ((l1 & l2) & HP).
  decomp_map HP; subst.
  destruct x; inversion HP4; subst.
  apply (f_equal list2fm) in HP.
  rewrite list2fm_retract in HP; subst.
  rewrite list2fm_elt.
  apply co_r, IHpi.
  etransitivity; [ | apply elts_fmmap ].
  unfold fmmap.
  etransitivity; [ | symmetry; apply elts_perm ].
  rewrite <- 2 list2fm_elt.
  etransitivity; [ | symmetry; apply Permutation_Type_map, elts_perm ].
  eapply Permutation_Type_trans in HP2; [ | apply elts_fmmap ].
  unfold fmmap in HP2.
  eapply Permutation_Type_trans in HP2; [ | symmetry; apply elts_perm ].
  eapply Permutation_Type_trans in HP2; [ | symmetry; apply Permutation_Type_map, elts_perm ].
  list_simpl in HP2.
  list_simpl.
  apply Permutation_Type_cons_app.
  symmetry.
  apply HP2.
- inversion a.
Qed.


(** ** 6. import properties *)

(** *** axiom expansion *)

Lemma ax_gen_r A : mell (add (dual A) (add A empty)).
Proof.
apply mellfrag2mell.
eapply ll_def.ex_r ; [ apply (ll_def.ax_exp (mell2ll (dual A))) | ].
rewrite <- mell2ll_dual, formulas.bidual, mell2ll_dual.
change (mell2ll (dual A) :: mell2ll A :: nil)
  with (map mell2ll (dual A :: A :: nil)).
apply Permutation_Type_map.
etransitivity; [ | symmetry; apply elts_add ]; reflexivity.
Qed.


(** *** cut admissibility *)

Lemma cut_r A m1 m2 : mell (add A m1) -> mell (add (dual A) m2) -> mell (sum m1 m2).
Proof.
intros pi1%mell2mellfrag pi2%mell2mellfrag.
destruct pi1 as [pi1]; destruct pi2 as [pi2].
apply mellfrag2mell.
eapply ll_def.ex_r; [ | apply Permutation_Type_map; symmetry; apply elts_sum ].
rewrite map_app.
eapply ll_cut.cut_r_axfree.
- intros a; destruct a.
- assert (Permutation_Type (map mell2ll (elts (add (dual A) m2)))
                           (map mell2ll (dual A :: elts m2)))
    as Helt2 by apply Permutation_Type_map, elts_add.
  cbn in Helt2; rewrite <- mell2ll_dual in Helt2.
  eapply ll_def.ex_r; [ | apply Helt2 ]; assumption.
- assert (Permutation_Type (map mell2ll (elts (add A m1)))
                           (map mell2ll (A :: elts m1)))
    as Helt by apply Permutation_Type_map, elts_add.
  eapply ll_def.ex_r; [ | apply Helt ]; eassumption.
Qed.

End Atoms.
