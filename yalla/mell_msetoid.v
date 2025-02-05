(** * Example of a concrete use of the yalla library: multi-set based MELL up to an equivalence relation *)

From Coq Require Import CMorphisms.
From OLlibs Require Import funtheory dectype fmsetoidlist_Type List_more Permutation_Type_more.


(** ** 0. load the [ll] library *)

From Yalla Require ll_cut.

Set Default Proof Using "Type".
Set Implicit Arguments.


Section Atoms.

Context {atom : DecType}.

(** ** 1. define formulas *)

Inductive formula :=
| var (_ : atom) | covar (_ : atom)
| one | bot
| tens (_ _ : formula) | parr (_ _ : formula)
| oc (_ : formula) | wn (_ : formula).

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
intro A. induction A; intros [] [=];
  try apply IHA in H0; try apply IHA1 in H0; try apply IHA2 in H1; subst; reflexivity.
Qed.

Lemma mell2ll_dual A : formulas.dual (mell2ll A) = mell2ll (dual A).
Proof. induction A; cbn; rewrite ? IHA, ? IHA1, ? IHA2; reflexivity. Qed.

Lemma mell2ll_map_wn l : map mell2ll (map wn l) = map formulas.wn (map mell2ll l).
Proof. induction l as [ | a l IHl]; [ | cbn; rewrite IHl ]; reflexivity. Qed.

Lemma mell2ll_map_wn_inv l1 l2 : map formulas.wn l1 = map mell2ll l2 ->
  exists l2', l2 = map wn l2' /\ l1 = map mell2ll l2'.
Proof.
induction l1 in l2 |-*; destruct l2 as [|f l2]; intros [=].
- exists nil. split; reflexivity.
- apply IHl1 in H1.
  destruct f; destr_eq H0. subst.
  destruct H1 as [l2' [-> ->]].
  exists (f :: l2'). split; reflexivity.
Qed.


(** *** 2bis. sequents *)

Instance fmsetoid_formula : FinMultisetoid (list _) formula := FMoidConstr_list formula.


(** ** 3. define proofs *)

Inductive mell : list formula -> Prop :=
| ax_r X : mell (add (covar X) (add (var X) empty))
| ex_r m1 m2 : mell m1 -> meq m1 m2 -> mell m2
| one_r : mell (add one empty)
| bot_r l : mell l -> mell (add bot l)
| tens_r A B l1 l2 : mell (add A l1) -> mell (add B l2) -> mell (add (tens A B) (sum l1 l2))
| parr_r A B l : mell (add A (add B l)) -> mell (add (parr A B) l)
| oc_r A l : mell (add A (fmmap wn l)) -> mell (add (oc A) (fmmap wn l))
| de_r A l : mell (add A l) -> mell (add (wn A) l)
| wk_r A l : mell l -> mell (add (wn A) l)
| co_r A l : mell (add (wn A) (add (wn A) l)) -> mell (add (wn A) l).

Instance mell_meq : Proper (meq ==> iff) mell.
Proof. intros m1 m2 Heq. split; intro; [ | symmetry in Heq ]; apply ex_r in Heq; assumption. Qed.


(** ** 4. characterize corresponding [ll] fragment *)

(*
From Yalla Require ll_prop.

Definition mell_fragment A := exists B, A = mell2ll B.

Lemma mell_is_fragment : ll_prop.fragment mell_fragment.
Proof.
intros A HfA B Hsf.
induction Hsf;
  try (apply IHHsf;
       destruct HfA as [B0 HfA];
       destruct B0; destr_eq HfA; subst;
       eexists; reflexivity).
assumption.
Qed.
*)

(** cut / axioms / pmix / permutation *)
Definition pfrag_mell :=  @ll_def.mk_pfrag atom  ll_def.pcut_none ll_def.NoAxioms ll_def.pmix_none true.
(*                                         atoms cut              axioms          mix              perm  *)


(** ** 5. prove equivalence of proof predicates *)

Lemma mell2mellfrag m : mell m -> inhabited (ll_def.ll pfrag_mell (map mell2ll (elts m))).
Proof.
intro pi. induction pi;
  try destruct IHpi as [IHpi]; try destruct IHpi1 as [IHpi1]; try destruct IHpi2 as [IHpi2];
  constructor; cbn; rewrite ? map_app;
  try now (constructor; eassumption).
- apply meq_perm in X.
  eapply ll_def.ex_r; [ eassumption | ].
  apply Permutation_Type_map; assumption.
- eapply ll_def.ex_r.
  + apply ll_def.tens_r.
    * assert (Helt := Permutation_Type_map mell2ll (elts_add A l1)).
      apply (ll_def.ex_r _ _ IHpi1) in Helt.
      cbn in Helt; eassumption.
    * assert (Helt := Permutation_Type_map mell2ll (elts_add B l2)).
      apply (ll_def.ex_r _ _ IHpi2) in Helt.
      cbn in Helt; eassumption.
  + apply Permutation_Type_cons; [ reflexivity | ].
    rewrite <- map_app.
    apply Permutation_Type_map.
    unfold sum, list2fm.
    cbn; rewrite fold_id.
    apply Permutation_Type_app_comm.
- unfold list2fm. rewrite fold_id, mell2ll_map_wn.
  unfold elts, add, fmmap, list2fm in IHpi. cbn in IHpi.
  rewrite fold_id, mell2ll_map_wn in IHpi.
  apply ll_def.oc_r. assumption.
Qed.

Lemma mellfrag2mell m : ll_def.ll pfrag_mell (map mell2ll (elts m)) -> mell m.
Proof.
intros pi. remember (map mell2ll (elts m)) as l. induction pi in m, Heql |- *;
  try (destruct m; destr_eq Heql; destruct f; destr_eq Heql; subst; constructor; apply IHpi; reflexivity);
  try discriminate f.
- destruct m; destr_eq Heql. destruct m; destr_eq H. symmetry in H0. rewrite (map_eq_nil _ _ H0).
  destruct f; destr_eq Heql. destruct f0; destr_eq H. subst.
  apply ax_r.
- subst. cbn in p. apply Permutation_Type_map_inv in p as [l' -> HP].
  eapply ex_r.
  + apply IHpi. reflexivity.
  + symmetry. assumption.
- remember (map formulas.wn lw') as l0. decomp_map Heql eqn:Heq.
  symmetry in Heq. apply mell2ll_map_wn_inv in Heq as [l [-> ->]].
  apply Permutation_Type_map_inv in p as [l' -> HP].
  cbn in Heql. unfold id in Heql. subst.
  eapply ex_r; [ apply IHpi; rewrite <- mell2ll_map_wn, <- ? map_app; reflexivity | ].
  symmetry in HP.
  apply Permutation_Type_app_head, Permutation_Type_app_tail, Permutation_Type_map. assumption.
- destruct m; destr_eq Heql. symmetry in H. rewrite (map_eq_nil _ _ H).
  destruct f; destr_eq Heql.
  apply one_r.
- destruct m; destr_eq Heql.
  destruct f; destr_eq Heql. subst.
  assert (Heq := H).
  symmetry in H. decomp_map H. subst.
  apply (@ex_r (add (tens f1 f2) (sum l1 l2))).
  + apply tens_r; [ apply IHpi1 | apply IHpi2 ]; reflexivity.
  + unfold sum, list2fm, add; cbn.
    apply Permutation_Type_cons; [ reflexivity | ].
    rewrite fold_id. apply Permutation_Type_app_comm.
- destruct m; destr_eq Heql.
  destruct f; destr_eq Heql. subst.
  apply mell2ll_map_wn_inv in H as [m' [-> ->]].
  replace (oc f :: map wn m')
     with (add (oc f) (fmmap wn m')) by (unfold fmmap, list2fm; cbn; rewrite fold_id; reflexivity).
  apply oc_r, IHpi.
  cbn. unfold list2fm. rewrite fold_id, mell2ll_map_wn. reflexivity.
- destruct a.
Qed.


(** ** 6. import properties *)

(** *** axiom expansion *)

Lemma ax_gen_r A : mell (add (dual A) (add A empty)).
Proof.
apply mellfrag2mell.
eapply ll_def.ex_r; [ apply ll_def.ax_exp | ].
rewrite mell2ll_dual. apply Permutation_Type_swap.
Qed.


(** *** cut admissibility *)

Lemma cut_r A m1 m2 : mell (add A m1) -> mell (add (dual A) m2) -> mell (sum m1 m2).
Proof.
intros [pi1]%mell2mellfrag [pi2]%mell2mellfrag. apply mellfrag2mell.
eapply ll_def.ex_r; [ | apply Permutation_Type_map; symmetry; apply elts_sum ].
cbn in pi2. rewrite <- mell2ll_dual in pi2. rewrite map_app.
refine (ll_cut.cut_r_axfree _ pi2 pi1).
intros [].
Qed.

End Atoms.
