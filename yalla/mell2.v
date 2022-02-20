(* mell2 example file for yalla library *)

(** * Example of a concrete use of the yalla library: unit-free MELL with mix2 rule *)

From Coq Require Import CMorphisms.
From OLlibs Require Import funtheory dectype List_more Permutation_Type_more Dependent_Forall_Type.


(** ** 0. load the [yalla] library *)

From Yalla Require Import atoms.
From Yalla Require ll_cut.

Set Implicit Arguments.


Section Atoms.

Context {atom : DecType}.

(** ** 1. define formulas *)

Inductive formula :=
| var : atom -> formula
| covar : atom -> formula
| tens : formula -> formula -> formula
| parr : formula -> formula -> formula
| oc : formula -> formula
| wn : formula -> formula.

Fixpoint dual A :=
match A with
| var x     => covar x
| covar x   => var x
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
| tens A B => formulas.tens (mell2ll A) (mell2ll B)
| parr A B => formulas.parr (mell2ll A) (mell2ll B)
| oc A     => formulas.oc (mell2ll A)
| wn A     => formulas.wn (mell2ll A)
end.

Lemma mell2ll_inj : injective mell2ll.
Proof.
intros A.
induction A ; intros B Heq ;
  destruct B ; inversion Heq ;
  try apply IHA in H0 ;
  try apply IHA1 in H0 ;
  try apply IHA2 in H1 ; subst ;
  reflexivity.
Qed.

Lemma mell2ll_dual A : formulas.dual (mell2ll A) = mell2ll (dual A).
Proof. induction A; cbn; rewrite ? IHA, ? IHA1, ? IHA2; reflexivity. Qed.

Lemma mell2ll_map_wn l :
  map mell2ll (map wn l) = map formulas.wn (map mell2ll l).
Proof. induction l; [ reflexivity | cbn; f_equal; apply IHl ]. Qed.

Lemma mell2ll_map_wn_inv l1 l2 :
  map formulas.wn l1 = map mell2ll l2 ->
    { l2' | l2 = map wn l2' /\ l1 = map mell2ll l2' }.
Proof.
induction l1 in l2 |- *; intros Heq; destruct l2 as [|f l2]; inversion Heq.
- exists nil; split; reflexivity.
- apply IHl1 in H1.
  destruct f; inversion H0; subst.
  destruct H1 as (l2' & Heq1 & H1); subst.
  exists (f :: l2'); split; reflexivity.
Qed.


(** ** 3. define proofs *)

Inductive mell : list formula -> Type :=
| ax_r : forall X, mell (covar X :: var X :: nil)
| ex_r : forall l1 l2, mell l1 ->
              Permutation_Type l1 l2 -> mell l2
| mix_r : forall l1 l2, mell l1 -> mell l2 ->
              mell (l1 ++ l2)
| tens_r : forall A B l1 l2,
              mell (A :: l1) -> mell (B :: l2) ->
              mell (tens A B :: l1 ++ l2)
| parr_r : forall A B l,
              mell (A :: B :: l) ->
              mell (parr A B :: l)
| oc_r : forall A l,
              mell (A :: map wn l) ->
              mell (oc A :: map wn l)
| de_r : forall A l,
              mell (A :: l) ->
              mell (wn A :: l)
| wk_r : forall A l,
              mell l ->
              mell (wn A :: l)
| co_r : forall A l,
              mell (wn A :: wn A :: l) ->
              mell (wn A :: l).

Instance mell_perm : Proper ((@Permutation_Type _) ==> arrow) mell.
Proof. intros l1 l2 HP pi; apply ex_r with l1; assumption. Qed.

(** ** 4. characterize corresponding [ll] fragment *)

(** cut / axioms / pmix / permutation *)
Definition pfrag_mell := @ll_def.mk_pfrag atom  false ll_def.NoAxioms ll_def.pmix2 true.
(*                                        atoms cut   axioms          mix          perm  *)


(** ** 5. prove equivalence of proof predicates *)

Lemma mell2mellfrag l : mell l -> ll_def.ll pfrag_mell (map mell2ll l).
Proof.
intros pi; induction pi; try (now constructor); rewrite ? map_app.
- eapply ll_def.ex_r; [ apply IHpi | ].
  apply Permutation_Type_map; assumption.
- replace (map mell2ll l1 ++ map mell2ll l2)
     with (concat (map mell2ll l1 :: map mell2ll l2 :: nil))
    by (cbn; rewrite app_nil_r; reflexivity).
  apply ll_def.mix_r; now repeat constructor.
- eapply ll_def.ex_r.
  + apply (ll_def.tens_r IHpi1 IHpi2).
  + cbn; rewrite map_app; apply Permutation_Type_cons, Permutation_Type_app_comm; reflexivity.
- cbn; rewrite mell2ll_map_wn.
  apply ll_def.oc_r.
  rewrite <- mell2ll_map_wn; assumption.
Qed.

Lemma mellfrag2mell l : ll_def.ll pfrag_mell (map mell2ll l) -> mell l.
Proof.
intros pi.
remember (map mell2ll l) as l0.
revert l Heql0; induction pi using ll_def.ll_nested_ind; intros l' Heql0; subst;
  try now (destruct l'; inversion Heql0; destruct f; inversion H0).
- symmetry in Heql0; decomp_map_inf Heql0; subst.
  destruct l1; inversion Heql4.
  destruct x; inversion Heql2.
  destruct x0; inversion Heql0.
  subst; subst.
  apply ax_r.
- cbn in p.
  apply Permutation_Type_map_inv in p as [l'' Heq HP].
  apply Permutation_Type_sym in HP.
  eapply ex_r, HP.
  apply (IHpi _ Heq).
- symmetry in Heql0; decomp_map_inf Heql0; subst; symmetry in Heql0.
  cbn in Heql0; apply mell2ll_map_wn_inv in Heql0 as (l & ? & ?); subst.
  apply Permutation_Type_map_inv in p as [l' Heq HP]; subst.
  eapply ex_r;
    [ apply IHpi; rewrite <- mell2ll_map_wn, <- ? map_app; reflexivity | ].
  apply Permutation_Type_app_head, Permutation_Type_app_tail.
  symmetry in HP; apply Permutation_Type_map; assumption.
- remember (length L) as n.
  destruct n; inversion eqpmix.
  destruct n; inversion eqpmix.
  destruct n; inversion eqpmix.
  destruct L; inversion Heqn.
  destruct L; inversion Heqn.
  destruct L; inversion Heqn.
  cbn in Heql0.
  symmetry in Heql0; decomp_map_inf Heql0; subst.
  cbn in *; clear H0 H1 H2 H3 Heqn eqpmix.
  destruct l5; inversion Heql4; rewrite app_nil_r; clear Heql4.
  apply mix_r.
  + destruct (In_Forall_inf_in (map mell2ll l2) PL); [ left; reflexivity | ].
    refine (ll_def.Dependent_Forall_inf_forall_formula _ _ X i _ eq_refl).
  + destruct (In_Forall_inf_in (map mell2ll l4) PL); [ right; left; reflexivity | ].
    refine (ll_def.Dependent_Forall_inf_forall_formula _ _ X i _ eq_refl).
- symmetry in Heql0; decomp_map_inf Heql0; subst.
  destruct x; inversion Heql2; subst.
  eapply ex_r; [ apply tens_r | ].
  + apply IHpi1; reflexivity.
  + apply IHpi2; reflexivity.
  + apply Permutation_Type_cons, Permutation_Type_app_comm; reflexivity.
- destruct l'; inversion Heql0.
  destruct f; inversion H0; subst.
  apply parr_r, IHpi; reflexivity.
- destruct l'; inversion Heql0.
  destruct f; inversion H0; subst.
  apply mell2ll_map_wn_inv in H1 as (l'' & Heq1 & Heq2); subst.
  apply oc_r, IHpi.
  cbn; rewrite mell2ll_map_wn; reflexivity.
- destruct l'; inversion Heql0.
  destruct f; inversion H0; subst.
  apply de_r, IHpi; reflexivity.
- destruct l'; inversion Heql0.
  destruct f; inversion H0; subst.
  apply wk_r, IHpi; reflexivity.
- destruct l'; inversion Heql0.
  destruct f; inversion H0; subst.
  apply co_r, IHpi; reflexivity.
- inversion f.
- destruct a.
Qed.


(** ** 6. import properties *)

(** *** axiom expansion *)

Lemma ax_gen_r A : mell (dual A :: A :: nil).
Proof.
apply mellfrag2mell.
cbn; rewrite <- mell2ll_dual.
eapply ll_def.ex_r; [ apply ll_def.ax_exp | apply Permutation_Type_swap ].
Qed.

(** *** cut admissibility *)

Lemma cut_r A l1 l2 :
  mell (A :: l1) -> mell (dual A :: l2) -> mell (l1 ++ l2).
Proof.
intros pi1 pi2.
apply mellfrag2mell.
rewrite map_app.
apply mell2mellfrag in pi1.
apply mell2mellfrag in pi2.
cbn in pi2; rewrite <- mell2ll_dual in pi2.
eapply ll_cut.cut_r_axfree; [ | eassumption | eassumption ].
intros a; destruct a.
Qed.

End Atoms.
