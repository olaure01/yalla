(* mell2 example file for yalla library *)



(** * Example of a concrete use of the yalla library: unit-free MELL with mix2 rule *)

Require Import CMorphisms.

Require Import funtheory.
Require Import List_more.
Require Import Permutation_Type_more.
Require Import Permutation_Type_solve.


(** ** 0. load the [yalla] library *)

Require ll_cut.


(** ** 1. define formulas *)

Inductive formula : Set :=
| var : formulas.Atom -> formula
| covar : formulas.Atom -> formula
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

Lemma mell2ll_dual : forall A, formulas.dual (mell2ll A) = mell2ll (dual A).
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
  map formulas.wn l1 = map mell2ll l2 ->
    { l2' | l2 = map wn l2' /\ l1 = map mell2ll l2' }.
Proof with try assumption ; try reflexivity.
induction l1 ; intros l2 Heq ;
  destruct l2 ; inversion Heq...
- exists nil ; split...
- apply IHl1 in H1.
  destruct f ; inversion H0 ; subst.
  destruct H1 as (l2' & Heq1 & H1) ; subst.
  exists (f :: l2') ; split...
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

#[export] Instance mell_perm : Proper ((@Permutation_Type _) ==> Basics.arrow) mell.
Proof.
intros l1 l2 HP pi.
eapply ex_r ; eassumption.
Qed.

(** ** 4. characterize corresponding [ll] fragment *)

(** cut / axioms / mix0 / mix2 / permutation *)
Definition pfrag_mell := ll_def.mk_pfrag false ll_def.NoAxioms false true true.
(*                                       cut   axioms          mix0  mix2 perm  *)


(** ** 5. prove equivalence of proof predicates *)

Lemma mell2mellfrag : forall l, mell l -> ll_def.ll pfrag_mell (map mell2ll l).
Proof with try eassumption ; try reflexivity. 
intros l pi.
induction pi ; try (now constructor) ; try rewrite map_app.
- eapply ll_def.ex_r...
  apply Permutation_Type_map...
- apply ll_def.mix2_r...
- eapply ll_def.ex_r.
  + apply (ll_def.tens_r _ _ _ _ _ IHpi1 IHpi2).
  + simpl ; Permutation_Type_solve.
- simpl ; rewrite mell2ll_map_wn.
  apply ll_def.oc_r.
  rewrite <- mell2ll_map_wn...
Qed.

Lemma mellfrag2mell : forall l, ll_def.ll pfrag_mell (map mell2ll l) -> mell l.
Proof with try eassumption ; try reflexivity.
intros l pi.
remember (map mell2ll l) as l0.
revert l Heql0 ; induction pi ; intros l' Heql0 ; subst ;
  try (destruct l' ; inversion Heql0 ;
       destruct f ; inversion H0 ; fail).
- symmetry in Heql0; decomp_map_inf Heql0 ; subst.
  destruct l1 ; inversion Heql4.
  destruct x ; inversion Heql2.
  destruct x0 ; inversion Heql0.
  subst ; subst.
  apply ax_r.
- simpl in p.
  apply Permutation_Type_map_inv in p.
  destruct p as [l'' Heq HP].
  apply Permutation_Type_sym in HP.
  eapply ex_r...
  apply IHpi...
- symmetry in Heql0; decomp_map_inf Heql0 ; subst; symmetry in Heql0.
  simpl in Heql0 ; apply mell2ll_map_wn_inv in Heql0 ;
    destruct Heql0 as (l & ? & ?) ; subst.
  apply Permutation_Type_map_inv in p ; destruct p as [l' Heq HP] ; subst.
  eapply ex_r ;
    [ apply IHpi ; rewrite <- mell2ll_map_wn ; rewrite <- ? map_app | ]...
  apply Permutation_Type_app_head.
  apply Permutation_Type_app_tail.
  symmetry in HP ; apply Permutation_Type_map...
- inversion f.
- symmetry in Heql0; decomp_map_inf Heql0 ; subst.
  apply mix_r.
  + apply IHpi2...
  + apply IHpi1...
- symmetry in Heql0; decomp_map_inf Heql0 ; subst.
  destruct x ; inversion Heql2 ; subst.
  eapply ex_r.
  apply tens_r.
  + apply IHpi1...
  + apply IHpi2...
  + Permutation_Type_solve.
- destruct l' ; inversion Heql0.
  destruct f ; inversion H0 ; subst.
  apply parr_r.
  apply IHpi...
- destruct l' ; inversion Heql0.
  destruct f ; inversion H0 ; subst.
  apply mell2ll_map_wn_inv in H1.
  destruct H1 as (l'' & Heq1 & Heq2) ; subst.
  apply oc_r.
  apply IHpi.
  simpl ; rewrite mell2ll_map_wn...
- destruct l' ; inversion Heql0.
  destruct f ; inversion H0 ; subst.
  apply de_r.
  apply IHpi...
- destruct l' ; inversion Heql0.
  destruct f ; inversion H0 ; subst.
  apply wk_r.
  apply IHpi...
- destruct l' ; inversion Heql0.
  destruct f ; inversion H0 ; subst.
  apply co_r.
  apply IHpi...
- inversion f.
- destruct a.
Qed.


(** ** 6. import properties *)

(** *** axiom expansion *)

Lemma ax_gen_r : forall A, mell (dual A :: A :: nil).
Proof.
intro A.
apply mellfrag2mell.
simpl ; rewrite <- mell2ll_dual.
eapply ll_def.ex_r ; [ apply ll_def.ax_exp | apply Permutation_Type_swap ].
Qed.

(** *** cut admissibility *)

Lemma cut_r : forall A l1 l2, 
  mell (A :: l1) -> mell (dual A :: l2) -> mell (l1 ++ l2).
Proof with try eassumption.
intros A l1 l2 pi1 pi2.
apply mellfrag2mell.
rewrite map_app.
apply mell2mellfrag in pi1.
apply mell2mellfrag in pi2.
simpl in pi2 ; rewrite <- mell2ll_dual in pi2.
eapply ll_cut.cut_r_axfree...
intros a ; destruct a.
Qed.
