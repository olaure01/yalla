(* mell_msetoid example file for yalla library *)


(** * Example of a concrete use of the yalla library: multi-set based MELL up to an equivalence relation *)

Require Import CMorphisms.

Require Import Injective.
Require Import fmsetoidlist_Type.
Require Import List_more.
Require Import Permutation_Type_more.


(** ** 0. load the [ll] library *)

Require ll_cut.


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
    exists l2', l2 = map wn l2' /\ l1 = map mell2ll l2'.
Proof with try assumption ; try reflexivity.
induction l1 ; intros l2 Heq ;
  destruct l2 ; inversion Heq...
- exists nil ; split...
- apply IHl1 in H1.
  destruct f ; inversion H0 ; subst.
  destruct H1 as (l2' & Heq1 & H1) ; subst.
  exists (f :: l2') ; split...
Qed.


(** *** 2bis. sequents *)

Instance fmsetoid_formula : FinMultisetoid (list _) formula :=
  FMoidConstr_list formula.


(** ** 3. define proofs *)

Inductive mell : list formula -> Prop :=
| ax_r : forall X, mell (add (covar X) (add (var X) empty))
| ex_r : forall m1 m2, mell m1 -> meq m1 m2 -> mell m2
| one_r : mell (add one empty)
| bot_r : forall l, mell l -> mell (add bot l)
| tens_r : forall A B l1 l2,
              mell (add A l1) -> mell (add B l2) ->
              mell (add (tens A B) (sum l1 l2))
| parr_r : forall A B l,
             mell (add A (add B l)) ->
             mell (add (parr A B) l)
| oc_r : forall A l,
           mell (add A (fmmap wn l)) ->
           mell (add (oc A) (fmmap wn l))
| de_r : forall A l,
           mell (add A l) ->
           mell (add (wn A) l)
| wk_r : forall A l,
           mell l ->
           mell (add (wn A) l)
| co_r : forall A l,
           mell (add (wn A) (add (wn A) l)) ->
           mell (add (wn A) l).

Instance mell_meq : Proper (meq ==> iff) mell.
Proof.
intros m1 m2 Heq.
split ; intros Hmell.
- apply ex_r in Heq ; assumption.
- symmetry in Heq.
  apply ex_r in Heq ; assumption.
Qed.


(** ** 4. characterize corresponding [ll] fragment *)

(*
Definition mell_fragment A := exists B, A = mell2ll B.

Lemma mell_is_fragment : ll_prop.fragment mell_fragment.
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

(** cut / axioms / pmix / permutation *)
Definition pfrag_mell := ll_def.mk_pfrag false ll_def.NoAxioms ll_def.pmix_none true.
(*                                       cut   axioms          mix              perm  *)


(** ** 5. prove equivalence of proof predicates *)

Lemma mell2mellfrag : forall m,
  mell m -> inhabited (ll_def.ll pfrag_mell (map mell2ll (elts m))).
Proof with try eassumption ; try reflexivity.
intros l pi.
induction pi ;
  try destruct IHpi as [IHpi] ;
  try destruct IHpi1 as [IHpi1] ;
  try destruct IHpi2 as [IHpi2] ;
  constructor ; simpl ; rewrite ? map_app ;
  try (now (constructor ; eassumption)).
- apply meq_perm in X.
  eapply ll_def.ex_r...
  apply Permutation_Type_map...
- eapply ll_def.ex_r.
  + apply ll_def.tens_r.
    * assert (Helt := Permutation_Type_map mell2ll (elts_add A l1)).
      apply (ll_def.ex_r _ _ _ IHpi1) in Helt.
      simpl in Helt...
    * assert (Helt := Permutation_Type_map mell2ll (elts_add B l2)).
      apply (ll_def.ex_r _ _ _ IHpi2) in Helt.
      simpl in Helt...
  + apply Permutation_Type_cons...
    rewrite <- map_app.
    apply Permutation_Type_map.
    unfold sum ; unfold list2fm.
    simpl ; rewrite fold_id.
    apply Permutation_Type_app_comm.
- unfold fmmap.
  unfold list2fm.
  unfold add.
  unfold empty.
  simpl.
  rewrite fold_id.
  rewrite mell2ll_map_wn.
  unfold elts in IHpi.
  unfold add in IHpi.
  unfold fmmap in IHpi.
  unfold list2fm in IHpi.
  simpl in IHpi.
  rewrite fold_id in IHpi.
  rewrite mell2ll_map_wn in IHpi.
  apply ll_def.oc_r...
Qed.

Lemma mellfrag2mell : forall m,
  ll_def.ll pfrag_mell (map mell2ll (elts m)) -> mell m.
Proof with try eassumption ; try reflexivity.
intros m pi.
remember (map mell2ll (elts m)) as l.
revert m Heql ; induction pi ; intros m Heql ;
  try (now (destruct m ; inversion Heql ;
            destruct f ; inversion H0)) ;
  try (now inversion f).
- destruct m ; inversion Heql.
  destruct m ; inversion H1.
  destruct f ; inversion H0 ; subst.
  destruct f0 ; inversion H2 ; subst.
  destruct m ; inversion H3.
  apply ax_r.
- subst.
  simpl in p.
  apply Permutation_Type_map_inv in p.
  destruct p as [l' Heq HP] ; subst.
  eapply ex_r.
  + apply IHpi...
  + symmetry...
- decomp_map Heql ; subst.
  apply mell2ll_map_wn_inv in Heql3 ; destruct Heql3 as (l & Heq1 & Heq2) ; subst.
  apply Permutation_Type_map_inv in p ; destruct p as [l' Heq HP] ; subst.
  simpl in Heql ; unfold id in Heql ; subst.
  eapply ex_r ;
    [ apply IHpi ; rewrite <- mell2ll_map_wn ; rewrite <- ? map_app | ]...
  apply Permutation_Type_app_head.
  apply Permutation_Type_app_tail.
  symmetry in HP ; apply Permutation_Type_map...
- destruct m ; inversion Heql.
  destruct f ; inversion H0 ; subst.
  destruct m ; inversion H1.
  apply one_r.
- destruct m ; inversion Heql.
  destruct f ; inversion H0 ; subst.
  apply bot_r.
  apply IHpi...
- destruct m ; inversion Heql.
  destruct f ; inversion H0 ; subst.
  assert (Heq := H1).
  decomp_map H1 ; subst.
  apply (ex_r (add (tens f1 f2) (sum l3 l0))).
  + apply tens_r.
    * apply IHpi1...
    * apply IHpi2...
  + unfold sum.
    unfold list2fm.
    unfold add.
    simpl.
    apply Permutation_Type_cons...
    rewrite fold_id.
    apply Permutation_Type_app_comm.
- destruct m ; inversion Heql.
  destruct f ; inversion H0 ; subst.
  apply parr_r.
  apply IHpi...
- destruct m ; inversion Heql.
  destruct f ; inversion H0 ; subst.
  apply mell2ll_map_wn_inv in H1.
  destruct H1 as (m' & Heq1 & Heq2) ; subst.
  replace (oc f :: map wn m')
     with (add (oc f) (fmmap wn m')).
  + apply oc_r.
    apply IHpi.
    unfold add.
    unfold fmmap.
    unfold list2fm.
    simpl.
    rewrite fold_id.
    rewrite mell2ll_map_wn...
  + unfold fmmap.
    unfold list2fm.
    unfold add.
    simpl.
    rewrite fold_id...
- destruct m ; inversion Heql.
  destruct f ; inversion H0 ; subst.
  apply de_r.
  apply IHpi...
- destruct m ; inversion Heql.
  destruct f ; inversion H0 ; subst.
  apply wk_r.
  apply IHpi...
- destruct m ; inversion Heql.
  destruct f ; inversion H0 ; subst.
  apply co_r.
  apply IHpi.
  change (formulas.wn (mell2ll f)) with (mell2ll (wn f))...
- inversion a.
Qed.


(** ** 6. import properties *)

(** *** axiom expansion *)

Lemma ax_gen_r : forall A, mell (add (dual A) (add A empty)).
Proof.
intro A.
apply mellfrag2mell.
eapply ll_def.ex_r ; [ apply ll_def.ax_exp | ].
rewrite mell2ll_dual.
apply Permutation_Type_swap.
Qed.


(** *** cut admissibility *)

Lemma cut_r : forall A m1 m2, 
  mell (add A m1) -> mell (add (dual A) m2) -> mell (sum m1 m2).
Proof with try eassumption.
intros A m1 m2 pi1 pi2.
apply mell2mellfrag in pi1 ; destruct pi1 as [pi1] ; simpl in pi1.
apply mell2mellfrag in pi2 ; destruct pi2 as [pi2] ; simpl in pi2.
apply mellfrag2mell.
eapply ll_def.ex_r ; [ | apply Permutation_Type_map ; symmetry ; apply elts_sum ].
rewrite map_app.
eapply ll_cut.cut_r_axfree...
- intros a ; destruct a.
- assert (Permutation_Type (map mell2ll (elts (add (dual A) m2)))
                           (map mell2ll (dual A :: elts m2)))
  as Helt2 by (apply Permutation_Type_map ; apply elts_add).
  simpl in Helt2 ; rewrite <- mell2ll_dual in Helt2.
  rewrite <- mell2ll_dual in pi2.
  eapply ll_def.ex_r ; [ | apply Helt2 ]...
Qed.

