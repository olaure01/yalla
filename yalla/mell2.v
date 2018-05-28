(* mell2 example file for yalla library *)
(* Coq 8.6 *)
(* v 1.0   Olivier Laurent *)


(** * Example of a concrete use of the yalla library: unit-free MELL with mix2 rule *)

Require Import Injective.
Require Import List_more.
Require Import Permutation_more.
Require Import Permutation_solve.


(** ** 0. load the [ll] library *)

Require ll.


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


(** ** 3. define proofs *)

Inductive mell : list formula -> Prop :=
| ax_r : forall X, mell (covar X :: var X :: nil)
| ex_r : forall l1 l2, mell l1 ->
              Permutation l1 l2 -> mell l2
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
Definition pfrag_mell := ll.mk_pfrag false (fun _ => False) false true true.
(*                                   cut   axioms           mix0  mix2 perm  *)


(** ** 5. prove equivalence of proof predicates *)

Lemma mell2mellfrag : forall l, mell l ->
    exists s, ll.ll pfrag_mell (map mell2ll l) s.
Proof with try reflexivity ; try eassumption.
intros l pi.
induction pi ;
  try destruct IHpi as [s' pi'] ;
  try destruct IHpi1 as [s1' pi1'] ;
  try destruct IHpi2 as [s2' pi2'] ;
  eexists ; simpl ; rewrite ? map_app.
- apply ll.ax_r.
- eapply ll.ex_r...
  apply Permutation_map...
- apply ll.mix2_r...
- eapply ll.ex_r.
  + apply (ll.tens_r _ _ _ _ _ _ _ pi1' pi2').
  + simpl ; perm_solve.
- apply ll.parr_r...
- rewrite mell2ll_map_wn.
  apply ll.oc_r.
  rewrite <- mell2ll_map_wn...
- apply ll.de_r...
- apply ll.wk_r...
- rewrite <- (app_nil_l (map _ _)).
  change nil with (map formulas.wn nil).
  apply ll.co_r...
Qed.

Lemma mellfrag2mell : forall l s,
  ll.ll pfrag_mell (map mell2ll l) s -> mell l.
Proof with try eassumption ; try reflexivity.
intros l s pi.
remember (map mell2ll l) as l0.
revert l Heql0 ; induction pi ; intros l' Heql0 ; subst ;
  try (destruct l' ; inversion Heql0 ;
       destruct f ; inversion H0 ; fail).
- decomp_map Heql0 ; subst.
  destruct l1 ; inversion Heql4.
  destruct x ; inversion Heql2.
  destruct x0 ; inversion Heql0.
  subst ; subst.
  apply ax_r.
- simpl in H.
  apply Permutation_map_inv in H.
  destruct H as (l'' & Heq & HP).
  symmetry in HP.
  eapply ex_r...
  apply IHpi...
- inversion f.
- decomp_map Heql0 ; subst.
  apply mix_r.
  + apply IHpi2...
  + apply IHpi1...
- decomp_map Heql0 ; subst.
  destruct x ; inversion Heql2 ; subst.
  eapply ex_r.
  apply tens_r.
  + apply IHpi1...
  + apply IHpi2...
  + perm_solve.
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
  decomp_map H1 ; subst.
  apply co_r.
  apply mell2ll_map_wn_inv in H3.
  destruct H3 as (l'' & Heq1 & Heq2) ; subst.
  eapply ex_r.
  + apply IHpi...
    rewrite <- mell2ll_map_wn.
    replace (formulas.wn (mell2ll f) :: map mell2ll (map wn l'')
         ++ formulas.wn (mell2ll f) :: map mell2ll l2)
       with (map mell2ll (wn f :: map wn l'' ++ wn f :: l2))...
    list_simpl...
  + perm_solve.
- inversion f.
- inversion H.
Qed.


(** ** 6. import properties *)

(** *** axiom expansion *)

Lemma ax_gen_r : forall A, mell (dual A :: A :: nil).
Proof.
intro A.
destruct (@ll.ax_exp pfrag_mell (formulas.dual (mell2ll A)))
  as [s Hax].
rewrite formulas.bidual in Hax.
rewrite mell2ll_dual in Hax.
eapply mellfrag2mell.
eassumption.
Qed.

(** *** cut elimination *)

Lemma cut_r : forall A l1 l2, 
  mell (A :: l1) -> mell (dual A :: l2) -> mell (l1 ++ l2).
Proof with try eassumption.
intros A l1 l2 pi1 pi2.
destruct (mell2mellfrag _ pi1) as [s1 pi1'] ; simpl in pi1'.
destruct (mell2mellfrag _ pi2) as [s2 pi2'] ; simpl in pi2'.
eapply ll.cut_r_axfree in pi1' ;
  [ | | rewrite mell2ll_dual ]...
- destruct pi1' as [s pi].
  rewrite <- map_app in pi.
  eapply mellfrag2mell...
- intros l Hax ; inversion Hax.
Qed.





