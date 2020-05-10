(* ll example file for yalla library *)


(** * Example of a concrete use of the yalla library: LL *)

Require Import CMorphisms.

Require Import funtheory.
Require Import List_more.
Require Import Permutation_Type_more.
Require Import Permutation_Type_solve.


(** ** 0. load the [yalla] library *)

Require ll_fragments.


(** ** 1. define formulas *)
Require Export ll.

Lemma pt2ypt : forall A l1 l2, @Permutation_Type A l1 l2 ->
  @Permutation_Type.Permutation_Type A l1 l2.
Proof.
intros A l1 l2 HP ; induction HP ; econstructor ; eassumption.
Qed.

Lemma ypt2pt : forall A l1 l2, @Permutation_Type.Permutation_Type A l1 l2 ->
  @Permutation_Type A l1 l2.
Proof.
intros A l1 l2 HP ; induction HP ; econstructor ; eassumption.
Qed.

Fixpoint dual A :=
match A with
| var x     => covar x
| covar x   => var x
| one       => bot
| bot       => one
| tens A B  => parr (dual B) (dual A)
| parr A B  => tens (dual B) (dual A)
| zero      => top
| top       => zero
| aplus A B => awith (dual A) (dual B)
| awith A B => aplus (dual A) (dual B)
| oc A      => wn (dual A)
| wn A      => oc (dual A)
end.


(** ** 2. define embedding into [formulas.formula] *)

Fixpoint ll2ll A :=
match A with
| var x     => formulas.var x
| covar x   => formulas.covar x
| one       => formulas.one
| bot       => formulas.bot
| tens A B  => formulas.tens (ll2ll A) (ll2ll B)
| parr A B  => formulas.parr (ll2ll A) (ll2ll B)
| zero      => formulas.zero
| top       => formulas.top
| awith A B => formulas.awith (ll2ll A) (ll2ll B)
| aplus A B => formulas.aplus (ll2ll A) (ll2ll B)
| oc A      => formulas.oc (ll2ll A)
| wn A      => formulas.wn (ll2ll A)
end.

Lemma ll2ll_inj : injective ll2ll.
Proof.
intros A.
induction A ; intros B Heq ;
  destruct B ; inversion Heq ;
  try apply IHA in H0 ;
  try apply IHA1 in H0 ;
  try apply IHA2 in H1 ; subst ;
  reflexivity.
Qed.

Lemma ll2ll_dual : forall A, formulas.dual (ll2ll A) = ll2ll (dual A).
Proof.
induction A ; simpl ;
  rewrite ? IHA ;
  rewrite ? IHA1 ;
  rewrite ? IHA2 ;
  reflexivity.
Qed.

Lemma ll2ll_map_wn : forall l,
  map ll2ll (map wn l) = map formulas.wn (map ll2ll l).
Proof with try reflexivity.
induction l...
simpl ; rewrite IHl...
Qed.

Lemma ll2ll_map_wn_inv : forall l1 l2,
  map formulas.wn l1 = map ll2ll l2 ->
    { l2' | l2 = map wn l2' /\ l1 = map ll2ll l2' }.
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

Instance ll_perm : Proper ((@Permutation_Type _) ==> Basics.arrow) ll.
Proof.
intros l1 l2 HP pi.
eapply ex_r ; eassumption.
Qed.

(** ** 4. characterize corresponding [ll] fragment *)

(* pfrag_ll *)

(** ** 5. prove equivalence of proof predicates *)

Lemma ll2llfrag : forall l, ll l -> ll_fragments.ll_ll (map ll2ll l).
Proof with try eassumption ; try reflexivity. 
intros l pi.
induction pi ; try (now constructor) ; try rewrite map_app.
- apply pt2ypt in p.
  eapply ll_def.ex_r...
  apply Permutation_Type_map...
- eapply ll_def.ex_r.
  + apply (ll_def.tens_r _ _ _ _ _ IHpi1 IHpi2).
  + simpl ; Permutation_Type_solve.
- simpl ; rewrite ll2ll_map_wn.
  apply ll_def.oc_r.
  rewrite <- ll2ll_map_wn...
Qed.

Lemma llfrag2ll : forall l, ll_fragments.ll_ll (map ll2ll l) -> ll l.
Proof with try eassumption ; try reflexivity.
intros l pi.
remember (map ll2ll l) as l0.
revert l Heql0 ; induction pi ; intros l' Heql0 ; subst ;
  try (inversion f ; fail).
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
  apply ypt2pt in HP.
  eapply ex_r...
  apply IHpi...
- symmetry in Heql0; decomp_map_inf Heql0 ; subst; symmetry in Heql0.
  simpl in Heql0 ; apply ll2ll_map_wn_inv in Heql0 ;
    destruct Heql0 as (l & ? & ?) ; subst.
  apply Permutation_Type_map_inv in p ; destruct p as [l' Heq HP] ; subst.
  eapply ex_r ;
    [ apply IHpi ; rewrite <- ll2ll_map_wn ; rewrite <- ? map_app | ]...
  apply ypt2pt.
  apply Permutation_Type_app_head.
  apply Permutation_Type_app_tail.
  symmetry in HP ; apply Permutation_Type_map...
- destruct l' ; inversion Heql0 ; destruct f ; inversion H0.
  destruct l' ; inversion H1.
  apply one_r.
- destruct l' ; inversion Heql0 ; destruct f ; inversion H0.
  apply bot_r.
  apply IHpi...
- symmetry in Heql0; decomp_map_inf Heql0 ; subst.
  destruct x ; inversion Heql2 ; subst.
  eapply ex_r.
  apply tens_r.
  + apply IHpi1...
  + apply IHpi2...
  + apply ypt2pt ; Permutation_Type_solve.
- destruct l' ; inversion Heql0.
  destruct f ; inversion H0 ; subst.
  apply parr_r.
  apply IHpi...
- destruct l' ; inversion Heql0 ; destruct f ; inversion H0.
  apply top_r.
- destruct l' ; inversion Heql0 ; destruct f ; inversion H0 ; subst.
  apply plus_r1.
  apply IHpi...
- destruct l' ; inversion Heql0 ; destruct f ; inversion H0 ; subst.
  apply plus_r2.
  apply IHpi...
- destruct l' ; inversion Heql0 ; destruct f ; inversion H0 ; subst.
  apply with_r.
  + apply IHpi1...
  + apply IHpi2...
- destruct l' ; inversion Heql0.
  destruct f ; inversion H0 ; subst.
  apply ll2ll_map_wn_inv in H1.
  destruct H1 as (l'' & Heq1 & Heq2) ; subst.
  apply oc_r.
  apply IHpi.
  simpl ; rewrite ll2ll_map_wn...
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
- destruct a.
Qed.


(** ** 6. import properties *)

(** *** axiom expansion *)

Lemma ax_gen_r : forall A, ll (dual A :: A :: nil).
Proof.
intro A.
apply llfrag2ll.
simpl ; rewrite <- ll2ll_dual.
eapply ll_def.ex_r ; [ apply ll_def.ax_exp
                     | apply Permutation_Type.Permutation_Type_swap ].
Qed.

(** *** cut admissibility *)

Lemma cut_r : forall A l1 l2, 
  ll (A :: l1) -> ll (dual A :: l2) -> ll (l1 ++ l2).
Proof with try eassumption.
intros A l1 l2 pi1 pi2.
apply llfrag2ll.
rewrite map_app.
eapply ll_cut.cut_r_axfree.
- intros a ; destruct a.
- apply ll2llfrag in pi2.
  simpl in pi2 ; rewrite <- ll2ll_dual in pi2...
- apply ll2llfrag in pi1...
Qed.
