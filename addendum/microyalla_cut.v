Require List_more.
Require ll_fragments.


(*** copy of microyalla/ll.v ***)

From Stdlib Require Export List.
Export ListNotations.

(* From ollibs/Permutation_Type.v *)

Inductive Permutation_Type {A} : list A -> list A -> Type :=
| Permutation_Type_nil_nil : Permutation_Type nil nil
| Permutation_Type_skip x l l' : Permutation_Type l l' -> Permutation_Type (x::l) (x::l')
| Permutation_Type_swap x y l : Permutation_Type (y::x::l) (x::y::l)
| Permutation_Type_trans l l' l'' :
    Permutation_Type l l' -> Permutation_Type l' l'' -> Permutation_Type l l''.


(* Adapted from yalla/formulas.v *)

(** A set of atoms for building formulas *)
Definition Atom := nat.

(** Formulas *)
Inductive formula : Set :=
| var : Atom -> formula
| covar : Atom -> formula
| one : formula
| bot : formula
| tens : formula -> formula -> formula
| parr : formula -> formula -> formula
| zero : formula
| top : formula
| aplus : formula -> formula -> formula
| awith : formula -> formula -> formula
| oc : formula -> formula
| wn : formula -> formula.


(* Adapted from yalla/ll_def.v *)

(** Rules *)
Inductive ll : list formula -> Type :=
| ax_r : forall X, ll (covar X :: var X :: nil)
| ex_r : forall l1 l2, ll l1 -> Permutation_Type l1 l2 -> ll l2
| one_r : ll (one :: nil)
| bot_r : forall l, ll l -> ll (bot :: l)
| tens_r : forall A B l1 l2, ll (A :: l1) -> ll (B :: l2) -> ll (tens A B :: l1 ++ l2)
| parr_r : forall A B l, ll (A :: B :: l) -> ll (parr A B :: l)
| top_r : forall l, ll (top :: l)
| plus_r1 : forall A B l, ll (A :: l) -> ll (aplus A B :: l)
| plus_r2 : forall A B l, ll (A :: l) -> ll (aplus B A :: l)
| with_r : forall A B l, ll (A :: l) -> ll (B :: l) -> ll (awith A B :: l)
| oc_r : forall A l, ll (A :: map wn l) -> ll (oc A :: map wn l)
| de_r : forall A l, ll (A :: l) -> ll (wn A :: l)
| wk_r : forall A l, ll l -> ll (wn A :: l)
| co_r : forall A l, ll (wn A :: wn A :: l) -> ll (wn A :: l).

(*** end of copy ***)


(*** Add definition of [dual] ***)

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

(*** end definition ***)


(*** copy of part of yalla/ll_smp.v *)

(* begin hide *)
Module YallaCutProof.

Import List_more.

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

Lemma ll2llfrag : forall l, ll l -> ll_fragments.ll_ll (map ll2ll l).
Proof with try eassumption ; try reflexivity.
intros l pi.
induction pi ; try (now constructor) ; try rewrite map_app.
- apply pt2ypt in p.
  eapply ll_def.ex_r...
  apply Permutation_Type.Permutation_Type_map...
- eapply ll_def.ex_r.
  + apply (ll_def.tens_r _ _ _ _ _ IHpi1 IHpi2).
  + simpl; rewrite map_app.
    apply Permutation_Type.Permutation_Type_cons; [reflexivity | ].
    apply Permutation_Type.Permutation_Type_app_comm.
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
- decomp_map Heql0 eqn:Heq. destruct Heq as [Heq1 [Heq2 ->%map_eq_nil]]. subst.
  destruct x ; inversion Heq1. destruct x0 ; inversion Heq2. subst.
  apply ax_r.
- simpl in p.
  apply Permutation_Type_more.Permutation_Type_map_inv in p.
  destruct p as [l'' Heq HP].
  apply Permutation_Type.Permutation_Type_sym in HP.
  apply ypt2pt in HP.
  eapply ex_r...
  apply IHpi...
- decomp_map Heql0 eqn:Heqw. subst.
  symmetry in Heqw. apply ll2ll_map_wn_inv in Heqw as [l [-> ->]].
  apply Permutation_Type_more.Permutation_Type_map_inv in p as [l' -> HP].
  eapply ex_r ;
    [ apply IHpi ; rewrite <- ll2ll_map_wn ; rewrite <- ? map_app | ]...
  apply ypt2pt.
  apply Permutation_Type.Permutation_Type_app_head.
  apply Permutation_Type.Permutation_Type_app_tail.
  apply Permutation_Type.Permutation_Type_sym in HP.
  apply Permutation_Type.Permutation_Type_map...
- destruct l' ; inversion Heql0 ; destruct f ; inversion H0.
  destruct l' ; inversion H1.
  apply one_r.
- destruct l' ; inversion Heql0 ; destruct f ; inversion H0.
  apply bot_r.
  apply IHpi...
- decomp_map Heql0 eqn:Hx. subst.
  destruct x; inversion Hx. subst.
  eapply ex_r.
  apply tens_r.
  + apply IHpi1...
  + apply IHpi2...
  + apply ypt2pt.
    apply Permutation_Type.Permutation_Type_cons; [reflexivity | ].
    apply Permutation_Type.Permutation_Type_app_comm.
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

Lemma yalla_cut_r : forall A l1 l2,
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

End YallaCutProof.
(* end hide *)

(*** end of copy ***)


Lemma microyalla_cut_r : forall A l1 l2,
  ll (A :: l1) -> ll (dual A :: l2) -> ll (l1 ++ l2).
Proof. exact YallaCutProof.yalla_cut_r. Qed.
