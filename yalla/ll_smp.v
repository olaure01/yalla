(* ll example file for yalla library *)

(** * Example of a concrete use of the yalla library: LL *)

From Coq Require Import CMorphisms.
From OLlibs Require Import funtheory infinite List_more Permutation_Type_more.


(** ** 0. load the [yalla] library *)

From Yalla Require Import atoms.
From Yalla Require ll_fragments.

Set Implicit Arguments.


Section Atoms.

Context {atom : InfDecType}.

(** ** 1. define formulas *)

Inductive formula :=
| var (_ : atom) | covar (_ : atom)
| one | bot
| tens (_ _ : formula) | parr (_ _ : formula)
| zero | top
| aplus (_ _ : formula) | awith (_ _ : formula)
| oc (_ : formula) | wn (_ : formula).

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
intros A. induction A; intros B Heq;
  destruct B; inversion Heq;
  try apply IHA in H0; try apply IHA1 in H0; try apply IHA2 in H1; subst; reflexivity.
Qed.

Lemma ll2ll_dual A : formulas.dual (ll2ll A) = ll2ll (dual A).
Proof. induction A; cbn; rewrite ? IHA, ? IHA1, ? IHA2; reflexivity. Qed.

Lemma ll2ll_map_wn l : map ll2ll (map wn l) = map formulas.wn (map ll2ll l).
Proof. induction l as [|a l IHl]; [ | cbn; rewrite IHl ]; reflexivity. Qed.

Lemma ll2ll_map_wn_inv l1 l2 : map formulas.wn l1 = map ll2ll l2 ->
  { l2' | l2 = map wn l2' & l1 = map ll2ll l2' }.
Proof.
induction l1 in l2 |- *; intro Heq; destruct l2; inversion Heq.
- exists nil; reflexivity.
- apply IHl1 in H1.
  destruct f; inversion H0; subst.
  destruct H1 as [l2' -> ->].
  exists (f :: l2'); reflexivity.
Qed.


(** ** 3. define proofs *)

Inductive ll : list formula -> Type :=
| ax_r X : ll (covar X :: var X :: nil)
| ex_r l1 l2 : ll l1 -> Permutation_Type l1 l2 -> ll l2
| one_r : ll (one :: nil)
| bot_r l : ll l -> ll (bot :: l)
| tens_r A B l1 l2 : ll (A :: l1) -> ll (B :: l2) -> ll (tens A B :: l1 ++ l2)
| parr_r A B l : ll (A :: B :: l) -> ll (parr A B :: l)
| top_r l : ll (top :: l)
| plus_r1 A B l : ll (A :: l) -> ll (aplus A B :: l)
| plus_r2 A B l : ll (A :: l) -> ll (aplus B A :: l)
| with_r A B l : ll (A :: l) -> ll (B :: l) -> ll (awith A B :: l)
| oc_r A l : ll (A :: List.map wn l) -> ll (oc A :: List.map wn l)
| de_r A l : ll (A :: l) -> ll (wn A :: l)
| wk_r A l : ll l -> ll (wn A :: l)
| co_r A l : ll (wn A :: wn A :: l) -> ll (wn A :: l).

Instance ll_perm : Proper ((@Permutation_Type _) ==> arrow) ll.
Proof. intros l1 l2 HP pi. eapply ex_r; eassumption. Qed.

(** ** 4. characterize corresponding [ll] fragment *)

(* pfrag_ll *)

(** ** 5. prove equivalence of proof predicates *)

Lemma ll2llfrag l : ll l -> ll_fragments.ll_ll (map ll2ll l).
Proof.
intros pi. induction pi; try (constructor; assumption); rewrite ? map_app.
- eapply ll_def.ex_r; [ eassumption | ].
  apply Permutation_Type_map. assumption.
- eapply ll_def.ex_r.
  + apply (ll_def.tens_r IHpi1 IHpi2).
  + list_simpl. apply Permutation_Type_cons, Permutation_Type_app_comm. reflexivity.
- cbn. rewrite ll2ll_map_wn. apply ll_def.oc_r. rewrite <- ll2ll_map_wn. assumption.
Qed.

Lemma llfrag2ll l : ll_fragments.ll_ll (map ll2ll l) -> ll l.
Proof.
intros pi.
remember (map ll2ll l) as l0.
induction pi in l, Heql0 |- *; subst; try discriminate f.
- symmetry in Heql0. decomp_map_inf Heql0. subst.
  destruct l2; inversion Heql4.
  destruct x; inversion Heql2.
  destruct x0; inversion Heql0.
  apply ax_r.
- cbn in p.
  apply Permutation_Type_map_inv in p as [l'' Heq HP%Permutation_Type_sym].
  eapply ex_r; [ apply IHpi | ]; eassumption.
- symmetry in Heql0. decomp_map_inf Heql0. subst. symmetry in Heql0.
  cbn in Heql0. apply ll2ll_map_wn_inv in Heql0 as [l -> ->].
  apply Permutation_Type_map_inv in p as [l' -> HP].
  eapply ex_r; [ apply IHpi; rewrite <- ll2ll_map_wn, <- ? map_app; reflexivity | ].
  symmetry in HP.
  apply Permutation_Type_app_head, Permutation_Type_app_tail, Permutation_Type_map. assumption.
- destruct l; inversion Heql0. destruct f; inversion H0. destruct l; inversion H1.
  apply one_r.
- destruct l; inversion Heql0. destruct f; inversion H0.
  apply bot_r, IHpi. assumption.
- symmetry in Heql0. decomp_map_inf Heql0. subst.
  destruct x; inversion Heql2; subst.
  eapply ex_r; [ apply tens_r | ].
  + apply IHpi1. reflexivity.
  + apply IHpi2. reflexivity.
  + apply Permutation_Type_cons; [ reflexivity | apply Permutation_Type_app_comm ].
- destruct l; inversion Heql0. destruct f; inversion H0. subst.
  apply parr_r, IHpi. reflexivity.
- destruct l; inversion Heql0. destruct f; inversion H0.
  apply top_r.
- destruct l; inversion Heql0. destruct f; inversion H0. subst.
  apply plus_r1, IHpi. reflexivity.
- destruct l; inversion Heql0. destruct f; inversion H0. subst.
  apply plus_r2, IHpi. reflexivity.
- destruct l; inversion Heql0. destruct f; inversion H0. subst.
  apply with_r; [ apply IHpi1 | apply IHpi2 ]; reflexivity.
- destruct l; inversion Heql0. destruct f; inversion H0. subst.
  apply ll2ll_map_wn_inv in H1 as [l'' -> ->].
  apply oc_r, IHpi.
  cbn. rewrite ll2ll_map_wn. reflexivity.
- destruct l; inversion Heql0. destruct f ; inversion H0. subst.
  apply de_r, IHpi. reflexivity.
- destruct l; inversion Heql0. destruct f; inversion H0. subst.
  apply wk_r, IHpi. reflexivity.
- destruct l; inversion Heql0. destruct f; inversion H0. subst.
  apply co_r, IHpi. reflexivity.
- destruct a.
Qed.


(** ** 6. import properties *)

(** *** axiom expansion *)

Lemma ax_gen_r A : ll (dual A :: A :: nil).
Proof.
apply llfrag2ll. cbn. rewrite <- ll2ll_dual.
eapply ll_def.ex_r; [ apply ll_def.ax_exp | apply Permutation_Type_swap ].
Qed.

(** *** cut admissibility *)

Lemma cut_r A l1 l2 : ll (A :: l1) -> ll (dual A :: l2) -> ll (l1 ++ l2).
Proof.
intros pi1%ll2llfrag pi2%ll2llfrag.
apply llfrag2ll.
rewrite map_app. eapply ll_cut.cut_r_axfree.
- intros [].
- cbn in pi2. rewrite <- ll2ll_dual in pi2. eassumption.
- assumption.
Qed.

End Atoms.
