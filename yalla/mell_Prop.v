(** * Example of a concrete use of the yalla library: unit-free MELL in Prop *)

From Coq Require Import Morphisms.
From OLlibs Require Import funtheory dectype List_more Permutation_more Permutation_Type_more.


(** ** 0. load the [yalla] library *)

From Yalla Require Import atoms.
From Yalla Require ll_cut.

Set Default Proof Using "Type".
Set Implicit Arguments.


Section Atoms.

Context {atom : DecType}.

(** ** 1. define formulas *)

Inductive formula :=
| var (_ : atom) | covar (_ : atom)
| tens (_ _ : formula) | parr (_ _ : formula)
| oc (_ : formula) | wn (_ : formula).

Fixpoint dual A :=
match A with
| var x    => covar x
| covar x  => var x
| tens A B => parr (dual B) (dual A)
| parr A B => tens (dual B) (dual A)
| oc A     => wn (dual A)
| wn A     => oc (dual A)
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
induction l1 as [|a l1 IHl1] in l2 |- *; intro Heq; destruct l2; inversion Heq.
- exists nil. split; reflexivity.
- apply IHl1 in H1.
  destruct f; inversion H0. subst.
  destruct H1 as (l2' & -> & ->).
  exists (f :: l2'). split; reflexivity.
Qed.


(** ** 3. define proofs *)

Inductive mell : list formula -> Prop :=
| ax_r X : mell (covar X :: var X :: nil)
| ex_r l1 l2 : mell l1 -> Permutation l1 l2 -> mell l2
| tens_r A B l1 l2 : mell (A :: l1) -> mell (B :: l2) -> mell (tens A B :: l1 ++ l2)
| parr_r A B l : mell (A :: B :: l) -> mell (parr A B :: l)
| oc_r A l : mell (A :: map wn l) -> mell (oc A :: map wn l)
| de_r A l : mell (A :: l) -> mell (wn A :: l)
| wk_r A l : mell l -> mell (wn A :: l)
| co_r A l : mell (wn A :: wn A :: l) -> mell (wn A :: l).

Instance mell_perm : Proper ((@Permutation _) ==> Basics.impl) mell.
Proof. intros l1 ? ? ?. apply ex_r with l1; assumption. Qed.


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
       destruct B0; inversion HfA; subst;
       eexists; reflexivity).
assumption.
Qed.
*)

(** cut / axioms / pmix / permutation *)
Definition pfrag_mell := @ll_def.mk_pfrag atom  ll_def.pcut_none ll_def.NoAxioms ll_def.pmix_none true.
(*                                        atoms cut              axioms          mix              perm  *)


(** ** 5. prove equivalence of proof predicates *)

Lemma mell2mellfrag l : mell l -> inhabited (ll_def.ll pfrag_mell (map mell2ll l)).
Proof.
intro pi. induction pi; try ((try inversion IHpi); do 2 constructor; assumption); rewrite ? map_app.
- apply Permutation_Permutation_transp in H. induction H; destruct IHpi as [IHpi].
  + constructor. assumption.
  + constructor.
    eapply ll_def.ex_r; [ eassumption | ].
    apply Permutation_Type_map, Permutation_Type_app_head, Permutation_Type_swap.
  + apply IHPermutation_transp2.
    * apply Permutation_Permutation_transp in H.
      eapply ex_r; eassumption.
    * apply IHPermutation_transp1; [ | constructor ]; assumption.
- destruct IHpi1 as [IHpi1], IHpi2 as [IHpi2]. constructor.
  eapply ll_def.ex_r.
  + exact (ll_def.tens_r IHpi1 IHpi2).
  + cbn. rewrite map_app.
    apply Permutation_Type_cons, Permutation_Type_app_comm. reflexivity.
- destruct IHpi. constructor.
  cbn. rewrite mell2ll_map_wn. apply ll_def.oc_r. rewrite <- mell2ll_map_wn. assumption.
Qed.

Lemma mellfrag2mell l : ll_def.ll pfrag_mell (map mell2ll l) -> mell l.
Proof.
intros pi.
remember (map mell2ll l) as l0.
induction pi in l, Heql0 |- *; subst;
  try (destruct l; destr_eq Heql0; destruct f; destr_eq Heql0; subst; now try (constructor; apply IHpi)).
- symmetry in Heql0. decomp_map Heql0. subst.
  rewrite (map_eq_nil _ _ Heql4).
  destruct x; destr_eq Heql2. destruct x0; destr_eq Heql0. subst.
  apply ax_r.
- cbn in p.
  apply Permutation_Type_map_inv in p
    as [l'' Heq HP%Permutation_Type_sym%Permutation_Type_Permutation].
  eapply ex_r; [ | eassumption ].
  apply IHpi. assumption.
- symmetry in Heql0. decomp_map Heql0. subst. symmetry in Heql0.
  destruct (mell2ll_map_wn_inv _ _ Heql0) as [l [-> ->]].
  apply Permutation_Type_map_inv in p as [l' ->].
  eapply (@ex_r (l3 ++ map wn l' ++ l6)).
  + apply IHpi. list_simpl. rewrite mell2ll_map_wn. reflexivity.
  + symmetry. apply Permutation_app_head, Permutation_app_tail, Permutation_map, Permutation_Type_Permutation, p.
- discriminate f.
- symmetry in Heql0. decomp_map Heql0. subst.
  destruct x; destr_eq Heql2. subst.
  eapply ex_r; [ apply tens_r | ].
  + apply IHpi1. reflexivity.
  + apply IHpi2. reflexivity.
  + apply Permutation_cons, Permutation_app_comm. reflexivity.
- destruct l; destr_eq Heql0. destruct f; destr_eq Heql0. subst.
  apply mell2ll_map_wn_inv in H as [l' [-> ->]].
  apply oc_r, IHpi. cbn. rewrite mell2ll_map_wn. reflexivity.
- discriminate f.
- destruct a.
Qed.

Lemma inhmellfrag2mell l : inhabited (ll_def.ll pfrag_mell (map mell2ll l)) -> mell l.
Proof. intros [pi]%(inhabited_covariant (mellfrag2mell _)). exact pi. Qed.


(** ** 6. import properties *)

(** *** axiom expansion *)

Lemma ax_gen_r A : mell (dual A :: A :: nil).
Proof.
apply mellfrag2mell. cbn. rewrite <- mell2ll_dual.
eapply ll_def.ex_r; [ apply ll_def.ax_exp | apply Permutation_Type_swap ].
Qed.

(** *** cut admissibility *)

Lemma cut_r A l1 l2 : mell (A :: l1) -> mell (dual A :: l2) -> mell (l1 ++ l2).
Proof.
intros [pi1]%mell2mellfrag [pi2]%mell2mellfrag. apply mellfrag2mell.
rewrite map_app. eapply ll_cut.cut_r_axfree; [ intros [] | rewrite mell2ll_dual | ]; eassumption.
Qed.

End Atoms.
