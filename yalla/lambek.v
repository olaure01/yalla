(* lambek example file for yalla library *)

(** * Example of a concrete use of the yalla library: a variant of the Lambek calculus
  tensor-free Lambek calculus with additive conjunction and its unit *)

From OLlibs Require Import dectype funtheory List_more Permutation_Type.


(** ** 0. load the [ill] library *)

From Yalla Require ill_cut.

Set Implicit Arguments.


Section Atoms.

Context { preiatom : DecType }.

(** ** 1. define formulas *)

Inductive lform :=
| lvar  : @iformulas.iatom preiatom -> lform
| ltop  : lform
| lwith : lform -> lform -> lform
| lpam  : lform -> lform -> lform.


(** ** 2. define embedding into [iformulas.iformula] *)

Fixpoint l2ill A :=
match A with
| lvar x    => iformulas.ivar x
| ltop      => iformulas.itop
| lwith A B => iformulas.iwith (l2ill A) (l2ill B)
| lpam A B  => iformulas.ilpam (l2ill A) (l2ill B)
end.

(*
Lemma l2ill_inj : injective l2ill.
Proof.
intros A; induction A; intros B Heq; destruct B; inversion Heq ;
  try apply IHA1 in H0; try apply IHA2 in H1; subst; reflexivity.
Qed.
*)


(** ** 3. define proofs *)

Inductive lprove : list lform -> lform -> Type :=
| ax_lr   : forall X, lprove (lvar X :: nil) (lvar X)
| top_lrr  : forall l, lprove l ltop
| with_lrr : forall A B l, lprove l A -> lprove l B -> lprove l (lwith A B)
| with_llr1 : forall A B C l1 l2, lprove (l1 ++ A :: l2) C ->
                                  lprove (l1 ++ lwith A B :: l2) C
| with_llr2 : forall A B C l1 l2, lprove (l1 ++ A :: l2) C ->
                                  lprove (l1 ++ lwith B A :: l2) C
| lpam_lrr  : forall A B l, lprove (l ++ A :: nil) B -> lprove l (lpam A B)
| lpam_llr : forall A B C l1 l2 l3,
                  lprove l2 A -> lprove (l1 ++ B :: l3) C ->
                  lprove (l1 ++ lpam A B :: l2 ++ l3) C.


(** ** 4. characterize corresponding [ill] fragment *)

(** cut / axioms / permutation *)
Definition ipfrag_lambek := @ill_def.mk_ipfrag preiatom false ill_def.NoIAxioms false.
(*                                             atoms    cut   axioms            perm  *)


(** ** 5. prove equivalence of proof predicates *)

Lemma l2illfrag l A : lprove l A -> ill_def.ill ipfrag_lambek (map l2ill l) (l2ill A).
Proof.
intros pi; induction pi;
  try (cbn in IHpi; rewrite ? map_app in IHpi);
  try (cbn in IHpi1; rewrite ? map_app in IHpi1);
  try (cbn in IHpi2; rewrite ? map_app in IHpi2);
  rewrite ? map_app; cbn; rewrite ? map_app;
  now constructor.
Qed.

Lemma illfrag2l l A :
  ill_def.ill ipfrag_lambek (map l2ill l) (l2ill A) -> lprove l A.
Proof.
intros pi.
remember (map l2ill l) as l0.
remember (l2ill A) as A0.
revert l A Heql0 HeqA0; induction pi;
  intros l' A' Heql0 HeqA0; subst;
  (try now (destruct A'; inversion HeqA0));
  (try now (symmetry in Heql0; decomp_map_inf Heql0; destruct x; inversion Heql0));
  (try now (symmetry in Heql0; decomp_map_inf Heql0; destruct x; inversion Heql3)).
- destruct A'; inversion HeqA0.
  destruct l'; inversion Heql0; destruct l' ; inversion Heql0.
  destruct l; inversion H3; subst.
  apply ax_lr.
- apply IHpi; [ assumption | reflexivity ].
- symmetry in Heql0; decomp_map_inf Heql0; subst.
  destruct l4; inversion Heql0; destruct lw'; inversion H0.
  + symmetry in p; apply Permutation_Type.Permutation_Type_nil in p; subst.
    apply IHpi; [ list_simpl | ]; reflexivity.
  + destruct l; inversion H1.
- destruct A'; inversion HeqA0; subst.
  apply lpam_lrr.
  apply IHpi; [ rewrite map_last | ]; reflexivity.
- symmetry in Heql0; decomp_map_inf Heql0; subst.
  destruct x; inversion Heql0; subst.
  apply lpam_llr; [ apply IHpi1 | apply IHpi2]; list_simpl; reflexivity.
- destruct A'; inversion HeqA0; subst.
  apply top_lrr.
- destruct A'; inversion HeqA0; subst.
  apply with_lrr; [ apply IHpi1 | apply IHpi2]; reflexivity.
- symmetry in Heql0; decomp_map_inf Heql0; subst.
  destruct x; inversion Heql0; subst.
  apply with_llr1.
  apply IHpi; [ list_simpl | ]; reflexivity.
- symmetry in Heql0; decomp_map_inf Heql0; subst.
  destruct x; inversion Heql0; subst.
  apply with_llr2.
  apply IHpi; [ list_simpl | ]; reflexivity.
- inversion f.
Qed.


(** ** 6. import properties *)

(** *** axiom expansion *)

Lemma ax_gen_r A : lprove (A :: nil) A.
Proof. apply illfrag2l, ill_def.ax_exp_ill. Qed.

(** *** cut admissibility *)

Lemma cut_r A l0 l1 l2 C :
  lprove l0 A -> lprove (l1 ++ A :: l2) C -> lprove (l1 ++ l0 ++ l2) C.
Proof.
intros pi1%l2illfrag pi2%l2illfrag.
rewrite map_app in pi2.
apply illfrag2l.
rewrite 2 map_app.
eapply ill_cut.cut_ir_axfree; [ intros a; destruct a | | ]; eassumption.
Qed.

End Atoms.
