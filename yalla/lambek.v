(** * Example of a concrete use of the yalla library: Lambek calculus *)

From OLlibs Require Import dectype funtheory List_more PermutationT.


(** ** 0. load the [ill] library *)

From Yalla Require ill_cut.

Set Default Proof Using "Type".
Set Implicit Arguments.


Section Atoms.

Context {preiatom : DecType}.

(** ** 1. define formulas *)

Inductive lform :=
| lvar (_ : @iformulas.iatom preiatom) | ltens (_ _: lform) | lpam (_ _ : lform) | lmap (_ _ : lform).


(** ** 2. define embedding into [iformulas.iformula] *)

Fixpoint l2ill A :=
match A with
| lvar x => iformulas.ivar x
| ltens A B => iformulas.itens (l2ill A) (l2ill B)
| lpam A B => iformulas.ilpam (l2ill A) (l2ill B)
| lmap A B => iformulas.ilmap (l2ill A) (l2ill B)
end.

(*
Lemma l2ill_inj : injective l2ill.
Proof.
intros A; induction A; intros B Heq; destruct B; destr_eq Heq;
  try apply IHA1 in Heq; try apply IHA2 in H; subst; try reflexivity.
Qed.
*)


(** ** 3. define proofs *)

Inductive lprove : list lform -> lform -> Type :=
| ax_lr X : lprove (lvar X :: nil) (lvar X)
| tens_lrr A B l1 l2 : lprove l1 A -> lprove l2 B -> lprove (l1 ++ l2) (ltens A B)
| tens_llr A B C l1 l2 : lprove (l1 ++ A :: B :: l2) C -> lprove (l1 ++ ltens A B :: l2) C
| lpam_lrr A B l : lprove (l ++ A :: nil) B -> lprove l (lpam A B)
| lpam_llr A B C l1 l2 l3 : lprove l2 A -> lprove (l1 ++ B :: l3) C -> lprove (l1 ++ lpam A B :: l2 ++ l3) C
| lmap_lrr A B l : lprove (A :: l) B -> lprove l (lmap A B)
| lmap_llr A B C l1 l2 l3 : lprove l2 A -> lprove (l1 ++ B :: l3) C -> lprove (l1 ++ l2 ++ lmap A B :: l3) C.


(** ** 4. characterize corresponding [ill] fragment *)

(** cut / axioms / permutation *)
Definition ipfrag_lambek := @ill_def.mk_ipfrag preiatom ill_def.ipcut_none ill_def.NoIAxioms false.
(*                                             atoms    cut                axioms            perm  *)


(** ** 5. prove equivalence of proof predicates *)

Lemma l2illfrag l A : lprove l A -> ill_def.ill ipfrag_lambek (map l2ill l) (l2ill A).
Proof.
intro pi. induction pi;
  try (cbn in IHpi; rewrite ? map_app in IHpi);
  try (cbn in IHpi1; rewrite ? map_app in IHpi1);
  try (cbn in IHpi2; rewrite ? map_app in IHpi2);
  rewrite ? map_app; cbn; rewrite ? map_app;
  now constructor.
Qed.

Lemma illfrag2l l A : ill_def.ill ipfrag_lambek (map l2ill l) (l2ill A) -> lprove l A.
Proof.
intro pi. remember (map l2ill l) as l0 eqn:Heql. remember (l2ill A) as A0 eqn:HeqA.
induction pi in l, A, Heql, HeqA |- *;
  (try now (destruct A; destr_eq HeqA));
  (try now (decomp_map Heql eqn:Hx; destruct x; destr_eq Hx)); subst.
- destruct A; destr_eq HeqA.
  destruct l as [|B l]; inversion Heql as [[H1 H2]]; destruct l; destr_eq H2.
  destruct B; destr_eq H1. subst.
  apply ax_lr.
- apply IHpi; [ assumption | reflexivity ].
- remember (map iformulas.ioc lw') as l4.
  decomp_map Heql eqn:Heq. subst.
  destruct l4; inversion Heq; destruct lw'; inversion H0.
  + symmetry in p. apply PermutationT.PermutationT_nil in p as ->.
    apply IHpi; [ list_simpl | ]; reflexivity.
  + destruct l; discriminate H1.
- destruct A; destr_eq HeqA. subst.
  decomp_map Heql. subst.
  apply tens_lrr; [ apply IHpi1 | apply IHpi2]; reflexivity.
- decomp_map Heql eqn:Hx. subst.
  destruct x; destr_eq Hx. subst.
  apply tens_llr.
  apply IHpi; [ list_simpl | ]; reflexivity.
- destruct A; destr_eq HeqA. subst.
  apply lpam_lrr.
  apply IHpi; [ rewrite map_last | ]; reflexivity.
- decomp_map Heql eqn:Hx. subst.
  destruct x; destr_eq Hx. subst.
  apply lpam_llr; [ apply IHpi1 | apply IHpi2]; list_simpl; reflexivity.
- destruct A; destr_eq HeqA. subst.
  apply lmap_lrr.
  apply IHpi; reflexivity.
- decomp_map Heql eqn:Hx. subst.
  destruct x; destr_eq Hx. subst.
  apply lmap_llr; [ apply IHpi1 | apply IHpi2]; list_simpl; reflexivity.
Qed.


(** ** 6. import properties *)

(** *** axiom expansion *)

Lemma ax_gen_r A : lprove (A :: nil) A.
Proof. apply illfrag2l, ill_def.ax_exp_ill. Qed.

(** *** cut admissibility *)

Lemma cut_r A l0 l1 l2 C : lprove l0 A -> lprove (l1 ++ A :: l2) C -> lprove (l1 ++ l0 ++ l2) C.
Proof.
intros pi1%l2illfrag pi2%l2illfrag. apply illfrag2l.
rewrite ? map_app in *. refine (ill_cut.cut_ir_axfree _ _ _ pi1 pi2).
intros [].
Qed.

End Atoms.
