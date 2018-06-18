(* lambek example file for yalla library *)

(* output in Type *)


(** * Example of a concrete use of the yalla library: a variant of the Lambek calculus
  tensor-free Lambek calculus with additive conjunction and its unit *)


Require Import Injective.
Require Import List_more.
Require Import List_Type_more.

(** ** 0. load the [ill] library *)

Require ill.


(** ** 1. define formulas *)

Inductive lform  : Set :=
| lvar  : iformulas.IAtom -> lform
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
Proof with try reflexivity.
intros A.
induction A ; intros B Heq ;
  destruct B ; inversion Heq ;
  try apply IHA1 in H0 ;
  try apply IHA2 in H1 ; subst...
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
Definition ipfrag_lambek := ill.mk_ipfrag false ill.NoIAxioms false.
(*                                        cut   axioms        perm  *)


(** ** 5. prove equivalence of proof predicates *)

Lemma l2illfrag : forall l A, lprove l A ->
  ill.ill ipfrag_lambek (map l2ill l) (l2ill A).
Proof with try reflexivity ; try eassumption.
intros l A pi.
induction pi ;
  try (simpl in IHpi ; rewrite ? map_app in IHpi) ;
  try (simpl in IHpi1 ; rewrite ? map_app in IHpi1) ;
  try (simpl in IHpi2; rewrite ? map_app in IHpi2) ;
  simpl ; rewrite ? map_app ;
  simpl ; rewrite ? map_app ;
  try now constructor.
Qed.

Lemma illfrag2l : forall l A,
  ill.ill ipfrag_lambek (map l2ill l) (l2ill A) -> lprove l A.
Proof with try eassumption ; try reflexivity.
intros l A pi.
remember (map l2ill l) as l0.
remember (l2ill A) as A0.
revert l A Heql0 HeqA0 ; induction pi ;
  intros l' A' Heql0 HeqA0 ; subst ;
  (try now (destruct A' ; inversion HeqA0)) ;
  (try now (decomp_map_Type Heql0 ; destruct x ; inversion Heql0)) ;
  (try now (decomp_map_Type Heql0 ; destruct x ; inversion Heql3)).
- destruct A' ; inversion HeqA0.
  destruct l' ; inversion Heql0 ;
    destruct l' ; inversion Heql0.
  destruct l ; inversion H3 ; subst ; subst.
  apply ax_lr.
- apply IHpi...
- destruct A' ; inversion HeqA0 ; subst.
  apply lpam_lrr.
  apply IHpi...
  rewrite map_last...
- decomp_map_Type Heql0 ; subst.
  destruct x ; inversion Heql0 ; subst.
  apply lpam_llr.
  + apply IHpi1...
  + apply IHpi2...
    list_simpl...
- destruct A' ; inversion HeqA0 ; subst.
  apply top_lrr.
- destruct A' ; inversion HeqA0 ; subst.
  apply with_lrr.
  + apply IHpi1...
  + apply IHpi2...
- decomp_map_Type Heql0 ; subst.
  destruct x ; inversion Heql0 ; subst.
  apply with_llr1.
  apply IHpi...
  list_simpl...
- decomp_map_Type Heql0 ; subst.
  destruct x ; inversion Heql0 ; subst.
  apply with_llr2.
  apply IHpi...
  list_simpl...
- inversion f.
Qed.


(** ** 6. import properties *)

Definition i2ac := yalla_ax.i2ac.
Definition i2ac_inj := yalla_ax.i2ac_inj.

(** *** axiom expansion *)

Lemma ax_gen_r : forall A, lprove (A :: nil) A.
Proof.
intro A.
apply illfrag2l.
apply ill.ax_exp_ill.
Qed.

(** *** cut elimination *)

Lemma cut_r : forall A l0 l1 l2 C,
  lprove l0 A -> lprove (l1 ++ A :: l2) C -> lprove (l1 ++ l0 ++ l2) C.
Proof with try eassumption.
intros A l0 l1 l2 C pi1 pi2.
apply l2illfrag in pi1.
apply l2illfrag in pi2 ; list_simpl in pi2.
eapply (@ill.cut_ir_nzeropos_axfree_by_ll _ i2ac_inj) in pi1...
- rewrite <- ? map_app in pi1.
  apply illfrag2l...
- intros a ; destruct a.
- replace (l2ill C :: map l2ill l1 ++ map l2ill l0 ++ map l2ill l2)
    with (map l2ill (C :: l1 ++ l0 ++ l2))
    by (list_simpl ; reflexivity).
  remember (C :: l1 ++ l0 ++ l2) as l ; clear.
  induction l ; constructor...
  clear ; induction a ; try now constructor.
  constructor...
  clear ; intros Hz.
  induction a2 ; try now inversion Hz.
Qed.




