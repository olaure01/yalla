(* lambek example file for yalla library *)
(* Coq 8.6 *)
(* v 1.0   Olivier Laurent *)


(** * Example of a concrete use of the yalla library: a variant of the Lambek calculus
  tensor-free Lambek calculus with additive conjunction and its unit *)


Require Import Injective.
Require Import List_more.

(** ** 0. load the [ill] library *)

Require ill.


(** ** 1. define formulas *)

Inductive lform  : Set :=
| lvar  : iformulas.IAtom -> lform
| ltop  : lform
| lwith : lform -> lform -> lform
| lmap  : lform -> lform -> lform.


(** ** 2. define embedding into [iformulas.iformula] *)

(** allow the use of the formula [top] in [ill] but not [zero] *)
Axiom ft : iformulas.iftop = true.
Axiom fz : iformulas.ifzer = false.

Definition Itop := @iformulas.itop ft.

Fixpoint l2ill A :=
match A with
| lvar x    => iformulas.ivar x
| ltop      => Itop
| lwith A B => iformulas.iwith (l2ill A) (l2ill B)
| lmap A B  => iformulas.ilmap (l2ill A) (l2ill B)
end.

Lemma l2ill_inj : injective l2ill.
Proof with try reflexivity.
intros A.
induction A ; intros B Heq ;
  destruct B ; inversion Heq ;
  try apply IHA1 in H0 ;
  try apply IHA2 in H1 ; subst...
Qed.


(** ** 3. define proofs *)

Inductive lprove : list lform -> lform -> Prop :=
| ax_lr   : forall X, lprove (lvar X :: nil) (lvar X)
| top_lrr  : forall l, lprove l ltop
| with_lrr : forall A B l, lprove l A -> lprove l B -> lprove l (lwith A B)
| with_llr1 : forall A B C l1 l2, lprove (l1 ++ A :: l2) C ->
                                  lprove (l1 ++ lwith A B :: l2) C
| with_llr2 : forall A B C l1 l2, lprove (l1 ++ A :: l2) C ->
                                  lprove (l1 ++ lwith B A :: l2) C
| lmap_lrr  : forall A B l, lprove (l ++ A :: nil) B -> lprove l (lmap A B)
| lmap_llr : forall A B C l1 l2 l3,
                  lprove l2 A -> lprove (l1 ++ B :: l3) C ->
                  lprove (l1 ++ lmap A B :: l2 ++ l3) C.


(** ** 4. characterize corresponding [ill] fragment *)

(** cut / axioms / permutation *)
Definition ipfrag_lambek := ill.mk_ipfrag false (fun _ _ => False) false.
(*                                        cut   axioms             perm  *)


(** ** 5. prove equivalence of proof predicates *)

Lemma l2illfrag : forall l A, lprove l A ->
  exists s, ill.ill ipfrag_lambek (map l2ill l) (l2ill A) s.
Proof with try reflexivity ; try eassumption.
intros l A pi.
induction pi ;
  try destruct IHpi as [s' pi'] ;
  try destruct IHpi1 as [s1' pi1'] ;
  try destruct IHpi2 as [s2' pi2'] ;
  eexists ;
  try (simpl in pi' ; rewrite ? map_app in pi') ;
  try (simpl in pi1' ; rewrite ? map_app in pi1') ;
  try (simpl in pi2' ; rewrite ? map_app in pi2') ;
  simpl ; rewrite ? map_app ;
  simpl ; rewrite ? map_app ;
  try (constructor ; eassumption ; fail).
Qed.

Lemma illfrag2l : forall l A s,
  ill.ill ipfrag_lambek (map l2ill l) (l2ill A) s -> lprove l A.
Proof with try eassumption ; try reflexivity.
intros l A s pi.
remember (map l2ill l) as l0.
remember (l2ill A) as A0.
revert l A Heql0 HeqA0 ; induction pi ;
  intros l' A' Heql0 HeqA0 ; subst ;
  try (destruct A' ; inversion HeqA0 ; fail) ;
  try (decomp_map Heql0 ;
       destruct x ; inversion Heql0 ; fail) ;
  try (decomp_map Heql0 ;
       destruct x ; inversion Heql3 ; fail).
- destruct A' ; inversion HeqA0.
  destruct l' ; inversion Heql0 ;
    destruct l' ; inversion Heql0.
  destruct l ; inversion H3 ; subst ; subst.
  apply ax_lr.
- apply IHpi...
- destruct A' ; inversion HeqA0 ; subst.
  apply lmap_lrr.
  apply IHpi...
  rewrite map_last...
- decomp_map Heql0 ; subst.
  destruct x ; inversion Heql0 ; subst.
  apply lmap_llr.
  + apply IHpi1...
  + apply IHpi2...
    list_simpl...
- destruct A' ; inversion HeqA0 ; subst.
  apply top_lrr.
- destruct A' ; inversion HeqA0 ; subst.
  apply with_lrr.
  + apply IHpi1...
  + apply IHpi2...
- decomp_map Heql0 ; subst.
  destruct x ; inversion Heql0 ; subst.
  apply with_llr1.
  apply IHpi...
  list_simpl...
- decomp_map Heql0 ; subst.
  destruct x ; inversion Heql0 ; subst.
  apply with_llr2.
  apply IHpi...
  list_simpl...
- inversion f.
- inversion H.
Qed.


(** ** 6. import properties *)

Parameter i2a : iformulas.IAtom -> formulas.Atom.
Axiom i2a_inj : injective i2a.

(** *** axiom expansion *)

Lemma ax_gen_r : forall A, lprove (A :: nil) A.
Proof.
intro A.
destruct (@ill.ax_exp_ill fz i2a i2a_inj ipfrag_lambek (l2ill A))
  as [s Hax].
eapply illfrag2l.
eassumption.
Qed.

(** *** cut elimination *)

Lemma cut_r : forall A l0 l1 l2 C,
  lprove l0 A -> lprove (l1 ++ A :: l2) C -> lprove (l1 ++ l0 ++ l2) C.
Proof with try eassumption.
intros A l0 l1 l2 C pi1 pi2.
destruct (l2illfrag _ _ pi1) as [s1 pi1'].
destruct (l2illfrag _ _ pi2) as [s2 pi2'] ; list_simpl in pi2'.
eapply (@ill.cut_ir_axfree fz i2a i2a_inj) in pi1'...
- destruct pi1' as [s pi].
  rewrite <- ? map_app in pi.
  eapply illfrag2l...
- intros l B Hax ; inversion Hax.
Qed.




