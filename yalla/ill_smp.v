(* ill example file for yalla library *)


(** * Example of a concrete use of the yalla library: ILL *)

From Coq Require Import CMorphisms.
Require Import funtheory List_more Permutation_Type_more Permutation_Type_solve.


(** ** 0. load the [yalla] library *)

Require ill_cut.


(** ** 1. define formulas *)
Inductive iformula : Set :=
| ivar  : iformulas.IAtom -> iformula
| ione  : iformula
| itens : iformula -> iformula -> iformula
| ilmap : iformula -> iformula -> iformula
| itop  : iformula
| iwith : iformula -> iformula -> iformula
| izero : iformula
| iplus : iformula -> iformula -> iformula
| ioc   : iformula -> iformula.


(** ** 2. define embedding into [formulas.formula] *)

Fixpoint ill2ill A :=
match A with
| ivar x    => iformulas.ivar x
| ione      => iformulas.ione
| itens A B => iformulas.itens (ill2ill A) (ill2ill B)
| ilmap A B => iformulas.ilmap (ill2ill A) (ill2ill B)
| itop      => iformulas.itop
| iwith A B => iformulas.iwith (ill2ill A) (ill2ill B)
| izero     => iformulas.izero
| iplus A B => iformulas.iplus (ill2ill A) (ill2ill B)
| ioc A     => iformulas.ioc (ill2ill A)
end.

Lemma ill2ill_inj : injective ill2ill.
Proof.
intros A.
induction A ; intros B Heq ;
  destruct B ; inversion Heq ;
  try apply IHA in H0 ;
  try apply IHA1 in H0 ;
  try apply IHA2 in H1 ; subst ;
  reflexivity.
Qed.

Lemma ill2ill_map_ioc : forall l,
  map ill2ill (map ioc l) = map iformulas.ioc (map ill2ill l).
Proof with try reflexivity.
induction l...
simpl ; rewrite IHl...
Qed.

Lemma ill2ill_map_ioc_inv : forall l1 l2,
  map iformulas.ioc l1 = map ill2ill l2 ->
    { l2' | l2 = map ioc l2' /\ l1 = map ill2ill l2' }.
Proof with try assumption ; try reflexivity.
induction l1 ; intros l2 Heq ;
  destruct l2 ; inversion Heq...
- exists nil ; split...
- apply IHl1 in H1.
  destruct i ; inversion H0 ; subst.
  destruct H1 as (l2' & Heq1 & H1) ; subst.
  exists (i :: l2') ; split...
Qed.


(** ** 3. define proofs *)

Inductive ill : list iformula -> iformula -> Type :=
| ax_ir : forall X, ill (ivar X :: nil) (ivar X)
| ex_ir : forall l1 l2 A, ill l1 A -> Permutation_Type l1 l2 -> ill l2 A
| one_irr : ill nil ione
| one_ilr : forall l A, ill l A -> ill (ione :: l) A
| tens_irr : forall A B l1 l2, ill l1 A -> ill l2 B -> ill (l1 ++ l2) (itens A B)
| tens_ilr : forall A B l C, ill (A :: B :: l) C -> ill (itens A B :: l) C
| lmap_irr : forall A B l, ill (A :: l) B -> ill l (ilmap A B)
| lmap_ilr : forall A B l1 l2 C, ill l1 A -> ill (B :: l2) C -> ill (ilmap A B :: l1 ++ l2) C
| top_irr : forall l, ill l itop
| with_irr : forall A B l, ill l A -> ill l B -> ill l (iwith A B)
| with_ilr1 : forall A B l C, ill (A :: l) C -> ill (iwith A B :: l) C
| with_ilr2 : forall A B l C, ill (A :: l) C -> ill (iwith B A :: l) C
| zero_ilr : forall l C, ill (izero :: l) C
| plus_irr1 : forall A B l, ill l A -> ill l (iplus A B)
| plus_irr2 : forall A B l, ill l A -> ill l (iplus B A)
| plus_ilr : forall A B l C, ill (A :: l) C -> ill (B :: l) C -> ill (iplus A B :: l) C
| oc_irr : forall A l, ill (List.map ioc l) A -> ill (List.map ioc l) (ioc A)
| de_ilr : forall A l C, ill (A :: l) C -> ill (ioc A :: l) C
| wk_ilr : forall A l C, ill l C -> ill (ioc A :: l) C
| co_ilr : forall A l C, ill (ioc A :: ioc A :: l) C -> ill (ioc A :: l) C.

Instance ill_perm {C} : Proper ((@Permutation_Type _) ==> Basics.arrow) (fun l => ill l C).
Proof.
intros l1 l2 HP pi.
eapply ex_ir ; eassumption.
Qed.

(** ** 4. characterize corresponding [ill] fragment *)

Definition ipfrag_ill := ill_def.mk_ipfrag false ill_def.NoIAxioms true.
(*                                         cut           axioms    perm  *)
Definition ill_ll := ill_def.ill ipfrag_ill.

(** ** 5. prove equivalence of proof predicates *)

Lemma ill2illfrag : forall l A, ill l A -> ill_ll (map ill2ill l) (ill2ill A).
Proof with try eassumption ; try reflexivity. 
intros l A pi.
induction pi ; rewrite <- (app_nil_l _) ; try (now constructor) ; try rewrite map_app.
- eapply ill_def.ex_ir...
  apply Permutation_Type_map...
- rewrite app_nil_l ; constructor...
- eapply ill_def.ex_ir.
  + simpl in IHpi2 ; rewrite <- (app_nil_l _) in IHpi2.
    apply (ill_def.lmap_ilr _ _ _ _ _ _ _ IHpi1 IHpi2).
  + simpl ; Permutation_Type_solve.
- simpl ; rewrite ill2ill_map_ioc.
  apply ill_def.oc_irr.
  rewrite <- ill2ill_map_ioc...
Qed.

Lemma illfrag2ill : forall l A, ill_ll (map ill2ill l) (ill2ill A) -> ill l A.
Proof with try eassumption ; try reflexivity.
intros l A pi.
remember (map ill2ill l) as l0 ; remember (ill2ill A) as A0.
revert l Heql0 A HeqA0 ; induction pi ; intros l' Heql0 A' HeqA0 ; subst ;
  try (inversion f ; fail) ;
  try (destruct A'; inversion HeqA0; subst;
         try (symmetry in Heql0; decomp_map_inf Heql0; subst); constructor;
         try (apply IHpi ; try assumption ; try reflexivity ; fail) ;
         try (apply IHpi1 ; try assumption ; try reflexivity ; fail) ;
         try (apply IHpi2 ; try assumption ; try reflexivity ; fail) ; fail).
- destruct A' ; inversion HeqA0.
  destruct l' ; inversion Heql0 ; destruct l' ; inversion Heql0.
  destruct i0 ; inversion H3 ; subst.
  apply ax_ir.
- simpl in p.
  apply Permutation_Type_map_inv in p.
  destruct p as [l'' Heq HP].
  apply Permutation_Type_sym in HP.
  eapply ex_ir...
  apply IHpi...
- symmetry in Heql0; decomp_map_inf Heql0; subst.
  simpl in Heql0; symmetry in Heql0; apply ill2ill_map_ioc_inv in Heql0;
    destruct Heql0 as (l & ? & ?); subst.
  apply Permutation_Type_map_inv in p ; destruct p as [l' Heq HP] ; subst.
  eapply ex_ir ;
    [ apply IHpi ; try reflexivity ;
      rewrite <- ill2ill_map_ioc ; rewrite <- ? map_app | ]...
  apply Permutation_Type_app_head.
  apply Permutation_Type_app_tail.
  symmetry in HP ; apply Permutation_Type_map...
- destruct A' ; inversion HeqA0.
  destruct l' ; inversion Heql0.
  apply one_irr.
- symmetry in Heql0; decomp_map_inf Heql0 ; subst.
  destruct x ; inversion Heql0.
  eapply ex_ir.
  + apply one_ilr.
    apply IHpi...
    rewrite <- ? map_app...
  + Permutation_Type_solve.
- symmetry in Heql0; decomp_map_inf Heql0 ; subst.
  destruct x ; inversion Heql0 ; subst.
  eapply ex_ir.
  + apply tens_ilr.
    eapply (ex_ir _ (x1 :: x2 :: l0 ++ l4)).
    * apply (IHpi (l0 ++ x1 :: x2 :: l4))...
      simpl ; rewrite map_app...
    * Permutation_Type_solve.
  + Permutation_Type_solve.
- symmetry in Heql0; decomp_map_inf Heql0 ; subst.
  destruct x ; inversion Heql0.
- symmetry in Heql0; decomp_map_inf Heql0 ; subst.
  destruct x; inversion Heql2.
- symmetry in Heql0; decomp_map_inf Heql0 ; subst.
  destruct x ; inversion Heql3 ; subst.
  eapply ex_ir.
  + apply lmap_ilr.
    * apply IHpi1...
    * eapply (ex_ir (l3 ++ x2 :: l7) (x2 :: l3 ++ l7)).
      -- apply IHpi2...
         simpl ; rewrite map_app...
      -- Permutation_Type_solve.
  + Permutation_Type_solve.
- symmetry in Heql0; decomp_map_inf Heql0 ; subst.
  destruct x; inversion Heql0.
- symmetry in Heql0; decomp_map_inf Heql0 ; subst.
  destruct x ; inversion Heql0 ; subst.
  eapply ex_ir.
  + apply with_ilr1.
    eapply (ex_ir _ (x1 :: l0 ++ l4)).
    * apply (IHpi (l0 ++ x1 :: l4))...
      simpl ; rewrite map_app...
    * Permutation_Type_solve.
  + Permutation_Type_solve.
- symmetry in Heql0; decomp_map_inf Heql0 ; subst.
  destruct x ; inversion Heql0 ; subst.
  eapply ex_ir.
  + apply with_ilr2.
    eapply (ex_ir _ (x2 :: l0 ++ l4)).
    * apply (IHpi (l0 ++ x2 :: l4))...
      simpl ; rewrite map_app...
    * Permutation_Type_solve.
  + Permutation_Type_solve.
- symmetry in Heql0; decomp_map_inf Heql0 ; subst.
  destruct x ; inversion Heql0 ; subst.
  eapply ex_ir.
  + eapply (zero_ilr (l0 ++ l4)).
  + Permutation_Type_solve.
- symmetry in Heql0; decomp_map_inf Heql0 ; subst.
  destruct x ; inversion Heql0 ; subst.
  eapply ex_ir.
  + apply plus_ilr.
    * eapply (ex_ir _ (x1 :: l0 ++ l4)).
      -- apply (IHpi1 (l0 ++ x1 :: l4))...
         simpl ; rewrite map_app...
      -- Permutation_Type_solve.
    * eapply (ex_ir _ (x2 :: l0 ++ l4)).
      -- apply (IHpi2 (l0 ++ x2 :: l4))...
         simpl ; rewrite map_app...
      -- Permutation_Type_solve.
  + Permutation_Type_solve.
- destruct A' ; inversion HeqA0 ; subst.
  apply ill2ill_map_ioc_inv in Heql0.
  destruct Heql0 as (l'' & Heq1 & Heq2) ; subst.
  apply oc_irr.
  apply IHpi...
  symmetry ; apply ill2ill_map_ioc.
- symmetry in Heql0; decomp_map_inf Heql0 ; subst.
  destruct x ; inversion Heql0 ; subst.
  eapply ex_ir.
  + apply de_ilr.
    eapply (ex_ir _ (x :: l0 ++ l4)).
    * apply (IHpi (l0 ++ x :: l4))...
      simpl ; rewrite map_app...
    * Permutation_Type_solve.
  + Permutation_Type_solve.
- symmetry in Heql0; decomp_map_inf Heql0 ; subst.
  destruct x ; inversion Heql0 ; subst.
  eapply ex_ir.
  + apply wk_ilr.
    apply (IHpi (l0 ++ l4))...
    simpl ; rewrite map_app...
  + Permutation_Type_solve.
- symmetry in Heql0; decomp_map_inf Heql0 ; subst.
  destruct x ; inversion Heql0 ; subst.
  eapply ex_ir.
  + apply co_ilr.
    eapply (ex_ir _ (ioc x :: ioc x :: l0 ++ l4)).
    * apply (IHpi (l0 ++ ioc x :: ioc x :: l4))...
      simpl ; rewrite map_app...
    * Permutation_Type_solve.
  + Permutation_Type_solve.
- destruct a.
Qed.


(** ** 6. import properties *)

(** *** axiom expansion *)

Lemma ax_gen_r : forall A, ill (A :: nil) A.
Proof.
intro A.
apply illfrag2ill.
apply ill_def.ax_exp_ill.
Qed.

(** *** cut admissibility *)

Lemma cut_r : forall A l1 l2 C, 
  ill l1 A -> ill (A :: l2) C -> ill (l1 ++ l2) C.
Proof with try eassumption.
intros A l1 l2 C pi1 pi2.
apply illfrag2ill.
rewrite map_app.
rewrite <- (app_nil_l _).
apply ill2illfrag in pi1.
apply ill2illfrag in pi2.
eapply ill_cut.cut_ir_axfree...
intros a ; destruct a.
Qed.
