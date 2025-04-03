(** * Example of a concrete use of the yalla library: ILL *)

From Stdlib Require Import CMorphisms.
From OLlibs Require Import funtheory dectype List_more PermutationT_more.


(** ** 0. load the [yalla] library *)

From Yalla Require ill_cut.

Set Default Proof Using "Type".
Set Implicit Arguments.


Section Atoms.

Context {preiatom : DecType}.

(** ** 1. define formulas *)
Inductive iformula :=
| ivar (_ : @iformulas.iatom preiatom)
| ione | itens (_ _ : iformula) | ilmap (_ _ : iformula)
| itop | iwith (_ _ : iformula) | izero | iplus (_ _ : iformula)
| ioc (_ : iformula).


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
intro A. induction A; intros B Heq; destruct B; inversion Heq;
  try apply IHA in H0; try apply IHA1 in H0; try apply IHA2 in H1; subst; reflexivity.
Qed.

Lemma ill2ill_map_ioc l : map ill2ill (map ioc l) = map iformulas.ioc (map ill2ill l).
Proof. induction l as [|a l IHl]; [ | cbn; rewrite IHl ]; reflexivity. Qed.

Lemma ill2ill_map_ioc_inv l1 l2 :
  map iformulas.ioc l1 = map ill2ill l2 -> { l2' | l2 = map ioc l2' & l1 = map ill2ill l2' }.
Proof.
induction l1 in l2 |- *; intro Heq; destruct l2; inversion Heq.
- exists nil; reflexivity.
- apply IHl1 in H1.
  destruct i; destr_eq H0; subst.
  destruct H1 as [l2' -> ->].
  exists (i :: l2'); reflexivity.
Qed.


(** ** 3. define proofs *)

Inductive ill : list iformula -> iformula -> Type :=
| ax_ir X : ill (ivar X :: nil) (ivar X)
| ex_ir l1 l2 A : ill l1 A -> PermutationT l1 l2 -> ill l2 A
| one_irr : ill nil ione
| one_ilr l A : ill l A -> ill (ione :: l) A
| tens_irr A B l1 l2 : ill l1 A -> ill l2 B -> ill (l1 ++ l2) (itens A B)
| tens_ilr A B l C : ill (A :: B :: l) C -> ill (itens A B :: l) C
| lmap_irr A B l : ill (A :: l) B -> ill l (ilmap A B)
| lmap_ilr A B l1 l2 C : ill l1 A -> ill (B :: l2) C -> ill (ilmap A B :: l1 ++ l2) C
| top_irr l : ill l itop
| with_irr A B l : ill l A -> ill l B -> ill l (iwith A B)
| with_ilr1 A B l C : ill (A :: l) C -> ill (iwith A B :: l) C
| with_ilr2 A B l C : ill (A :: l) C -> ill (iwith B A :: l) C
| zero_ilr l C : ill (izero :: l) C
| plus_irr1 A B l : ill l A -> ill l (iplus A B)
| plus_irr2 A B l : ill l A -> ill l (iplus B A)
| plus_ilr A B l C : ill (A :: l) C -> ill (B :: l) C -> ill (iplus A B :: l) C
| oc_irr A l : ill (List.map ioc l) A -> ill (List.map ioc l) (ioc A)
| de_ilr A l C : ill (A :: l) C -> ill (ioc A :: l) C
| wk_ilr A l C : ill l C -> ill (ioc A :: l) C
| co_ilr A l C : ill (ioc A :: ioc A :: l) C -> ill (ioc A :: l) C.

Instance ill_perm C : Proper ((@PermutationT _) ==> arrow) (fun l => ill l C).
Proof. intros l1 l2 HP pi. eapply ex_ir; eassumption. Qed.

(** ** 4. characterize corresponding [ill] fragment *)

Definition ipfrag_ill := @ill_def.mk_ipfrag preiatom ill_def.ipcut_none ill_def.NoIAxioms true.
(*                                          atoms    cut                axioms    perm  *)
Definition ill_ll := ill_def.ill ipfrag_ill.

(** ** 5. prove equivalence of proof predicates *)

Lemma ill2illfrag l A : ill l A -> ill_ll (map ill2ill l) (ill2ill A).
Proof.
intros pi. induction pi; rewrite <- (app_nil_l _); try (now constructor); rewrite ? map_app.
- eapply ill_def.ex_ir; [ eassumption | ].
  apply PermutationT_map. assumption.
- rewrite app_nil_l. constructor; assumption.
- eapply ill_def.ex_ir.
  + cbn in IHpi2. rewrite <- (app_nil_l _) in IHpi2. exact (ill_def.lmap_ilr _ _ _ _ _ _ IHpi1 IHpi2).
  + cbn. symmetry. apply PermutationT_cons_app. rewrite map_app. reflexivity.
- cbn. rewrite ill2ill_map_ioc. apply ill_def.oc_irr.
  rewrite <- ill2ill_map_ioc. assumption.
Qed.

Lemma illfrag2ill l A : ill_ll (map ill2ill l) (ill2ill A) -> ill l A.
Proof.
intros pi.
remember (map ill2ill l) as l0 eqn:Heql0. remember (ill2ill A) as A0 eqn:HeqA0.
revert l Heql0 A HeqA0; induction pi; intros l' Heql0 A' HeqA0; subst;
  try discriminate f;
  try (now destruct A'; destr_eq HeqA0; subst;
         try (symmetry in Heql0; decomp_map Heql0; subst); constructor;
         try (now apply IHpi); try (now apply IHpi1); try (now apply IHpi2)).
- destruct A'; destr_eq HeqA0.
  destruct l'; inversion Heql0; destruct l'; destr_eq Heql0.
  destruct i0; destr_eq H0; subst.
  apply ax_ir.
- cbn in p. apply PermutationT_map_inv in p as [l'' Heq HP%PermutationT_sym].
  eapply ex_ir; [ | eassumption ].
  apply IHpi; [ assumption | reflexivity ].
- remember (map iformulas.ioc lw') as l0.
  decomp_map Heql0 eqn:Heq. subst.
  symmetry in Heq. apply ill2ill_map_ioc_inv in Heq as [l -> ->].
  apply PermutationT_map_inv in p as [l' -> HP%PermutationT_sym].
  eapply ex_ir; [ apply IHpi; [ | reflexivity];
                  rewrite <- ill2ill_map_ioc, <- ? map_app; reflexivity | ].
  apply PermutationT_app_head, PermutationT_app_tail, PermutationT_map. assumption.
- decomp_map Heql0 eqn:Heq. subst l'.
  destruct x; destr_eq Heq.
  eapply ex_ir.
  + apply one_ilr.
    apply IHpi; [ rewrite <- ! map_app | ]; reflexivity.
  + apply PermutationT_middle.
- decomp_map Heql0 eqn:Heq. subst l'.
  destruct x; destr_eq Heq. subst.
  eapply ex_ir.
  + apply tens_ilr.
    eapply (@ex_ir _ (x1 :: x2 :: l1 ++ l2)).
    * apply (IHpi (l1 ++ x1 :: x2 :: l2)); [ cbn; rewrite map_app | ]; reflexivity.
    * symmetry. apply PermutationT_cons_app, PermutationT_middle.
  + apply PermutationT_middle.
- decomp_map Heql0 eqn:Heq. subst l'.
  destruct x; destr_eq Heq.
- decomp_map Heql0 eqn:Heq. subst l'.
  destruct x; destr_eq Heq.
- decomp_map Heql0 eqn:Heq. subst l'.
  destruct x; destr_eq Heq. subst.
  eapply ex_ir.
  + apply lmap_ilr.
    * apply IHpi1; reflexivity.
    * eapply (@ex_ir (l1 ++ x2 :: l2) (x2 :: l1 ++ l2)).
      -- apply IHpi2; [ cbn; rewrite map_app | ]; reflexivity.
      -- symmetry. apply PermutationT_middle.
  + rewrite ? app_assoc.
    apply PermutationT_cons_app, PermutationT_app_tail, PermutationT_app_comm.
- decomp_map Heql0 eqn:Heq. subst l'. destruct Heq as [Heq _].
  destruct x; destr_eq Heq.
- decomp_map Heql0 eqn:Heq. subst l'.
  destruct x; destr_eq Heq. subst.
  eapply ex_ir.
  + apply with_ilr1.
    eapply (@ex_ir _ (x1 :: l1 ++ l2)).
    * apply (IHpi (l1 ++ x1 :: l2)); [ cbn; rewrite map_app | ]; reflexivity.
    * symmetry. apply PermutationT_middle.
  + apply PermutationT_middle.
- decomp_map Heql0 eqn:Heq. subst l'.
  destruct x; destr_eq Heq. subst.
  eapply ex_ir.
  + apply with_ilr2.
    eapply (@ex_ir _ (x2 :: l1 ++ l2)).
    * apply (IHpi (l1 ++ x2 :: l2)); [ cbn; rewrite map_app | ]; reflexivity.
    * symmetry. apply PermutationT_middle.
  + apply PermutationT_middle.
- decomp_map Heql0 eqn:Heq. subst l'.
  destruct x; destr_eq Heq.
  eapply ex_ir; [ | apply PermutationT_middle ].
  apply zero_ilr.
- decomp_map Heql0 eqn:Heq. subst l'.
  destruct x; destr_eq Heq. subst.
  eapply ex_ir.
  + apply plus_ilr.
    * eapply (@ex_ir _ (x1 :: l1 ++ l2)).
      -- apply (IHpi1 (l1 ++ x1 :: l2)); [ cbn; rewrite map_app | ]; reflexivity.
      -- symmetry. apply PermutationT_middle.
    * eapply (@ex_ir _ (x2 :: l1 ++ l2)).
      -- apply (IHpi2 (l1 ++ x2 :: l2)); [ cbn; rewrite map_app | ]; reflexivity.
      -- symmetry. apply PermutationT_middle.
  + apply PermutationT_middle.
- destruct A'; destr_eq HeqA0. subst.
  apply ill2ill_map_ioc_inv in Heql0 as [l'' -> -> ].
  apply oc_irr, IHpi; [ | reflexivity ].
  symmetry. apply ill2ill_map_ioc.
- decomp_map Heql0 eqn:Heq. subst l'.
  destruct x; destr_eq Heq. subst.
  eapply ex_ir.
  + apply de_ilr.
    eapply (@ex_ir _ (x :: l1 ++ l2)).
    * apply (IHpi (l1 ++ x :: l2)); [ cbn; rewrite map_app | ]; reflexivity.
    * symmetry. apply PermutationT_middle.
  + apply PermutationT_middle.
- decomp_map Heql0 eqn:Heq. subst l'.
  destruct x; destr_eq Heq. subst.
  eapply ex_ir.
  + apply wk_ilr.
    apply (IHpi (l1 ++ l2)); [ cbn; rewrite map_app | ]; reflexivity.
  + apply PermutationT_middle.
- decomp_map Heql0 eqn:Heq. subst l'.
  destruct x; destr_eq Heq. subst.
  eapply ex_ir.
  + apply co_ilr.
    eapply (@ex_ir _ (ioc x :: ioc x :: l1 ++ l2)).
    * apply (IHpi (l1 ++ ioc x :: ioc x :: l2)); [ cbn; rewrite map_app | ]; reflexivity.
    * symmetry.
      etransitivity; [ apply PermutationT_cons_app, PermutationT_cons_app | ]; reflexivity.
  + apply PermutationT_middle.
- destruct a.
Qed.


(** ** 6. import properties *)

(** *** axiom expansion *)

Lemma ax_gen_r A : ill (A :: nil) A.
Proof. apply illfrag2ill, ill_def.ax_exp_ill. Qed.

(** *** cut admissibility *)

Lemma cut_r A l1 l2 C : ill l1 A -> ill (A :: l2) C -> ill (l1 ++ l2) C.
Proof.
intros pi1%ill2illfrag pi2%ill2illfrag.
apply illfrag2ill.
rewrite map_app, <- (app_nil_l _).
eapply ill_cut.cut_ir_axfree; [ intros [] | | ]; eassumption.
Qed.

End Atoms.
