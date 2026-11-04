From Stdlib Require Import CMorphisms.
From OLlibs Require Import funtheory List_more PermutationT_more.
From Yalla Require Import ill_cut.
From NanoYalla Require Export macroill. (* order matters *)

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Proof Using Clear Unused.
Set Implicit Arguments.


Instance ex_iPermutationT : Proper ((@PermutationT _) ==> eq ==> iffT) ill.
Proof.
intros ? ? HP ? C ->.
refine (PermutationT_rect_transp (fun l1 l2 => iffT (ill l1 C) (ill l2 C)) _ _ _ HP);
 try now split; auto using ex_t_ir.
intros l l' l'' HP' [] HP'' []. split; auto.
Qed.

Fixpoint nill2ill A :=
match A with
| ivar x    => @iformulas.ivar nat_infdectype (Some x)
| ione      => iformulas.ione
| itens A B => iformulas.itens (nill2ill A) (nill2ill B)
| ilmap A B => iformulas.ilmap (nill2ill A) (nill2ill B)
| itop      => iformulas.itop
| iwith A B => iformulas.iwith (nill2ill A) (nill2ill B)
| izero     => iformulas.izero
| iplus A B => iformulas.iplus (nill2ill A) (nill2ill B)
| ioc A     => iformulas.ioc (nill2ill A)
end.

Lemma nill2ill_inj : injective nill2ill.
Proof.
intro A. induction A; intros B Heq; destruct B; inversion Heq;
  try apply IHA in H0; try apply IHA1 in H0; try apply IHA2 in H1; subst; reflexivity.
Qed.

Lemma nill2ill_map_ioc l : map nill2ill (map ioc l) = map iformulas.ioc (map nill2ill l).
Proof. induction l as [ | a l IHl ]; [ | cbn in *; rewrite IHl ]; reflexivity. Qed.

Lemma nill2ill_map_ioc_inv l1 l2 : map iformulas.ioc l1 = map nill2ill l2 ->
  { l2' | l2 = map ioc l2' & l1 = map nill2ill l2' }.
Proof.
induction l1 in l2 |- *; intro Heq; destruct l2; inversion Heq.
- exists nil; reflexivity.
- apply IHl1 in H1.
  destruct i; destr_eq H0; subst.
  destruct H1 as [l2' -> ->].
  exists (i :: l2'); reflexivity.
Qed.

Definition ill_ll := @ill_ll nat_infdectype.

Lemma nill2illfrag l A : ill l A -> ill_ll (map nill2ill l) (nill2ill A).
Proof.
intros pi. induction pi; rewrite <- (app_nil_l _); try (now constructor); rewrite ? map_app.
- eapply ill_def.ex_ir; [ eassumption | ].
  rewrite map_app. cbn. apply PermutationT_app_head, PermutationT_swap.
- rewrite app_nil_l. constructor; assumption.
- eapply ill_def.ex_ir.
  + cbn in IHpi2. rewrite <- (app_nil_l _) in IHpi2. exact (ill_def.lmap_ilr _ _ _ _ _ _ IHpi1 IHpi2).
  + cbn. symmetry. apply PermutationT_cons_app. rewrite map_app. reflexivity.
- cbn. rewrite nill2ill_map_ioc. apply ill_def.oc_irr.
  rewrite <-nill2ill_map_ioc. assumption.
Qed.

Lemma illfrag2nill l A : ill_ll (map nill2ill l) (nill2ill A) -> ill l A.
Proof.
intro pi. remember (map nill2ill l) as l0 eqn:Heql0. remember (nill2ill A) as A0 eqn:HeqA0.
revert l Heql0 A HeqA0; induction pi; intros l' Heql0 A' HeqA0; subst;
  try discriminate f;
  try (now destruct A'; destr_eq HeqA0; subst;
         try (symmetry in Heql0; decomp_map_eq Heql0; subst); constructor;
         try (now apply IHpi); try (now apply IHpi1); try (now apply IHpi2));
  try change map with List.map in Heql0.
- destruct A'; destr_eq HeqA0.
  destruct l'; inversion Heql0; destruct l'; destr_eq Heql0.
  destruct i0; destr_eq H0. subst. injection H0 as [= ->].
  apply ax_ir.
- cbn in p. apply PermutationT_map_inv in p as [l'' Heq HP%PermutationT_sym].
  eapply ex_iPermutationT; [ symmetry in HP; eassumption | reflexivity | ].
  apply IHpi; [ assumption | reflexivity ].
- remember (ListDef.map iformulas.ioc lw') as l0.
  decomp_map_eq Heql0 eqn:Heq. subst.
  symmetry in Heq. apply nill2ill_map_ioc_inv in Heq as [l -> ->].
  apply PermutationT_map_inv in p as [l' -> HP%PermutationT_sym].
  eapply ex_iPermutationT;
     [ | reflexivity | apply IHpi; [ rewrite <-nill2ill_map_ioc, <-?map_app | ]; reflexivity ].
  apply PermutationT_app_head, PermutationT_app_tail, PermutationT_map. symmetry. assumption.
- decomp_map_eq Heql0. subst.
  destruct A'; destr_eq HeqA0.
  apply one_irr.
- decomp_map_eq Heql0 eqn:Heq. subst.
  destruct x; destr_eq Heq.
  apply one_ilr_ext, IHpi; [ rewrite map_app | ]; reflexivity.
- decomp_map_eq Heql0. subst.
  destruct A'; destr_eq HeqA0. subst.
  apply tens_irr; [ apply IHpi1 | apply IHpi2 ]; reflexivity.
- decomp_map_eq Heql0 eqn:Heq. subst l'.
  destruct x; destr_eq Heq. subst.
  apply tens_ilr_ext, IHpi; [ rewrite map_app | ]; reflexivity.
- decomp_map_eq Heql0 eqn:Heq. subst l'.
  destruct x; destr_eq Heq.
- decomp_map_eq Heql0 eqn:Heq. subst l'.
  destruct x; destr_eq Heq. subst.
  eapply (@ex_iPermutationT (ilmap x1 x2 :: l0 ++ l1 ++ l2)).
  + cons2app. rewrite !app_assoc. apply PermutationT_app_tail. rewrite <-!app_assoc, PermutationT_app_comm.
    rewrite app_assoc. apply PermutationT_app_tail, PermutationT_app_comm.
  + reflexivity.
  + apply lmap_ilr.
    * apply IHpi1; reflexivity.
    * eapply (@ex_iPermutationT (l1 ++ x2 :: l2)).
      -- symmetry. apply PermutationT_middle.
      -- reflexivity.
      -- apply IHpi2; [ cbn; rewrite map_app | ]; reflexivity.
- decomp_map_eq Heql0 eqn:Heq. subst l'.
  destruct x; destr_eq Heq. subst.
  apply with_ilr1_ext, IHpi; [ cbn; rewrite map_app | ]; reflexivity.
- decomp_map_eq Heql0 eqn:Heq. subst l'.
  destruct x; destr_eq Heq. subst.
  apply with_ilr2_ext, IHpi; [ cbn; rewrite map_app | ]; reflexivity.
- decomp_map_eq Heql0 eqn:Heq. subst l'.
  destruct x; destr_eq Heq.
  apply zero_ilr_ext.
- decomp_map_eq Heql0 eqn:Heq. subst l'.
  destruct x; destr_eq Heq. subst.
  apply plus_ilr_ext.
  + apply (IHpi1 (l1 ++ x1 :: l2)); [ cbn; rewrite map_app | ]; reflexivity.
  + apply (IHpi2 (l1 ++ x2 :: l2)); [ cbn; rewrite map_app | ]; reflexivity.
- destruct A'; destr_eq HeqA0. subst.
  apply nill2ill_map_ioc_inv in Heql0 as [l'' -> -> ].
  apply oc_irr, IHpi; [ | reflexivity ].
  symmetry. apply nill2ill_map_ioc.
- decomp_map_eq Heql0 eqn:Heq. subst l'.
  destruct x; destr_eq Heq. subst.
  apply de_ilr_ext, IHpi; [ cbn; rewrite map_app | ]; reflexivity.
- decomp_map_eq Heql0 eqn:Heq. subst l'.
  destruct x; destr_eq Heq. subst.
  apply wk_ilr_ext, IHpi; [ cbn; rewrite map_app | ]; reflexivity.
- decomp_map_eq Heql0 eqn:Heq. subst l'.
  destruct x; destr_eq Heq. subst.
  apply co_ilr_ext, IHpi; [ cbn; rewrite map_app | ]; reflexivity.
- destruct a.
Qed.

Lemma cut_ir : icut_admissibility.
Proof.
intros A l1 l2 C pi1%nill2illfrag pi2%nill2illfrag. apply illfrag2nill.
rewrite map_app.
refine (ill_cut.cut_ir_axfree _ nil _ pi1 pi2). intros [].
Qed.

Definition cut_ir_ext := cut_ir.
