(** * Atomic cut admissibility for Intuitionistic Linear Logic *)

From OLlibs Require Import dectype List_more GPermutation_Type.
From Yalla Require Export ill_def.

Set Default Proof Using "Type".
Set Implicit Arguments.


Section Atoms.

Context {preiatom : DecType} {P : @ipfrag preiatom}.
Variable P_gax_noN_l : noN_iax P.
Variable X : option preiatom.
Variable P_gax_cut : forall b l1 l2, fst (projT2 (ipgax P) b) = l1 ++ ivar X :: l2 ->
  forall a, snd (projT2 (ipgax P) a) = ivar X ->
  { c | l1 ++ fst (projT2 (ipgax P) a) ++ l2 = fst (projT2 (ipgax P) c)
      & snd (projT2 (ipgax P) b) = snd (projT2 (ipgax P) c) }.

Lemma subs_gax_l l0 l1 l2 b : fst (projT2 (ipgax P) b) = l1 ++ ivar X :: l2 ->
  ill P l0 (ivar X) -> ill P (l1 ++ l0 ++ l2) (snd (projT2 (ipgax P) b)).
Proof using P_gax_noN_l P_gax_cut.
intros Hb pi. remember (ivar X) as A eqn:HeqX.
induction pi; inversion HeqX; subst;
  try (list_simpl; rewrite app_assoc; constructor;
       list_simpl; rewrite ? app_comm_cons, (app_assoc l0); apply IHpi; assumption).
- cbn. rewrite <- Hb. apply (gax_ir b).
- apply (ex_ir (l1 ++ l0 ++ l2)).
  + apply IHpi; assumption.
  + apply PEPermutation_Type_app_head, PEPermutation_Type_app_tail. assumption.
- list_simpl. rewrite app_assoc. eapply ex_oc_ir; [ | eassumption ].
  list_simpl. rewrite (app_assoc l0), (app_assoc _ l3), <- (app_assoc l0). apply IHpi; assumption.
- list_simpl. rewrite app_assoc. apply lpam_ilr; [ assumption | ].
  list_simpl. rewrite ? app_comm_cons, (app_assoc l3). apply IHpi2; assumption.
- exfalso. apply (P_gax_noN_l b). rewrite Hb. apply in_inf_elt.
- list_simpl. rewrite app_assoc. apply lmap_ilr; [ assumption | ].
  list_simpl. rewrite app_comm_cons, (app_assoc l3). apply IHpi2; assumption.
- exfalso. apply (P_gax_noN_l b). rewrite Hb. apply in_inf_elt.
- list_simpl. rewrite app_assoc.
  apply plus_ilr; list_simpl; rewrite app_comm_cons, (app_assoc l0); [ apply IHpi1 | apply IHpi2 ]; assumption.
- list_simpl. rewrite app_assoc. apply cut_ir with A; [ assumption .. | ].
  list_simpl. rewrite app_comm_cons, (app_assoc l3). apply IHpi2; assumption.
- destruct (P_gax_cut b _ _ Hb a eq_refl) as [? -> ->]. apply gax_ir.
Qed.

Lemma cut_at_ir_gax l0 l1 l2 C :
  ill P l0 (ivar X) -> ill P (l1 ++ ivar X :: l2) C -> ill P (l1 ++ l0 ++ l2) C.
Proof using P_gax_noN_l P_gax_cut.
intros pi1 pi2. remember (l1 ++ ivar X :: l2) as l eqn:Heql.
induction pi2 in l1, l2, Heql |- *; subst;
  try (constructor; list_simpl; rewrite ? app_comm_cons; apply IHpi2; list_simpl; reflexivity);
  try (trichot_elt_elt_inf_exec Heql;
       [ list_simpl; constructor; rewrite ? app_comm_cons, app_assoc; apply IHpi2; list_simpl; reflexivity
       | inversion Heql1
       | rewrite 2 app_assoc; constructor; list_simpl; apply IHpi2; list_simpl; reflexivity ]).
- unit_vs_elt_inv Heql. injection Heql as [= ->]. list_simpl. assumption.
- apply PEPermutation_Type_vs_elt_subst in p as [(l4, l5) HP ->].
  specialize (HP l0). symmetry in HP. refine (ex_ir _ _ _ _ HP).
  apply IHpi2. reflexivity.
- dichot_elt_app_inf_exec Heql; subst.
  + rewrite 2 app_assoc. eapply ex_oc_ir; [ | eassumption ].
    list_simpl. apply IHpi2. list_simpl. reflexivity.
  + dichot_elt_app_inf_exec Heql1; subst.
    * symmetry in Heql0. decomp_map_inf Heql0. discriminate Heql0.
    * rewrite <- 2 app_assoc. eapply ex_oc_ir; [ | eassumption ]. rewrite 2 app_assoc.
      apply IHpi2. list_simpl. reflexivity.
- nil_vs_elt_inv Heql.
- dichot_elt_app_inf_exec Heql; subst.
  + rewrite 2 app_assoc. apply tens_irr; [ | assumption ].
    list_simpl. apply IHpi2_1. reflexivity.
  + rewrite <- app_assoc. apply tens_irr; [ assumption | ].
    apply IHpi2_2. reflexivity.
- trichot_elt_elt_inf_exec Heql.
  + dichot_elt_app_inf_exec Heql1; subst.
    * list_simpl. rewrite (app_assoc l), (app_assoc (l ++ l0)). apply lpam_ilr; [ | assumption ].
      list_simpl. apply IHpi2_1. reflexivity.
    * list_simpl. apply lpam_ilr; [ assumption | ].
      rewrite app_comm_cons, app_assoc. apply IHpi2_2. list_simpl. reflexivity.
  + discriminate Heql1.
  + rewrite 2 app_assoc. apply lpam_ilr; [ assumption | ].
    list_simpl. apply IHpi2_2. list_simpl. reflexivity.
- destruct l1; inversion Heql; subst.
  list_simpl. apply gen_ilr, IHpi2. reflexivity.
- rewrite app_assoc in Heql. trichot_elt_elt_inf_exec Heql.
  + list_simpl. apply lmap_ilr; [ assumption | ].
    rewrite app_comm_cons, app_assoc. apply IHpi2_2. list_simpl. reflexivity.
  + discriminate Heql1.
  + dichot_elt_app_inf_exec Heql0; subst.
    * list_simpl. rewrite 2 app_assoc. apply lmap_ilr; [ assumption | ].
      list_simpl. apply IHpi2_2. list_simpl. reflexivity.
    * list_simpl. rewrite (app_assoc l6), (app_assoc (l6 ++ l0)). apply lmap_ilr; [ | assumption ].
      list_simpl. apply IHpi2_1. reflexivity.
- assert ({l2' | l2 = l2' ++ ineg A :: nil & l = l1 ++ ivar X :: l2' }) as [l2' -> ->].
  { clear - Heql. induction l2 in Heql |- * using rev_rect.
    + exfalso. enough (ineg A = ivar X) as Hd by discriminate Hd.
      rewrite <- (last_last l1 (ivar X) (ivar X)), <- (last_last l (ineg A) (ivar X)), Heql. reflexivity.
    + rewrite app_comm_cons, app_assoc in Heql. apply app_inj_tail in Heql as [-> ->].
      exists l2; reflexivity. }
  rewrite 2 app_assoc. apply neg_ilr.
  list_simpl. apply IHpi2. reflexivity.
- apply with_irr; [ apply IHpi2_1 | apply IHpi2_2]; reflexivity.
- trichot_elt_elt_inf_exec Heql.
  + list_simpl.
    apply plus_ilr; rewrite app_comm_cons, app_assoc; [ apply IHpi2_1 | apply IHpi2_2 ]; list_simpl; reflexivity.
  + discriminate Heql1.
  + rewrite 2 app_assoc.
    apply plus_ilr; list_simpl; [ apply IHpi2_1 | apply IHpi2_2 ]; list_simpl; reflexivity.
- decomp_map_inf Heql. discriminate.
- trichot_elt_app_inf_exec Heql; subst.
  + rewrite 2 app_assoc. apply cut_ir with A; [ assumption .. | ].
    list_simpl. apply IHpi2_2. list_simpl. reflexivity.
  + list_simpl. rewrite (app_assoc l), (app_assoc (l ++ l0)). apply cut_ir with A; [ assumption | | assumption ].
    list_simpl. apply IHpi2_1. reflexivity.
  + list_simpl. apply cut_ir with A; [ assumption .. | ].
    rewrite app_comm_cons, app_assoc. apply IHpi2_2. list_simpl. reflexivity.
- apply subs_gax_l; assumption.
Qed.

End Atoms.
