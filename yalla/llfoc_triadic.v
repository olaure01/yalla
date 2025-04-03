(** * Andreoli's triadic system for focusing *)

From Stdlib Require Import Wf_nat Lia.
From OLlibs Require Import Datatypes_more Bool_more infinite List_more PermutationT_more.
From Yalla Require Import ll_fragments llfoc.

Set Implicit Arguments.


Section Atoms.

Context {atom : InfDecType}.
Notation formula := (@formula atom).
Notation aformula := (@aformula atom).
Notation sformula := (@sformula atom).
Notation is_Foc := (@is_Foc atom).

(** * Triadic system *)

Inductive atrifoc : list formula -> list formula -> list formula -> Type :=
| foc_tfr A lw ls1 ls2 : sformula A -> strifoc lw (ls1 ++ ls2) A -> atrifoc lw (ls1 ++ A :: ls2) nil
| focd_tfr A lw1 lw2 ls : (forall X, A <> covar X) ->
    strifoc (lw1 ++ A :: lw2) ls A -> atrifoc (lw1 ++ A :: lw2) ls nil
| bot_tfr lw ls l : atrifoc lw ls l -> atrifoc lw ls (bot :: l)
| parr_tfr A B lw ls l : atrifoc lw ls (A :: B :: l) -> atrifoc lw ls (parr A B :: l)
| top_tfr lw ls l : ForallT Foc ls -> atrifoc lw ls (top :: l)
| with_tfr A B lw ls l : atrifoc lw ls (A :: l) -> atrifoc lw ls (B :: l) -> atrifoc lw ls (awith A B :: l)
| wn_tfr A lw ls l : atrifoc (A :: lw) ls l -> atrifoc lw ls (wn A :: l)
| as_tfr A lw ls l : Foc A -> atrifoc lw (A :: ls) l -> atrifoc lw ls (A :: l)
with strifoc : list formula -> list formula -> formula -> Type :=
| ax_tfr X lw : strifoc lw (covar X :: nil) (var X)
| axd_tfr X lw1 lw2 : strifoc (lw1 ++ covar X :: lw2) nil (var X)
| exs_tfr A lw ls1 ls2 : strifoc lw ls1 A -> PermutationT ls1 ls2 -> strifoc lw ls2 A
  (* some shuffle is necessary below the tens_tfr rule *)
| one_tfr lw : strifoc lw nil one
| tens_tfr A B lw ls1 ls2 : strifoc lw ls1 A -> strifoc lw ls2 B -> strifoc lw (ls1 ++ ls2) (tens A B)
| plus_tfr1 A B lw ls : strifoc lw ls A -> strifoc lw ls (aplus A B)
| plus_tfr2 A B lw ls : strifoc lw ls A -> strifoc lw ls (aplus B A)
| oc_tfr A lw : atrifoc lw nil (A :: nil) -> strifoc lw nil (oc A)
| unfoc_tfr A lw ls : aformula A -> atrifoc lw ls (A :: nil) -> strifoc lw ls A.
(* alternative: remove constraint on [covar] in [focd_tfr] and remove [axd_tfr] *)

Scheme astrifoc_rect := Induction for atrifoc Sort Type
  with satrifoc_rect := Induction for strifoc Sort Type.
Combined Scheme trifoc_rect from astrifoc_rect, satrifoc_rect.

Lemma tsync_context :
  (forall lw ls l, atrifoc lw ls l -> ForallT Foc ls)
* (forall lw ls A, strifoc lw ls A -> ForallT Foc ls).
Proof.
apply trifoc_rect; try now intros; assumption + constructor.
- intros A lw ls1 ls2 Hs%(inl : _ -> Foc _) pi HF.
  apply ForallT_app; [ | constructor; [ assumption | ] ].
  + exact (ForallT_app_l _ _ HF).
  + exact (ForallT_app_r _ _ HF).
- intros A lw ls1 ls2 _ _ HF.
  inversion HF. assumption.
- intros X _.
  constructor; [ right | ]; constructor.
- intros A lw ls1 ls2 pi HF HP.
  eapply PermutationT_ForallT; eassumption.
- intros A B lw ls1 ls2 pi1 HF1 pi2 HF2.
  apply ForallT_app; assumption.
Qed.

Lemma exw_tfr :
  (forall lw ls l, atrifoc lw ls l -> forall lw0, PermutationT lw lw0 -> atrifoc lw0 ls l)
* (forall lw ls A, strifoc lw ls A -> forall lw0, PermutationT lw lw0 -> strifoc lw0 ls A).
Proof.
apply trifoc_rect; try now intros; constructor; try apply X; try apply X0.
- intros A lw1 lw2 ls Hnc pi IHpi lw0 HP.
  symmetry in HP. destruct (PermutationT_vs_elt_inv _ _ _ HP) as [(l1, l2) ->].
  apply focd_tfr, IHpi; [ | symmetry ]; assumption.
- intros A lw ls l pi IHpi lw0 HP.
  apply wn_tfr, IHpi, PermutationT_cons; [ reflexivity | assumption ].
- intros X lw1 lw2 lw0 HP.
  symmetry in HP. destruct (PermutationT_vs_elt_inv _ _ _ HP) as [(l1, l2) ->].
  apply axd_tfr.
- intros A lw ls1 ls2 pi IHpi HP' lw0 HP.
  eapply exs_tfr; [ | eassumption ].
  apply IHpi, HP.
Qed.

Lemma ex_tfr :
  (forall lw ls l, atrifoc lw ls l -> forall ls0, PermutationT ls ls0 -> atrifoc lw ls0 l)
* (forall lw ls A, strifoc lw ls A -> forall ls0, PermutationT ls ls0 -> strifoc lw ls0 A).
Proof.
apply trifoc_rect; try now (intros; constructor; auto).
- intros A lw ls1 ls2 Hs pi IHpi ls0 HP.
  symmetry in HP. destruct (PermutationT_vs_elt_inv _ _ _ HP) as [(l1, l2) ->].
  apply foc_tfr, IHpi; [ assumption | ].
  symmetry in HP. exact (PermutationT_app_inv _ _ _ _ _ HP).
- intros lw ls l HF ls0 HP.
  apply top_tfr.
  apply PermutationT_ForallT with ls; assumption.
- intros X lw ls0 HP.
  apply PermutationT_length_1_inv in HP as ->.
  apply ax_tfr.
- intros X lw1 lw2 ls0 HP.
  apply PermutationT_nil in HP as ->.
  apply axd_tfr.
- intros A lw ls1 ls2 pi IHpi HP' ls0 HP.
  apply IHpi.
  transitivity ls2; assumption.
- intros lw ls0 HP.
  apply PermutationT_nil in HP as ->.
  apply one_tfr.
- intros A B lw ls1 ls2 pi1 IHpi1 pi2 IHpi2 lw0 HP.
  eapply exs_tfr; [ | eassumption ].
  now apply tens_tfr.
- intros A lw pi IHpi ls0 HP.
  apply PermutationT_nil in HP as ->.
  now apply oc_tfr.
Qed.

Lemma wk_list_tfr lw0 :
  (forall lw ls l, atrifoc lw ls l -> atrifoc (lw ++ lw0) ls l)
* (forall lw ls A, strifoc lw ls A -> strifoc (lw ++ lw0) ls A).
Proof.
apply trifoc_rect; try (intros; list_simpl; econstructor; eassumption).
intros ? ? ? ? ? _ pi2. list_simpl in pi2. list_simpl. constructor; assumption.
Qed.

Lemma wk_tfr C lw ls :
  (forall l, atrifoc lw ls l -> atrifoc (C :: lw) ls l)
* (forall A, strifoc lw ls A -> strifoc (C :: lw) ls A).
Proof.
split; intros P pi; (eapply exw_tfr; [ apply wk_list_tfr, pi | symmetry; apply PermutationT_cons_append ]).
Qed.

Lemma co_tfr C :
  (forall lw ls l, atrifoc lw ls l ->
     forall lw1 lw2, lw = lw1 ++ C :: C :: lw2 -> atrifoc (lw1 ++ C :: lw2) ls l)
* (forall lw ls A, strifoc lw ls A ->
     forall lw1 lw2, lw = lw1 ++ C :: C :: lw2 -> strifoc (lw1 ++ C :: lw2) ls A).
Proof.
apply trifoc_rect; intros; subst; try now (econstructor; eauto).
- assert (pi := X _ _ H).
  assert (InT A (lw0 ++ C :: lw3)) as [(l1, l2) HA]%inT_split.
  { enough (inclT (lw0 ++ C :: C :: lw3) (lw0 ++ C :: lw3)) as Hi
      by (apply Hi; rewrite <- H; apply inT_elt).
    apply inclT_app_app; [ apply inclT_refl | ].
    now intros D [->|HD]; [ left | ]. }
  rewrite ? HA in *.
  apply focd_tfr; assumption.
- apply wn_tfr.
  rewrite app_comm_cons. apply X. reflexivity.
- assert (InT (covar X) (lw0 ++ C :: lw3)) as [(l1, l2) ->]%inT_split.
  { enough (inclT (lw0 ++ C :: C :: lw3) (lw0 ++ C :: lw3)) as Hi
      by (apply Hi; rewrite <- H; apply inT_elt).
    apply inclT_app_app; [ apply inclT_refl | ].
    now intros D [->|HD]; [ left | ]. }
  apply axd_tfr.
Qed.

Lemma de_tfr C :
  (forall lw ls l, atrifoc lw ls l ->
     forall ls1 ls2, ls = ls1 ++ C :: ls2 -> atrifoc (lw ++ C :: nil) (ls1 ++ ls2) l)
* (forall lw ls A, strifoc lw ls A ->
     forall ls1 ls2, ls = ls1 ++ C :: ls2 -> strifoc (lw ++ C :: nil) (ls1 ++ ls2) A).
Proof.
apply trifoc_rect; intros; subst; try now (econstructor; eauto); try now (destruct ls1; destr_eq H).
- decomp_elt_eq_elt H.
  + list_simpl. apply foc_tfr; [ assumption | ].
    rewrite app_assoc. apply X. rewrite <- app_assoc. reflexivity.
  + apply focd_tfr, wk_list_tfr; [ | assumption ].
    intros Y ->. inversion s.
  + rewrite app_assoc. apply foc_tfr; [ assumption | ]. rewrite <- app_assoc.
    apply X. list_simpl. reflexivity.
- list_simpl. apply focd_tfr; [ assumption | ].
  rewrite app_comm_cons, app_assoc. apply X. reflexivity.
- apply top_tfr. apply ForallT_app.
  + apply ForallT_app_l in f. assumption.
  + apply ForallT_app_r in f. inversion f. assumption.
- constructor; [ assumption | ].
  rewrite app_comm_cons. apply X. reflexivity.
- decomp_unit_eq_elt H. apply axd_tfr.
- destruct (PermutationT_vs_elt_inv _ _ _ p) as [(l1, l2) ->].
  apply PermutationT_app_inv in p.
  eapply ex_tfr; [ | eassumption ].
  apply X. reflexivity.
- decomp_elt_eq_app H; subst.
  + rewrite app_assoc. apply tens_tfr.
    * apply X. reflexivity.
    * apply wk_list_tfr. assumption.
  + rewrite <- app_assoc. apply tens_tfr.
    * apply wk_list_tfr. assumption.
    * apply X0. reflexivity.
Qed.

Lemma bot_gen_tfr lw ls l1 l2 : atrifoc lw ls (l1 ++ l2) -> atrifoc lw ls (l1 ++ bot :: l2).
Proof.
remember (list_sum (map fsize l1)) as n eqn:Heqn.
revert lw ls l1 Heqn; induction n using lt_wf_rect; intros lw ls [|C l1] -> pi.
- apply bot_tfr. assumption.
- list_simpl. destruct C;
    try (inversion pi; subst; apply as_tfr; [ left; constructor | ];
         apply X with (list_sum (map fsize l1)); simpl; try lia; assumption).
  + inversion pi. subst.
    apply as_tfr; [ right; constructor | ].
    apply X with (list_sum (map fsize l1)); simpl; try lia; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply bot_tfr.
    apply X with (list_sum (map fsize l1)); simpl; try lia; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply parr_tfr; rewrite 2 app_comm_cons.
    apply X with (list_sum (map fsize (C1 :: C2 :: l1))); cbn; try lia; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply top_tfr. assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply with_tfr; rewrite app_comm_cons.
    * apply X with (list_sum (map fsize (C1 :: l1))); cbn; try lia; assumption.
    * apply X with (list_sum (map fsize (C2 :: l1))); cbn; try lia; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply wn_tfr.
    apply X with (list_sum (map fsize l1)); simpl; try lia; assumption.
Qed.

Lemma parr_gen_tfr A B lw ls l1 l2 : atrifoc lw ls (l1 ++ A :: B :: l2) -> atrifoc lw ls (l1 ++ parr A B :: l2).
Proof.
remember (list_sum (map fsize l1)) as n eqn:Heqn.
revert lw ls l1 Heqn; induction n using lt_wf_rect; intros lw ls [|C l1] -> pi.
- apply parr_tfr. assumption.
- list_simpl. destruct C;
    try (inversion pi; subst; apply as_tfr; [ left; constructor | ];
         apply X with (list_sum (map fsize l1)); simpl; try lia; assumption).
  + inversion pi. subst.
    apply as_tfr; [ right; constructor | ].
    apply X with (list_sum (map fsize l1)); simpl; try lia; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply bot_tfr.
    apply X with (list_sum (map fsize l1)); simpl; try lia; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply parr_tfr. rewrite 2 app_comm_cons.
    apply X with (list_sum (map fsize (C1 :: C2 :: l1))); simpl; try lia; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply top_tfr. assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply with_tfr; rewrite app_comm_cons.
    * apply X with (list_sum (map fsize (C1 :: l1))); simpl; try lia; assumption.
    * apply X with (list_sum (map fsize (C2 :: l1))); simpl; try lia; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply wn_tfr.
    apply X with (list_sum (map fsize l1)); simpl; try lia; assumption.
Qed.

Lemma top_gen_tfr lw ls l1 l2 : ForallT Foc ls -> atrifoc lw ls (l1 ++ top :: l2).
Proof.
remember (list_sum (map fsize l1)) as n eqn:Heqn.
revert lw ls l1 Heqn; induction n using lt_wf_rect; intros lw ls [|C l1] -> HF.
- apply top_tfr. assumption.
- list_simpl. destruct C;
    try (apply as_tfr; [ left; constructor | ];
    apply X with (list_sum (map fsize l1)); simpl; try lia;
    constructor; [ left; constructor | assumption ]).
  + apply as_tfr; [ right; constructor | ].
    apply X with (list_sum (map fsize l1)); simpl; try lia.
    constructor; [ right; constructor | assumption ].
  + apply bot_tfr.
    apply X with (list_sum (map fsize l1)); simpl; try lia; assumption.
  + apply parr_tfr. rewrite 2 app_comm_cons.
    apply X with (list_sum (map fsize (C1 :: C2 :: l1))); simpl; try lia; assumption.
  + apply top_tfr. assumption.
  + apply with_tfr; rewrite app_comm_cons.
    * apply X with (list_sum (map fsize (C1 :: l1))); simpl; try lia; assumption.
    * apply X with (list_sum (map fsize (C2 :: l1))); simpl; try lia; assumption.
  + apply wn_tfr.
    apply X with (list_sum (map fsize l1)); simpl; try lia; assumption.
Qed.

Lemma with_gen_tfr A B lw ls l1 l2 : atrifoc lw ls (l1 ++ A :: l2) -> atrifoc lw ls (l1 ++ B :: l2) ->
  atrifoc lw ls (l1 ++ awith A B :: l2).
Proof.
remember (list_sum (map fsize l1)) as n eqn:Heqn.
revert lw ls l1 Heqn; induction n using lt_wf_rect; intros lw ls [|C l1] -> pi1 pi2.
- apply with_tfr; assumption.
- list_simpl. destruct C;
    try (inversion pi1; inversion pi2; subst; apply as_tfr; [ left; constructor | ];
         apply X with (list_sum (map fsize l1)); simpl; try lia; assumption).
  + inversion pi1. inversion pi2. subst.
    apply as_tfr; [ right; constructor | ].
    apply X with (list_sum (map fsize l1)); simpl; try lia; assumption.
  + inversion pi1; subst; [ | inversion X0; inversion X2; inversion H ].
    inversion pi2; subst; [ | inversion X1; inversion X3; inversion H ].
    apply bot_tfr.
    apply X with (list_sum (map fsize l1)); simpl; try lia; assumption.
  + inversion pi1; subst; [ | inversion X0; inversion X2; inversion H ].
    inversion pi2; subst; [ | inversion X1; inversion X3; inversion H ].
    apply parr_tfr. rewrite 2 app_comm_cons.
    apply X with (list_sum (map fsize (C1 :: C2 :: l1))); simpl; try lia; assumption.
  + inversion pi1; subst; [ | inversion X0; inversion X2; inversion H ].
    inversion pi2; subst; [ | inversion X1; inversion X3; inversion H ].
    apply top_tfr. assumption.
  + inversion pi1; subst; [ | inversion X0; inversion X2; inversion H ].
    inversion pi2; subst; [ | inversion X2; inversion X4; inversion H ].
    apply with_tfr; rewrite app_comm_cons.
    * apply X with (list_sum (map fsize (C1 :: l1))); simpl; try lia; assumption.
    * apply X with (list_sum (map fsize (C2 :: l1))); simpl; try lia; assumption.
  + inversion pi1; subst; [ | inversion X0; inversion X2; inversion H ].
    inversion pi2; subst; [ | inversion X1; inversion X3; inversion H ].
    apply wn_tfr.
    apply X with (list_sum (map fsize l1)); simpl; try lia; assumption.
Qed.

Lemma wn_gen_tfr A lw ls l1 l2 : atrifoc (A :: lw) ls (l1 ++ l2) -> atrifoc lw ls (l1 ++ wn A :: l2).
Proof.
remember (list_sum (map fsize l1)) as n eqn:Heqn.
revert lw ls l1 Heqn; induction n using lt_wf_rect; intros lw ls [|C l1] -> pi.
- apply wn_tfr. assumption.
- list_simpl. destruct C;
    try (inversion pi; subst; apply as_tfr; [ left; constructor | ];
         apply X with (list_sum (map fsize l1)); simpl; try lia; assumption).
  + inversion pi. subst.
    apply as_tfr; [ right; constructor | ].
    apply X with (list_sum (map fsize l1)); simpl; try lia; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply bot_tfr.
    apply X with (list_sum (map fsize l1)); simpl; try lia; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply parr_tfr. rewrite 2 app_comm_cons.
    apply X with (list_sum (map fsize (C1 :: C2 :: l1))); simpl; try lia; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply top_tfr. assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply with_tfr; rewrite app_comm_cons.
    * apply X with (list_sum (map fsize (C1 :: l1))); simpl; try lia; assumption.
    * apply X with (list_sum (map fsize (C2 :: l1))); simpl; try lia; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply wn_tfr.
    apply X with (list_sum (map fsize l1)); simpl; try lia.
    apply exw_tfr with (C :: A :: lw); [ assumption | apply PermutationT_swap ].
Qed.

Lemma unfoc_gen_tfr A lw ls l1 l2 : Foc A -> atrifoc lw (A :: ls) (l1 ++ l2) -> atrifoc lw ls (l1 ++ A :: l2).
Proof.
remember (list_sum (map fsize l1)) as n eqn:Heqn.
revert lw ls l1 Heqn; induction n using lt_wf_rect; intros lw ls [|C l1] -> HF pi.
- apply as_tfr; assumption.
- list_simpl. destruct C;
    try (inversion pi; subst; apply as_tfr; [ left; constructor | ];
         apply X with (list_sum (map fsize l1)); simpl; try lia; [ assumption | ];
         eapply ex_tfr; [ eassumption | apply PermutationT_swap ]).
  + inversion pi. subst.
    apply as_tfr; [ right; constructor | ].
    apply X with (list_sum (map fsize l1)); simpl; try lia; [ assumption | ].
    eapply ex_tfr; [ eassumption | apply PermutationT_swap ].
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply bot_tfr.
    apply X with (list_sum (map fsize l1)); simpl; try lia; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply parr_tfr. rewrite 2 app_comm_cons.
    apply X with (list_sum (map fsize (C1 :: C2 :: l1))); simpl; try lia; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply top_tfr.
    inversion X0; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply with_tfr; rewrite app_comm_cons.
    * apply X with (list_sum (map fsize (C1 :: l1))); simpl; try lia; assumption.
    * apply X with (list_sum (map fsize (C2 :: l1))); simpl; try lia; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply wn_tfr.
    apply X with (list_sum (map fsize l1)); simpl; try lia; assumption.
Qed.

Lemma exa_tfr lw ls l : atrifoc lw ls l -> forall l0, PermutationT l l0 -> atrifoc lw ls l0.
Proof.
revert lw ls l.
apply (astrifoc_rect (fun lw ls l _ => forall l0, PermutationT l l0 -> atrifoc lw ls l0)
                     (fun _ _ _ _ => unit)); try now constructor.
- intros A lw ls1 ls2 Hs pi _ l0 ->%PermutationT_nil.
  apply foc_tfr, pi. assumption.
- intros A lw1 lw2 ls Hnc pi _ ls0 ->%PermutationT_nil.
  apply focd_tfr, pi. assumption.
- intros lw ls l pi IHpi l0 HP.
  symmetry in HP. destruct (PermutationT_vs_cons_inv HP) as [(l1, l2) ->].
  symmetry in HP. apply PermutationT_cons_app_inv in HP.
  apply bot_gen_tfr, IHpi. assumption.
- intros A B lw ls l pi IHpi l0 HP.
  symmetry in HP. destruct (PermutationT_vs_cons_inv HP) as [(l1, l2) ->].
  symmetry in HP. apply PermutationT_cons_app_inv in HP.
  apply parr_gen_tfr, IHpi.
  do 2 apply PermutationT_cons_app. assumption.
- intros lw ls l HF l0 HP.
  symmetry in HP. destruct (PermutationT_vs_cons_inv HP) as [(l1, l2) ->].
  symmetry in HP. apply PermutationT_cons_app_inv in HP.
  apply top_gen_tfr. assumption.
- intros A B lw ls l pi1 IHpi1 pi2 IHpi2 l0 HP.
  symmetry in HP. destruct (PermutationT_vs_cons_inv HP) as [(l1, l2) ->].
  symmetry in HP. apply PermutationT_cons_app_inv in HP.
  apply with_gen_tfr; [ apply IHpi1 | apply IHpi2]; apply PermutationT_cons_app; assumption.
- intros A lw ls l pi IHpi l0 HP.
  symmetry in HP. destruct (PermutationT_vs_cons_inv HP) as [(l1, l2) ->].
  symmetry in HP. apply PermutationT_cons_app_inv in HP.
  apply wn_gen_tfr, IHpi. assumption.
- intros A lw ls l Hf pi IHpi ls0 HP.
  symmetry in HP. destruct (PermutationT_vs_cons_inv HP) as [(l1, l2) ->].
  symmetry in HP. apply PermutationT_cons_app_inv in HP.
  apply unfoc_gen_tfr, IHpi; assumption.
Qed.

Lemma unfoc_tfr_rev A lw ls : aformula A -> strifoc lw ls A -> atrifoc lw ls (A :: nil).
Proof. intros Ha pi. induction pi; (try now inversion Ha); [ apply (fst ex_tfr _ ls1) | ]; auto. Qed.

Lemma trifoc_set:
  (forall lw ls l, atrifoc lw ls l -> atrifoc (nodup (@eq_dt_dec formulas_dectype) lw) ls l)
* (forall lw ls A, strifoc lw ls A -> strifoc (nodup (@eq_dt_dec formulas_dectype) lw) ls A).
Proof.
apply trifoc_rect; try (now constructor); try (now econstructor; eassumption).
- intros A lw1 lw2 ls pi IHpi.
  assert (InT A (nodup (@eq_dt_dec formulas_dectype) (lw1 ++ A :: lw2))) as [(l1, l2) ->]%inT_split
    by apply (in_inT (@eq_dt_dec formulas_dectype)), nodup_In, in_elt.
  apply focd_tfr. assumption.
- intros A lw ls l pi IHpi.
  apply wn_tfr.
  cbn in IHpi. destruct (in_dec _ A lw) as [Hin|Hnin]; [ | assumption ].
  eapply exw_tfr; [ | symmetry; apply PermutationT_cons_append ].
  apply wk_list_tfr. assumption.
- intros X lw1 lw2.
  assert (InT (covar X) (nodup (@eq_dt_dec formulas_dectype) (lw1 ++ covar X :: lw2)))
    as [(l1, l2) ->]%inT_split
    by apply (in_inT (@eq_dt_dec formulas_dectype)), nodup_In, in_elt.
  apply axd_tfr.
Qed.


(** * From monadic to triadic *)

Lemma wFoc_wn_Foc_partition l lw ls : ForallT wFoc l -> partition is_wn l = (map wn lw, ls) ->
  partition is_Foc ls = (ls, nil).
Proof.
intros HF Hp.
apply forallb_true_partition.
rewrite partition_as_filter in Hp. injection Hp as [= _ <-].
induction l as [|a l IHl]; [ reflexivity | ].
cbn. inversion_clear HF.
destruct (wn_spec a) as [Hwn|Hnwn]; [ inversion Hwn; subst | cbn; apply andb_true_iff ]; cbn; rewrite IHl; auto.
split; [ | reflexivity ].
destruct (Foc_spec a) as [ | Hntt ]; [ reflexivity | contradiction Hntt ].
apply wFoc_not_wn_Foc; assumption.
Qed.

Lemma mon_to_tri l Pi : llFoc l Pi ->
  (forall A, Pi = Some A -> forall lw ls, partition is_wn l = (map wn lw, ls) -> strifoc lw ls A)
* (Pi = None -> forall lw lsa ls la,
                  partition is_wn l = (map wn lw, lsa) -> partition is_Foc lsa = (ls, la) ->
                  atrifoc lw ls la).
Proof.
intros pi; induction pi; (split; [ intros A' Hs lw ls Hp | intros Hn ]);
  try inversion Hs; try inversion Hn; subst.
- cbn in Hp. injection Hp as [= Heq <-]. symmetry in Heq. apply map_eq_nil in Heq as ->. apply ax_tfr.
- intros lw lsa ls la Hp1 Hp2.
  remember (partition is_wn l1) as p' eqn:Hp'. symmetry in Hp'. destruct p' as [lw' lsa'].
  destruct (PermutationT_partition _ p Hp' Hp1).
  remember (partition is_Foc lsa') as p'' eqn:Hp''. symmetry in Hp''. destruct p'' as [ls' la'].
  destruct (PermutationT_partition _ p1 Hp'' Hp2).
  apply PermutationT_map_inv in p0 as [lw'' ->]. symmetry in p0.
  apply exw_tfr with lw''; [ | assumption ].
  apply ex_tfr with ls'; [ | assumption ].
  apply exa_tfr with la'; [ | assumption ].
  eapply (snd IHpi); [ reflexivity | reflexivity | assumption ].
- intros lw lsa ls la Hp1 Hp2.
  assert (Hs := (inl : _ -> Foc _) (sync_focus_F pi)).
  assert (HF := wFoc_context pi).
  assert (is_wn A = false) as Hwn
    by now destruct (wn_spec A) as [Hw | Hnw]; [ exfalso; apply (Foc_not_wn (Hs, Hw)) | ].
  cbn in Hp1. rewrite Hwn in Hp1.
  remember (partition is_wn l) as p. destruct p as [p1 p2].
  assert (ForallT Foc p2) as Hlsa.
  { apply (ForallT_arrow _ (fun A => (uncurry (@wFoc_not_wn_Foc _ A)))).
    apply ForallT_prod.
    - assert (Hincl := partition_incl2T is_wn l).
      rewrite <- Heqp in Hincl. cbn in Hincl.
      apply (inclT_ForallT Hincl). assumption.
    - rewrite partition_as_filter in Heqp. injection Heqp as [= -> ->].
      apply (reflectT_iffT (ForallT_forallb_reflectT _ _ _ (fun D => (reflectT_neg (wn_spec D))))),
            forallb_filter. }
  assert (forall x, InT x lsa -> is_Foc x = true) as Hlsa'.
  { injection Hp1 as [= -> <-].
    clear - Hs Hlsa. intros B [->|Hin]; destruct (Foc_spec B); auto.
    exfalso. apply n. apply ForallT_forall with p2; assumption. }
  apply forallb_forallT, forallb_filter_id in Hlsa'.
  rewrite <- Hlsa', partition_as_filter, filter_negb_filter in Hp2.
  injection Hp2 as [= <- <-]. injection Hp1 as [= -> <-]. rewrite 2 Hlsa'.
  rewrite <- (app_nil_l (A :: _)). apply foc_tfr; [ apply (sync_focus_F pi) | ].
  apply IHpi; [ reflexivity | f_equal ].
- cbn in Hp. injection Hp as [= Heq <-]. symmetry in Heq. apply map_eq_nil in Heq as ->. apply one_tfr.
- intros lw lsa ls la Hp1 Hp2.
  cbn in Hp1. destruct (partition is_wn l). injection Hp1 as [= -> <-].
  specialize (snd IHpi eq_refl lw l1). clear IHpi. intros IHpi.
  cbn in Hp2. destruct (partition is_Foc l1). injection Hp2 as [= <- <-].
  apply bot_tfr, IHpi; reflexivity.
- rewrite partition_app in Hp.
  destruct (partition is_wn l1) eqn:Hp1, (partition is_wn l2) eqn:Hp2. cbn in Hp. injection Hp as [= Hp <-].
  decomp_map Hp. subst.
  apply tens_tfr.
  + apply wk_list_tfr.
    destruct (polarity A); pol_simpl.
    * apply IHpi1, Hp1. reflexivity.
    * apply unfoc_tfr; [ assumption | ].
      assert (partition is_Foc l0 = (l0, nil)) as Hp' by now apply (@wFoc_wn_Foc_partition l1 l).
      destruct (wn_spec A) as [Hwn|Hnwn]; [ inversion Hwn; subst | destruct (Foc_spec A) as [Htt|Hntt] ].
      -- apply wn_tfr.
         cbn in IHpi1. apply IHpi1 with (lsa := l0); [ reflexivity | | eassumption ].
         rewrite Hp1. reflexivity.
      -- apply as_tfr; [ assumption | ].
         apply IHpi1 with (lsa := A :: l0); [ reflexivity | | ]; cbn.
         ++ rewrite Hp1.
            apply (reflectT_iffT (reflectT_neg (wn_spec _))), negb_true_iff in Hnwn as ->.
            reflexivity.
         ++ rewrite Hp'. apply (reflectT_iffT (Foc_spec _)) in Htt as ->. reflexivity.
      -- apply IHpi1 with (lsa := A :: l0); [ reflexivity | | ]; cbn.
         ++ rewrite Hp1.
            apply (reflectT_iffT (reflectT_neg (wn_spec _))), negb_true_iff in Hnwn as ->.
            reflexivity.
         ++ rewrite Hp'.
            apply (reflectT_iffT (reflectT_neg (Foc_spec _))), negb_true_iff in Hntt as ->.
            reflexivity.
  + apply exw_tfr with (l3 ++ l); [ apply wk_list_tfr | apply PermutationT_app_comm ].
    destruct (polarity B); pol_simpl.
    * apply IHpi2, Hp2. reflexivity.
    * apply unfoc_tfr; [ assumption | ].
      assert (partition is_Foc l4 = (l4, nil)) as Hp' by now apply (@wFoc_wn_Foc_partition l2 l3).
      destruct (wn_spec B) as [Hwn|Hnwn]; [ inversion Hwn; subst | destruct (Foc_spec B) as [Htt|Hntt] ].
      -- apply wn_tfr.
         cbn in IHpi2. apply IHpi2 with (lsa := l4); [ reflexivity | | eassumption ].
         rewrite Hp2. reflexivity.
      -- apply as_tfr; [ assumption | ].
         apply IHpi2 with (lsa := B :: l4); [ reflexivity | | ]; cbn.
         ++ rewrite Hp2.
            apply (reflectT_iffT (reflectT_neg (wn_spec _))), negb_true_iff in Hnwn as ->.
            reflexivity.
         ++ rewrite Hp'. apply (reflectT_iffT (Foc_spec _)) in Htt as ->. reflexivity.
      -- apply IHpi2 with (lsa := B :: l4); [ reflexivity | | ]; cbn.
         ++ rewrite Hp2.
            apply (reflectT_iffT (reflectT_neg (wn_spec _))), negb_true_iff in Hnwn as ->.
            reflexivity.
         ++ rewrite Hp'.
            apply (reflectT_iffT (reflectT_neg (Foc_spec _))), negb_true_iff in Hntt as ->.
            reflexivity.
- intros lw lsa ls la Hp1 Hp2.
  cbn in Hp1. destruct (partition is_wn l) eqn:Hp. injection Hp1 as [= -> <-].
  cbn in Hp2. destruct (partition is_Foc l1) eqn:Hp'. injection Hp2 as [= <- <-].
  apply parr_tfr.
  destruct (wn_spec A) as [HwnA|HnwnA]; [ inversion HwnA; subst | destruct (Foc_spec A) as [HttA|HnttA] ].
  + apply wn_tfr.
    destruct (wn_spec B) as [HwnB|HnwnB]; [ inversion HwnB; subst | destruct (Foc_spec B) as [HttB|HnttB] ].
    * apply wn_tfr.
      eapply exw_tfr; [ | apply PermutationT_swap ].
      eapply IHpi, Hp'; [ | cbn; rewrite Hp ]; reflexivity.
    * apply as_tfr; [ assumption | ].
      eapply IHpi; [ reflexivity | | ].
      -- cbn. rewrite Hp.
         apply (reflectT_iffT (reflectT_neg (wn_spec _))), negb_true_iff in HnwnB as ->.
         reflexivity.
      -- cbn. rewrite Hp'. apply (reflectT_iffT (Foc_spec _)) in HttB as ->. reflexivity.
    * eapply IHpi; [ reflexivity | | ].
      -- cbn. rewrite Hp.
         apply (reflectT_iffT (reflectT_neg (wn_spec _))), negb_true_iff in HnwnB as ->.
         reflexivity.
      -- cbn. rewrite Hp'.
         apply (reflectT_iffT (reflectT_neg (Foc_spec _))), negb_true_iff in HnttB as ->.
         reflexivity.
  + apply as_tfr; [ assumption | ].
    destruct (wn_spec B) as [HwnB|HnwnB]; [ inversion HwnB; subst | destruct (Foc_spec B) as [HttB|HnttB] ].
    * apply wn_tfr.
      eapply IHpi; [ reflexivity | | ].
      -- cbn. rewrite Hp.
         apply (reflectT_iffT (reflectT_neg (wn_spec _))), negb_true_iff in HnwnA as ->.
         reflexivity.
      -- cbn. rewrite Hp'. apply (reflectT_iffT (Foc_spec _)) in HttA as ->. reflexivity.
    * apply as_tfr; [ assumption | ].
      eapply ex_tfr; [ | apply PermutationT_swap ].
      eapply IHpi; [ reflexivity | | ].
      -- cbn. rewrite Hp.
         apply (reflectT_iffT (reflectT_neg (wn_spec _))), negb_true_iff in HnwnB as ->.
         apply (reflectT_iffT (reflectT_neg (wn_spec _))), negb_true_iff in HnwnA as ->.
         reflexivity.
      -- cbn. rewrite Hp'.
         apply (reflectT_iffT (Foc_spec _)) in HttB as ->.
         apply (reflectT_iffT (Foc_spec _)) in HttA as ->.
         reflexivity.
    * eapply IHpi; [ reflexivity | | ].
      -- cbn. rewrite Hp.
         apply (reflectT_iffT (reflectT_neg (wn_spec _))), negb_true_iff in HnwnB as ->.
         apply (reflectT_iffT (reflectT_neg (wn_spec _))), negb_true_iff in HnwnA as ->.
         reflexivity.
      -- cbn. rewrite Hp'.
         apply (reflectT_iffT (reflectT_neg (Foc_spec _))), negb_true_iff in HnttB as ->.
         apply (reflectT_iffT (Foc_spec _)) in HttA as ->.
         reflexivity.
  + eapply exa_tfr; [ | apply PermutationT_swap ].
    destruct (wn_spec B) as [HwnB|HnwnB]; [ inversion HwnB; subst | destruct (Foc_spec B) as [HttB|HnttB] ].
    * apply wn_tfr.
      eapply IHpi; [ reflexivity | | ].
      -- cbn. rewrite Hp.
         apply (reflectT_iffT (reflectT_neg (wn_spec _))), negb_true_iff in HnwnA as ->.
         reflexivity.
      -- cbn. rewrite Hp'.
         apply (reflectT_iffT (reflectT_neg (Foc_spec _))), negb_true_iff in HnttA as ->.
         reflexivity.
    * apply as_tfr; [ assumption | ].
      eapply IHpi; [ reflexivity | | ].
      -- cbn. rewrite Hp.
         apply (reflectT_iffT (reflectT_neg (wn_spec _))), negb_true_iff in HnwnB as ->.
         apply (reflectT_iffT (reflectT_neg (wn_spec _))), negb_true_iff in HnwnA as ->.
         reflexivity.
      -- cbn. rewrite Hp'.
         apply (reflectT_iffT (Foc_spec _)) in HttB as ->.
         apply (reflectT_iffT (reflectT_neg (Foc_spec _))), negb_true_iff in HnttA as ->.
         reflexivity.
    * eapply exa_tfr; [ | apply PermutationT_swap ].
      eapply IHpi; [ reflexivity | | ].
      -- cbn. rewrite Hp.
         apply (reflectT_iffT (reflectT_neg (wn_spec _))), negb_true_iff in HnwnB as ->.
         apply (reflectT_iffT (reflectT_neg (wn_spec _))), negb_true_iff in HnwnA as ->.
         reflexivity.
      -- cbn. rewrite Hp'.
         apply (reflectT_iffT (reflectT_neg (Foc_spec _))), negb_true_iff in HnttB as ->.
         apply (reflectT_iffT (reflectT_neg (Foc_spec _))), negb_true_iff in HnttA as ->.
         reflexivity.
- intros lw lsa ls la Hp1 Hp2.
  cbn in Hp1. destruct (partition is_wn l). injection Hp1 as [= -> <-].
  assert (ForallT Foc ls) as Htt.
  { rewrite partition_as_filter in Hp2. injection Hp2 as [= <- <-].
    apply forall_ForallT.
    intros C [_ HC]%filter_InT_inv.
    apply (reflectT_iffT (Foc_spec _)), HC. }
  cbn in Hp2. destruct (partition is_Foc l1). injection Hp2 as [= <- <-].
  apply top_tfr, Htt.
- apply plus_tfr1.
  destruct (polarity A) as [HsA|HaA]; pol_simpl.
  + now apply IHpi.
  + apply unfoc_tfr; [ assumption | ].
    assert (partition is_Foc ls = (ls, nil)) as Hp' by now apply (@wFoc_wn_Foc_partition l lw).
    destruct (wn_spec A) as [Hwn|Hnwn]; [ inversion Hwn; subst | destruct (Foc_spec A) as [Htt|Hntt] ].
    * apply wn_tfr.
      cbn in IHpi. apply IHpi with (lsa := ls); [ reflexivity | | eassumption ].
      rewrite Hp. reflexivity.
    * apply as_tfr; [ assumption | ].
      apply IHpi with (lsa := A :: ls); [ reflexivity | | ]; cbn.
      -- rewrite Hp.
         apply (reflectT_iffT (reflectT_neg (wn_spec _))), negb_true_iff in Hnwn as ->.
         reflexivity.
      -- rewrite Hp'. apply (reflectT_iffT (Foc_spec _)) in Htt as ->. reflexivity.
    * apply IHpi with (lsa := A :: ls); [ reflexivity | | ]; cbn.
      -- rewrite Hp.
         apply (reflectT_iffT (reflectT_neg (wn_spec _))), negb_true_iff in Hnwn as ->.
         reflexivity.
      -- rewrite Hp'.
         apply (reflectT_iffT (reflectT_neg (Foc_spec _))), negb_true_iff in Hntt as ->.
         reflexivity.
- apply plus_tfr2.
  destruct (polarity A) as [HsA|HaA]; pol_simpl.
  + now apply IHpi.
  + apply unfoc_tfr; [ assumption | ].
    assert (partition is_Foc ls = (ls, nil)) as Hp' by now apply (@wFoc_wn_Foc_partition l lw).
    destruct (wn_spec A) as [Hwn|Hnwn]; [ inversion Hwn; subst | destruct (Foc_spec A) as [Htt|Hntt] ].
    * apply wn_tfr.
      cbn in IHpi. apply IHpi with (lsa := ls); [ reflexivity | | eassumption ].
      rewrite Hp. reflexivity.
    * apply as_tfr; [ assumption | ].
      apply IHpi with (lsa := A :: ls); [ reflexivity | | ]; cbn.
      -- rewrite Hp.
         apply (reflectT_iffT (reflectT_neg (wn_spec _))), negb_true_iff in Hnwn as ->.
         reflexivity.
      -- rewrite Hp'.
         apply (reflectT_iffT (Foc_spec _)) in Htt as ->.
         reflexivity.
    * apply IHpi with (lsa := A :: ls); [ reflexivity | | ]; cbn.
      -- rewrite Hp.
         apply (reflectT_iffT (reflectT_neg (wn_spec _))), negb_true_iff in Hnwn as ->.
         reflexivity.
      -- rewrite Hp'.
         apply (reflectT_iffT (reflectT_neg (Foc_spec _))), negb_true_iff in Hntt as ->.
         reflexivity.
- intros lw lsa ls la Hp1 Hp2.
  cbn in Hp1. destruct (partition is_wn l) eqn:Hp. injection Hp1 as [= -> <-].
  cbn in Hp2. destruct (partition is_Foc l1) eqn:Hp'. injection Hp2 as [= <- <-].
  apply with_tfr.
  + destruct (wn_spec A) as [Hwn|Hnwn]; [ inversion Hwn; subst | destruct (Foc_spec A) as [Htt|Hntt] ].
    * apply wn_tfr.
      eapply IHpi1, Hp'; [ | cbn; rewrite Hp]; reflexivity.
    * apply as_tfr; [ assumption | ].
      eapply IHpi1; [ reflexivity | | ].
      -- cbn. rewrite Hp.
         apply (reflectT_iffT (reflectT_neg (wn_spec _))), negb_true_iff in Hnwn as ->.
         reflexivity.
      -- cbn. rewrite Hp'. apply (reflectT_iffT (Foc_spec _)) in Htt as ->. reflexivity.
    * eapply IHpi1; [ reflexivity | | ].
      -- cbn. rewrite Hp.
         apply (reflectT_iffT (reflectT_neg (wn_spec _))), negb_true_iff in Hnwn as ->.
         reflexivity.
      -- cbn. rewrite Hp'.
         apply (reflectT_iffT (reflectT_neg (Foc_spec _))), negb_true_iff in Hntt as ->.
         reflexivity.
  + destruct (wn_spec B) as [Hwn|Hnwn]; [ inversion Hwn; subst | destruct (Foc_spec B) as [Htt|Hntt] ].
    * apply wn_tfr.
      eapply IHpi2, Hp'; [ | cbn; rewrite Hp ]; reflexivity.
    * apply as_tfr; [ assumption | ].
      eapply IHpi2; [ reflexivity | | ].
      -- cbn. rewrite Hp.
         apply (reflectT_iffT (reflectT_neg (wn_spec _))), negb_true_iff in Hnwn as ->.
         reflexivity.
      -- cbn. rewrite Hp'. apply (reflectT_iffT (Foc_spec _)) in Htt as ->. reflexivity.
    * eapply IHpi2; [ reflexivity | | ].
      -- cbn. rewrite Hp.
         apply (reflectT_iffT (reflectT_neg (wn_spec _))), negb_true_iff in Hnwn as ->.
         reflexivity.
      -- cbn. rewrite Hp'.
         apply (reflectT_iffT (reflectT_neg (Foc_spec _))), negb_true_iff in Hntt as ->.
         reflexivity.
- assert (ls = nil) as ->.
  { clear - Hp. induction l as [|A l IHl] in Hp, lw |- *; cbn in Hp.
    - injection Hp as [= _ <-]. reflexivity.
    - destruct (partition is_wn (map wn l)). injection Hp as [= Heq ->].
      symmetry in Heq. decomp_map Heq. subst.
      exact (IHl _ eq_refl). }
  apply oc_tfr.
  destruct (wn_spec A) as [Hwn|Hnwn]; [ inversion Hwn; subst | destruct (Foc_spec A) as [Htt|Hntt] ].
  + apply wn_tfr.
    cbn in IHpi. apply IHpi with (lsa := nil); [ reflexivity | | reflexivity ].
    rewrite Hp. reflexivity.
  + apply as_tfr; [ assumption | ].
    apply IHpi with (lsa := A :: nil); [ reflexivity | | ]; cbn.
    * rewrite Hp.
      apply (reflectT_iffT (reflectT_neg (wn_spec _))), negb_true_iff in Hnwn as ->.
      reflexivity.
    * apply (reflectT_iffT (Foc_spec _)) in Htt as ->. reflexivity.
  + apply IHpi with (lsa := A :: nil); [ reflexivity | | ]; cbn.
    * rewrite Hp.
      apply (reflectT_iffT (reflectT_neg (wn_spec _))), negb_true_iff in Hnwn as ->.
      reflexivity.
    * apply (reflectT_iffT (reflectT_neg (Foc_spec _))), negb_true_iff in Hntt as ->.
      reflexivity.
- intros lw lsa ls la Hp1 Hp2.
  assert (partition is_Foc lsa = (lsa, nil)) as Hp'.
  { apply (@wFoc_wn_Foc_partition (wn A :: l) lw); [ | assumption ].
    constructor; [ | assumption ]. right. constructor. }
  rewrite Hp2 in Hp'. injection Hp' as [= -> ->].
  cbn in Hp1. destruct (partition is_wn l) eqn:Hp. injection Hp1 as [= Heq <-].
  decomp_map Heq eqn:Hx. injection Hx as [= ->]. subst.
  destruct (wn_spec A) as [Hwn|Hnwn]; [ inversion Hwn; subst | destruct (Foc_spec A) as [Htt|Hntt] ].
  + apply (focd_tfr nil), wk_tfr, unfoc_tfr, wn_tfr; [ intros ? [=] | constructor | ].
    cbn in IHpi. eapply IHpi; [ reflexivity | | eassumption ].
    rewrite Hp. list_simpl. reflexivity.
  + destruct (covar_spec A) as [Hc|Hnc]; [ inversion Hc; subst | ].
    * assert (aformula (covar X)) by constructor. pol_simpl. cbn in IHpi.
      eapply exw_tfr; [ | symmetry; apply PermutationT_cons_append ].
      rewrite <- (app_nil_l l1). eapply de_tfr; [ | reflexivity ].
      eapply IHpi; [ reflexivity | | ].
      -- rewrite Hp. reflexivity.
      -- cbn. rewrite Hp2. reflexivity.
    * apply (focd_tfr nil), wk_tfr; [ intros ? [= ->]; contradiction Hnc; constructor | ].
      assert (sformula A) as HA by (destruct Htt; [ assumption | contradiction Hnc ]).
      pol_simpl. cbn in IHpi. eapply IHpi, Hp. reflexivity.
  + assert (aformula A) as HA
      by (destruct A; (try now constructor); contradiction Hntt; now repeat constructor).
    pol_simpl. 
    apply (focd_tfr nil), wk_tfr, unfoc_tfr; [ now intros ? ->; apply Hntt; right | assumption | ].
    cbn in IHpi. eapply IHpi with (lsa := A :: l1); [ reflexivity | | ].
    * rewrite Hp.
      apply (reflectT_iffT (reflectT_neg (wn_spec _))), negb_true_iff in Hnwn as ->.
      reflexivity.
    * cbn. rewrite Hp2.
      apply (reflectT_iffT (reflectT_neg (Foc_spec _))), negb_true_iff in Hntt as ->.
      reflexivity.
- intros lw lsa ls la Hp1 Hp2.
  cbn in Hp1. destruct (partition is_wn l). injection Hp1 as [= Heq <-].
  decomp_map Heq. subst.
  change (x :: l0) with ((x :: nil) ++ l0).
  apply (fst exw_tfr (l0 ++ x :: nil)); [ | apply PermutationT_app_comm ].
  apply wk_list_tfr.
  exact (snd IHpi eq_refl _ l1 _ _ eq_refl Hp2).
- intros lw lsa ls la Hp1 Hp2.
  assert (Hp1' := Hp1).
  cbn in Hp1'. destruct (partition is_wn l). injection Hp1' as [= Heq <-].
  decomp_map Heq eqn:Hx. injection Hx as [= ->]. subst.
  rewrite <- (app_nil_l (A :: _)). eapply co_tfr; [ | reflexivity ].
  list_simpl. eapply IHpi; [ reflexivity | | eassumption ].
  cbn in Hp1. cbn. destruct (partition is_wn l). injection Hp1 as [= -> ->]. reflexivity.
Qed.


(** * From triadic to monadic *)

Lemma tri_to_mon:
  (forall lw ls l, atrifoc lw ls l -> llFoc (map wn lw ++ ls ++ l) None)
* (forall lw ls A, strifoc lw ls A ->
     {'(lw', lx, l') & (inclT lw' lw * inclT lx lw * ForallT covar_formula lx
                      * PermutationT l' (map wn lw' ++ lx ++ ls))%type
                      & llFoc (polcont l' A) (polfoc A) }).
Proof.
apply trifoc_rect.
- intros A lw ls1 ls2 Hs pi [((lw', lx), l') [[[Hincl Hinclx] Hcv] HP] IHpi]. list_simpl. pol_simpl.
  eapply incl_Foc; [ | rewrite 2 app_assoc; apply PermutationT_middle | exact Hincl | exact Hinclx | ].
  + rewrite <- ! app_assoc. eapply ex_Fr; [ apply foc_Fr, IHpi | ].
    now apply PermutationT_cons.
  + eapply ForallT_arrow; [ | exact Hcv ]. intros C HC. inversion HC. constructor.
- intros A lw1 lw2 ls Hnc pi [((lw', lx), ls') [[[Hincl Hinclx] Hcv] HP] IHpi]. list_simpl.
  apply de_Fr in IHpi.
  + replace (map wn lw1 ++ wn A :: map wn lw2 ++ ls) with (map wn (lw1 ++ A :: lw2) ++ ls)
      by (list_simpl; reflexivity).
    assert (inclT (A :: lw') (lw1 ++ A :: lw2)) as Hincl'
      by (intros C [-> | Hin%Hincl]; [ apply inT_elt | assumption ]).
    eapply incl_Foc; [ | reflexivity | exact Hincl' | exact Hinclx | ].
    * eapply ex_Fr; [ eassumption | ].
      cbn. now apply PermutationT_cons.
    * eapply ForallT_arrow; [ | exact Hcv ]. intros C HC. inversion HC. constructor.
  + symmetry in HP. apply (PermutationT_ForallT HP).
    apply ForallT_app; [ | apply ForallT_app ].
    * apply forall_ForallT. intros ? [y <- _]%inT_map_inv. apply wFoc_wn.
    * eapply ForallT_arrow; [ | exact Hcv ]. intros C HC. inversion HC. left. right. constructor.
    * apply tsync_context in pi. eapply ForallT_arrow; [ apply Foc_wFoc | assumption ].
- intros lw ls l pi IHpi.
  eapply ex_Fr; [ apply bot_Fr, IHpi | ].
  rewrite ?(app_assoc _ ls). apply PermutationT_middle.
- intros A B lw ls l pi IHpi.
  eapply ex_Fr; [ apply parr_Fr; eapply ex_Fr; [ apply IHpi | ]
                | rewrite ?(app_assoc _ ls); apply PermutationT_middle ].
  transitivity (A :: map wn lw ++ ls ++ B :: l).
  + rewrite ?(app_assoc _ ls). symmetry. apply PermutationT_middle.
  + apply PermutationT_cons; [ reflexivity | ].
    rewrite ?(app_assoc _ ls). symmetry. apply PermutationT_middle.
- intros lw ls l HF.
  apply (@ex_Fr _ (top :: map wn lw ++ ls ++ l)); [ apply top_gen_Fr | ].
  rewrite ?(app_assoc _ ls). apply PermutationT_middle.
- intros A B lw ls l pi1 IHpi1 pi2 IHpi2.
  eapply ex_Fr; [ apply with_Fr; eapply ex_Fr; [ apply IHpi1 | | apply IHpi2 | ]
                | rewrite ?(app_assoc _ ls); apply PermutationT_middle ].
  + rewrite ?(app_assoc _ ls). symmetry. apply PermutationT_middle.
  + rewrite ?(app_assoc _ ls). symmetry. apply PermutationT_middle.
- intros A lw ls l _ IHpi.
  eapply ex_Fr; [ apply IHpi | ].
  rewrite ?(app_assoc _ ls). apply PermutationT_middle.
- intros A lw ls l _ _ IHpi.
  eapply ex_Fr; [ apply IHpi | ].
  etransitivity; [ rewrite <- app_comm_cons; symmetry; apply PermutationT_middle | ].
  rewrite ?(app_assoc _ ls). apply PermutationT_middle.
- intros X lw. cbn. exists (nil, nil, covar X :: nil).
  + repeat split; [ intros ? [] | intros ? [] | constructor | reflexivity ].
  + apply ax_Fr.
- intros X lw1 lw2. exists (nil, covar X :: nil, covar X :: nil).
  + repeat split; [ intros ? [] | | | reflexivity ].
    * intros C [-> | [] ]. apply inT_elt.
    * repeat constructor.
  + apply ax_Fr.
- intros A lw ls1 ls2 _ [((lw', lx), ls') [[[Hincl Hinclx] Hcv] HPs] IHpi] HP.
  exists (lw', lx, ls'); [ repeat split; try assumption | assumption ].
  etransitivity; [ exact HPs | ].
  rewrite ! app_assoc. now apply PermutationT_app.
- intros lw. cbn. exists (nil, nil, nil).
  + repeat split; [ intros ? [] | intros ? [] | constructor | reflexivity ].
  + apply one_Fr.
- intros A B lw ls1 ls2 pi1 [((lw1', lx1), l1') [[[Hincl1 Hinclx1] Hcv1] HP1] IHpi1]
                        pi2 [((lw2', lx2), l2') [[[Hincl2 Hinclx2] Hcv2] HP2] IHpi2]. cbn.
  exists (lw1' ++ lw2', lx1 ++ lx2, l1' ++ l2');
    [ repeat split; try (apply inclT_app; assumption); [ apply ForallT_app; assumption | ] | ].
  { transitivity ((map wn lw1' ++ lx1 ++ ls1) ++ map wn lw2' ++ lx2 ++ ls2).
    - apply PermutationT_app; assumption.
    - list_simpl. apply PermutationT_app; [ reflexivity | ].
      rewrite <- (app_nil_l (lx1 ++ _)). apply PermutationT_app_middle.
      cbn. rewrite <- (app_nil_l (ls1 ++ _)). rewrite (app_assoc _ _ (ls1 ++ _)).
      apply PermutationT_app_middle. list_simpl. reflexivity. }
  apply tens_Fr; [ assumption .. | | ].
  + symmetry in HP1. apply (PermutationT_ForallT HP1).
    apply ForallT_app; [ | apply ForallT_app ].
    * apply forall_ForallT. intros ? [y <- _]%inT_map_inv. apply wFoc_wn.
    * eapply ForallT_arrow; [ | exact Hcv1 ].
      intros C HC. inversion HC. left. right. constructor.
    * apply tsync_context in pi1. eapply ForallT_arrow; [ apply Foc_wFoc | eassumption ].
  + symmetry in HP2. apply (PermutationT_ForallT HP2).
    apply ForallT_app; [ | apply ForallT_app ].
    * apply forall_ForallT. intros ? [y <- _]%inT_map_inv. apply wFoc_wn.
    * eapply ForallT_arrow; [ | exact Hcv2 ].
      intros C HC. inversion HC. left. right. constructor.
    * apply tsync_context in pi2. eapply ForallT_arrow; [ apply Foc_wFoc | eassumption ].
- intros A B lw ls pi [((lw', lx), l') [[[Hincl Hinclx] Hcv] HP] IHpi]. cbn.
  exists (lw', lx, l'); [ repeat split; assumption | ].
  apply plus_Fr1; [ assumption | ].
  symmetry in HP. apply (PermutationT_ForallT HP).
  apply ForallT_app; [ | apply ForallT_app ].
  + apply forall_ForallT. intros ? [y <- _]%inT_map_inv. apply wFoc_wn.
  + eapply ForallT_arrow; [ | exact Hcv ]. intros C HC. inversion HC. left. right. constructor.
  + apply tsync_context in pi. eapply ForallT_arrow; [ apply Foc_wFoc | eassumption ].
- intros A B lw ls pi [((lw', lx), l') [[[Hincl Hinclx] Hcv] HP] IHpi]. cbn.
  exists (lw', lx, l'); [ repeat split; assumption | ].
  apply plus_Fr2; [ assumption | ].
  symmetry in HP. apply (PermutationT_ForallT HP).
  apply ForallT_app; [ | apply ForallT_app ].
  + apply forall_ForallT. intros ? [y <- _]%inT_map_inv. apply wFoc_wn.
  + eapply ForallT_arrow; [ | exact Hcv ]. intros C HC. inversion HC. left. right. constructor.
  + apply tsync_context in pi. eapply ForallT_arrow; [ apply Foc_wFoc | eassumption ].
- intros A lw pi IHpi. exists (lw, nil, map wn lw); list_simpl;
    [ repeat split; [ apply inclT_refl | intros ? [] | constructor | reflexivity ] | ].
  eapply oc_Fr, ex_Fr; [ apply IHpi | ].
  symmetry. apply PermutationT_cons_append.
- intros A lw ls Ha pi IHpi.
  exists (lw, nil, map wn lw ++ ls); list_simpl;
    [ repeat split; [ apply inclT_refl | intros ? [] | constructor | reflexivity ] | ].
  pol_simpl. eapply ex_Fr; [ apply IHpi | ].
  symmetry. list_simpl. rewrite app_assoc. apply PermutationT_cons_append.
Qed.

Lemma mon_tri_equiv l lw lsa ls la : partition is_wn l = (map wn lw, lsa) -> partition is_Foc lsa = (ls, la) ->
  iffT (llFoc l None) (atrifoc lw ls la).
Proof.
intros Hp1 Hp2. split; intro pi.
- eapply mon_to_tri; [ | reflexivity | | ]; eassumption.
- apply tri_to_mon in pi.
  eapply ex_Fr; [ exact pi | ].
  apply partition_PermutationT in Hp1, Hp2.
  symmetry. etransitivity; [ apply Hp1 | ].
  apply PermutationT_app_head, Hp2.
Qed.

End Atoms.

(* TODO analyse embeddings to compare bottom wn-rules in tri and top wn-rules in mon *)
