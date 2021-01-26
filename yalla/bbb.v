(* bbb library for yalla *)


(** * Study of Linear Logic enriched with [bot = oc bot] *)

From Coq Require Import BoolOrder.
From OLlibs Require Import infinite List_more
                           Permutation_Type_more Permutation_Type_solve Dependent_Forall_Type.
From Yalla Require Import ll_fragments.


Section Atoms.

Context { atom : InfDecType }.
Notation formula := (@formula atom).
Notation llR := (@llR atom).

(** ** The system [ll_bbb] *)
(** It contains [ll_mix2] but allows [mix0] as well above one side of each [mix2] rule. *)

Inductive ll_bbb : list formula -> Type :=
| ax_bbb_r : forall X, ll_bbb (covar X :: var X :: nil)
| ex_bbb_r : forall l1 l2, ll_bbb l1 -> Permutation_Type l1 l2 -> ll_bbb l2
| mix2_bbb_r : forall l1 l2, ll_bbb l1 -> ll_mix02 l2 -> ll_bbb (l2 ++ l1)
| one_bbb_r : ll_bbb (one :: nil)
| bot_bbb_r : forall l, ll_bbb l -> ll_bbb (bot :: l)
| tens_bbb_r : forall A B l1 l2,
                ll_bbb (A :: l1) -> ll_bbb (B :: l2) -> ll_bbb (tens A B :: l2 ++ l1)
| parr_bbb_r : forall A B l, ll_bbb (A :: B :: l) -> ll_bbb (parr A B :: l)
| top_bbb_r : forall l, ll_bbb (top :: l)
| plus_bbb_r1 : forall A B l, ll_bbb (A :: l) -> ll_bbb (aplus A B :: l)
| plus_bbb_r2 : forall A B l, ll_bbb (A :: l) -> ll_bbb (aplus B A :: l)
| with_bbb_r : forall A B l, ll_bbb (A :: l) -> ll_bbb (B :: l) ->
                                   ll_bbb (awith A B :: l)
| oc_bbb_r : forall A l, ll_bbb (A :: map wn l) -> ll_bbb (oc A :: map wn l)
| de_bbb_r : forall A l, ll_bbb (A :: l) -> ll_bbb (wn A :: l)
| wk_bbb_r : forall A l, ll_bbb l -> ll_bbb (wn A :: l)
| co_bbb_r : forall A l, ll_bbb (wn A :: wn A :: l) -> ll_bbb (wn A :: l).

(** Generalized weakening for lists *)
Lemma wk_list_bbb_r : forall l l', ll_bbb l' ->
  ll_bbb (map wn l ++ l').
Proof with myeeasy.
induction l ; intros...
apply wk_bbb_r.
apply IHl...
Qed.

(** Generalized contraction for lists *)
Lemma co_list_bbb_r : forall l l',
ll_bbb (map wn l ++ map wn l ++ l') -> ll_bbb (map wn l ++ l').
Proof with myeeasy.
induction l ; intros...
apply (ex_bbb_r (map wn l ++ wn a :: l')); [ | Permutation_Type_solve ].
apply IHl.
apply (ex_bbb_r (wn a :: map wn l ++ map wn l ++ l')); [ | Permutation_Type_solve ].
apply co_bbb_r.
eapply ex_bbb_r; [ apply X | Permutation_Type_solve ].
Qed.

(** Reversibility of [bot] in [ll_bbb] *)
Lemma bot_rev_bbb : forall l, ll_bbb l ->
  forall l1 l2, l = l1 ++ bot :: l2 -> ll_bbb (l1 ++ l2).
Proof with myeeasy.
intros l pi; induction pi; intros l1' l2' Heq; subst.
- exfalso.
  destruct l1' ; inversion Heq.
  destruct l1' ; inversion H1.
  destruct l1' ; inversion H3.
- assert (HP := p).
  apply Permutation_Type_vs_elt_inv in p.
  destruct p as [(l3 & l4) Heq] ; cbn in Heq ; subst.
  apply Permutation_Type_app_inv in HP.
  eapply ex_bbb_r ; [ | apply HP ].
  apply IHpi...
- dichot_elt_app_inf_exec Heq ; subst.
  + rewrite app_assoc ; apply mix2_bbb_r...
    eapply bot_rev...
    intros a ; destruct a.
  + rewrite <- app_assoc ; apply mix2_bbb_r...
    apply IHpi...
- exfalso.
  destruct l1' ; inversion Heq.
  destruct l1' ; inversion H1.
- destruct l1' ; inversion Heq ; subst...
  list_simpl ; eapply bot_bbb_r.
  apply IHpi...
- rewrite app_comm_cons in Heq ; dichot_elt_app_inf_exec Heq ; subst.
  + destruct l1' ; inversion Heq0 ; subst.
    list_simpl.
    rewrite app_assoc ; apply tens_bbb_r...
    rewrite app_comm_cons.
    apply IHpi2...
  + list_simpl.
    apply tens_bbb_r...
    rewrite app_comm_cons.
    apply IHpi1...
- destruct l1' ; inversion Heq ; subst.
  rewrite 2 app_comm_cons in IHpi.
  list_simpl ; eapply parr_bbb_r...
  rewrite 2 app_comm_cons.
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; apply top_bbb_r...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply plus_bbb_r1...
  rewrite app_comm_cons.
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply plus_bbb_r2...
  rewrite app_comm_cons.
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply with_bbb_r...
  + rewrite app_comm_cons.
    apply IHpi1...
  + rewrite app_comm_cons.
    apply IHpi2...
- exfalso.
  destruct l1' ; inversion Heq.
  decomp_map H1; inversion H1.
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply de_bbb_r...
  rewrite app_comm_cons.
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply wk_bbb_r...
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply co_bbb_r...
  rewrite 2 app_comm_cons.
  apply IHpi...
Qed.

(** [ll_mix2] is contained in [ll_bbb] *)
Lemma mix2_to_bbb : forall l, ll_mix2 l -> ll_bbb l.
Proof with myeeasy.
intros l H ; induction H using ll_nested_ind ; try now constructor.
- apply (ex_bbb_r l1)...
- apply (Permutation_Type_map wn) in p.
  eapply ex_bbb_r...
  Permutation_Type_solve.
- repeat (destruct L; try now inversion eqpmix).
  cbn; rewrite app_nil_r.
  assert (ll_bbb l1) as pi1.
  { destruct (In_Forall_inf_in _ PL (in_inf_elt l1 (l0 :: nil) nil)) as [pi Hin].
    refine (Dependent_Forall_inf_forall_formula _ _ X Hin). }
  inversion PL; inversion X1; subst; clear X1 X2 X3.
  apply mix2_bbb_r...
  eapply stronger_pfrag...
  nsplit 4...
  + intros a ; exists a...
  + intro n.
    repeat (destruct n; try apply BoolOrder.le_refl; try apply BoolOrder.le_true).
- destruct a.
Qed.

(** [ll_bbb] is contained in [ll_mix02] *)
Lemma bbb_to_mix02 : forall l, ll_bbb l -> ll_mix02 l.
Proof with myeasy.
intros l H ; induction H ; try now constructor.
- apply (ex_r _ l1)...
- rewrite<- (app_nil_r _).
  rewrite<- app_assoc.
  change (l2 ++ l1 ++ nil) with (concat (l2 :: l1 :: nil)).
  apply mix_r...
  do 2 (apply Forall_inf_cons; try assumption).
  apply Forall_inf_nil.
Qed.

Lemma mix2_std_bbb_r : forall l1 l2,
  ll_bbb l1 -> ll_bbb l2 -> ll_bbb (l2 ++ l1).
Proof.
intros l1 l2 pi1 pi2.
apply bbb_to_mix02 in pi2.
apply mix2_bbb_r ; assumption.
Qed.

(** [ll_bbb] as an enriched [ll] system *)

Lemma bbb_to_ll : forall l,
  ll_bbb l -> ll_ll (wn (tens (wn one) bot) :: l).
Proof with myeeasy ; try (cbn; Permutation_Type_solve).
intros l pi; induction pi;
  (try now (apply wk_r ; constructor)) ;
  try now (eapply ex_r ; [ | apply Permutation_Type_swap ] ;
           constructor ; eapply ex_r ; [ eassumption | cbn; Permutation_Type_solve ]).
- eapply ex_r...
- apply co_r.
  apply co_r.
  apply de_r.
  apply (ex_r _ (tens (wn one) bot :: (wn (tens (wn one) bot) :: l1)
                                   ++ (wn (tens (wn one) bot) :: l2)))...
  apply tens_r...
  + apply mix02_to_ll'' with true true true...
    apply stronger_pfrag with (pfrag_mix02)...
    nsplit 4...
    * intro a; split with a...
    * intros n.
      repeat (destruct n; try reflexivity).
  + apply bot_r...
- apply co_r.
  apply (ex_r _ (tens A B :: (wn (tens (wn one) bot) :: l2)
                          ++ (wn (tens (wn one) bot) :: l1)))...
  apply tens_r ; eapply ex_r ; [ apply IHpi1 | | apply IHpi2 | ] ...
- eapply ex_r ; [ | apply Permutation_Type_swap ].
  apply with_r.
  + eapply ex_r ; [ apply IHpi1 | ]...
  + eapply ex_r ; [ apply IHpi2 | ]...
- apply (ex_r _ (oc A :: map wn (tens (wn one) bot :: l)))...
  apply oc_r.
  eapply ex_r...
Qed.

Lemma ll_to_bbb : forall l,
  ll_ll l -> forall l' (l0 l1 : list unit),
  Permutation_Type l (l' ++ map (fun _ => tens (wn one) bot) l1
                         ++ map (fun _ => wn (tens (wn one) bot)) l0)  ->
  ll_bbb l'.
Proof with myeeasy ; try (cbn; Permutation_Type_solve).
intros l pi; induction pi using ll_nested_ind; intros l' l0' l1' HP.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; cbn in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  apply Permutation_Type_length_1_inv in HP.
  apply app_eq_unit_inf in HP.
  destruct HP as [[Heq1 Heq2] | [Heq1 Heq2]] ; subst ; destruct l' ; inversion Heq ; subst.
  + destruct l1' ; inversion H0.
    destruct l0' ; inversion H1.
  + destruct l' ; inversion H1.
    * destruct l1' ; inversion H0.
      destruct l0' ; inversion H2.
    * destruct l' ; inversion H2.
      rewrite H3.
      apply ax_bbb_r.
  + destruct l1' ; inversion H0.
    destruct l0' ; inversion H1.
  + destruct l' ; inversion H1.
    * destruct l1' ; inversion H0.
      destruct l0' ; inversion H2.
    * destruct l' ; inversion H2.
      rewrite H3.
      eapply ex_bbb_r ; [ apply ax_bbb_r | ]...
- cbn in p.
  eapply IHpi.
  etransitivity...
- eapply IHpi.
  etransitivity...
  apply (Permutation_Type_map wn) in p ; Permutation_Type_solve.
- inversion eqpmix.
- apply Permutation_Type_length_1_inv in HP.
  destruct l' ; inversion HP.
  + destruct l1' ; inversion H0.
    destruct l0' ; inversion H1.
  + apply app_eq_nil in H1 ; destruct H1 ; subst.
    apply one_bbb_r.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; cbn in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_elt_app_inf_exec Heq ; subst.
  + rewrite app_assoc in HP.
    apply IHpi in HP.
    eapply ex_bbb_r ; [ apply bot_bbb_r | ]...
  + dichot_elt_app_inf_exec Heq1 ; subst.
    * symmetry in Heq0; decomp_map_inf Heq0; inversion Heq0.
    * symmetry in Heq2; decomp_map_inf Heq2; inversion Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; cbn in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_elt_app_inf_exec Heq ; subst.
  + rewrite app_assoc in HP.
    remember (l'l ++ l) as l'.
    apply Permutation_Type_app_app_inv in HP as [[[[l1a l2a] l3a] l4a] [[HP1 HP2] [HP3 HP4]]];
      cbn in HP1, HP2, HP3, HP4.
    apply Permutation_Type_app_app_inv in HP4 as [[[[l1b l2b] l3b] l4b] [[HP1b HP2b] [HP3b HP4b]]];
      cbn in HP1b, HP2b, HP3b, HP4b.
    symmetry in HP1b.
    apply Permutation_Type_map_inv in HP1b as [la Heqa _].
    symmetry in Heqa; decomp_map_inf Heqa; cbn in Heqa1, Heqa2; subst.
    symmetry in HP2b.
    apply Permutation_Type_map_inv in HP2b as [lb Heqb _].
    symmetry in Heqb; decomp_map_inf Heqb; cbn in Heqb1, Heqb2; subst.
    apply (Permutation_Type_app_head l2a) in HP4b.
    assert (IHP1 := Permutation_Type_trans HP2 HP4b).
    apply (@Permutation_Type_cons _ A _ eq_refl) in IHP1.
    rewrite app_comm_cons in IHP1.
    apply (Permutation_Type_app_head l1a) in HP3b.
    assert (IHP2 := Permutation_Type_trans HP1 HP3b).
    apply (@Permutation_Type_cons _ B _ eq_refl) in IHP2.
    rewrite app_comm_cons in IHP2.
    apply IHpi in IHP1.
    apply IHpi0 in IHP2.
    symmetry in HP3.
    apply (Permutation_Type_cons_app _ _ (tens A B)) in HP3.
    eapply ex_bbb_r ; [ apply tens_bbb_r | apply HP3 ]...
  + dichot_elt_app_inf_exec Heq1 ; subst.
    * symmetry in Heq0; decomp_map_inf Heq0; inversion Heq0; subst; list_simpl in HP.
      rewrite (app_assoc (map _ l5)) in HP.
      rewrite <- map_app in HP.
      remember (l5 ++ l7) as l0 ; clear Heql0.
      apply Permutation_Type_app_app_inv in HP as [[[[l1a l2a] l3a] l4a] [[HP1 HP2] [HP3 HP4]]];
        cbn in HP1, HP2, HP3, HP4.
      apply Permutation_Type_app_app_inv in HP4 as [[[[l1b l2b] l3b] l4b] [[HP1b HP2b] [HP3b HP4b]]];
        cbn in HP1b, HP2b, HP3b, HP4b.
      symmetry in HP1b.
      apply Permutation_Type_map_inv in HP1b as [la Heqa _].
      symmetry in Heqa; decomp_map_inf Heqa; cbn in Heqa1, Heqa2; subst.
      symmetry in HP2b.
      apply Permutation_Type_map_inv in HP2b as [lb Heqb _].
      symmetry in Heqb; decomp_map_inf Heqb; cbn in Heqb1, Heqb2; subst.
      apply (Permutation_Type_app_head l2a) in HP4b.
      assert (IHP1 := Permutation_Type_trans HP2 HP4b).
      eapply (ex_r _ _ ((l2a ++ map (fun _ : unit => tens (wn one) bot) l8)
                       ++ map (fun _ => wn one) (tt :: nil)
                       ++ map (fun _ => wn (tens (wn one) bot)) l10)) in pi1...
      assert (ll pfrag_ll (l2a ++ wn one ::
                   map (fun _ : unit => wn (tens (wn one) bot)) (l8 ++ l10)))
        as pi1'.
      { clear - pi1 ; revert l2a l10 pi1 ; induction l8 ; intros l1 l2 pi ;
          list_simpl in pi ; list_simpl...
        list_simpl in IHl8.
        apply (ex_r _ (l1 ++
                wn one :: map (fun _ : unit => wn (tens (wn one) bot)) (l8 ++ tt :: l2)))...
        apply IHl8.
        eapply ex_r ; [ | apply Permutation_Type_app_comm ] ; list_simpl.
        eapply ex_r ; [ | cons2app ; apply Permutation_Type_app_comm ] ; list_simpl.
        apply de_r.
        eapply ex_r ; [ apply pi | ]... }
      apply (Permutation_Type_app_head l1a) in HP3b.
      assert (IHP2 := Permutation_Type_trans HP1 HP3b).
      apply (@Permutation_Type_cons _ bot _ eq_refl) in IHP2.
      rewrite app_comm_cons in IHP2.
      apply IHpi0 in IHP2.
      assert (Permutation_Type (l2a ++ l1a) l') as HP' by Permutation_Type_solve.
      eapply ex_bbb_r ; [ apply mix2_bbb_r | apply HP' ]...
      -- rewrite <- app_nil_l.
         eapply bot_rev_bbb...
      -- apply (stronger_pfrag (pmixupd_point_pfrag (pmixupd_point_pfrag pfrag_ll 0 true) 2 true)) ;
           [ | eapply ll_to_mix02'''_axcut ]...
         ++ nsplit 4...
            ** intros a; split with a...
            ** intro n.
               repeat (destruct n; myeasy)...
         ++ intros a ; destruct a.
         ++ intros a ; destruct a.
         ++ eapply ex_r in pi1' ; [  | apply Permutation_Type_app_comm ]...
    * symmetry in Heq2; decomp_map_inf Heq2; inversion Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; cbn in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_elt_app_inf_exec Heq ; subst.
  + rewrite app_assoc in HP.
    apply (@Permutation_Type_cons _ B _ eq_refl) in HP.
    apply (@Permutation_Type_cons _ A _ eq_refl) in HP.
    rewrite 2 app_comm_cons in HP.
    apply IHpi in HP.
    eapply ex_bbb_r ; [ apply parr_bbb_r | ]...
  + dichot_elt_app_inf_exec Heq1 ; subst.
    * symmetry in Heq0; decomp_map_inf Heq0; inversion Heq0.
    * symmetry in Heq2; decomp_map_inf Heq2; inversion Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; cbn in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_elt_app_inf_exec Heq ; subst.
  + eapply ex_bbb_r ; [ apply top_bbb_r | apply Permutation_Type_middle ]...
  + dichot_elt_app_inf_exec Heq1 ; subst.
    * symmetry in Heq0; decomp_map_inf Heq0; inversion Heq0.
    * symmetry in Heq2; decomp_map_inf Heq2; inversion Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; cbn in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_elt_app_inf_exec Heq ; subst.
  + rewrite app_assoc in HP.
    apply (@Permutation_Type_cons _ A _ eq_refl) in HP.
    rewrite app_comm_cons in HP.
    apply IHpi in HP.
    eapply ex_bbb_r ; [ apply plus_bbb_r1 | ]...
  + dichot_elt_app_inf_exec Heq1 ; subst.
    * symmetry in Heq0; decomp_map_inf Heq0; inversion Heq0.
    * symmetry in Heq2; decomp_map_inf Heq2; inversion Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; cbn in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_elt_app_inf_exec Heq ; subst.
  + rewrite app_assoc in HP.
    apply (@Permutation_Type_cons _ A _ eq_refl) in HP.
    rewrite app_comm_cons in HP.
    apply IHpi in HP.
    eapply ex_bbb_r ; [ apply plus_bbb_r2 | ]...
  + dichot_elt_app_inf_exec Heq1 ; subst.
    * symmetry in Heq0; decomp_map_inf Heq0; inversion Heq0.
    * symmetry in Heq2; decomp_map_inf Heq2; inversion Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; cbn in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_elt_app_inf_exec Heq ; subst.
  + rewrite app_assoc in HP.
    assert (HP2 := HP).
    apply (@Permutation_Type_cons _ A _ eq_refl) in HP.
    rewrite app_comm_cons in HP.
    apply IHpi in HP.
    apply (@Permutation_Type_cons _ B _ eq_refl) in HP2.
    rewrite app_comm_cons in HP2.
    apply IHpi0 in HP2.
    eapply ex_bbb_r ; [ apply with_bbb_r | apply Permutation_Type_middle ]...
  + dichot_elt_app_inf_exec Heq1 ; subst.
    * symmetry in Heq0; decomp_map_inf Heq0; inversion Heq0.
    * symmetry in Heq2; decomp_map_inf Heq2; inversion Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; cbn in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_elt_app_inf_exec Heq ; subst.
  + symmetry in HP.
    apply Permutation_Type_map_inv in HP as [l' Heq HP].
    symmetry in Heq; decomp_map_inf Heq; cbn in Heq1, Heq2, Heq3, Heq5; subst ; cbn in HP.
    apply (Permutation_Type_map wn) in HP.
    list_simpl in HP.
    rewrite app_assoc in HP.
    rewrite <- map_app in HP.
    apply (@Permutation_Type_cons _ A _ eq_refl) in HP.
    rewrite app_comm_cons in HP.
    rewrite Heq2, Heq5 in HP.
    apply IHpi in HP.
    eapply ex_bbb_r ; [ apply oc_bbb_r | ]...
  + dichot_elt_app_inf_exec Heq1 ; subst.
    * symmetry in Heq0; decomp_map_inf Heq0; inversion Heq0.
    * symmetry in Heq2; decomp_map_inf Heq2; inversion Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; cbn in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_elt_app_inf_exec Heq ; subst.
  + rewrite app_assoc in HP.
    apply (@Permutation_Type_cons _ A _ eq_refl) in HP.
    rewrite app_comm_cons in HP.
    apply IHpi in HP.
    eapply ex_bbb_r ; [ apply de_bbb_r | ]...
  + dichot_elt_app_inf_exec Heq1 ; subst.
    * symmetry in Heq0; decomp_map_inf Heq0; inversion Heq0.
    * symmetry in Heq2; decomp_map_inf Heq2; cbn in Heq1, Heq2, Heq3; subst; cbn in HP.
      inversion Heq2 ; subst.
      list_simpl in HP ; rewrite <- map_app in HP.
      apply (@Permutation_Type_cons _ (tens (wn one) bot) _ eq_refl) in HP.
      assert (Permutation_Type (tens (wn one) bot :: l0)
                               (l' ++ map (fun _ : unit => tens (wn one) bot) (tt :: l1')
                                   ++ map (fun _ : unit => wn (tens (wn one) bot)) (l2 ++ l5)))
        as HP' by (etransitivity ; [ apply HP | ] ; Permutation_Type_solve). 
      apply IHpi in HP'...
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; cbn in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_elt_app_inf_exec Heq ; subst.
  + rewrite app_assoc in HP.
    apply IHpi in HP.
    eapply ex_bbb_r ; [ apply wk_bbb_r | ]...
  + dichot_elt_app_inf_exec Heq1 ; subst.
    * symmetry in Heq0; decomp_map_inf Heq0; inversion Heq0.
    * symmetry in Heq2; decomp_map_inf Heq2 ; cbn in Heq1, Heq2, Heq3; subst; cbn in HP.
      inversion Heq2 ; subst.
      list_simpl in HP ; rewrite <- map_app in HP.
      apply IHpi in HP...
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; cbn in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_elt_app_inf_exec Heq ; subst.
  + rewrite app_assoc in HP.
    apply (@Permutation_Type_cons _ (wn A) _ eq_refl) in HP.
    apply (@Permutation_Type_cons _ (wn A) _ eq_refl) in HP.
    rewrite 2 app_comm_cons in HP.
    apply IHpi in HP.
    eapply ex_bbb_r ; [ apply co_bbb_r | ]...
  + dichot_elt_app_inf_exec Heq1 ; subst.
    * symmetry in Heq0; decomp_map_inf Heq0; inversion Heq0.
    * symmetry in Heq2; decomp_map_inf Heq2 ; cbn in Heq1, Heq2, Heq3; subst; cbn in HP.
      inversion Heq2 ; subst.
      list_simpl in HP ; rewrite <- map_app in HP.
    apply (@Permutation_Type_cons _ (wn (tens (wn one) bot)) _ eq_refl) in HP.
    apply (@Permutation_Type_cons _ (wn (tens (wn one) bot)) _ eq_refl) in HP.
    apply (@Permutation_Type_trans _ (wn (tens (wn one) bot) ::
                                      wn (tens (wn one) bot) :: l0)) in HP...
    assert (Permutation_Type (wn (tens (wn one) bot) :: wn (tens (wn one) bot) :: l0)
       (l' ++ map (fun _ : unit => tens (wn one) bot) l1' ++
              map (fun _ : unit => wn (tens (wn one) bot)) (tt :: tt :: l2 ++ l5)))
      as HP' by (etransitivity ; [ apply HP | Permutation_Type_solve ]).
    apply IHpi in HP'...
- inversion f.
- destruct a.
Qed.

(** ** Cut admissibility for [ll_bbb] *)

Theorem cut_bbb_r : forall A l1 l2,
  ll_bbb (dual A :: l1) -> ll_bbb (A :: l2) -> ll_bbb (l2 ++ l1).
Proof.
intros A l1 l2 pi1 pi2.
apply bbb_to_ll in pi1.
apply bbb_to_ll in pi2.
eapply ex_r in pi1 ; [ | apply Permutation_Type_swap ].
eapply ex_r in pi2 ; [ | apply Permutation_Type_swap ].
apply (cut_ll_r _ _ _ pi1) in pi2.
apply (ex_r _ _ ((l2 ++ l1) ++ map (fun _ => tens (wn one) bot) (@nil unit)
                            ++ map (fun _ => wn (tens (wn one) bot)) (tt :: tt :: nil))) in pi2 ;
 [ | cbn; Permutation_Type_solve ].
eapply ll_to_bbb in pi2 ; [ | reflexivity ].
assumption.
Qed.


(** ** Comparison with LL + [bot = oc bot] *)

Lemma mix2_bb_r : forall l1 l2, llR (oc bot) l1 -> llR (oc bot) l2 ->
  llR (oc bot) (l2 ++ l1).
Proof with myeeasy.
intros l1 l2 pi1 pi2.
eapply (cut_r _ one)...
- apply bot_r...
- cons2app.
  eapply (cut_r _ (oc bot)).
  + apply wk_r...
  + apply (gax_r (pfrag_llR (oc bot)) false).
Unshelve. all : reflexivity.
Qed.

Lemma mix2_to_bb : forall l, ll_mix2 l -> llR (oc bot) l.
Proof with myeeasy.
intros l pi; induction pi using ll_nested_ind ; try now econstructor.
- eapply ex_r...
- eapply ex_wn_r...
- repeat (destruct L; try now inversion eqpmix).
  cbn; rewrite app_nil_r.
  apply mix2_bb_r...
  + assert (In_inf l1 (l0 :: l1 :: nil)) as Hin.
    { right; left... }
    apply (In_Forall_inf_in _ PL) in Hin as [pi Hin].
    refine (Dependent_Forall_inf_forall_formula _ _ X Hin).
  + assert (In_inf l0 (l0 :: l1 :: nil)) as Hin by now left.
    apply (In_Forall_inf_in _ PL) in Hin as [pi Hin].
    refine (Dependent_Forall_inf_forall_formula _ _ X Hin).
Qed.

Theorem bb_to_bbb : forall l, llR (oc bot) l -> ll_bbb l.
Proof with myeeasy ; try (cbn; Permutation_Type_solve).
intros l pi.
induction pi ; try now econstructor.
- eapply ex_bbb_r...
- eapply ex_bbb_r...
  apply (Permutation_Type_map wn) in p ; Permutation_Type_solve.
- eapply cut_bbb_r...
- destruct a ; cbn.
  + apply de_bbb_r.
    apply one_bbb_r.
  + rewrite <- (app_nil_l (one :: _)).
    rewrite app_comm_cons.
    apply mix2_bbb_r.
    * apply one_bbb_r.
    * change nil with (map (@wn atom) nil).
      apply oc_r.
      eapply bot_r.
      change (map wn nil) with (concat (@nil (list formula))).
      apply mix_r...
      apply Forall_inf_nil.
Qed.

(** The converse of [bb_to_bbb] is proved in the [nn] library. *)

(** *** Examples *)
(*
Goal ll_bbb (one :: oc (parr one one) :: nil).
Proof with myeeasy.
change (one :: oc (parr one one) :: nil)
  with ((one :: nil) ++ oc (parr one one) :: nil).
eapply mix2_bbb_r.
- change nil with (map wn nil).
  apply oc_bbb_r.
  apply parr_bbb_r.
  cbn.
  change (one :: one :: nil) with ((one :: nil) ++ one :: nil).
  apply mix2_bbb_r.
  + apply one_bbb_r.
  + eapply one_r.
- eapply one_r.
Qed.

Goal llR (oc bot) (one :: oc (parr one one) :: nil).
Proof with myeeasy.
assert (llR (oc bot) ((one :: nil) ++ one :: nil))
  as Hr by (eapply mix2_bb_r ; apply one_r).
change (one :: oc (parr one one) :: nil)
  with ((one :: nil) ++ oc (parr one one) :: nil).
eapply mix2_bb_r.
- change nil with (map wn nil).
  apply oc_r.
  apply parr_r...
- apply one_r.
Qed.
*)

Example bbb_ex :
  ll_bbb (one :: oc (tens (parr one one) bot) :: nil).
Proof with myeeasy ; try Permutation_Type_solve.
change (one :: oc (tens (parr one one) bot) :: nil)
  with ((@one atom :: nil) ++ (oc (tens (parr one one) bot) :: nil)).
apply (ex_bbb_r ((oc (tens (parr one one) bot) :: nil) ++ one :: nil))...
eapply mix2_bbb_r.
- apply one_bbb_r.
- change (oc (tens (parr one one) bot) :: nil)
    with (@oc atom (tens (parr one one) bot) :: map wn (nil ++ nil)).
  eapply oc_r.
  rewrite map_app.
  eapply tens_r.
  + eapply parr_r.
    cbn.
    change (one :: one :: nil) with (concat ((@one atom :: nil) :: (one :: nil) :: nil)).
    apply mix_r...
    repeat (apply Forall_inf_cons; try apply one_r).
    apply Forall_inf_nil.
  + eapply bot_r.
    change (map wn nil) with (concat (@nil (list formula))).
    apply mix_r...
    apply Forall_inf_nil.
Qed.

Example bb_ex :
  llR (oc bot) (one :: oc (tens (parr one one) bot) :: nil).
Proof with myeeasy.
assert (Hax :=  gax_r (@pfrag_llR atom (oc bot)) false) ; cbn in Hax.
assert (llR (oc bot) ((one :: nil) ++ one :: nil))
  as Hr by (eapply mix2_bb_r ; apply one_r).
eapply (@cut_r _ (pfrag_llR _) eq_refl) in Hax...
- apply Hax.
- eapply ex_r ; [ | apply Permutation_Type_swap ].
  cbn; change (wn one :: nil) with (map (@wn atom) (one :: nil)).
  apply oc_r.
  cbn; rewrite <- (app_nil_l nil), app_comm_cons.
  apply tens_r.
  + apply parr_r...
  + apply bot_r, de_r, one_r.
Qed.


(** ** Additional results on a weakened version of [ll_bbb]
 without [mix2] above [mix2] on the [mix0] side *)
Inductive ll_bbb0 : list formula -> Type :=
| ax_bbb0_r : forall X, ll_bbb0 (covar X :: var X :: nil)
| ex_bbb0_r : forall l1 l2, ll_bbb0 l1 -> Permutation_Type l1 l2 -> ll_bbb0 l2
| mix2_bbb0_r : forall l1 l2, ll_bbb0 l1 -> ll_mix0 l2 -> ll_bbb0 (l2 ++ l1)
| one_bbb0_r : ll_bbb0 (one :: nil)
| bot_bbb0_r : forall l, ll_bbb0 l -> ll_bbb0 (bot :: l)
| tens_bbb0_r : forall A B l1 l2, ll_bbb0 (A :: l1) -> ll_bbb0 (B :: l2) ->
                               ll_bbb0 (tens A B :: l2 ++ l1)
| parr_bbb0_r : forall A B l, ll_bbb0 (A :: B :: l) -> ll_bbb0 (parr A B :: l)
| top_bbb0_r : forall l, ll_bbb0 (top :: l)
| plus_bbb0_r1 : forall A B l, ll_bbb0 (A :: l) -> ll_bbb0 (aplus A B :: l)
| plus_bbb0_r2 : forall A B l, ll_bbb0 (A :: l) -> ll_bbb0 (aplus B A :: l)
| with_bbb0_r : forall A B l, ll_bbb0 (A :: l) -> ll_bbb0 (B :: l) ->
                              ll_bbb0 (awith A B :: l)
| oc_bbb0_r : forall A l, ll_bbb0 (A :: map wn l) -> ll_bbb0 (oc A :: map wn l)
| de_bbb0_r : forall A l, ll_bbb0 (A :: l) -> ll_bbb0 (wn A :: l)
| wk_bbb0_r : forall A l, ll_bbb0 l -> ll_bbb0 (wn A :: l)
| co_bbb0_r : forall A l, ll_bbb0 (wn A :: wn A :: l) -> ll_bbb0 (wn A :: l).

(** The example given above in [ll_bbb] and [llR (oc bot)] is not cut-free provable
    in [ll_bbb0]. *)
Lemma mix0_bbb0_false : ll_bbb0 nil -> False.
Proof with myeasy.
intros pi.
remember nil as l.
revert Heql ; induction pi ; intros Heql ; inversion Heql ; subst.
- symmetry in p.
  apply Permutation_Type_nil in p ; intuition.
- apply app_eq_nil in Heql.
  destruct Heql ; subst ; intuition.
Qed.

Lemma ex_implies_mix2_mix02 : forall l,
  ll_bbb0 l -> Permutation_Type l (one :: oc (tens (parr one one) bot) :: nil) ->
    @ll_mix0 atom (one :: one :: nil).
Proof with myeeasy.
intros l H; induction H; intro HP;
  try now (apply Permutation_Type_sym in HP ;
       apply Permutation_Type_length_2_inv in HP as [HP | HP] ;
       inversion HP).
- apply IHll_bbb0.
  Permutation_Type_solve.
- apply Permutation_Type_sym in HP.
  apply Permutation_Type_length_2_inv in HP.
  destruct HP as [HP | HP].
  + symmetry in HP.
    rewrite <- (app_nil_l (one :: _)) in HP.
    dichot_elt_app_inf_exec HP ; subst.
    * apply eq_sym in HP1.
      apply app_eq_unit_inf in HP1.
      destruct HP1 ; destruct p ; subst.
      -- clear - H.
         exfalso.
         remember (oc (tens (parr one one) bot) :: nil) as l.
         revert Heql ; induction H ; intro Heql ; inversion Heql ; subst.
         ++ symmetry in p.
            apply Permutation_Type_length_1_inv in p.
            apply IHll_bbb0...
         ++ apply app_eq_unit in Heql.
            destruct Heql ; destruct H0 ; subst.
            ** apply IHll_bbb0...
            ** eapply mix0_bbb0_false...
         ++ rewrite_all H2.
            clear - H.
            remember (tens (parr one one) bot :: nil) as l.
            revert Heql ; induction H ; intro Heql ; inversion Heql ; subst.
            ** symmetry in p.
               apply Permutation_Type_length_1_inv in p.
               apply IHll_bbb0...
            ** apply app_eq_unit in Heql.
               destruct Heql ; destruct H0 ; subst.
               --- apply IHll_bbb0...
               --- eapply mix0_bbb0_false...
            ** apply app_eq_nil in H4.
               destruct H4 ; subst.
               clear - H0.
               remember (bot :: nil) as l.
               revert Heql ; induction H0 ; intro Heql ; inversion Heql ; subst.
               --- symmetry in p.
                   apply Permutation_Type_length_1_inv in p.
                   apply IHll_bbb0...
               --- apply app_eq_unit_inf in Heql.
                   destruct Heql ; destruct p ; subst.
                   +++ apply IHll_bbb0...
                   +++ eapply mix0_bbb0_false...
               --- eapply mix0_bbb0_false...
      -- exfalso.
         eapply mix0_bbb0_false...
    * symmetry in HP0.
      apply app_eq_nil in HP0.
      destruct HP0 ; subst.
      apply IHll_bbb0...
  + symmetry in HP.
    rewrite <- (app_nil_l (oc _::_)) in HP.
    dichot_elt_app_inf_exec HP ; subst.
    * symmetry in HP1.
      apply app_eq_unit_inf in HP1.
      destruct HP1 ; destruct p ; subst.
      -- clear - l ; rename l into H.
         cbn in H.
         remember (oc (tens (parr one one) bot) :: nil) as l.
         revert Heql ; induction H ; intro Heql ; inversion Heql ; subst.
         ++ symmetry in p.
            cbn in p.
            apply Permutation_Type_length_1_inv in p.
            apply IHll...
         ++ destruct l1 ; inversion Heql.
            ** destruct lw' ; inversion Heql ; cbn in H0 ; subst.
               symmetry in p ; apply Permutation_Type_nil in p ; subst.
               intuition.
            ** apply app_eq_nil in H3 ; destruct H3 as [Heq1 Heq2] ; subst.
               apply app_eq_nil in Heq2 ; destruct Heq2 as [Heq2 ?] ; subst.
               destruct lw' ; inversion Heq2 ; subst.
               symmetry in p ; apply Permutation_Type_nil in p ; subst.
               intuition.
         ++ repeat (destruct L; inversion i; try now inversion Heql).
         ++ rewrite_all H2.
            clear - H.
            remember (tens (parr one one) bot :: nil) as l.
            revert Heql ; induction H ; intro Heql ; inversion Heql ; subst.
            ** symmetry in p.
               cbn in p.
               apply Permutation_Type_length_1_inv in p.
               apply IHll...
            ** destruct l1 ; inversion Heql.
               --- destruct lw' ; inversion Heql ; cbn in H0 ; subst.
                   symmetry in p ; apply Permutation_Type_nil in p ; subst.
                   intuition.
               --- apply app_eq_nil in H3 ; destruct H3 as [Heq1 Heq2] ; subst.
                   apply app_eq_nil in Heq2 ; destruct Heq2 as [Heq2 ?] ; subst.
                   destruct lw' ; inversion Heq2 ; subst.
                   symmetry in p ; apply Permutation_Type_nil in p ; subst.
                   intuition.
            ** repeat (destruct L; inversion i; try now inversion H0).
            ** apply app_eq_nil in H4.
               destruct H4 ; subst.
               clear - H.
               remember (parr one one :: nil) as l.
               revert Heql ; induction H ; intro Heql ; inversion Heql ; subst...
               --- symmetry in p.
                   cbn in p.
                   apply Permutation_Type_length_1_inv in p.
                   apply IHll...
               --- destruct l1 ; inversion Heql.
                   +++ destruct lw' ; inversion Heql ; cbn in H0 ; subst.
                       symmetry in p ; apply Permutation_Type_nil in p ; subst.
                       intuition.
                   +++ apply app_eq_nil in H3 ; destruct H3 as [Heq1 Heq2] ; subst.
                       apply app_eq_nil in Heq2 ; destruct Heq2 as [Heq2 ?] ; subst.
                       destruct lw' ; inversion Heq2 ; subst.
                       symmetry in p ; apply Permutation_Type_nil in p ; subst.
                       intuition.
               --- repeat (destruct L; inversion i; try now inversion H0).
               --- inversion f.
               --- destruct a.
            ** inversion f.
            ** destruct a.
         ++ inversion f.
         ++ destruct a.
      -- exfalso.
         eapply mix0_bbb0_false...
    * symmetry in HP0.
      apply app_eq_nil in HP0.
      destruct HP0 ; subst.
      apply IHll_bbb0.
      Permutation_Type_solve.
- symmetry in HP.
  apply Permutation_Type_length_2_inv in HP.
  destruct HP as [HP | HP] ; inversion HP.
  destruct l ; inversion H2.
Defined.

Lemma ex_not_bbb0 :
  ll_bbb0 (one :: oc (tens (parr one one) bot) :: nil) -> False.
Proof.
intros H.
apply (@mix0_not_mix2 atom).
eapply ex_implies_mix2_mix02 ; [ eassumption | reflexivity ].
Qed.

Lemma bbb_neq_bbb0 : { l & prod (ll_bbb l) (ll_bbb0 l -> False) }.
Proof.
eexists ; split ; [ apply bbb_ex | apply ex_not_bbb0 ].
Qed.

(** The same example is provable in [ll_bbb0] with cut,
    thus cut admissibility does not hold for [ll_bbb0]. *)

Section bbb0_with_cut.

Hypothesis cut_bbb0_r : forall A l1 l2,
  ll_bbb0 (dual A :: l1) -> ll_bbb0 (A :: l2) -> ll_bbb0 (l2 ++ l1).

Theorem llR_oc_bot_to_bbb0_cut : forall l,
  llR (oc bot) l -> ll_bbb0 l.
Proof with myeeasy.
intros l pi.
induction pi ; (try now inversion f) ; try now constructor.
- eapply ex_bbb0_r...
- eapply ex_bbb0_r...
  apply (Permutation_Type_map wn) in p ; Permutation_Type_solve.
- eapply cut_bbb0_r...
- destruct a ; cbn.
  + apply de_bbb0_r.
    apply one_bbb0_r.
  + rewrite <- (app_nil_l (one :: _)).
    rewrite app_comm_cons.
    apply mix2_bbb0_r.
    * apply one_bbb0_r.
    * change nil with (map (@wn atom) nil).
      apply oc_r.
      eapply bot_r.
      change (map wn nil) with (concat (@nil (list formula))).
      apply mix_r...
      apply Forall_inf_nil.
Qed.

Example bbb0_cut_ex :
  ll_bbb0 (one :: oc (tens (parr one one) bot) :: nil).
Proof.
apply llR_oc_bot_to_bbb0_cut.
apply bb_ex.
Qed.

End bbb0_with_cut.

Lemma cut_not_rule_bbb0 :
(forall A l1 l2,
  ll_bbb0 (dual A :: l1) -> ll_bbb0 (A :: l2) -> ll_bbb0 (l2 ++ l1))
    -> False.
Proof.
intros Hcut.
apply ex_not_bbb0.
apply bbb0_cut_ex.
assumption.
Qed.

End Atoms.
