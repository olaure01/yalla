(* ll_cut library for yalla *)


(** * Cut admissibility for [ll] *)

Require Import Arith_base.

Require Import funtheory.
Require Import List_more.
Require Import List_more.
Require Import Permutation_Type_more.
Require Import GPermutation_Type.
Require Import flat_map_more.

Require Export ll_def.


Section Cut_Elim_Proof.

Context {P : pfrag}.

Hypothesis P_gax_at : forall a, Forall atomic (projT2 (pgax P) a).

Lemma cut_oc_comm : pcut P = false -> forall n A l1 l2, ll P (l1 ++ wn A :: l2) -> 
  (forall lw (pi0 : ll P (dual A :: map wn lw)), psize pi0 < n -> ll P (l1 ++ map wn lw ++ l2)) ->
  forall l3 l4 (pi1 : ll P (l3 ++ oc (dual A) :: l4)), psize pi1 <= n -> ll P (l1 ++ l4 ++ l3 ++ l2).
Proof with myeasy_perm_Type.
intros P_cutfree n A l1 l2 pi2 ; induction n ; intros IH l3 l4 pi1 Hs ;
  remember (l3 ++ oc (dual A) :: l4) as l ; destruct_ll pi1 f X l Hl Hr HP a ;
  try (exfalso ; simpl in Hs ; clear -Hs ; myeasy ; fail) ; try inversion Heql ; subst.
- destruct l3 ; inversion Heql ; subst.
  destruct l3 ; inversion H2 ; subst.
  destruct l3 ; inversion H3.
- simpl in Hs.
  apply PCPermutation_Type_vs_elt_inv in HP.
  destruct HP as [[l3' l4'] Heq HP] ; simpl in Heq ; simpl in HP ; subst.
  assert (PEPermutation_Type (pperm P) (l1 ++ l4' ++ l3' ++ l2) (l1 ++ l4 ++ l3 ++ l2)) as HP'.
  { apply PEPermutation_Type_app_head.
    rewrite 2 app_assoc ; apply PEPermutation_Type_app_tail.
    symmetry... }
  apply PEPermutation_PCPermutation_Type in HP'.
  apply (ex_r _ (l1 ++ l4' ++ l3' ++ l2))...
  simpl in Hs ; refine (IHn _ _ _ Hl _)...
  intros ; refine (IH _ pi0 _)...
- symmetry in H0 ; trichot_elt_app_inf_exec H0 ; subst.
  + list_simpl ; rewrite app_assoc.
    eapply ex_wn_r...
    revert Hl Hs ; list_simpl ; intros Hl Hs.
    rewrite (app_assoc l5) ; rewrite (app_assoc _ l0) ; rewrite <- (app_assoc l5).
    refine (IHn _ _ _ Hl _)...
    intros ; refine (IH _ pi0 _)...
  + destruct H2 as [H2 H3]; simpl in H2; symmetry in H2; decomp_map_inf H2.
    inversion H2.
  + list_simpl ; rewrite 2 app_assoc.
    eapply ex_wn_r...
    revert Hl Hs ; simpl ; rewrite 2 app_assoc ; intros Hl Hs.
    list_simpl ; rewrite (app_assoc l) ; rewrite (app_assoc _ l6).
    refine (IHn _ _ _ Hl _)...
    intros ; refine (IH _ pi0 _)...
- destruct l3 ; inversion H0.
- dichot_elt_app_inf_exec H0 ; subst.
  + list_simpl.
    eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    apply mix2_r...
    eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    simpl in Hs ; refine (IHn _ _ _ Hr _)...
    intros ; refine (IH _ pi0 _)...
  + eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    apply mix2_r...
    eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    simpl in Hs ; refine (IHn _ _ _ Hl _)...
    intros ; refine (IH _ pi0 _)...
- destruct l3 ; inversion H0.
  destruct l3 ; inversion H2.
- destruct l3 ; inversion H0 ; subst.
  eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  apply bot_r...
  eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  simpl in Hs ; refine (IHn _ _ _ Hl _)...
  intros ; refine (IH _ pi0 _)...
- destruct l3 ; inversion H0 ; subst.
  dichot_elt_app_inf_exec H2 ; subst.
  + list_simpl.
    eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    rewrite app_comm_cons ; eapply ex_r ; [ | symmetry ; apply PCPermutation_Type_app_rot ] ; list_simpl.
    rewrite 3 app_assoc ; apply tens_r...
    list_simpl ; rewrite app_comm_cons ; eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    revert Hr Hs ; simpl ; rewrite (app_comm_cons _ _ B) ; intros Hr Hs.
    refine (IHn _ _ _ Hr _)...
    intros ; refine (IH _ pi0 _)...
  + eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    apply tens_r...
    list_simpl ; rewrite app_comm_cons ; eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    revert Hl Hs ; simpl ; rewrite (app_comm_cons _ _ A0) ; intros Hl Hs.
    refine (IHn _ _ _ Hl _)...
    intros ; refine (IH _ pi0 _)...
- destruct l3 ; inversion H0 ; subst.
  eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  apply parr_r...
  rewrite 2 app_comm_cons ; eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  revert Hl Hs ; simpl ; rewrite (app_comm_cons _ _ B) ; rewrite (app_comm_cons _ _ A0) ; intros Hl Hs.
  simpl in Hs ; refine (IHn _ _ _ Hl _) ; simpl...
  intros ; refine (IH _ pi0 _)...
- destruct l3 ; inversion H0 ; subst.
  eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  apply top_r...
- destruct l3 ; inversion H0 ; subst.
  eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  apply plus_r1...
  rewrite app_comm_cons ; eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  revert Hl Hs ; simpl ; rewrite (app_comm_cons _ _ A0) ; intros Hl Hs.
  simpl in Hs ; refine (IHn _ _ _ Hl _) ; simpl...
  intros ; refine (IH _ pi0 _)...
- destruct l3 ; inversion H0 ; subst.
  eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  apply plus_r2...
  rewrite app_comm_cons ; eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  revert Hl Hs ; simpl ; rewrite (app_comm_cons _ _ A0) ; intros Hl Hs.
  simpl in Hs ; refine (IHn _ _ _ Hl _) ; simpl...
  intros ; refine (IH _ pi0 _)...
- destruct l3 ; inversion H0 ; subst.
  eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  apply with_r...
  + rewrite app_comm_cons ; eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    revert Hl Hs ; simpl ; rewrite (app_comm_cons _ _ A0) ; intros Hl Hs.
    simpl in Hs ; refine (IHn _ _ _ Hl _) ; simpl...
    intros ; refine (IH _ pi0 _)...
  + rewrite app_comm_cons ; eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    revert Hr Hs ; simpl ; rewrite (app_comm_cons _ _ B) ; intros Hr Hs.
    simpl in Hs ; refine (IHn _ _ _ Hr _) ; simpl...
    intros ; refine (IH _ pi0 _)...
- destruct l3 ; inversion H0 ; subst.
  + refine (IH _ _ _)...
  + decomp_map_inf H2; inversion H2.
- destruct l3 ; inversion H0 ; subst.
  eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  apply de_r...
  rewrite app_comm_cons ; eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  revert Hl Hs ; simpl ; rewrite (app_comm_cons _ _ A0) ; intros Hl Hs.
  simpl in Hs ; refine (IHn _ _ _ Hl _) ; simpl...
  intros ; refine (IH _ pi0 _)...
- destruct l3 ; inversion H0 ; subst.
  eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  apply wk_r...
  eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  simpl in Hs ; refine (IHn _ _ _ Hl _) ; simpl...
  intros ; refine (IH _ pi0 _)...
- destruct l3 ; inversion H0 ; subst.
  eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  apply co_r...
  rewrite 2 app_comm_cons ; eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
  revert Hl Hs ; simpl ; rewrite 2 (app_comm_cons _ _ (wn A0)) ; intros Hl Hs.
  simpl in Hs ; refine (IHn _ _ _ Hl _) ; simpl...
  intros ; refine (IH _ pi0 _)...
- rewrite f in P_cutfree ; inversion P_cutfree.
- exfalso.
  assert (Hat := P_gax_at a) ; rewrite H0 in Hat.
  apply Forall_app in Hat ; destruct Hat as [_ Hat] ; inversion Hat.
  inversion H2.
Qed.

Lemma substitution_oc : pcut P = false -> forall A,
  (forall l0 l1 l2, ll P (dual A :: l0) -> ll P (l1 ++ A :: l2) -> ll P (l1 ++ l0 ++ l2)) ->
  forall lw l, ll P (dual A :: map wn lw) -> ll P l -> forall l' L,
  l = l' ++ flat_map (cons (wn A)) L -> ll P (l' ++ flat_map (app (map wn lw)) L).
Proof with myeasy_perm_Type.
intros P_cutfree A IHcut lw l pi1 pi2.
induction pi2 ; intros l' L Heq ; subst.
- destruct L ; list_simpl in Heq ; subst.
  + list_simpl ; apply ax_r.
  + exfalso.
    destruct l' ; inversion Heq.
    destruct l' ; inversion H1.
    destruct l' ; inversion H3.
- case_eq (pperm P) ; intros Hperm ; rewrite Hperm in p ; simpl in p ; subst.
  + destruct (Permutation_Type_app_flat_map_cst _ (map wn lw) _ _ p) as [[L' l''] (Hnil' & HeqL' & HPL')] ;
      simpl in Hnil' ; simpl in HeqL' ; simpl in HPL' ; subst.
    eapply ex_r ; [ | rewrite Hperm ; simpl ; apply HPL' ].
    apply IHpi2...
  + destruct (CPermutation_Type_app_flat_map_cst _ (map wn lw) _ _ p) as [[L' l''] (Hnil' & HeqL' & HPL')] ;
      simpl in Hnil' ; simpl in HeqL' ; simpl in HPL' ; subst.
    eapply ex_r ; [ | rewrite Hperm ; simpl ; apply HPL' ].
    apply IHpi2...
- assert (injective wn) as Hinj by now intros x y Hxy; inversion Hxy.
  destruct (Permutation_Type_flat_map_cons_flat_map_app_cst _ Hinj lw _ _ _ _ p Heq)
    as [[[[[[lw1' lw2'] l1'] l2'] l''] L'] (H1 & H2 & H3 & H4)].
  rewrite <- H4 ; apply (ex_wn_r _ _ lw1')...
  rewrite H3 ; apply IHpi2...
- symmetry in Heq.
  apply app_eq_nil in Heq.
  destruct Heq as [Heq' Heq] ; subst.
  destruct L ; inversion Heq.
  list_simpl ; apply mix0_r...
- app_vs_app_flat_map_cst_inv Heq.
  + list_simpl ; apply mix2_r...
    apply IHpi2_1...
  + rewrite flat_map_app ; list_simpl.
    rewrite 3 app_assoc ; apply mix2_r...
    * apply IHpi2_1...
    * list_simpl.
      replace (flat_map (app (map wn lw)) L0 ++ map wn lw ++ l)
         with (flat_map (app (map wn lw)) (L0 ++ l :: nil))
        by (rewrite flat_map_app ; list_simpl ; reflexivity).
      apply IHpi2_2...
  + rewrite flat_map_app ; rewrite app_assoc ; apply mix2_r...
    * rewrite <- (app_nil_l _).
      apply IHpi2_1...
    * apply IHpi2_2...
- destruct L ; list_simpl in Heq ; subst.
  + list_simpl ; apply one_r.
  + exfalso.
    destruct l' ; inversion Heq.
    destruct l' ; inversion H1.
- destruct l' ; inversion Heq ; [ destruct L ; inversion H0 | ] ; subst.
  simpl ; apply bot_r.
  apply IHpi2...
- destruct l' ; inversion Heq ; [ destruct L ; inversion H0 | ] ; subst.
  app_vs_app_flat_map_cst_inv H1.
  + list_simpl ; apply tens_r...
    rewrite app_comm_cons in IHpi2_1 ; rewrite app_comm_cons ; apply IHpi2_1...
  + rewrite flat_map_app ; list_simpl.
    rewrite 3 app_assoc ; apply tens_r...
    * rewrite app_comm_cons in IHpi2_1 ; rewrite app_comm_cons ; apply IHpi2_1...
    * list_simpl.
      replace (flat_map (app (map wn lw)) L0 ++ map wn lw ++ l)
         with (flat_map (app (map wn lw)) (L0 ++ l :: nil))
        by (rewrite flat_map_app ; list_simpl ; reflexivity).
      rewrite app_comm_cons in IHpi2_2 ; rewrite app_comm_cons ; apply IHpi2_2...
  + rewrite flat_map_app ; rewrite app_assoc ; simpl ; apply tens_r...
    * rewrite <- (app_nil_l (flat_map _ _)) ; rewrite app_comm_cons.
      apply IHpi2_1...
    * rewrite app_comm_cons in IHpi2_2 ; rewrite app_comm_cons ; apply IHpi2_2...
- destruct l' ; inversion Heq ; [ destruct L ; inversion H0 | ] ; subst.
  simpl ; apply parr_r.
  rewrite 2 app_comm_cons ; apply IHpi2...
- destruct l' ; inversion Heq ; [ destruct L ; inversion H0 | ] ; subst.
  apply top_r.
- destruct l' ; inversion Heq ; [ destruct L ; inversion H0 | ] ; subst.
  simpl ; apply plus_r1.
  rewrite app_comm_cons ; apply IHpi2...
- destruct l' ; inversion Heq ; [ destruct L ; inversion H0 | ] ; subst.
  simpl ; apply plus_r2.
  rewrite app_comm_cons ; apply IHpi2...
- destruct l' ; inversion Heq ; [ destruct L ; inversion H0 | ] ; subst.
  simpl ; apply with_r.
  + rewrite app_comm_cons ; apply IHpi2_1...
  + rewrite app_comm_cons ; apply IHpi2_2...
- destruct l' ; inversion Heq ; [ destruct L ; inversion H0 | ] ; subst.
  assert ({ Lw | flat_map (app (map wn lw)) L = map wn Lw }) as [Lw HeqLw].
  { clear Heq pi2 IHpi2 ; revert l' H1 ; clear ; induction L ; intros l' Heq.
    - exists nil...
    - simpl in Heq; decomp_map_inf Heq; subst.
      inversion Heq3 ; subst ; simpl.
      list_simpl in IHL; rewrite Heq5 in IHL ; list_simpl in IHL.
      rewrite app_comm_cons in IHL ; rewrite app_assoc in IHL.
      destruct (IHL _ eq_refl) as [Lw Heq'].
      exists (lw ++ l4 ++ Lw) ; list_simpl ; rewrite <- Heq'... }
  decomp_map_inf H1; subst.
  list_simpl; rewrite HeqLw, <- map_app; apply oc_r.
  specialize IHpi2 with (A0 :: map wn l1) L; rewrite <- H3 in IHpi2; list_simpl in IHpi2.
  list_simpl; rewrite <- HeqLw, app_comm_cons; apply IHpi2...
- destruct l' ; inversion Heq ; subst ; list_simpl.
  + destruct L ; inversion H0 ; subst.
    list_simpl.
    assert (pi2' := IHpi2 (A :: l0) L eq_refl) ; simpl in pi2'.
    rewrite <- (app_nil_l _) in pi2'.
    apply (IHcut _ _ _ pi1 pi2').
  + apply de_r.
    rewrite app_comm_cons in IHpi2 ; rewrite app_comm_cons ; apply IHpi2...
- destruct l' ; inversion Heq ; subst ; list_simpl.
  + destruct L ; inversion H0 ; subst.
    list_simpl.
    apply wk_list_r.
    apply IHpi2...
  + apply wk_r.
    apply IHpi2...
- destruct l' ; inversion Heq ; subst ; list_simpl.
  + destruct L ; inversion H0 ; subst.
    list_simpl.
    apply co_list_r.
    replace (map wn lw ++ map wn lw ++ l0 ++ flat_map (app (map wn lw)) L)
       with (nil ++ flat_map (app (map wn lw)) ((nil :: nil) ++ (l0 :: nil) ++ L))
     by (rewrite flat_map_app ; list_simpl ; reflexivity).
    apply IHpi2...
  + apply co_r.
    rewrite 2 app_comm_cons in IHpi2 ; rewrite 2 app_comm_cons ; apply IHpi2...
- rewrite f in P_cutfree ; inversion P_cutfree.
- destruct L ; list_simpl in Heq ; subst.
  + list_simpl ; apply gax_r.
  + exfalso.
    specialize P_gax_at with a ; rewrite Heq in P_gax_at.
    apply Forall_app in P_gax_at as [_ Hat].
    inversion Hat; inversion H1.
Qed.


Hypothesis P_gax_cut : forall a b x l1 l2 l3 l4,
  projT2 (pgax P) a = (l1 ++ dual x :: l2) -> projT2 (pgax P) b = (l3 ++ x :: l4) ->
  { c | projT2 (pgax P) c = l3 ++ l2 ++ l1 ++ l4 }.

Theorem cut_r_gaxat : forall A l1 l2,
  ll P (dual A :: l1) -> ll P (A :: l2) -> ll P (l2 ++ l1).
Proof with myeasy_perm_Type.
case_eq (pcut P) ; intros P_cutfree.
{ intros A l1 l2 pi1 pi2 ; eapply cut_r... }
enough (forall c s A l0 l1 l2 (pi1 : ll P (dual A :: l0)) (pi2 : ll P (l1 ++ A :: l2)),
          s = psize pi1 + psize pi2 -> fsize A <= c -> ll P (l1 ++ l0 ++ l2)) as IH.
{ intros A l1 l2 pi1 pi2.
  rewrite <- (app_nil_l _) in pi2.
  apply (ex_r _ (nil ++ l1 ++ l2))...
  refine (IH _ _ A _ _ _ pi1 pi2 _ _)... }
induction c as [c IHcut0] using lt_wf_rect.
assert (forall A, fsize A < c -> forall l0 l1 l2,
          ll P (dual A :: l0) -> ll P (l1 ++ A :: l2) -> ll P (l1 ++ l0 ++ l2)) as IHcut
  by (intros A Hs l0 l1 l2 pi1 pi2 ; refine (IHcut0 _ _ _ _ _ _ _ pi1 pi2 _ _) ; myeasy_perm_Type) ;
  clear IHcut0.
induction s as [s IHsize0] using lt_wf_rect.
assert (forall A l0 l1 l2 (pi1 : ll P (dual A :: l0)) (pi2 : ll P (l1 ++ A :: l2)),
          psize pi1 + psize pi2 < s -> fsize A <= c -> ll P (l1 ++ l0 ++ l2))
  as IHsize by (intros ; eapply IHsize0 ; myeasy_perm_Type) ; clear IHsize0.
intros A l0 l1 l2 pi1 pi2 Heqs Hc.
rewrite_all Heqs ; clear s Heqs.
remember (l1 ++ A :: l2) as l ; destruct_ll pi2 f X l Hl Hr HP a.
- (* ax_r *)
  destruct l1 ; inversion Heql ; subst.
  + eapply ex_r...
  + unit_vs_elt_inv H1 ; list_simpl...
- (* ex_r *)
  simpl in IHsize.
  destruct (PCPermutation_Type_vs_elt_inv _ _ _ _ _ HP) as [[p1 p2] HP' Heq] ; simpl in Heq ; simpl in HP' ; subst.
  apply (PEPermutation_Type_app_head _ l0) in HP'.
  eapply ex_r ; [ refine (IHsize _ _ _ _ pi1 Hl _ _) | ]...
  apply PEPermutation_PCPermutation_Type in HP' ; unfold id in HP' ; simpl in HP'.
  symmetry in HP' ; etransitivity ; [ | etransitivity ; [ apply HP' | ] ]...
- (* ex_wn_r *)
  symmetry in Heql ; trichot_elt_app_inf_exec Heql ; list_simpl ; subst.
  + rewrite 2 app_assoc ; eapply ex_wn_r ; [ | apply HP ] ; rewrite <- 2 app_assoc.
    revert Hl IHsize ; list_simpl ; intros Hl IHsize.
    refine (IHsize _ _ _ _ pi1 Hl _ _)...
  + destruct Heql1 as [Heql1 Heql2] ; subst.
    simpl in Heql1; symmetry in Heql1; decomp_map_inf Heql1 ; subst ; simpl in HP ; simpl in pi1 ; simpl.
    rewrite app_assoc ; rewrite <- (app_nil_l (map wn l7 ++ l3)).
    simpl in IHsize.
    destruct (Permutation_Type_vs_elt_inv _ _ _ HP) as [[lw1 lw2] Heq] ; simpl in Heq ; subst.
    revert Hl IHsize ; list_simpl ; rewrite (app_assoc l) ; intros Hl IHsize.
    rewrite app_assoc ; rewrite <- (app_nil_l (map wn l7 ++ l3)).
    refine (cut_oc_comm _ (psize pi1) x _ _ _ _ _ _ _ _)...
    * list_simpl ; replace (map wn l2 ++ wn x :: map wn l7 ++ l3)
                      with (map wn (l2 ++ x :: l7) ++ l3) by (list_simpl ; reflexivity).
      eapply ex_wn_r...
      list_simpl ; rewrite app_assoc...
    * intros lw pi0 Hs.
      list_simpl.
      apply Permutation_Type_app_inv in HP.
      list_simpl in HP ; apply (Permutation_Type_app_middle lw) in HP.
      rewrite (app_assoc (map wn l2)) ; rewrite (app_assoc _ _ l3) ; rewrite <- (app_assoc (map wn l2)).
      rewrite <- 2 map_app.
      eapply ex_wn_r...
      list_simpl ; rewrite app_assoc.
      remember (oc_r _ _ _ pi0) as pi0'.
      change (oc (dual x)) with (dual (wn x)) in pi0'.
      refine (IHsize _ _ _ _ pi0' Hl _ _) ; subst ; simpl...
  + rewrite <- 2 app_assoc.
    eapply ex_wn_r ; [ | apply HP ].
    rewrite (app_assoc (map wn lw)) ; rewrite (app_assoc l).
    revert Hl IHsize ; simpl ; rewrite (app_assoc (map wn lw) l5 _) ; rewrite (app_assoc l) ; intros Hl IHsize.
    refine (IHsize _ _ _ _ pi1 Hl _ _)...
- (* mix0_r *)
  destruct l1 ; inversion Heql.
- (* mix2_r *)
  dichot_elt_app_inf_exec Heql ; subst.
  + rewrite 2 app_assoc ; apply mix2_r...
    rewrite <- app_assoc ; refine (IHsize _ _ _ _ pi1 Hr _ _) ; simpl...
  + list_simpl ; apply mix2_r...
    refine (IHsize _ _ _ _ pi1 Hl _ _) ; simpl...
- (* one_r *)
  unit_vs_elt_inv Heql ; list_simpl...
  remember (one_r _) as Hone ; clear HeqHone.
  remember (dual one :: l0) as l' ; destruct_ll pi1 f X l Hl2 Hr2 HP a ; try inversion Heql' ;
    simpl in IHsize.
  + (* ex_r *)
    destruct (PCPermutation_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] HP' Heq] ; simpl in Heq ; simpl in HP' ; subst.
    apply PEPermutation_PCPermutation_Type in HP' ; unfold id in HP' ; simpl in HP'.
    eapply ex_r ; [ | etransitivity ; [ apply PCPermutation_Type_app_comm | symmetry ; apply HP' ] ].
    revert Hone IHsize ; change one with (dual bot) ; intros Hone IHsize.
    refine (IHsize _ _ _ _ Hone Hl2 _ _)...
  + (* ex_wn_r *)
    destruct l ; inversion Heql' ; [ destruct lw' ; inversion Heql' | ] ; subst.
    * assert (lw = nil) by (clear - HP ; symmetry in HP ; apply (Permutation_Type_nil HP)) ; subst.
      list_simpl in Heql' ; subst ; list_simpl in Hl2.
      revert Hl2 IHsize ; simpl ; change bot with (dual one) ; intros Hl2 IHsize.
      revert Hone IHsize ; rewrite <- (app_nil_l (one :: _)) ; intros Hone IHsize.
      replace l0 with (nil ++ l0 ++ nil) by (list_simpl ; reflexivity).
      refine (IHsize _ _ _ _ Hl2 Hone _ _)...
    * eapply ex_wn_r ; [ | apply HP ].
      revert Hl2 IHsize ; simpl ; change bot with (dual one) ; intros Hl2 IHsize.
      revert Hone IHsize ; rewrite <- (app_nil_l (one :: _)) ; intros Hone IHsize.
      replace (l ++ map wn lw ++ l2) with (nil ++ (l ++ map wn lw ++ l2) ++ nil) by (list_simpl ; reflexivity).
      refine (IHsize _ _ _ _ Hl2 Hone _ _)...
  + (* mix2_r *)
    destruct l2 ; inversion H0 ; list_simpl in H0 ; subst.
    * revert Hl2 IHsize ; change bot with (dual one) ; intros Hl2 IHsize.
      revert Hone IHsize ; rewrite <- (app_nil_l (one :: nil)) ; intros Hone IHsize.
      replace l0 with (nil ++ l0 ++ nil) by (list_simpl ; reflexivity).
      refine (IHsize _ _ _ _ Hl2 Hone _ _)...
    * apply mix2_r...
      revert Hr2 IHsize ; change bot with (dual one) ; intros Hr2 IHsize.
      revert Hone IHsize ; rewrite <- (app_nil_l (one :: nil)) ; intros Hone IHsize.
      replace l2 with (nil ++ l2 ++ nil) by (list_simpl ; reflexivity).
      refine (IHsize _ _ _ _ Hr2 Hone _ _)...
  + (* bot_r *)
    inversion Heql' ; subst...
  + (* cut_r *)
    rewrite f in P_cutfree ; inversion P_cutfree.
  + (* gax_r *)
    exfalso.
    assert (Hat := P_gax_at a) ; rewrite H0 in Hat ; inversion Hat.
    inversion H2.
- (* bot_r *)
  destruct l1 ; inversion Heql ; subst ; list_simpl.
  + (* main case *)
    remember (bot_r _ _ Hl) as Hbot ; clear HeqHbot.
    remember (dual bot :: l0) as l' ; destruct_ll pi1 f X l Hl2 Hr2 HP a ; try inversion Heql' ;
      simpl in IHsize.
    * (* ex_r *)
      destruct (PCPermutation_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] HP' Heq] ; simpl in Heq ; simpl in HP' ; subst.
      apply (PEPermutation_Type_app_tail _ _ _ l2) in HP'.
      apply PEPermutation_PCPermutation_Type in HP' ; unfold id in HP' ; list_simpl in HP'.
      eapply ex_r ; [ | symmetry ; apply HP' ].
      eapply ex_r ; [ | symmetry ; apply PCPermutation_Type_app_rot ].
      revert Hbot IHsize ; change bot with (dual one) ; intros Hbot IHsize.
      refine (IHsize _ _ _ _ Hbot Hl2 _ _)...
    * (* ex_wn_r *)
      destruct l ; inversion Heql' ; [ destruct lw' ; inversion Heql' | ] ; subst.
      -- assert (lw = nil) by (clear - HP ; symmetry in HP ; apply (Permutation_Type_nil HP)) ; subst.
         list_simpl in Heql' ; subst ; list_simpl in Hl2.
         revert Hl2 IHsize ; simpl ; change one with (dual bot) ; intros Hl2 IHsize.
         revert Hbot IHsize ; rewrite <- (app_nil_l (bot :: _)) ; intros Hbot IHsize.
         refine (IHsize _ _ _ _ Hl2 Hbot _ _)...
      -- list_simpl ; eapply ex_wn_r ; [ | apply HP ] ; rewrite 2 app_assoc ; rewrite <- (app_assoc l).
         revert Hl2 IHsize ; simpl ; change one with (dual bot) ; intros Hl2 IHsize.
         revert Hbot IHsize ; rewrite <- (app_nil_l (bot :: _)) ; intros Hbot IHsize.
         refine (IHsize _ _ _ _ Hl2 Hbot _ _)...
    * (* mix2_r *)
      destruct l3 ; inversion H0 ; list_simpl in H0 ; subst ; list_simpl.
      -- revert Hl2 IHsize ; change one with (dual bot) ; intros Hl2 IHsize.
         revert Hbot IHsize ; rewrite <- (app_nil_l (bot :: _)) ; intros Hbot IHsize.
         refine (IHsize _ _ _ _ Hl2 Hbot _ _)...
      -- eapply ex_r ; [ | apply PCPermutation_Type_app_rot ].
         rewrite app_assoc ; apply mix2_r...
         eapply ex_r ; [ | apply PCPermutation_Type_app_comm ].
         revert Hr2 IHsize ; change one with (dual bot) ; intros Hr2 IHsize.
         revert Hbot IHsize ; rewrite <- (app_nil_l (bot :: _)) ; intros Hbot IHsize.
         refine (IHsize _ _ _ _ Hr2 Hbot _ _)...
    * (* one_r *)
      list_simpl...
    * (* cut_r *)
      rewrite f in P_cutfree ; inversion P_cutfree.
    * (* gax_r *)
      exfalso.
      assert (Hat := P_gax_at a) ; rewrite H0 in Hat ; inversion Hat.
      inversion H2.
  + (* commutative case *)
    apply bot_r.
    refine (IHsize _ _ _ _ pi1 Hl _ _) ; simpl...
- (* tens_r *)
  destruct l1 ; inversion Heql ; subst ; list_simpl.
  + (* main case *)
    remember (dual (tens A0 B) :: l0) as l' ; destruct_ll pi1 f X l Hl2 Hr2 HP a ; try inversion Heql'.
    * (* ex_r *)
      remember (tens_r _ _ _ _ _ Hl Hr) as Htens ; clear HeqHtens.
      destruct (PCPermutation_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] HP' Heq] ; simpl in Heq ; simpl in HP' ; subst.
      apply (PEPermutation_Type_app_tail _ _ _ (l4 ++ l3)) in HP'.
      apply PEPermutation_PCPermutation_Type in HP' ; unfold id in HP' ; list_simpl in HP'.
      eapply ex_r ; [ | symmetry ; apply HP' ].
      eapply ex_r ; [ | symmetry ; apply PCPermutation_Type_app_rot ].
      revert Htens IHsize ; simpl ;
        replace (tens A0 B) with (dual (parr (dual B) (dual A0)))
          by (simpl ; rewrite 2 bidual ; reflexivity) ;
        intros Htens IHsize.
      refine (IHsize _ _ _ _ Htens Hl2 _ _)...
      simpl in Hc ; simpl ; rewrite 2 fsize_dual...
    * (* ex_wn_r *)
      remember (tens_r _ _ _ _ _ Hl Hr) as Htens ; clear HeqHtens.
      destruct l ; inversion Heql' ; [ destruct lw' ; inversion Heql' | ] ; subst.
      -- assert (lw = nil) by (clear - HP ; symmetry in HP ; apply (Permutation_Type_nil HP)) ; subst.
         list_simpl in Heql' ; subst ; list_simpl in Hl2.
         revert Hl2 IHsize ; simpl ; change (parr (dual B) (dual A0)) with (dual (tens A0 B)) ;
           intros Hl2 IHsize.
         revert Htens IHsize ; rewrite <- (app_nil_l (tens _ _ :: _)) ; intros Htens IHsize.
         refine (IHsize _ _ _ _ Hl2 Htens _ _)...
      -- list_simpl ; eapply ex_wn_r ; [ | apply HP ] ; rewrite 2 app_assoc ; rewrite <- (app_assoc l).
         revert Hl2 IHsize ; simpl ; change (parr (dual B) (dual A0)) with (dual (tens A0 B)) ;
           intros Hl2 IHsize.
         revert Htens IHsize ; rewrite <- (app_nil_l (tens _ _ :: _)) ; intros Htens IHsize.
         refine (IHsize _ _ _ _ Hl2 Htens _ _)...
    * (* mix2_r *)
      remember (tens_r _ _ _ _ _ Hl Hr) as Htens ; clear HeqHtens.
      destruct l2 ; inversion H0 ; list_simpl in H0 ; subst ; list_simpl.
      -- revert Hl2 IHsize ; simpl ; change (parr (dual B) (dual A0)) with (dual (tens A0 B)) ;
           intros Hl2 IHsize.
         revert Htens IHsize ; rewrite <- (app_nil_l (tens _ _ :: _)) ; intros Htens IHsize.
         refine (IHsize _ _ _ _ Hl2 Htens _ _)...
      -- eapply ex_r ; [ | apply PCPermutation_Type_app_rot ].
         rewrite app_assoc ; apply mix2_r...
         eapply ex_r ; [ | apply PCPermutation_Type_app_comm ].
         revert Hr2 IHsize ; simpl ; change (parr (dual B) (dual A0)) with (dual (tens A0 B)) ;
           intros Hr2 IHsize.
         revert Htens IHsize ; rewrite <- (app_nil_l (tens _ _ :: _)) ; intros Htens IHsize.
         refine (IHsize _ _ _ _ Hr2 Htens _ _)...
    * (* parr_r *)
      clear IHsize ; subst.
      rewrite <- (app_nil_l (A0 :: _)) in Hl ; simpl in Hc ; list_simpl.
      rewrite <- (bidual B) in Hr.
      refine (IHcut _ _ _ _ _ Hr _)...
      -- rewrite fsize_dual...
      -- eapply ex_r ; [ | apply PCPermutation_Type_app_comm ].
         list_simpl in Hl ; rewrite <- (bidual A0) in Hl.
         change ((dual B :: l3) ++ l0) with ((dual B :: nil) ++ l3 ++ l0).
         refine (IHcut _ _ _ _ _ Hl _)...
         rewrite fsize_dual...
    * (* cut_r *)
      rewrite f in P_cutfree ; inversion P_cutfree.
    * (* gax_r *)
      exfalso.
      assert (Hat := P_gax_at a) ; rewrite H0 in Hat ; inversion Hat.
      inversion H2.
  + (* commutative case *)
    dichot_elt_app_inf_exec H1; subst.
    * rewrite 2 app_assoc ; apply tens_r...
      revert Hr IHsize ; simpl ; rewrite (app_comm_cons _ _ B) ; intros Hr IHsize.
      rewrite <- app_assoc ; refine (IHsize _ _ _ _ pi1 Hr _ _) ; simpl...
    * list_simpl ; apply tens_r...
      revert Hl IHsize ; simpl ; rewrite (app_comm_cons _ _ A0) ; intros Hl IHsize.
      refine (IHsize _ _ _ _ pi1 Hl _ _) ; simpl...
- (* parr_r *)
  destruct l1 ; inversion Heql ; subst ; list_simpl.
  + (* main case *)
    remember (dual (parr A0 B) :: l0) as l' ; destruct_ll pi1 f X l Hl2 Hr2 HP a ; try inversion Heql'.
    * (* ex_r *)
      remember (parr_r _ _ _ _ Hl) as Hparr ; clear HeqHparr.
      destruct (PCPermutation_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] HP' Heq] ; simpl in Heq ; simpl in HP' ; subst.
      apply (PEPermutation_Type_app_tail _ _ _ l2) in HP'.
      apply PEPermutation_PCPermutation_Type in HP' ; unfold id in HP' ; list_simpl in HP'.
      eapply ex_r ; [ | symmetry ; apply HP' ].
      eapply ex_r ; [ | symmetry ; apply PCPermutation_Type_app_rot ].
      revert Hparr IHsize ; simpl ;
        replace (parr A0 B) with (dual (tens (dual B) (dual A0)))
          by (simpl ; rewrite 2 bidual ; reflexivity) ;
        intros Hparr IHsize.
      refine (IHsize _ _ _ _ Hparr Hl2 _ _)...
      simpl in Hc ; simpl ; rewrite 2 fsize_dual...
    * (* ex_wn_r *)
      remember (parr_r _ _ _ _ Hl) as Hparr ; clear HeqHparr.
      destruct l ; inversion Heql' ; [ destruct lw' ; inversion Heql' | ] ; subst.
      -- assert (lw = nil) by (clear - HP ; symmetry in HP ; apply (Permutation_Type_nil HP)) ; subst.
         list_simpl in Heql' ; subst ; list_simpl in Hl2.
         revert Hl2 IHsize ; simpl ; change (tens (dual B) (dual A0)) with (dual (parr A0 B)) ;
           intros Hl2 IHsize.
         revert Hparr IHsize ; rewrite <- (app_nil_l (parr _ _ :: _)) ; intros Hparr IHsize.
         refine (IHsize _ _ _ _ Hl2 Hparr _ _)...
      -- list_simpl ; eapply ex_wn_r ; [ | apply HP ] ; rewrite 2 app_assoc ; rewrite <- (app_assoc l).
         revert Hl2 IHsize ; simpl ; change (tens (dual B) (dual A0)) with (dual (parr A0 B)) ;
           intros Hl2 IHsize.
         revert Hparr IHsize ; rewrite <- (app_nil_l (parr _ _ :: _)) ; intros Hparr IHsize.
         refine (IHsize _ _ _ _ Hl2 Hparr _ _)...
    * (* mix2_r *)
      remember (parr_r _ _ _ _ Hl) as Hparr ; clear HeqHparr.
      destruct l3 ; inversion H0 ; list_simpl in H0 ; subst ; list_simpl.
      -- revert Hl2 IHsize ; simpl ; change (tens (dual B) (dual A0)) with (dual (parr A0 B)) ;
           intros Hl2 IHsize.
         revert Hparr IHsize ; rewrite <- (app_nil_l (parr _ _ :: _)) ; intros Hparr IHsize.
         refine (IHsize _ _ _ _ Hl2 Hparr _ _)...
      -- eapply ex_r ; [ | apply PCPermutation_Type_app_rot ].
         rewrite app_assoc ; apply mix2_r...
         eapply ex_r ; [ | apply PCPermutation_Type_app_comm ].
         revert Hr2 IHsize ; simpl ; change (tens (dual B) (dual A0)) with (dual (parr A0 B)) ;
           intros Hr2 IHsize.
         revert Hparr IHsize ; rewrite <- (app_nil_l (parr _ _ :: _)) ; intros Hparr IHsize.
         refine (IHsize _ _ _ _ Hr2 Hparr _ _)...
    * (* tens_r *)
      clear IHsize ; subst.
      rewrite <- (app_nil_l (A0 :: _)) in Hl ; simpl in Hc ; list_simpl.
      refine (IHcut _ _ _ _ _ Hl2 _)...
      rewrite <- (app_nil_l _) ; refine (IHcut _ _ _ _ _ Hr2 _)...
    * (* cut_r *)
      rewrite f in P_cutfree ; inversion P_cutfree.
    * (* gax_r *)
      exfalso.
      assert (Hat := P_gax_at a) ; rewrite H0 in Hat ; inversion Hat.
      inversion H2.
  + (* commutative case *)
    apply parr_r.
    revert Hl IHsize ; simpl ; rewrite (app_comm_cons l1 _ B) ; rewrite (app_comm_cons _ _ A0) ;
      intros Hl IHsize.
    refine (IHsize _ _ _ _ pi1 Hl _ _) ; simpl...
- (* top_r *)
  destruct l1 ; inversion Heql ; subst ; list_simpl.
  + (* main case *)
    remember (dual top :: l0) as l' ; destruct_ll pi1 f X l Hl2 Hr2 HP a ; try inversion Heql'.
    * (* ex_r *)
      remember (top_r _ l2) as Htop ; clear HeqHtop.
      destruct (PCPermutation_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] HP' Heq] ; simpl in Heq ; simpl in HP' ; subst.
      apply (PEPermutation_Type_app_tail _ _ _ l2) in HP'.
      apply PEPermutation_PCPermutation_Type in HP' ; unfold id in HP' ; list_simpl in HP'.
      eapply ex_r ; [ | symmetry ; apply HP' ].
      eapply ex_r ; [ | symmetry ; apply PCPermutation_Type_app_rot ].
      revert Htop IHsize ; simpl ; change top with (dual zero) ; intros Hplus IHsize.
      refine (IHsize _ _ _ _ Hplus Hl2 _ _)...
    * (* ex_wn_r *)
      remember (top_r _ l2) as Htop ; clear HeqHtop.
      destruct l ; inversion Heql' ; [ destruct lw' ; inversion Heql' | ] ; subst.
      -- assert (lw = nil) by (clear - HP ; symmetry in HP ; apply (Permutation_Type_nil HP)) ; subst.
         list_simpl in Heql' ; subst ; list_simpl in Hl2.
         revert Hl2 IHsize ; simpl ; change zero with (dual top) ; intros Hl2 IHsize.
         revert Htop IHsize ; rewrite <- (app_nil_l (top :: _)) ; intros Htop IHsize.
         refine (IHsize _ _ _ _ Hl2 Htop _ _)...
      -- list_simpl ; eapply ex_wn_r ; [ | apply HP ] ; rewrite 2 app_assoc ; rewrite <- (app_assoc l).
         revert Hl2 IHsize ; simpl ; change zero with (dual top) ; intros Hl2 IHsize.
         revert Htop IHsize ; rewrite <- (app_nil_l (top :: _)) ; intros Htop IHsize.
         refine (IHsize _ _ _ _ Hl2 Htop _ _)...
    * (* mix2_r *)
      remember (top_r _ l2) as Htop ; clear HeqHtop.
      destruct l3 ; inversion H0 ; list_simpl in H0 ; subst ; list_simpl.
      -- revert Hl2 IHsize ; simpl ; change zero with (dual top) ; intros Hl2 IHsize.
         revert Htop IHsize ; rewrite <- (app_nil_l (top :: _)) ; intros Htop IHsize.
         refine (IHsize _ _ _ _ Hl2 Htop _ _)...
      -- eapply ex_r ; [ | apply PCPermutation_Type_app_rot ].
         rewrite app_assoc ; apply mix2_r...
         eapply ex_r ; [ | apply PCPermutation_Type_app_comm ].
         revert Hr2 IHsize ; simpl ; change zero with (dual top) ; intros Hr2 IHsize.
         revert Htop IHsize ; rewrite <- (app_nil_l (top :: _)) ; intros Htop IHsize.
         refine (IHsize _ _ _ _ Hr2 Htop _ _)...
    * (* cut_r *)
      rewrite f in P_cutfree ; inversion P_cutfree.
    * (* gax_r *)
      exfalso.
      assert (Hat := P_gax_at a) ; rewrite H0 in Hat ; inversion Hat.
      inversion H2.
  + (* commutative case *)
    apply top_r.
- (* plus_r1 *)
  destruct l1 ; inversion Heql ; subst ; list_simpl.
  + (* main case *)
    remember (dual (aplus A0 B) :: l0) as l' ; destruct_ll pi1 f X l Hl2 Hr2 HP a ; try inversion Heql'.
    * (* ex_r *)
      remember (plus_r1 _ _ _ _ Hl) as Hplus ; clear HeqHplus.
      destruct (PCPermutation_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] HP' Heq] ; simpl in Heq ; simpl in HP' ; subst.
      apply (PEPermutation_Type_app_tail _ _ _ l2) in HP'.
      apply PEPermutation_PCPermutation_Type in HP' ; unfold id in HP' ; list_simpl in HP'.
      eapply ex_r ; [ | symmetry ; apply HP' ].
      eapply ex_r ; [ | symmetry ; apply PCPermutation_Type_app_rot ].
      revert Hplus IHsize ; simpl ;
        replace (aplus A0 B) with (dual (awith (dual A0) (dual B)))
          by (simpl ; rewrite 2 bidual ; reflexivity) ;
        intros Hplus IHsize.
      refine (IHsize _ _ _ _ Hplus Hl2 _ _)...
      simpl ; rewrite 2 fsize_dual...
    * (* ex_wn_r *)
      remember (plus_r1 _ _ _ _ Hl) as Hplus ; clear HeqHplus.
      destruct l ; inversion Heql' ; [ destruct lw' ; inversion Heql' | ] ; subst.
      -- assert (lw = nil) by (clear - HP ; symmetry in HP ; apply (Permutation_Type_nil HP)) ; subst.
         list_simpl in Heql' ; subst ; list_simpl in Hl2.
         revert Hl2 IHsize ; simpl ; change (awith (dual A0) (dual B)) with (dual (aplus A0 B)) ;
           intros Hl2 IHsize.
         revert Hplus IHsize ; rewrite <- (app_nil_l (aplus _ _ :: _)) ; intros Hplus IHsize.
         refine (IHsize _ _ _ _ Hl2 Hplus _ _)...
      -- list_simpl ; eapply ex_wn_r ; [ | apply HP ] ; rewrite 2 app_assoc ; rewrite <- (app_assoc l).
         revert Hl2 IHsize ; simpl ; change (awith (dual A0) (dual B)) with (dual (aplus A0 B)) ;
           intros Hl2 IHsize.
         revert Hplus IHsize ; rewrite <- (app_nil_l (aplus _ _ :: _)) ; intros Hplus IHsize.
         refine (IHsize _ _ _ _ Hl2 Hplus _ _)...
    * (* mix2_r *)
      remember (plus_r1 _ _ _ _ Hl) as Hplus ; clear HeqHplus.
      destruct l3 ; inversion H0 ; list_simpl in H0 ; subst ; list_simpl.
      -- revert Hl2 IHsize ; simpl ; change (awith (dual A0) (dual B)) with (dual (aplus A0 B)) ;
           intros Hl2 IHsize.
         revert Hplus IHsize ; rewrite <- (app_nil_l (aplus _ _ :: _)) ; intros Hplus IHsize.
         refine (IHsize _ _ _ _ Hl2 Hplus _ _)...
      -- eapply ex_r ; [ | apply PCPermutation_Type_app_rot ].
         rewrite app_assoc ; apply mix2_r...
         eapply ex_r ; [ | apply PCPermutation_Type_app_comm ].
         revert Hr2 IHsize ; simpl ; change (awith (dual A0) (dual B)) with (dual (aplus A0 B)) ;
           intros Hr2 IHsize.
         revert Hplus IHsize ; rewrite <- (app_nil_l (aplus _ _ :: _)) ; intros Hplus IHsize.
         refine (IHsize _ _ _ _ Hr2 Hplus _ _)...
    * (* with_r *)
      clear IHsize ; subst.
      rewrite <- (app_nil_l (A0 :: _)) in Hl ; simpl in Hc ; refine (IHcut _ _ _ _ _ Hl2 Hl)...
    * (* cut_r *)
      rewrite f in P_cutfree ; inversion P_cutfree.
    * (* gax_r *)
      exfalso.
      assert (Hat := P_gax_at a) ; rewrite H0 in Hat ; inversion Hat.
      inversion H2.
  + (* commutative case *)
    apply plus_r1.
    revert Hl IHsize ; simpl ; rewrite (app_comm_cons l1 _ A0) ; intros Hl IHsize.
    refine (IHsize _ _ _ _ pi1 Hl _ _) ; simpl...
- (* plus_r2 *)
  destruct l1 ; inversion Heql ; subst ; list_simpl.
  + (* main case *)
    remember (dual (aplus B A0) :: l0) as l' ; destruct_ll pi1 f X l Hl2 Hr2 HP a ; try inversion Heql'.
    * (* ex_r *)
      remember (plus_r2 _ _ _ _ Hl) as Hplus ; clear HeqHplus.
      destruct (PCPermutation_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] HP' Heq] ; simpl in Heq ; simpl in HP' ; subst.
      apply (PEPermutation_Type_app_tail _ _ _ l2) in HP'.
      apply PEPermutation_PCPermutation_Type in HP' ; unfold id in HP' ; list_simpl in HP'.
      eapply ex_r ; [ | symmetry ; apply HP' ].
      eapply ex_r ; [ | symmetry ; apply PCPermutation_Type_app_rot ].
      revert Hplus IHsize ; simpl ;
        replace (aplus B A0) with (dual (awith (dual B) (dual A0)))
          by (simpl ; rewrite 2 bidual ; reflexivity) ;
        intros Hplus IHsize.
      refine (IHsize _ _ _ _ Hplus Hl2 _ _)...
      simpl ; rewrite 2 fsize_dual...
    * (* ex_wn_r *)
      remember (plus_r2 _ _ _ _ Hl) as Hplus ; clear HeqHplus.
      destruct l ; inversion Heql' ; [ destruct lw' ; inversion Heql' | ] ; subst.
      -- assert (lw = nil) by (clear - HP ; symmetry in HP ; apply (Permutation_Type_nil HP)) ; subst.
         list_simpl in Heql' ; subst ; list_simpl in Hl2.
         revert Hl2 IHsize ; simpl ; change (awith (dual B) (dual A0)) with (dual (aplus B A0)) ;
           intros Hl2 IHsize.
         revert Hplus IHsize ; rewrite <- (app_nil_l (aplus _ _ :: _)) ; intros Hplus IHsize.
         refine (IHsize _ _ _ _ Hl2 Hplus _ _)...
      -- list_simpl ; eapply ex_wn_r ; [ | apply HP ] ; rewrite 2 app_assoc ; rewrite <- (app_assoc l).
         revert Hl2 IHsize ; simpl ; change (awith (dual B) (dual A0)) with (dual (aplus B A0)) ;
           intros Hl2 IHsize.
         revert Hplus IHsize ; rewrite <- (app_nil_l (aplus _ _ :: _)) ; intros Hplus IHsize.
         refine (IHsize _ _ _ _ Hl2 Hplus _ _)...
    * (* mix2_r *)
      remember (plus_r2 _ _ _ _ Hl) as Hplus ; clear HeqHplus.
      destruct l3 ; inversion H0 ; list_simpl in H0 ; subst ; list_simpl.
      -- revert Hl2 IHsize ; simpl ; change (awith (dual B) (dual A0)) with (dual (aplus B A0)) ;
           intros Hl2 IHsize.
         revert Hplus IHsize ; rewrite <- (app_nil_l (aplus _ _ :: _)) ; intros Hplus IHsize.
         refine (IHsize _ _ _ _ Hl2 Hplus _ _)...
      -- eapply ex_r ; [ | apply PCPermutation_Type_app_rot ].
         rewrite app_assoc ; apply mix2_r...
         eapply ex_r ; [ | apply PCPermutation_Type_app_comm ].
         revert Hr2 IHsize ; simpl ; change (awith (dual B) (dual A0)) with (dual (aplus B A0)) ;
           intros Hr2 IHsize.
         revert Hplus IHsize ; rewrite <- (app_nil_l (aplus _ _ :: _)) ; intros Hplus IHsize.
         refine (IHsize _ _ _ _ Hr2 Hplus _ _)...
    * (* with_r *)
      clear IHsize ; subst.
      rewrite <- (app_nil_l (A0 :: _)) in Hl ; simpl in Hc ; refine (IHcut _ _ _ _ _ Hr2 Hl)...
    * (* cut_r *)
      rewrite f in P_cutfree ; inversion P_cutfree.
    * (* gax_r *)
      exfalso.
      assert (Hat := P_gax_at a) ; rewrite H0 in Hat ; inversion Hat.
      inversion H2.
  + (* commutative case *)
    apply plus_r2.
    revert Hl IHsize ; simpl ; rewrite (app_comm_cons l1 _ A0) ; intros Hl IHsize.
    refine (IHsize _ _ _ _ pi1 Hl _ _) ; simpl...
- (* with_r *)
  destruct l1 ; inversion Heql ; subst ; list_simpl.
  + (* main case *)
    remember (dual (awith A0 B) :: l0) as l' ; destruct_ll pi1 f X l Hl2 Hr2 HP a ; try inversion Heql'.
    * (* ex_r *)
      remember (with_r _ _ _ _ Hl Hr) as Hwith ; clear HeqHwith.
      destruct (PCPermutation_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] HP' Heq] ; simpl in Heq ; simpl in HP' ; subst.
      apply (PEPermutation_Type_app_tail _ _ _ l2) in HP'.
      apply PEPermutation_PCPermutation_Type in HP' ; unfold id in HP' ; list_simpl in HP'.
      eapply ex_r ; [ | symmetry ; apply HP' ].
      eapply ex_r ; [ | symmetry ; apply PCPermutation_Type_app_rot ].
      revert Hwith IHsize ; simpl ;
        replace (awith A0 B) with (dual (aplus (dual A0) (dual B)))
          by (simpl ; rewrite 2 bidual ; reflexivity) ;
        intros Hwith IHsize.
      refine (IHsize _ _ _ _ Hwith Hl2 _ _)...
      simpl ; rewrite 2 fsize_dual...
    * (* ex_wn_r *)
      remember (with_r _ _ _ _ Hl Hr) as Hwith ; clear HeqHwith.
      destruct l ; inversion Heql' ; [ destruct lw' ; inversion Heql' | ] ; subst.
      -- assert (lw = nil) by (clear - HP ; symmetry in HP ; apply (Permutation_Type_nil HP)) ; subst.
         list_simpl in Heql' ; subst ; list_simpl in Hl2.
         revert Hl2 IHsize ; simpl ; change (aplus (dual A0) (dual B)) with (dual (awith A0 B)) ;
           intros Hl2 IHsize.
         revert Hwith IHsize ; rewrite <- (app_nil_l (awith _ _ :: _)) ; intros Hwith IHsize.
         refine (IHsize _ _ _ _ Hl2 Hwith _ _)...
      -- list_simpl ; eapply ex_wn_r ; [ | apply HP ] ; rewrite 2 app_assoc ; rewrite <- (app_assoc l).
         revert Hl2 IHsize ; simpl ; change (aplus (dual A0) (dual B)) with (dual (awith A0 B)) ;
           intros Hl2 IHsize.
         revert Hwith IHsize ; rewrite <- (app_nil_l (awith _ _ :: _)) ; intros Hwith IHsize.
         refine (IHsize _ _ _ _ Hl2 Hwith _ _)...
    * (* mix2_r *)
      remember (with_r _ _ _ _ Hl Hr) as Hwith ; clear HeqHwith.
      destruct l3 ; inversion H0 ; list_simpl in H0 ; subst ; list_simpl.
      -- revert Hl2 IHsize ; simpl ; change (aplus (dual A0) (dual B)) with (dual (awith A0 B)) ;
           intros Hl2 IHsize.
         revert Hwith IHsize ; rewrite <- (app_nil_l (awith _ _ :: _)) ; intros Hwith IHsize.
         refine (IHsize _ _ _ _ Hl2 Hwith _ _)...
      -- eapply ex_r ; [ | apply PCPermutation_Type_app_rot ].
         rewrite app_assoc ; apply mix2_r...
         eapply ex_r ; [ | apply PCPermutation_Type_app_comm ].
         revert Hr2 IHsize ; simpl ; change (aplus (dual A0) (dual B)) with (dual (awith A0 B)) ;
           intros Hr2 IHsize.
         revert Hwith IHsize ; rewrite <- (app_nil_l (awith _ _ :: _)) ; intros Hwith IHsize.
         refine (IHsize _ _ _ _ Hr2 Hwith _ _)...
    * (* plus_r1 *)
      clear IHsize ; subst.
      rewrite <- (app_nil_l (A0 :: _)) in Hl ; simpl in Hc ; refine (IHcut _ _ _ _ _ Hl2 Hl)...
    * (* plus_r2 *)
      clear IHsize ; subst.
      rewrite <- (app_nil_l (B :: _)) in Hr ; simpl in Hc ; refine (IHcut _ _ _ _ _ Hl2 Hr)...
    * (* cut_r *)
      rewrite f in P_cutfree ; inversion P_cutfree.
    * (* gax_r *)
      exfalso.
      assert (Hat := P_gax_at a) ; rewrite H0 in Hat ; inversion Hat.
      inversion H2.
  + (* commutative case *)
    apply with_r.
    * revert Hl IHsize ; simpl ; rewrite (app_comm_cons l1 _ A0) ; intros Hl IHsize.
      refine (IHsize _ _ _ _ pi1 Hl _ _) ; simpl...
    * revert Hr IHsize ; simpl ; rewrite (app_comm_cons l1 _ B) ; intros Hr IHsize.
      refine (IHsize _ _ _ _ pi1 Hr _ _) ; simpl...
- (* oc_r *)
  destruct l1 ; inversion Heql ; subst ; list_simpl.
  + (* main case *)
    remember (dual (oc A0) :: l0) as l' ; destruct_ll pi1 f X lo Hl2 Hr2 HP a ; try inversion Heql'.
    * (* ex_r *)
      remember (oc_r _ _ _ Hl) as Hoc ; clear HeqHoc.
      destruct (PCPermutation_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] HP' Heq] ; simpl in Heq ; simpl in HP' ; subst.
      apply (PEPermutation_Type_app_tail _ _ _ (map wn l)) in HP'.
      apply PEPermutation_PCPermutation_Type in HP' ; unfold id in HP' ; list_simpl in HP'.
      eapply ex_r ; [ | symmetry ; apply HP' ].
      eapply ex_r ; [ | symmetry ; apply PCPermutation_Type_app_rot ].
      revert Hoc IHsize ; simpl ;
        replace (oc A0) with (dual (wn (dual A0))) by (simpl ; rewrite bidual ; reflexivity) ;
        intros Hoc IHsize.
      refine (IHsize _ _ _ _ Hoc Hl2 _ _)...
      simpl ; rewrite fsize_dual...
    * (* ex_wn_r *)
      remember (oc_r _ _ _ Hl) as Hoc ; clear HeqHoc.
      destruct lo ; inversion H0 ; [ destruct lw' ; inversion H0 | ] ; subst.
      -- assert (lw = nil) by (clear - HP ; symmetry in HP ; apply (Permutation_Type_nil HP)) ; subst.
         list_simpl in Heql' ; subst ; list_simpl in Hl2.
         revert Hl2 IHsize ; simpl ; change (wn (dual A0)) with (dual (oc A0)) ;
           intros Hl2 IHsize.
         revert Hoc IHsize ; rewrite <- (app_nil_l (oc _ :: _)) ; intros Hoc IHsize.
         refine (IHsize _ _ _ _ Hl2 Hoc _ _)...
      -- destruct (Permutation_Type_vs_cons_inv HP) as [[lw1 lw2] Heq] ; simpl in Heq ; subst.
         assert (Permutation_Type (lw1 ++ l ++ lw2) (l ++ lw')) as HP'.
         { rewrite <- (app_nil_l (l ++ lw')).
           apply Permutation_Type_app_middle.
           rewrite <- (app_nil_l lw').
           apply (Permutation_Type_app_inv _ _ _ _ (dual A0))... }
         eapply ex_r ; [ | apply PCPermutation_Type_app_comm ].
         rewrite app_assoc ; rewrite <- map_app ; rewrite <- (app_nil_l _) ; eapply ex_wn_r ; [ | apply HP' ].
         list_simpl.
         revert Hl2 IHsize ; list_simpl ;intros Hl2 IHsize.
         revert Hoc IHsize ; replace (oc A0) with (dual (wn (dual A0)))
                               by (list_simpl ; rewrite bidual ; reflexivity) ; intros Hoc IHsize.
         refine (IHsize _ _ _ _ Hoc Hl2 _ _)...
         simpl ; rewrite fsize_dual...
      -- list_simpl ; eapply ex_wn_r ; [ | apply HP ] ; rewrite 2 app_assoc ; rewrite <- (app_assoc lo).
         revert Hl2 IHsize ; simpl ; change (wn (dual A0)) with (dual (oc A0)) ;
           intros Hl2 IHsize.
         revert Hoc IHsize ; rewrite <- (app_nil_l (oc _ :: _)) ; intros Hoc IHsize.
         refine (IHsize _ _ _ _ Hl2 Hoc _ _)...
    * (* mix2_r *)
      remember (oc_r _ _ _ Hl) as Hoc ; clear HeqHoc.
      destruct l2 ; inversion H0 ; list_simpl in H0 ; subst ; list_simpl.
      -- revert Hl2 IHsize ; simpl ; change (wn (dual A0)) with (dual (oc A0)) ;
           intros Hl2 IHsize.
         revert Hoc IHsize ; rewrite <- (app_nil_l (oc _ :: _)) ; intros Hoc IHsize.
         refine (IHsize _ _ _ _ Hl2 Hoc _ _)...
      -- eapply ex_r ; [ | apply PCPermutation_Type_app_rot ].
         rewrite app_assoc ; apply mix2_r...
         eapply ex_r ; [ | apply PCPermutation_Type_app_comm ].
         revert Hr2 IHsize ; simpl ; change (wn (dual A0)) with (dual (oc A0)) ;
           intros Hr2 IHsize.
         revert Hoc IHsize ; rewrite <- (app_nil_l (oc _ :: _)) ; intros Hoc IHsize.
         refine (IHsize _ _ _ _ Hr2 Hoc _ _)...
    * (* oc_r *)
      clear IHsize ; subst.
      rewrite <- (app_nil_l (A0 :: _)) in Hl ; simpl in Hc ; refine (IHcut _ _ _ _ _ Hl2 Hl)...
    * (* wk_r *)
      clear IHsize ; subst.
      eapply ex_r ; [ | apply PCPermutation_Type_app_comm ].
      apply wk_list_r...
    * (* co_r *)
      clear IHsize ; subst.
      eapply ex_r ; [ | apply PCPermutation_Type_app_comm ].
      apply co_list_r.
      replace (map wn l ++ map wn l ++ l0)
         with (nil ++ flat_map (app (map wn l)) (nil :: nil ++ l0 :: nil))
        by (list_simpl ; reflexivity).
      rewrite <- (bidual A0) in Hl.
      refine (substitution_oc _ (dual A0) _ _ _ _ _ _ _ eq_refl) ; list_simpl...
      intros l1 l2 l3 pi1 pi2 ; eapply (IHcut (dual A0))...
      rewrite fsize_dual ; simpl...
    * (* cut_r *)
      rewrite f in P_cutfree ; inversion P_cutfree.
    * (* gax_r *)
      exfalso.
      assert (Hat := P_gax_at a) ; rewrite H0 in Hat ; inversion Hat.
      inversion H2.
  + (* commutative case *)
    decomp_map_inf H1; subst; simpl in pi1, Hl; simpl.
    rewrite app_comm_cons ; rewrite <- (app_nil_l (map wn l6)).
    refine (cut_oc_comm _ (psize pi1) x _ _ _ _ _ _ _ _)...
    * list_simpl ; replace (map wn l4 ++ wn x :: map wn l6)
                      with (map wn (l4 ++ x :: l6)) by (list_simpl ; reflexivity).
      apply oc_r...
    * intros lw pi0 Hs.
      list_simpl ; replace (map wn l4 ++ map wn lw ++ map wn l6)
                      with (map wn (l4 ++ lw ++ l6)) by (list_simpl ; reflexivity).
      apply oc_r...
      list_simpl ; rewrite app_comm_cons.
      remember (oc_r _ _ _ pi0) as pi0'.
      change (oc (dual x)) with (dual (wn x)) in pi0'.
      revert Hl IHsize ; list_simpl ; rewrite (app_comm_cons _ _ A0) ; intros Hl IHsize.
      refine (IHsize _ _ _ _ pi0' Hl _ _) ; subst ; simpl...
- (* de_r *)
  destruct l1 ; inversion Heql ; subst ; list_simpl.
  + (* main case *)
    remember (dual (wn A0) :: l0) as l' ; destruct_ll pi1 f X l Hl2 Hr2 HP a ; try inversion Heql'.
    * (* ex_r *)
      remember (de_r _ _ _ Hl) as Hde ; clear HeqHde.
      destruct (PCPermutation_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] HP' Heq] ; simpl in Heq ; simpl in HP' ; subst.
      apply (PEPermutation_Type_app_tail _ _ _ l2) in HP'.
      apply PEPermutation_PCPermutation_Type in HP' ; unfold id in HP' ; list_simpl in HP'.
      eapply ex_r ; [ | symmetry ; apply HP' ].
      eapply ex_r ; [ | symmetry ; apply PCPermutation_Type_app_rot ].
      revert Hde IHsize ; simpl ;
        replace (wn A0) with (dual (oc (dual A0))) by (simpl ; rewrite bidual ; reflexivity) ;
        intros Hde IHsize.
      refine (IHsize _ _ _ _ Hde Hl2 _ _)...
      simpl ; rewrite fsize_dual...
    * (* ex_wn_r *)
      remember (de_r _ _ _ Hl) as Hde ; clear HeqHde.
      destruct l ; inversion Heql' ; [ destruct lw' ; inversion Heql' | ] ; subst.
      -- assert (lw = nil) by (clear - HP ; symmetry in HP ; apply (Permutation_Type_nil HP)) ; subst.
         list_simpl in Heql' ; subst ; list_simpl in Hl2.
         revert Hl2 IHsize ; simpl ; change (oc (dual A0)) with (dual (wn A0)) ;
           intros Hl2 IHsize.
         revert Hde IHsize ; rewrite <- (app_nil_l (wn _ :: _)) ; intros Hde IHsize.
         refine (IHsize _ _ _ _ Hl2 Hde _ _)...
      -- list_simpl ; eapply ex_wn_r ; [ | apply HP ] ; rewrite 2 app_assoc ; rewrite <- (app_assoc l).
         revert Hl2 IHsize ; simpl ; change (oc (dual A0)) with (dual (wn A0)) ;
           intros Hl2 IHsize.
         revert Hde IHsize ; rewrite <- (app_nil_l (wn _ :: _)) ; intros Hde IHsize.
         refine (IHsize _ _ _ _ Hl2 Hde _ _)...
    * (* mix2_r *)
      remember (de_r _ _ _ Hl) as Hde ; clear HeqHde.
      destruct l3 ; inversion H0 ; list_simpl in H0 ; subst ; list_simpl.
      -- revert Hl2 IHsize ; simpl ; change (oc (dual A0)) with (dual (wn A0)) ;
           intros Hl2 IHsize.
         revert Hde IHsize ; rewrite <- (app_nil_l (wn _ :: _)) ; intros Hde IHsize.
         refine (IHsize _ _ _ _ Hl2 Hde _ _)...
      -- eapply ex_r ; [ | apply PCPermutation_Type_app_rot ].
         rewrite app_assoc ; apply mix2_r...
         eapply ex_r ; [ | apply PCPermutation_Type_app_comm ].
         revert Hr2 IHsize ; simpl ; change (oc (dual A0)) with (dual (wn A0)) ;
           intros Hr2 IHsize.
         revert Hde IHsize ; rewrite <- (app_nil_l (wn _ :: _)) ; intros Hde IHsize.
         refine (IHsize _ _ _ _ Hr2 Hde _ _)...
    * (* oc_r *)
      clear IHsize ; subst.
      rewrite <- (app_nil_l (A0 :: _)) in Hl ; simpl in Hc ; refine (IHcut _ _ _ _ _ Hl2 Hl)...
    * (* cut_r *)
      rewrite f in P_cutfree ; inversion P_cutfree.
    * (* gax_r *)
      exfalso.
      assert (Hat := P_gax_at a) ; rewrite H0 in Hat ; inversion Hat.
      inversion H2.
  + (* commutative case *)
    apply de_r.
    revert Hl IHsize ; simpl ; rewrite (app_comm_cons l1 _ A0) ; intros Hl IHsize.
    refine (IHsize _ _ _ _ pi1 Hl _ _) ; simpl...
- (* wk_r *)
  destruct l1 ; inversion Heql ; subst ; list_simpl.
  + (* main case *)
    remember (dual (wn A0) :: l0) as l' ; destruct_ll pi1 f X l Hl2 Hr2 HP a ; try inversion Heql'.
    * (* ex_r *)
      remember (wk_r _ A0 _ Hl) as Hwk ; clear HeqHwk.
      destruct (PCPermutation_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] HP' Heq] ; simpl in Heq ; simpl in HP' ; subst.
      apply (PEPermutation_Type_app_tail _ _ _ l2) in HP'.
      apply PEPermutation_PCPermutation_Type in HP' ; unfold id in HP' ; list_simpl in HP'.
      eapply ex_r ; [ | symmetry ; apply HP' ].
      eapply ex_r ; [ | symmetry ; apply PCPermutation_Type_app_rot ].
      revert Hwk IHsize ; simpl ;
        replace (wn A0) with (dual (oc (dual A0))) by (simpl ; rewrite bidual ; reflexivity) ;
        intros Hwk IHsize.
      refine (IHsize _ _ _ _ Hwk Hl2 _ _)...
      simpl ; rewrite fsize_dual...
    * (* ex_wn_r *)
      remember (wk_r _ A0 _ Hl) as Hwk ; clear HeqHwk.
      destruct l ; inversion Heql' ; [ destruct lw' ; inversion Heql' | ] ; subst.
      -- assert (lw = nil) by (clear - HP ; symmetry in HP ; apply (Permutation_Type_nil HP)) ; subst.
         list_simpl in Heql' ; subst ; list_simpl in Hl2.
         revert Hl2 IHsize ; simpl ; change (oc (dual A0)) with (dual (wn A0)) ;
           intros Hl2 IHsize.
         revert Hwk IHsize ; rewrite <- (app_nil_l (wn _ :: _)) ; intros Hwk IHsize.
         refine (IHsize _ _ _ _ Hl2 Hwk _ _)...
      -- list_simpl ; eapply ex_wn_r ; [ | apply HP ] ; rewrite 2 app_assoc ; rewrite <- (app_assoc l).
         revert Hl2 IHsize ; simpl ; change (oc (dual A0)) with (dual (wn A0)) ;
           intros Hl2 IHsize.
         revert Hwk IHsize ; rewrite <- (app_nil_l (wn _ :: _)) ; intros Hwk IHsize.
         refine (IHsize _ _ _ _ Hl2 Hwk _ _)...
    * (* mix2_r *)
      remember (wk_r _ A0 _ Hl) as Hwk ; clear HeqHwk.
      destruct l3 ; inversion H0 ; list_simpl in H0 ; subst ; list_simpl.
      -- revert Hl2 IHsize ; simpl ; change (oc (dual A0)) with (dual (wn A0)) ;
           intros Hl2 IHsize.
         revert Hwk IHsize ; rewrite <- (app_nil_l (wn _ :: _)) ; intros Hwk IHsize.
         refine (IHsize _ _ _ _ Hl2 Hwk _ _)...
      -- eapply ex_r ; [ | apply PCPermutation_Type_app_rot ].
         rewrite app_assoc ; apply mix2_r...
         eapply ex_r ; [ | apply PCPermutation_Type_app_comm ].
         revert Hr2 IHsize ; simpl ; change (oc (dual A0)) with (dual (wn A0)) ;
           intros Hr2 IHsize.
         revert Hwk IHsize ; rewrite <- (app_nil_l (wn _ :: _)) ; intros Hwk IHsize.
         refine (IHsize _ _ _ _ Hr2 Hwk _ _)...
    * (* oc_r *)
      clear IHsize ; subst.
      apply wk_list_r...
    * (* cut_r *)
      rewrite f in P_cutfree ; inversion P_cutfree.
    * (* gax_r *)
      exfalso.
      assert (Hat := P_gax_at a) ; rewrite H0 in Hat ; inversion Hat.
      inversion H2.
  + (* commutative case *)
    apply wk_r.
    refine (IHsize _ _ _ _ pi1 Hl _ _) ; simpl...
- (* co_r *)
  destruct l1 ; inversion Heql ; subst ; list_simpl.
  + (* main case *)
    remember (dual (wn A0) :: l0) as l' ; destruct_ll pi1 f X l Hl2 Hr2 HP a ; try inversion Heql'.
    * (* ex_r *)
      remember (co_r _ _ _ Hl) as Hco ; clear HeqHco.
      destruct (PCPermutation_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] HP' Heq] ; simpl in Heq ; simpl in HP' ; subst.
      apply (PEPermutation_Type_app_tail _ _ _ l2) in HP'.
      apply PEPermutation_PCPermutation_Type in HP' ; unfold id in HP' ; list_simpl in HP'.
      eapply ex_r ; [ | symmetry ; apply HP' ].
      eapply ex_r ; [ | symmetry ; apply PCPermutation_Type_app_rot ].
      revert Hco IHsize ; simpl ;
        replace (wn A0) with (dual (oc (dual A0)))
          by (simpl ; rewrite bidual ; reflexivity) ;
        intros Hco IHsize.
      refine (IHsize _ _ _ _ Hco Hl2 _ _)...
      simpl in Hc ; simpl ; rewrite fsize_dual...
    * (* ex_wn_r *)
      remember (co_r _ _ _ Hl) as Hco ; clear HeqHco.
      destruct l ; inversion Heql' ; [ destruct lw' ; inversion Heql' | ] ; subst.
      -- assert (lw = nil) by (clear - HP ; symmetry in HP ; apply (Permutation_Type_nil HP)) ; subst.
         list_simpl in Heql' ; subst ; list_simpl in Hl2.
         revert Hl2 IHsize ; simpl ; change (oc (dual A0)) with (dual (wn A0)) ;
           intros Hl2 IHsize.
         revert Hco IHsize ; rewrite <- (app_nil_l (wn _ :: _)) ; intros Hco IHsize.
         refine (IHsize _ _ _ _ Hl2 Hco _ _)...
      -- list_simpl ; eapply ex_wn_r ; [ | apply HP ] ; rewrite 2 app_assoc ; rewrite <- (app_assoc l).
         revert Hl2 IHsize ; simpl ; change (oc (dual A0)) with (dual (wn A0)) ;
           intros Hl2 IHsize.
         revert Hco IHsize ; rewrite <- (app_nil_l (wn _ :: _)) ; intros Hco IHsize.
         refine (IHsize _ _ _ _ Hl2 Hco _ _)...
    * (* mix2_r *)
      remember (co_r _ _ _ Hl) as Hco ; clear HeqHco.
      destruct l3 ; inversion H0 ; list_simpl in H0 ; subst ; list_simpl.
      -- revert Hl2 IHsize ; simpl ; change (oc (dual A0)) with (dual (wn A0)) ;
           intros Hl2 IHsize.
         revert Hco IHsize ; rewrite <- (app_nil_l (wn _ :: _)) ; intros Hco IHsize.
         refine (IHsize _ _ _ _ Hl2 Hco _ _)...
      -- eapply ex_r ; [ | apply PCPermutation_Type_app_rot ].
         rewrite app_assoc ; apply mix2_r...
         eapply ex_r ; [ | apply PCPermutation_Type_app_comm ].
         revert Hr2 IHsize ; simpl ; change (oc (dual A0)) with (dual (wn A0)) ;
           intros Hr2 IHsize.
         revert Hco IHsize ; rewrite <- (app_nil_l (wn _ :: _)) ; intros Hco IHsize.
         refine (IHsize _ _ _ _ Hr2 Hco _ _)...
    * (* oc_r *)
      clear IHsize ; subst.
      apply co_list_r.
      replace (map wn l ++ map wn l ++ l2)
         with (nil ++ flat_map (app (map wn l)) (nil :: nil ++ l2 :: nil))
        by (list_simpl ; reflexivity).
      refine (substitution_oc _ A0 _ _ _ _ _ _ _ eq_refl) ; list_simpl...
      intros l1' l2' l3' pi1 pi2 ; eapply (IHcut A0)...
    * (* cut_r *)
      rewrite f in P_cutfree ; inversion P_cutfree.
    * (* gax_r *)
      exfalso.
      assert (Hat := P_gax_at a) ; rewrite H0 in Hat ; inversion Hat.
      inversion H2.
  + (* commutative case *)
    apply co_r.
    revert Hl IHsize ; simpl ; rewrite (app_comm_cons l1 _ (wn A0)) ; rewrite (app_comm_cons _ _ (wn A0)) ;
      intros Hl IHsize.
    refine (IHsize _ _ _ _ pi1 Hl _ _) ; simpl...
- (* cut_r *)
  rewrite f in P_cutfree ; inversion P_cutfree.
- (* gax_r *)
  clear IHcut IHsize Hc.
  specialize P_gax_at with a ; rewrite Heql in P_gax_at.
  assert (atomic A) as Hat
   by now (apply Forall_app in P_gax_at as [_ P_gax_at2]; inversion P_gax_at2).
  remember (dual A :: l0) as l.
  rewrite <- (app_nil_l l2) ; rewrite <- (app_nil_l (dual A :: l0)) in Heql0.
  remember nil as l3 ; clear Heql3.
  revert l3 l0 Heql0 ; induction pi1 ; intros l4 l5 Heq ; subst.
  + destruct l4 ; inversion Heq ; subst.
    * destruct A ; inversion H0 ; subst.
      list_simpl ; rewrite <- Heql ; apply (gax_r _ a).
    * destruct l4 ; inversion H1 ; subst.
      -- destruct A ; inversion H0 ; subst.
         list_simpl ; rewrite <- Heql ; apply (gax_r _ a).
      -- destruct l4 ; inversion H2.
  + apply PCPermutation_Type_vs_elt_inv in p.
    destruct p as [[l4' l5'] Heq p] ; simpl in Heq ; simpl in p ; subst.
    assert (PEPermutation_Type (pperm P) (l1 ++ l5' ++ l4' ++ l2) (l1 ++ l5 ++ l4 ++ l2)) as HP'.
    { apply PEPermutation_Type_app_head.
      rewrite 2 app_assoc ; apply PEPermutation_Type_app_tail.
      symmetry... }
    apply PEPermutation_PCPermutation_Type in HP'.
    apply (ex_r _ (l1 ++ l5' ++ l4' ++ l2))...
    apply IHpi1...
  + symmetry in Heq; trichot_elt_app_inf_exec Heq; subst.
    * list_simpl ; rewrite app_assoc.
      eapply ex_wn_r...
      list_simpl.
      rewrite (app_assoc l) ; rewrite (app_assoc _ l3) ; rewrite <- (app_assoc l).
      apply IHpi1 ; list_simpl...
    * destruct Heq1 as [Heq1 Heq2]; symmetry in Heq1; decomp_map_inf Heq1.
      exfalso ; destruct A ; inversion Heq1 ; subst ; inversion Hat.
    * list_simpl ; rewrite 2 app_assoc.
      eapply ex_wn_r...
      list_simpl ; rewrite (app_assoc l0) ; rewrite (app_assoc _ l6).
      apply IHpi1 ; list_simpl...
  + destruct l4 ; inversion Heq.
  + dichot_elt_app_inf_exec Heq; subst.
    * list_simpl.
      eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
      apply mix2_r...
      eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
      apply IHpi1_2 ; list_simpl...
    * eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
      apply mix2_r...
      eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
      apply IHpi1_1 ; list_simpl...
  + exfalso ; destruct l4 ; inversion Heq.
    * destruct A ; inversion H0 ; subst ; inversion Hat.
    * destruct l4 ; inversion H1.
  + destruct l4 ; inversion Heq ; subst ;
      try (exfalso ; destruct A ; inversion H0 ; subst ; inversion Hat ; fail).
    eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    apply bot_r...
    eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    apply IHpi1 ; list_simpl...
  + destruct l4 ; inversion Heq ; subst ;
      try (exfalso ; destruct A ; inversion H0 ; subst ; inversion Hat ; fail).
    dichot_elt_app_inf_exec H1; subst.
    * list_simpl.
      eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
      rewrite app_comm_cons ; eapply ex_r ; [ | symmetry ; apply PCPermutation_Type_app_rot ] ; list_simpl.
      rewrite 3 app_assoc ; apply tens_r...
      list_simpl ; rewrite app_comm_cons ; eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
      rewrite app_comm_cons ; apply IHpi1_2 ; list_simpl...
    * eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
      apply tens_r...
      list_simpl ; rewrite app_comm_cons ; eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
      rewrite app_comm_cons ; apply IHpi1_1 ; list_simpl...
  + destruct l4 ; inversion Heq ; subst ;
      try (exfalso ; destruct A ; inversion H0 ; subst ; inversion Hat ; fail).
    eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    apply parr_r...
    rewrite 2 app_comm_cons ; eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    rewrite 2 app_comm_cons ; apply IHpi1 ; list_simpl...
  + destruct l4 ; inversion Heq ; subst ;
      try (exfalso ; destruct A ; inversion H0 ; subst ; inversion Hat ; fail).
    eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    apply top_r...
  + destruct l4 ; inversion Heq ; subst ;
      try (exfalso ; destruct A ; inversion H0 ; subst ; inversion Hat ; fail).
    eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    apply plus_r1...
    rewrite app_comm_cons ; eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    rewrite app_comm_cons ; apply IHpi1 ; list_simpl...
  + destruct l4 ; inversion Heq ; subst ;
      try (exfalso ; destruct A ; inversion H0 ; subst ; inversion Hat ; fail).
    eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    apply plus_r2...
    rewrite app_comm_cons ; eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    rewrite app_comm_cons ; apply IHpi1 ; list_simpl...
  + destruct l4 ; inversion Heq ; subst ;
      try (exfalso ; destruct A ; inversion H0 ; subst ; inversion Hat ; fail).
    eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    apply with_r...
    * rewrite app_comm_cons ; eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
      rewrite app_comm_cons ; apply IHpi1_1 ; list_simpl...
    * rewrite app_comm_cons ; eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
      rewrite app_comm_cons ; apply IHpi1_2 ; list_simpl...
  + destruct l4 ; inversion Heq ; subst ;
      try (exfalso ; destruct A ; inversion H0 ; subst ; inversion Hat ; fail).
    exfalso; decomp_map_inf H1; destruct A; inversion H1; subst; inversion Hat.
  + destruct l4 ; inversion Heq ; subst ;
      try (exfalso ; destruct A ; inversion H0 ; subst ; inversion Hat ; fail).
    eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    apply de_r...
    rewrite app_comm_cons ; eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    rewrite app_comm_cons ; apply IHpi1 ; list_simpl...
  + destruct l4 ; inversion Heq ; subst ;
      try (exfalso ; destruct A ; inversion H0 ; subst ; inversion Hat ; fail).
    eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    apply wk_r...
    eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    apply IHpi1 ; list_simpl...
  + destruct l4 ; inversion Heq ; subst ;
      try (exfalso ; destruct A ; inversion H0 ; subst ; inversion Hat ; fail).
    eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    apply co_r...
    rewrite 2 app_comm_cons ; eapply ex_r ; [ | apply PCPermutation_Type_app_rot ] ; list_simpl.
    rewrite 2 app_comm_cons ; apply IHpi1 ; list_simpl...
  + rewrite f in P_cutfree ; inversion P_cutfree.
  + destruct (P_gax_cut a0 a _ _ _ _ _ Heq Heql) as [x Hcut].
    rewrite <- Hcut ; apply (gax_r _ x).
Qed.

End Cut_Elim_Proof.


(** ** Variants on cut admissibility *)

(** If axioms are atomic and closed under cut, then the cut rule is admissible:
provability is preserved if we remove the cut rule. *)
Lemma cut_admissible {P} :
  (forall a, Forall atomic (projT2 (pgax P) a)) ->
  (forall a b x l1 l2 l3 l4,
     projT2 (pgax P) a = (l1 ++ dual x :: l2) -> projT2 (pgax P) b = (l3 ++ x :: l4) ->
     { c | projT2 (pgax P) c = l3 ++ l2 ++ l1 ++ l4 }) ->
  forall l, ll P l -> ll (cutrm_pfrag P) l.
Proof.
intros Hgax_at Hgax_cut l pi.
induction pi ; try (econstructor ; myeeasy ; fail).
- eapply cut_r_gaxat ; eassumption.
- assert (pgax P = pgax (cutrm_pfrag P)) as Hcut by reflexivity.
  revert a ; rewrite Hcut ; apply gax_r.
Qed.

(** If there are no axioms (except the identity rule), then the cut rule is valid. *)
Lemma cut_r_axfree {P} : (projT1 (pgax P) -> False) -> forall A l1 l2, 
  ll P (dual A :: l1) -> ll P (A :: l2) -> ll P (l2 ++ l1).
Proof.
intros P_axfree A l1 l2 pi1 pi2.
eapply cut_r_gaxat ; try eassumption.
all: intros a ; exfalso ; apply (P_axfree a).
Qed.

(** If there are no axioms (except the identity rule), then the cut rule is admissible:
provability is preserved if we remove the cut rule. *)
Lemma cut_admissible_axfree {P} : (projT1 (pgax P) -> False) -> forall l,
  ll P l -> ll (cutrm_pfrag P) l.
Proof.
intros P_axfree l pi.
eapply cut_admissible ; try eassumption.
all: intros a ; exfalso ; apply (P_axfree a).
Qed.
