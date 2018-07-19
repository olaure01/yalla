(* ll_mix library for yalla *)

(** * Results around [mix] rule not requiring cut elimination *)

Require Import List_more.
Require Import List_Type_more.
Require Import Permutation_Type_more.
Require Import Permutation_Type_solve.
Require Import genperm_Type.

Require Import ll_def.


(** ** Results on [mix0] *)

Definition mix0add_pfrag P :=
  mk_pfrag (pcut P) (pgax P) true (pmix2 P) (pperm P).

Lemma mix0_to_ll {P} : pperm P = true -> forall b0 bp l,
  ll (mk_pfrag P.(pcut) P.(pgax) b0 P.(pmix2) bp) l -> ll P (wn one :: l).
Proof with myeeasy ; try PCperm_Type_solve.
intros fp b0 bp l pi.
eapply (ext_wn_param _ P fp _ (one :: nil)) in pi.
- eapply ex_r...
- intros Hcut...
- simpl ; intros a.
  eapply ex_r ; [ | apply PCperm_Type_last ].
  apply wk_r.
  apply gax_r.
- intros.
  eapply de_r.
  eapply one_r.
- intros Hpmix2 Hpmix2'.
  exfalso.
  simpl in Hpmix2.
  rewrite Hpmix2 in Hpmix2'.
  inversion Hpmix2'.
Qed.

Lemma ll_to_mix0 {P} : (forall a, Forall atomic (projT2 (pgax P) a)) ->
  pperm P = true -> forall l,
  ll P (wn one :: l) -> ll (mix0add_pfrag P) l.
Proof with myeeasy ; try PCperm_Type_solve.
intros Hgax Hperm.
enough (forall l, ll P l -> forall l' (l0 l1 : list unit),
  Permutation_Type l (l' ++ map (fun _ => one) l1
                         ++ map (fun _ => wn one) l0)  ->
  ll (mix0add_pfrag P) l').
{ intros l pi.
  eapply (X _ pi l (tt :: nil) nil)... }
intros l pi.
induction pi ; intros l' l0' l1' HP.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; simpl in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  apply Permutation_Type_length_1_inv in HP.
  apply app_eq_unit_Type in HP.
  destruct HP as [[Heq1 Heq2] | [Heq1 Heq2]] ; subst ; destruct l' ; inversion Heq ; subst.
  + destruct l1' ; inversion H0.
    destruct l0' ; inversion H1.
  + destruct l' ; inversion H1.
    * destruct l1' ; inversion H0.
      destruct l0' ; inversion H2.
    * destruct l' ; inversion H2.
      rewrite H3.
      apply ax_r.
  + destruct l1' ; inversion H0.
    destruct l0' ; inversion H1.
  + destruct l' ; inversion H1.
    * destruct l1' ; inversion H0.
      destruct l0' ; inversion H2.
    * destruct l' ; inversion H2.
      rewrite H3.
      eapply ex_r ; [ apply ax_r | ]...
- rewrite Hperm in p ; simpl in p.
  eapply IHpi.
  etransitivity...
- apply Permutation_Type_nil in HP.
  destruct l' ; inversion HP.
  rewrite H0.
  apply mix0_r...
- apply Permutation_Type_app_app_inv in HP.
  destruct HP as [[[l1a l2a] [l3a l4a]] [[HP1 HP2] [HP3 HP4]]] ;
    simpl in HP1 ; simpl in HP2 ; simpl in HP3 ; simpl in HP4.
  apply Permutation_Type_app_app_inv in HP4.
  destruct HP4 as [[[l1b l2b] [l3b l4b]] [[HP1b HP2b] [HP3b HP4b]]] ;
    simpl in HP1b ; simpl in HP2b ; simpl in HP3b ; simpl in HP4b.
  symmetry in HP1b.
  apply Permutation_Type_map_inv in HP1b.
  destruct HP1b as [la Heqa _].
  decomp_map_Type Heqa ; simpl in Heqa1 ; simpl in Heqa2 ; subst.
  symmetry in HP2b.
  apply Permutation_Type_map_inv in HP2b.
  destruct HP2b as [lb Heqb _].
  decomp_map_Type Heqb ; simpl in Heqb1 ; simpl in Heqb2 ; subst.
  apply (Permutation_Type_app_head l2a) in HP4b.
  assert (IHP1 := Permutation_Type_trans HP2 HP4b).
  apply (Permutation_Type_app_head l1a) in HP3b.
  assert (IHP2 := Permutation_Type_trans HP1 HP3b).
  apply IHpi1 in IHP1.
  apply IHpi2 in IHP2.
  symmetry in HP3.
  eapply ex_r ; [ apply mix2_r | simpl ; rewrite Hperm ; apply HP3 ]...
- apply Permutation_Type_length_1_inv in HP.
  destruct l' ; inversion HP.
  + apply mix0_r...
  + apply app_eq_nil in H1 ; destruct H1 ; subst.
    apply one_r.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; simpl in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_assoc in HP.
    apply IHpi in HP.
    eapply ex_r ; [ apply bot_r | simpl ; rewrite Hperm ]...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * decomp_map_Type Heq0.
      inversion Heq0.
    * decomp_map_Type Heq2.
      inversion Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; simpl in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_assoc in HP.
    remember (l'l ++ l) as l'.
    apply Permutation_Type_app_app_inv in HP.
    destruct HP as [[[l1a l2a] [l3a l4a]] [[HP1 HP2] [HP3 HP4]]] ;
      simpl in HP1 ; simpl in HP2 ; simpl in HP3 ; simpl in HP4.
    apply Permutation_Type_app_app_inv in HP4.
    destruct HP4 as [[[l1b l2b] [l3b l4b]] [[HP1b HP2b] [HP3b HP4b]]] ;
      simpl in HP1b ; simpl in HP2b ; simpl in HP3b ; simpl in HP4b.
    symmetry in HP1b.
    apply Permutation_Type_map_inv in HP1b.
    destruct HP1b as [la Heqa _].
    decomp_map_Type Heqa ; simpl in Heqa1 ; simpl in Heqa2 ; subst.
    symmetry in HP2b.
    apply Permutation_Type_map_inv in HP2b.
    destruct HP2b as [lb Heqb _].
    decomp_map_Type Heqb ; simpl in Heqb1 ; simpl in Heqb2 ; subst.
    apply (Permutation_Type_app_head l2a) in HP4b.
    assert (IHP1 := Permutation_Type_trans HP2 HP4b).
    apply (@Permutation_Type_cons _ A _ eq_refl) in IHP1.
    rewrite app_comm_cons in IHP1.
    apply (Permutation_Type_app_head l1a) in HP3b.
    assert (IHP2 := Permutation_Type_trans HP1 HP3b).
    apply (@Permutation_Type_cons _ B _ eq_refl) in IHP2.
    rewrite app_comm_cons in IHP2.
    apply IHpi1 in IHP1.
    apply IHpi2 in IHP2.
    symmetry in HP3.
    apply (Permutation_Type_cons_app _ _ (tens A B)) in HP3.
    eapply ex_r ; [ apply tens_r | simpl ; rewrite Hperm ; apply HP3 ]...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * exfalso.
      decomp_map_Type Heq0 ; inversion Heq0.
    * decomp_map_Type Heq2.
      inversion Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; simpl in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_assoc in HP.
    apply (@Permutation_Type_cons _ B _ eq_refl) in HP.
    apply (@Permutation_Type_cons _ A _ eq_refl) in HP.
    rewrite 2 app_comm_cons in HP.
    apply IHpi in HP.
    eapply ex_r ; [ apply parr_r | simpl ; rewrite Hperm ]...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * decomp_map_Type Heq0.
      inversion Heq0.
    * decomp_map_Type Heq2.
      inversion Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; simpl in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_Type_elt_app_exec Heq ; subst.
  + eapply ex_r ; [ apply top_r
                  | simpl ; rewrite Hperm ; apply Permutation_Type_middle ]...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * decomp_map_Type Heq0.
      inversion Heq0.
    * decomp_map_Type Heq2.
      inversion Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; simpl in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_assoc in HP.
    apply (@Permutation_Type_cons _ A _ eq_refl) in HP.
    rewrite app_comm_cons in HP.
    apply IHpi in HP.
    eapply ex_r ; [ apply plus_r1 | simpl ; rewrite Hperm ]...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * decomp_map_Type Heq0.
      inversion Heq0.
    * decomp_map_Type Heq2.
      inversion Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; simpl in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_assoc in HP.
    apply (@Permutation_Type_cons _ A _ eq_refl) in HP.
    rewrite app_comm_cons in HP.
    apply IHpi in HP.
    eapply ex_r ; [ apply plus_r2 | simpl ; rewrite Hperm ]...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * decomp_map_Type Heq0.
      inversion Heq0.
    * decomp_map_Type Heq2.
      inversion Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; simpl in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_assoc in HP.
    assert (HP2 := HP).
    apply (@Permutation_Type_cons _ A _ eq_refl) in HP.
    rewrite app_comm_cons in HP.
    apply IHpi1 in HP.
    apply (@Permutation_Type_cons _ B _ eq_refl) in HP2.
    rewrite app_comm_cons in HP2.
    apply IHpi2 in HP2.
    eapply ex_r ; [ apply with_r
                  | simpl ; rewrite Hperm ; apply Permutation_Type_middle ]...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * decomp_map_Type Heq0.
      inversion Heq0.
    * decomp_map_Type Heq2.
      inversion Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; simpl in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_Type_elt_app_exec Heq ; subst.
  + symmetry in HP.
    apply Permutation_Type_map_inv in HP.
    destruct HP as [l' Heq HP].
    decomp_map_Type Heq ;
      simpl in Heq1 ; simpl in Heq2 ; simpl in Heq3 ; simpl in Heq5 ; subst ;
      simpl in HP.
    apply (Permutation_Type_map wn) in HP.
    list_simpl in HP.
    rewrite app_assoc in HP.
    rewrite <- map_app in HP.
    apply (@Permutation_Type_cons _ A _ eq_refl) in HP.
    rewrite app_comm_cons in HP.
    rewrite <- Heq2 in HP.
    rewrite <- Heq5 in HP.
    apply IHpi in HP.
    eapply ex_r ; [ apply oc_r | simpl ; rewrite Hperm ]...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * decomp_map_Type Heq0.
      inversion Heq0.
    * decomp_map_Type Heq2.
      inversion Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; simpl in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_assoc in HP.
    apply (@Permutation_Type_cons _ A _ eq_refl) in HP.
    rewrite app_comm_cons in HP.
    apply IHpi in HP.
    eapply ex_r ; [ apply de_r | simpl ; rewrite Hperm ]...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * decomp_map_Type Heq0.
      inversion Heq0.
    * decomp_map_Type Heq2 ; simpl in Heq1 ; simpl in Heq2 ; simpl in Heq3 ; subst ; simpl in HP.
      inversion Heq2 ; subst.
      list_simpl in HP ; rewrite <- map_app in HP.
      apply (@Permutation_Type_cons _ one _ eq_refl) in HP.
      assert (Permutation_Type (one :: l)
                               (l' ++ map (fun _ : unit => one) (tt :: l1')
                                   ++ map (fun _ : unit => wn one) (l1 ++ l4)))
        as HP' by (etransitivity ; [ apply HP | ] ; perm_Type_solve). 
      apply IHpi in HP'...
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; simpl in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_assoc in HP.
    apply IHpi in HP.
    eapply ex_r ; [ apply wk_r | simpl ; rewrite Hperm ]...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * decomp_map_Type Heq0.
      inversion Heq0.
    * decomp_map_Type Heq2 ; simpl in Heq1 ; simpl in Heq2 ; simpl in Heq3 ; subst ; simpl in HP.
      inversion Heq2 ; subst.
      list_simpl in HP ; rewrite <- map_app in HP.
      apply IHpi in HP...
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; simpl in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_assoc in HP.
    apply (@Permutation_Type_cons _ (wn A) _ eq_refl) in HP.
    apply (@Permutation_Type_cons _ (wn A) _ eq_refl) in HP.
    apply (@Permutation_Type_trans _ (wn A :: map wn lw ++ wn A :: l)) in HP...
    rewrite 3 app_comm_cons in HP.
    rewrite <- app_comm_cons in HP.
    apply IHpi in HP.
    eapply ex_r ; [ apply co_std_r | simpl ; rewrite Hperm ]...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * decomp_map_Type Heq0.
      inversion Heq0.
    * decomp_map_Type Heq2 ; simpl in Heq1 ; simpl in Heq2 ; simpl in Heq3 ; subst ; simpl in HP.
      inversion Heq2 ; subst.
      list_simpl in HP ; rewrite <- map_app in HP.
    apply (@Permutation_Type_cons _ (wn one) _ eq_refl) in HP.
    apply (@Permutation_Type_cons _ (wn one) _ eq_refl) in HP.
    apply (@Permutation_Type_trans _ (wn one :: map wn lw ++ wn one :: l)) in HP...
    assert (Permutation_Type (wn one :: map wn lw ++ wn one :: l)
       (l' ++ map (fun _ : unit => one) l1' ++
              map (fun _ : unit => wn one) (tt :: tt :: l1 ++ l4)))
      as HP' by (etransitivity ; [ apply HP | perm_Type_solve ]).
    apply IHpi in HP'...
- apply Permutation_Type_app_app_inv in HP.
  destruct HP as [[[l1a l2a] [l3a l4a]] [[HP1 HP2] [HP3 HP4]]] ;
    simpl in HP1 ; simpl in HP2 ; simpl in HP3 ; simpl in HP4.
  apply Permutation_Type_app_app_inv in HP4.
  destruct HP4 as [[[l1b l2b] [l3b l4b]] [[HP1b HP2b] [HP3b HP4b]]] ;
    simpl in HP1b ; simpl in HP2b ; simpl in HP3b ; simpl in HP4b.
  symmetry in HP1b.
  apply Permutation_Type_map_inv in HP1b.
  destruct HP1b as [la Heqa _].
  decomp_map_Type Heqa ; simpl in Heqa1 ; simpl in Heqa2 ; subst.
  symmetry in HP2b.
  apply Permutation_Type_map_inv in HP2b.
  destruct HP2b as [lb Heqb _].
  decomp_map_Type Heqb ; simpl in Heqb1 ; simpl in Heqb2 ; subst.
  apply (Permutation_Type_app_head l2a) in HP4b.
  assert (IHP1 := Permutation_Type_trans HP2 HP4b).
  apply (@Permutation_Type_cons _ (dual A) _ eq_refl) in IHP1.
  rewrite app_comm_cons in IHP1.
  apply (Permutation_Type_app_head l1a) in HP3b.
  assert (IHP2 := Permutation_Type_trans HP1 HP3b).
  apply (@Permutation_Type_cons _ A _ eq_refl) in IHP2.
  rewrite app_comm_cons in IHP2.
  apply IHpi1 in IHP1.
  apply IHpi2 in IHP2.
  symmetry in HP3.
  eapply ex_r ; [ eapply cut_r | simpl ; rewrite Hperm ; apply HP3 ]...
- destruct l1' ; destruct l0' ; simpl in HP.
  + eapply ex_r ; [ apply gax_r | simpl ; rewrite Hperm ]...
  + exfalso.
    apply Permutation_Type_vs_elt_inv in HP.
    specialize (Hgax a).
    destruct HP as [[l1 l2] Heq] ; rewrite Heq in Hgax.
    apply Forall_elt in Hgax.
    inversion Hgax.
  + exfalso.
    apply Permutation_Type_vs_elt_inv in HP.
    specialize (Hgax a).
    destruct HP as [[l1 l2] Heq] ; rewrite Heq in Hgax.
    apply Forall_elt in Hgax.
    inversion Hgax.
  + exfalso.
    apply Permutation_Type_vs_elt_inv in HP.
    specialize (Hgax a).
    destruct HP as [[l1 l2] Heq] ; rewrite Heq in Hgax.
    apply Forall_elt in Hgax.
    inversion Hgax.
Qed.


(** ** Results on [mix2] *)

Definition mix2add_pfrag P :=
  mk_pfrag (pcut P) (pgax P) (pmix0 P) true (pperm P).

Lemma mix2_to_ll {P} : pperm P = true -> forall b2 bp l,
  ll (mk_pfrag P.(pcut) P.(pgax) P.(pmix0) b2 bp) l -> ll P (wn (tens bot bot) :: l).
Proof with myeeasy ; try PCperm_Type_solve.
intros fp b2 bp l pi.
eapply (ext_wn_param _ P fp _ (tens bot bot :: nil)) in pi.
- eapply ex_r...
- intros Hcut...
- simpl ; intros a.
  eapply ex_r ; [ | apply PCperm_Type_last ].
  apply wk_r.
  apply gax_r.
- intros Hpmix0 Hpmix0'.
  exfalso.
  simpl in Hpmix0.
  rewrite Hpmix0 in Hpmix0'.
  inversion Hpmix0'.
- intros _ _ l1 l2 pi1 pi2.
  apply (ex_r _ (wn (tens bot bot) :: l2 ++ l1))...
  apply co_std_r.
  apply co_std_r.
  apply de_r.
  eapply ex_r.
  + apply tens_r ; apply bot_r ; [ apply pi1 | apply pi2 ].
  + rewrite fp...
Qed.

Lemma ll_to_mix2 {P} : (forall a, Forall atomic (projT2 (pgax P) a)) ->
  pperm P = true -> forall l,
  ll P (wn (tens bot bot) :: l) -> ll (mix2add_pfrag P) l.
Proof with myeeasy ; try PCperm_Type_solve.
intros Hgax Hperm.
enough (forall l, ll P l -> forall l' (l0 l1 : list unit),
  Permutation_Type l (l' ++ map (fun _ => tens bot bot) l1
                         ++ map (fun _ => wn (tens bot bot)) l0)  ->
  ll (mix2add_pfrag P) l').
{ intros l pi.
  eapply (X _ pi l (tt :: nil) nil)... }
intros l pi.
induction pi ; intros l' l0' l1' HP.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; simpl in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  apply Permutation_Type_length_1_inv in HP.
  apply app_eq_unit_Type in HP.
  destruct HP as [[Heq1 Heq2] | [Heq1 Heq2]] ; subst ; destruct l' ; inversion Heq ; subst.
  + destruct l1' ; inversion H0.
    destruct l0' ; inversion H1.
  + destruct l' ; inversion H1.
    * destruct l1' ; inversion H0.
      destruct l0' ; inversion H2.
    * destruct l' ; inversion H2.
      rewrite H3.
      apply ax_r.
  + destruct l1' ; inversion H0.
    destruct l0' ; inversion H1.
  + destruct l' ; inversion H1.
    * destruct l1' ; inversion H0.
      destruct l0' ; inversion H2.
    * destruct l' ; inversion H2.
      rewrite H3.
      eapply ex_r ; [ apply ax_r | ]...
- rewrite Hperm in p ; simpl in p.
  eapply IHpi.
  etransitivity...
- apply Permutation_Type_nil in HP.
  destruct l' ; inversion HP.
  rewrite H0.
  apply mix0_r...
- apply Permutation_Type_app_app_inv in HP.
  destruct HP as [[[l1a l2a] [l3a l4a]] [[HP1 HP2] [HP3 HP4]]] ;
    simpl in HP1 ; simpl in HP2 ; simpl in HP3 ; simpl in HP4.
  apply Permutation_Type_app_app_inv in HP4.
  destruct HP4 as [[[l1b l2b] [l3b l4b]] [[HP1b HP2b] [HP3b HP4b]]] ;
    simpl in HP1b ; simpl in HP2b ; simpl in HP3b ; simpl in HP4b.
  symmetry in HP1b.
  apply Permutation_Type_map_inv in HP1b.
  destruct HP1b as [la Heqa _].
  decomp_map_Type Heqa ; simpl in Heqa1 ; simpl in Heqa2 ; subst.
  symmetry in HP2b.
  apply Permutation_Type_map_inv in HP2b.
  destruct HP2b as [lb Heqb _].
  decomp_map_Type Heqb ; simpl in Heqb1 ; simpl in Heqb2 ; subst.
  apply (Permutation_Type_app_head l2a) in HP4b.
  assert (IHP1 := Permutation_Type_trans HP2 HP4b).
  apply (Permutation_Type_app_head l1a) in HP3b.
  assert (IHP2 := Permutation_Type_trans HP1 HP3b).
  apply IHpi1 in IHP1.
  apply IHpi2 in IHP2.
  symmetry in HP3.
  eapply ex_r ; [ apply mix2_r | simpl ; rewrite Hperm ; apply HP3 ]...
- apply Permutation_Type_length_1_inv in HP.
  destruct l' ; inversion HP.
  + destruct l1' ; inversion H0.
    destruct l0' ; inversion H1.
  + apply app_eq_nil in H1 ; destruct H1 ; subst.
    apply one_r.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; simpl in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_assoc in HP.
    apply IHpi in HP.
    eapply ex_r ; [ apply bot_r | simpl ; rewrite Hperm ]...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * decomp_map_Type Heq0.
      inversion Heq0.
    * decomp_map_Type Heq2.
      inversion Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; simpl in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_assoc in HP.
    remember (l'l ++ l) as l'.
    apply Permutation_Type_app_app_inv in HP.
    destruct HP as [[[l1a l2a] [l3a l4a]] [[HP1 HP2] [HP3 HP4]]] ;
      simpl in HP1 ; simpl in HP2 ; simpl in HP3 ; simpl in HP4.
    apply Permutation_Type_app_app_inv in HP4.
    destruct HP4 as [[[l1b l2b] [l3b l4b]] [[HP1b HP2b] [HP3b HP4b]]] ;
      simpl in HP1b ; simpl in HP2b ; simpl in HP3b ; simpl in HP4b.
    symmetry in HP1b.
    apply Permutation_Type_map_inv in HP1b.
    destruct HP1b as [la Heqa _].
    decomp_map_Type Heqa ; simpl in Heqa1 ; simpl in Heqa2 ; subst.
    symmetry in HP2b.
    apply Permutation_Type_map_inv in HP2b.
    destruct HP2b as [lb Heqb _].
    decomp_map_Type Heqb ; simpl in Heqb1 ; simpl in Heqb2 ; subst.
    apply (Permutation_Type_app_head l2a) in HP4b.
    assert (IHP1 := Permutation_Type_trans HP2 HP4b).
    apply (@Permutation_Type_cons _ A _ eq_refl) in IHP1.
    rewrite app_comm_cons in IHP1.
    apply (Permutation_Type_app_head l1a) in HP3b.
    assert (IHP2 := Permutation_Type_trans HP1 HP3b).
    apply (@Permutation_Type_cons _ B _ eq_refl) in IHP2.
    rewrite app_comm_cons in IHP2.
    apply IHpi1 in IHP1.
    apply IHpi2 in IHP2.
    symmetry in HP3.
    apply (Permutation_Type_cons_app _ _ (tens A B)) in HP3.
    eapply ex_r ; [ apply tens_r | simpl ; rewrite Hperm ; apply HP3 ]...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * decomp_map_Type Heq0.
      inversion Heq0 ; subst ; list_simpl in HP.
      rewrite (app_assoc (map _ l4)) in HP.
      rewrite <- map_app in HP.
      remember (l4 ++ l6) as l0 ; clear Heql0.
      apply Permutation_Type_app_app_inv in HP.
      destruct HP as [[[l1a l2a] [l3a l4a]] [[HP1 HP2] [HP3 HP4]]] ;
        simpl in HP1 ; simpl in HP2 ; simpl in HP3 ; simpl in HP4.
      apply Permutation_Type_app_app_inv in HP4.
      destruct HP4 as [[[l1b l2b] [l3b l4b]] [[HP1b HP2b] [HP3b HP4b]]] ;
        simpl in HP1b ; simpl in HP2b ; simpl in HP3b ; simpl in HP4b.
      symmetry in HP1b.
      apply Permutation_Type_map_inv in HP1b.
      destruct HP1b as [la Heqa _].
      decomp_map_Type Heqa ; simpl in Heqa1 ; simpl in Heqa2 ; subst.
      symmetry in HP2b.
      apply Permutation_Type_map_inv in HP2b.
      destruct HP2b as [lb Heqb _].
      decomp_map_Type Heqb ; simpl in Heqb1 ; simpl in Heqb2 ; subst.
      apply (Permutation_Type_app_head l2a) in HP4b.
      assert (IHP1 := Permutation_Type_trans HP2 HP4b).
      apply (@Permutation_Type_cons _ bot _ eq_refl) in IHP1.
      rewrite app_comm_cons in IHP1.
      apply IHpi1 in IHP1.
      rewrite <- app_nil_l in IHP1.
      eapply bot_rev_axat in IHP1 ; [ | apply Hgax | reflexivity ].
      list_simpl in IHP1.
      apply (Permutation_Type_app_head l1a) in HP3b.
      assert (IHP2 := Permutation_Type_trans HP1 HP3b).
      apply (@Permutation_Type_cons _ bot _ eq_refl) in IHP2.
      rewrite app_comm_cons in IHP2.
      apply IHpi2 in IHP2.
      rewrite <- app_nil_l in IHP2.
      eapply bot_rev_axat in IHP2 ; [ | apply Hgax | reflexivity ].
      list_simpl in IHP2.
      assert (Permutation_Type (l2a ++ l1a) l') as HP' by perm_Type_solve.
      eapply ex_r ; [ apply mix2_r | simpl ; rewrite Hperm ; apply HP' ]...
    * decomp_map_Type Heq2.
      inversion Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; simpl in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_assoc in HP.
    apply (@Permutation_Type_cons _ B _ eq_refl) in HP.
    apply (@Permutation_Type_cons _ A _ eq_refl) in HP.
    rewrite 2 app_comm_cons in HP.
    apply IHpi in HP.
    eapply ex_r ; [ apply parr_r | simpl ; rewrite Hperm ]...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * decomp_map_Type Heq0.
      inversion Heq0.
    * decomp_map_Type Heq2.
      inversion Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; simpl in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_Type_elt_app_exec Heq ; subst.
  + eapply ex_r ; [ apply top_r
                  | simpl ; rewrite Hperm ; apply Permutation_Type_middle ]...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * decomp_map_Type Heq0.
      inversion Heq0.
    * decomp_map_Type Heq2.
      inversion Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; simpl in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_assoc in HP.
    apply (@Permutation_Type_cons _ A _ eq_refl) in HP.
    rewrite app_comm_cons in HP.
    apply IHpi in HP.
    eapply ex_r ; [ apply plus_r1 | simpl ; rewrite Hperm ]...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * decomp_map_Type Heq0.
      inversion Heq0.
    * decomp_map_Type Heq2.
      inversion Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; simpl in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_assoc in HP.
    apply (@Permutation_Type_cons _ A _ eq_refl) in HP.
    rewrite app_comm_cons in HP.
    apply IHpi in HP.
    eapply ex_r ; [ apply plus_r2 | simpl ; rewrite Hperm ]...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * decomp_map_Type Heq0.
      inversion Heq0.
    * decomp_map_Type Heq2.
      inversion Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; simpl in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_assoc in HP.
    assert (HP2 := HP).
    apply (@Permutation_Type_cons _ A _ eq_refl) in HP.
    rewrite app_comm_cons in HP.
    apply IHpi1 in HP.
    apply (@Permutation_Type_cons _ B _ eq_refl) in HP2.
    rewrite app_comm_cons in HP2.
    apply IHpi2 in HP2.
    eapply ex_r ; [ apply with_r
                  | simpl ; rewrite Hperm ; apply Permutation_Type_middle ]...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * decomp_map_Type Heq0.
      inversion Heq0.
    * decomp_map_Type Heq2.
      inversion Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; simpl in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_Type_elt_app_exec Heq ; subst.
  + symmetry in HP.
    apply Permutation_Type_map_inv in HP.
    destruct HP as [l' Heq HP].
    decomp_map_Type Heq ;
      simpl in Heq1 ; simpl in Heq2 ; simpl in Heq3 ; simpl in Heq5 ; subst ;
      simpl in HP.
    apply (Permutation_Type_map wn) in HP.
    list_simpl in HP.
    rewrite app_assoc in HP.
    rewrite <- map_app in HP.
    apply (@Permutation_Type_cons _ A _ eq_refl) in HP.
    rewrite app_comm_cons in HP.
    rewrite <- Heq2 in HP.
    rewrite <- Heq5 in HP.
    apply IHpi in HP.
    eapply ex_r ; [ apply oc_r | simpl ; rewrite Hperm ]...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * decomp_map_Type Heq0.
      inversion Heq0.
    * decomp_map_Type Heq2.
      inversion Heq2.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; simpl in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_assoc in HP.
    apply (@Permutation_Type_cons _ A _ eq_refl) in HP.
    rewrite app_comm_cons in HP.
    apply IHpi in HP.
    eapply ex_r ; [ apply de_r | simpl ; rewrite Hperm ]...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * decomp_map_Type Heq0.
      inversion Heq0.
    * decomp_map_Type Heq2 ; simpl in Heq1 ; simpl in Heq2 ; simpl in Heq3 ; subst ; simpl in HP.
      inversion Heq2 ; subst.
      list_simpl in HP ; rewrite <- map_app in HP.
      apply (@Permutation_Type_cons _ (tens bot bot) _ eq_refl) in HP.
      assert (Permutation_Type (tens bot bot :: l)
                               (l' ++ map (fun _ : unit => tens bot bot) (tt :: l1')
                                   ++ map (fun _ : unit => wn (tens bot bot)) (l1 ++ l4)))
        as HP' by (etransitivity ; [ apply HP | ] ; perm_Type_solve). 
      apply IHpi in HP'...
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; simpl in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_assoc in HP.
    apply IHpi in HP.
    eapply ex_r ; [ apply wk_r | simpl ; rewrite Hperm ]...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * decomp_map_Type Heq0.
      inversion Heq0.
    * decomp_map_Type Heq2 ; simpl in Heq1 ; simpl in Heq2 ; simpl in Heq3 ; subst ; simpl in HP.
      inversion Heq2 ; subst.
      list_simpl in HP ; rewrite <- map_app in HP.
      apply IHpi in HP...
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as [[l'l l'r] Heq] ; simpl in Heq.
  rewrite Heq in HP.
  apply Permutation_Type_cons_app_inv in HP.
  dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_assoc in HP.
    apply (@Permutation_Type_cons _ (wn A) _ eq_refl) in HP.
    apply (@Permutation_Type_cons _ (wn A) _ eq_refl) in HP.
    apply (@Permutation_Type_trans _ (wn A :: map wn lw ++ wn A :: l)) in HP...
    rewrite 3 app_comm_cons in HP.
    rewrite <- app_comm_cons in HP.
    apply IHpi in HP.
    eapply ex_r ; [ apply co_std_r | simpl ; rewrite Hperm ]...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * decomp_map_Type Heq0.
      inversion Heq0.
    * decomp_map_Type Heq2 ; simpl in Heq1 ; simpl in Heq2 ; simpl in Heq3 ; subst ; simpl in HP.
      inversion Heq2 ; subst.
      list_simpl in HP ; rewrite <- map_app in HP.
    apply (@Permutation_Type_cons _ (wn (tens bot bot)) _ eq_refl) in HP.
    apply (@Permutation_Type_cons _ (wn (tens bot bot)) _ eq_refl) in HP.
    apply (@Permutation_Type_trans _ (wn (tens bot bot) :: map wn lw ++ wn (tens bot bot) :: l)) in HP...
    assert (Permutation_Type (wn (tens bot bot) :: map wn lw ++ wn (tens bot bot) :: l)
       (l' ++ map (fun _ : unit => tens bot bot) l1' ++
              map (fun _ : unit => wn (tens bot bot)) (tt :: tt :: l1 ++ l4)))
      as HP' by (etransitivity ; [ apply HP | perm_Type_solve ]).
    apply IHpi in HP'...
- apply Permutation_Type_app_app_inv in HP.
  destruct HP as [[[l1a l2a] [l3a l4a]] [[HP1 HP2] [HP3 HP4]]] ;
    simpl in HP1 ; simpl in HP2 ; simpl in HP3 ; simpl in HP4.
  apply Permutation_Type_app_app_inv in HP4.
  destruct HP4 as [[[l1b l2b] [l3b l4b]] [[HP1b HP2b] [HP3b HP4b]]] ;
    simpl in HP1b ; simpl in HP2b ; simpl in HP3b ; simpl in HP4b.
  symmetry in HP1b.
  apply Permutation_Type_map_inv in HP1b.
  destruct HP1b as [la Heqa _].
  decomp_map_Type Heqa ; simpl in Heqa1 ; simpl in Heqa2 ; subst.
  symmetry in HP2b.
  apply Permutation_Type_map_inv in HP2b.
  destruct HP2b as [lb Heqb _].
  decomp_map_Type Heqb ; simpl in Heqb1 ; simpl in Heqb2 ; subst.
  apply (Permutation_Type_app_head l2a) in HP4b.
  assert (IHP1 := Permutation_Type_trans HP2 HP4b).
  apply (@Permutation_Type_cons _ (dual A) _ eq_refl) in IHP1.
  rewrite app_comm_cons in IHP1.
  apply (Permutation_Type_app_head l1a) in HP3b.
  assert (IHP2 := Permutation_Type_trans HP1 HP3b).
  apply (@Permutation_Type_cons _ A _ eq_refl) in IHP2.
  rewrite app_comm_cons in IHP2.
  apply IHpi1 in IHP1.
  apply IHpi2 in IHP2.
  symmetry in HP3.
  eapply ex_r ; [ eapply cut_r | simpl ; rewrite Hperm ; apply HP3 ]...
- destruct l1' ; destruct l0' ; simpl in HP.
  + eapply ex_r ; [ apply gax_r | simpl ; rewrite Hperm ]...
  + exfalso.
    apply Permutation_Type_vs_elt_inv in HP.
    specialize (Hgax a).
    destruct HP as [[l1 l2] Heq] ; rewrite Heq in Hgax.
    apply Forall_elt in Hgax.
    inversion Hgax.
  + exfalso.
    apply Permutation_Type_vs_elt_inv in HP.
    specialize (Hgax a).
    destruct HP as [[l1 l2] Heq] ; rewrite Heq in Hgax.
    apply Forall_elt in Hgax.
    inversion Hgax.
  + exfalso.
    apply Permutation_Type_vs_elt_inv in HP.
    specialize (Hgax a).
    destruct HP as [[l1 l2] Heq] ; rewrite Heq in Hgax.
    apply Forall_elt in Hgax.
    inversion Hgax.
Qed.


(** ** Results on [mix0] and [mix2] together *)

Lemma mix02_to_ll {P} : pperm P = true -> forall b1 b2 bp l,
  ll (mk_pfrag P.(pcut) P.(pgax) b1 b2 bp) l -> ll P (wn (tens (wn one) (wn one)) :: l).
Proof with myeeasy ; try PCperm_Type_solve.
intros fp b1 b2 bp l pi.
eapply (ext_wn_param _ P fp _ (tens (wn one) (wn one) :: nil)) in pi.
- eapply ex_r...
- intros Hcut...
- simpl ; intros a.
  eapply ex_r ; [ | apply PCperm_Type_last ].
  apply wk_r.
  apply gax_r.
- intros Hpmix0 Hpmix0'.
  apply de_r...
  rewrite <- (app_nil_l nil).
  apply tens_r ; apply de_r ; apply one_r.
- intros _ _ l1 l2 pi1 pi2.
  apply (ex_r _ (wn (tens (wn one) (wn one)) :: l2 ++ l1))...
  apply co_std_r.
  apply co_std_r.
  apply de_r.
  eapply ex_r.
  + apply tens_r ; apply wk_r ; [ apply pi1 | apply pi2 ].
  + rewrite fp...
Qed.

Lemma mix02_to_ll' {P} : pperm P = true -> forall b0 b2 bp l,
  ll (mk_pfrag P.(pcut) P.(pgax) b0 b2 bp) l -> ll P (wn one :: wn (tens bot bot) :: l).
Proof with myeasy.
intros Hperm b0 b2 bp l pi.
eapply mix0_to_ll...
eapply mix2_to_ll...
apply pi.
Qed.

Lemma ll_to_mix02 {P} : (forall a, Forall atomic (projT2 (pgax P) a)) ->
  pperm P = true -> forall l,
  ll P (wn one :: wn (tens bot bot) :: l) -> ll (mix2add_pfrag (mix0add_pfrag P)) l.
Proof with myeasy.
intros Hgax Hperm l pi.
apply ll_to_mix2...
apply ll_to_mix0...
Qed.


