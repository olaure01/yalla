(* ll_fragments library for yalla *)


(* output in Type *)


(** * Definitions of various Linear Logic fragments *)

Require Import Bool_more.
Require Import List_more.
Require Import List_Type_more.
Require Import Permutation_Type_more.
Require Import Permutation_Type_solve.
Require Import genperm_Type.

Require Export ll_prop.
Require Import subs.


(** ** Standard linear logic: [ll_ll] (no mix, no axiom, commutative) *)

(** cut / axioms / mix0 / mix2 / permutation *)
Definition pfrag_ll :=  mk_pfrag false NoAxioms false false true.
(*                               cut   axioms   mix0  mix2  perm  *)

Definition ll_ll := ll pfrag_ll.

Lemma cut_ll_r : forall A l1 l2,
  ll_ll (dual A :: l1) -> ll_ll (A :: l2) -> ll_ll (l2 ++ l1).
Proof with myeeasy.
intros A l1 l2 pi1 pi2.
eapply cut_r_axfree...
intros a ; destruct a.
Qed.

Lemma cut_ll_admissible :
  forall l, ll (cutupd_pfrag pfrag_ll true) l -> ll_ll l.
Proof with myeeasy.
intros l pi.
induction pi ; try (now econstructor).
- eapply ex_r...
- eapply ex_wn_r...
- eapply cut_ll_r...
Qed.



(** ** Linear logic with mix0: [ll_mix0] (no mix2, no axiom, commutative) *)

(** cut / axioms / mix0 / mix2 / permutation *)
Definition pfrag_mix0 := mk_pfrag false NoAxioms true false true.
(*                                cut   axioms   mix0 mix2  perm  *)

Definition ll_mix0 := ll pfrag_mix0.

Definition mix0add_pfrag P :=
  mk_pfrag (pcut P) (pgax P) true (pmix2 P) (pperm P).

Lemma cut_mix0_r : forall A l1 l2, 
  ll_mix0 (dual A :: l1) -> ll_mix0 (A :: l2) -> ll_mix0 (l2 ++ l1).
Proof with myeeasy.
intros A l1 l2 pi1 pi2.
eapply cut_r_axfree...
intros a ; destruct a.
Qed.

Lemma cut_mix0_admissible :
  forall l, ll (cutupd_pfrag pfrag_mix0 true) l -> ll_mix0 l.
Proof with myeeasy.
intros l pi.
induction pi ; try (now econstructor).
- eapply ex_r...
- eapply ex_wn_r...
- eapply cut_mix0_r...
Qed.

(** Provability in [ll_mix0] is equivalent to adding [wn one] in [ll] *)

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

Lemma ll_to_mix0_axat {P} : (forall a, Forall atomic (projT2 (pgax P) a)) ->
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
- apply (Permutation_Type_map wn) in p.
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
    rewrite 2 app_comm_cons in HP.
    apply IHpi in HP.
    eapply ex_r ; [ apply co_r | simpl ; rewrite Hperm ]...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * decomp_map_Type Heq0.
      inversion Heq0.
    * decomp_map_Type Heq2 ; simpl in Heq1 ; simpl in Heq2 ; simpl in Heq3 ; subst ; simpl in HP.
      inversion Heq2 ; subst.
      list_simpl in HP ; rewrite <- map_app in HP.
      apply (@Permutation_Type_cons _ (wn one) _ eq_refl) in HP.
      apply (@Permutation_Type_cons _ (wn one) _ eq_refl) in HP.
      assert (Permutation_Type (wn one :: wn one :: l)
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

Lemma ll_to_mix0_cut {P} : forall l,
  ll P (wn one :: l) -> ll (mk_pfrag true P.(pgax) true P.(pmix2) P.(pperm)) l.
Proof with myeasy.
intros l pi.
eapply stronger_pfrag in pi.
- rewrite <- (app_nil_r l).
  eapply cut_r ; [ | | apply pi]...
  change nil with (map wn nil).
  apply oc_r.
  apply bot_r.
  eapply mix0_r...
- nsplit 5...
  + destruct pcut...
  + intros a.
    exists a...
  + destruct pmix0...
Qed.

Lemma mix0_wn_one : forall l, ll_mix0 (wn one :: l) -> ll_mix0 l.
Proof with myeeasy.
intros l pi.
(* an alternative proof is by introducing a cut with (oc bot) *)
assert (pfrag_mix0 = mk_pfrag pfrag_mix0.(pcut) pfrag_mix0.(pgax)
                              true pfrag_mix0.(pmix2) true)
  as Heqfrag by reflexivity.
apply cut_mix0_admissible.
apply ll_to_mix0_cut.
apply co_r.
eapply mix0_to_ll...
Qed.


(** Provability in [ll_mix0] is equivalent to provability of [ll]
extended with the provability of [bot :: bot :: nil] *)

Lemma mix0_to_ll_bot {P} : pcut P = true -> pperm P = true -> forall bc b0 bp l,
  ll (mk_pfrag bc P.(pgax) b0 P.(pmix2) bp) l ->
    ll (axupd_pfrag P (existT (fun x => x -> list formula) _
                              (fun a => match a with
                                        | inl x => projT2 (pgax P) x
                                        | inr tt => bot :: bot :: nil
                                        end))) l.
Proof with myeeasy ; try (unfold PCperm_Type ; PCperm_Type_solve).
remember (axupd_pfrag P (existT (fun x => x -> list formula) _
                                (fun a => match a with
                                          | inl x => projT2 (pgax P) x
                                          | inr tt => bot :: bot :: nil
                                          end))) as P'.
intros fc fp bc b0 bp l pi.
eapply stronger_pfrag in pi.
- eapply mix0_to_ll in pi...
  assert (pcut P' = true) as fc' by (rewrite HeqP' ; simpl ; assumption).
  apply (stronger_pfrag _ P') in pi.
  + assert (ll P' (bot :: map wn nil)) as pi'.
    { change (bot :: map wn nil) with ((bot :: nil) ++ nil).
      eapply (@cut_r _ fc' bot).
      - apply one_r.
      - assert ({ b | bot :: bot :: nil = projT2 (pgax P') b })
          as [b Hgax] by (rewrite HeqP' ; now (exists (inr tt))).
        rewrite Hgax.
        apply gax_r. }
    apply oc_r in pi'.
    rewrite <- (app_nil_l l).
    eapply (@cut_r _ fc' (oc bot)) ; [ simpl ; apply pi | apply pi' ].
  + nsplit 5 ; rewrite HeqP'...
    simpl ; intros a ; exists (inl a)...
- nsplit 5 ; intros ; simpl...
  + rewrite fc.
    destruct bc...
  + exists a...
Qed.

Lemma ll_bot_to_mix0 {P} : forall l,
  ll (axupd_pfrag P (existT (fun x => x -> list formula) _
                              (fun a => match a with
                                        | inl x => projT2 (pgax P) x
                                        | inr tt => bot :: bot :: nil
                                        end))) l
  -> ll (mk_pfrag P.(pcut) P.(pgax) true P.(pmix2) P.(pperm)) l.
Proof with myeeasy.
intros l pi.
remember (mk_pfrag P.(pcut) P.(pgax) true P.(pmix2) P.(pperm)) as P'.
apply (stronger_pfrag _
  (axupd_pfrag P' (existT (fun x => x -> list formula) _
                          (fun a => match a with
                                    | inl x => projT2 (pgax P) x
                                    | inr tt => bot :: bot :: nil
                                    end)))) in pi.
- eapply ax_gen...
  clear - HeqP' ; simpl ; intros a.
  destruct a.
  + assert ({ b | projT2 (pgax P) p = projT2 (pgax P') b })
      as [b Hgax] by (rewrite HeqP' ; now exists p).
    rewrite Hgax.
    apply gax_r.
  + destruct u.
    apply bot_r.
    apply bot_r.
    apply mix0_r.
    rewrite HeqP'...
- rewrite HeqP' ; nsplit 5 ; simpl ; intros...
  + exists a...
  + destruct (pmix0 P)...
Qed.

(** [mix2] is not valid in [ll_mix0] *)

Lemma mix0_not_mix2 : ll_mix0 (one :: one :: nil) -> False.
Proof.
intros pi.
remember (one :: one :: nil) as l.
revert Heql ; induction pi ; intros Heql ; subst ; try inversion Heql.
- apply IHpi.
  simpl in p ; apply Permutation_Type_sym in p.
  apply Permutation_Type_length_2_inv in p.
  destruct p ; assumption.
- destruct l1 ; destruct lw' ; inversion Heql ; subst.
  + now symmetry in p ; apply Permutation_Type_nil in p ; subst.
  + now symmetry in p ; apply Permutation_Type_nil in p ; subst.
  + destruct l1 ; inversion H2.
    destruct l1 ; inversion H3.
- inversion f.
- inversion f.
- destruct a.
Qed.


(** ** Linear logic with mix2: [ll_mix2] (no mix0, no axiom, commutative) *)

(** cut / axioms / mix0 / mix2 / permutation *)
Definition pfrag_mix2 := mk_pfrag false NoAxioms false true true.
(*                                cut   axioms   mix0  mix2 perm  *)

Definition ll_mix2 := ll pfrag_mix2.

Definition mix2add_pfrag P :=
  mk_pfrag (pcut P) (pgax P) (pmix0 P) true (pperm P).

Lemma cut_mix2_r : forall A l1 l2,
  ll_mix2 (dual A :: l1) -> ll_mix2 (A :: l2) -> ll_mix2 (l2 ++ l1).
Proof with myeeasy.
intros A l1 l2 pi1 pi2.
eapply cut_r_axfree...
intros a ; destruct a.
Qed.

Lemma cut_mix2_admissible :
  forall l, ll (cutupd_pfrag pfrag_mix2 true) l -> ll_mix2 l.
Proof with myeeasy.
intros l pi.
induction pi ; try (now econstructor).
- eapply ex_r...
- eapply ex_wn_r...
- eapply cut_mix2_r...
Qed.

(** Provability in [ll_mix2] is equivalent to adding [wn (tens bot bot)] in [ll] *)

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
  apply co_r.
  apply co_r.
  apply de_r.
  eapply ex_r.
  + apply tens_r ; apply bot_r ; [ apply pi1 | apply pi2 ].
  + rewrite fp...
Qed.

Lemma ll_to_mix2_axat {P} : (forall a, Forall atomic (projT2 (pgax P) a)) ->
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
- apply (Permutation_Type_map wn) in p.
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
    rewrite 3 app_comm_cons in HP.
    apply IHpi in HP.
    eapply ex_r ; [ apply co_r | simpl ; rewrite Hperm ]...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * decomp_map_Type Heq0.
      inversion Heq0.
    * decomp_map_Type Heq2 ; simpl in Heq1 ; simpl in Heq2 ; simpl in Heq3 ; subst ; simpl in HP.
      inversion Heq2 ; subst.
      list_simpl in HP ; rewrite <- map_app in HP.
      apply (@Permutation_Type_cons _ (wn (tens bot bot)) _ eq_refl) in HP.
      apply (@Permutation_Type_cons _ (wn (tens bot bot)) _ eq_refl) in HP.
      assert (Permutation_Type (wn (tens bot bot) :: wn (tens bot bot) :: l)
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

Lemma ll_to_mix2_cut {P} : forall l,
  ll P (wn (tens bot bot) :: l) -> ll (mk_pfrag true P.(pgax) P.(pmix0) true P.(pperm)) l.
Proof with myeasy.
intros l pi.
eapply stronger_pfrag in pi.
- rewrite <- (app_nil_r l).
  eapply cut_r ; [ | | apply pi]...
  change nil with (map wn nil).
  apply oc_r.
  apply parr_r.
  change (one :: one :: map wn nil) with ((one :: nil) ++ one :: nil).
  eapply mix2_r...
  + apply one_r.
  + apply one_r.
- nsplit 5...
  + destruct pcut...
  + intros a.
    exists a...
  + destruct pmix2...
Qed.

(** Provability in [ll_mix2] is equivalent to provability of [ll]
extended with the provability of [one :: one :: nil] *)

Lemma mix2_to_ll_one_one {P} : pcut P = true -> pperm P = true -> forall bc b2 bp l,
  ll (mk_pfrag bc P.(pgax) P.(pmix0) b2 bp) l ->
    ll (axupd_pfrag P (existT (fun x => x -> list formula) _
                              (fun a => match a with
                                        | inl x => projT2 (pgax P) x
                                        | inr tt => one :: one :: nil
                                        end))) l.
Proof with myeeasy ; try (unfold PCperm_Type ; PCperm_Type_solve).
remember (axupd_pfrag P (existT (fun x => x -> list formula) _
                                (fun a => match a with
                                          | inl x => projT2 (pgax P) x
                                          | inr tt => one :: one :: nil
                                          end))) as P'.
intros fc fp bc b2 bp l pi.
eapply stronger_pfrag in pi.
- eapply mix2_to_ll in pi...
  assert (pcut P' = true) as fc' by (rewrite HeqP' ; simpl ; assumption).
  apply (stronger_pfrag _ P') in pi.
  + assert (ll P' (parr one one :: map wn nil)) as pi'.
    { change (parr one one :: map wn nil) with ((parr one one :: nil) ++ nil).
      eapply (@cut_r _ fc' bot).
      - apply one_r.
      - apply bot_r.
        apply parr_r.
         assert ({ b | one :: one :: nil = projT2 (pgax P') b })
          as [b Hgax] by (rewrite HeqP' ; now (exists (inr tt))).
        rewrite Hgax.
        apply gax_r. }
    apply oc_r in pi'.
    rewrite <- (app_nil_l l).
    eapply (@cut_r _ fc' (oc (parr one one))) ; [ simpl ; apply pi | apply pi' ].
  + nsplit 5 ; rewrite HeqP'...
    simpl ; intros a ; exists (inl a)...
- nsplit 5 ; intros ; simpl...
  + rewrite fc.
    destruct bc...
  + exists a...
Qed.

Lemma ll_one_one_to_mix2 {P} : forall l,
  ll (axupd_pfrag P (existT (fun x => x -> list formula) _
                              (fun a => match a with
                                        | inl x => projT2 (pgax P) x
                                        | inr tt => one :: one :: nil
                                        end))) l
  -> ll (mk_pfrag P.(pcut) P.(pgax) P.(pmix0) true P.(pperm)) l.
Proof with myeeasy.
intros l pi.
remember (mk_pfrag P.(pcut) P.(pgax) P.(pmix0) true P.(pperm)) as P'.
apply (stronger_pfrag _
  (axupd_pfrag P' (existT (fun x => x -> list formula) _
                          (fun a => match a with
                                    | inl x => projT2 (pgax P) x
                                    | inr tt => one :: one :: nil
                                    end)))) in pi.
- eapply ax_gen...
  clear - HeqP' ; simpl ; intros a.
  destruct a.
  + assert ({ b | projT2 (pgax P) p = projT2 (pgax P') b })
      as [b Hgax] by (rewrite HeqP' ; now exists p).
    rewrite Hgax.
    apply gax_r.
  + destruct u.
    change (one :: one :: nil) with ((one :: nil) ++ one :: nil).
    rewrite HeqP'.
    apply mix2_r...
    * apply one_r.
    * apply one_r.
- rewrite HeqP' ; nsplit 5 ; simpl ; intros...
  + exists a...
  + destruct (pmix2 P)...
Qed.

(** [mix0] is not valid in [ll_mix2] *)

Lemma mix2_not_mix0 : ll_mix2 nil -> False.
Proof.
intros pi.
remember nil as l.
revert Heql ; induction pi ; intros Heql ; subst ; try inversion Heql.
- apply IHpi.
  simpl in p ; apply Permutation_Type_sym in p.
  apply Permutation_Type_nil in p.
  assumption.
- apply app_eq_nil in Heql ; destruct Heql as [Heql Heql2].
  apply app_eq_nil in Heql2 ; destruct Heql2 as [Heql2 _] ; subst.
  destruct lw' ; inversion Heql2.
  symmetry in p ; apply Permutation_Type_nil in p ; subst.
  intuition.
- inversion f.
- apply IHpi2.
  apply app_eq_nil in Heql.
  apply Heql.
- inversion f.
- destruct a.
Qed.


(** ** Linear logic with both mix0 and mix2: [ll_mix02] (no axiom, commutative) *)

(** cut / axioms / mix0 / mix2 / permutation *)
Definition pfrag_mix02 := mk_pfrag false NoAxioms true true true.
(*                                 cut   axioms   mix0 mix2 perm  *)

Definition ll_mix02 := ll pfrag_mix02.

Lemma cut_mix02_r : forall A l1 l2,
  ll_mix02 (dual A :: l1) -> ll_mix02 (A :: l2) -> ll_mix02 (l2 ++ l1).
Proof with myeeasy.
intros A l1 l2 pi1 pi2.
eapply cut_r_axfree...
intros a ; destruct a.
Qed.

Lemma cut_mix02_admissible :
  forall l, ll (cutupd_pfrag pfrag_mix02 true) l -> ll_mix02 l.
Proof with myeeasy.
intros l pi.
induction pi ; try (now econstructor).
- eapply ex_r...
- eapply ex_wn_r...
- eapply cut_mix02_r...
Qed.

(** Provability in [ll_mix02] is equivalent to adding [wn (tens (wn one) (wn one))] in [ll] *)

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
  apply co_r.
  apply co_r.
  apply de_r.
  eapply ex_r.
  + apply tens_r ; apply wk_r ; [ apply pi1 | apply pi2 ].
  + rewrite fp...
Qed.

Lemma ll_to_mix02_cut {P} : forall l,
  ll P (wn (tens (wn one) (wn one)) :: l) -> ll (mk_pfrag true P.(pgax) true true P.(pperm)) l.
Proof with myeasy.
intros l pi.
eapply stronger_pfrag in pi.
- rewrite <- (app_nil_r l).
  eapply cut_r ; [ | | apply pi]...
  change nil with (map wn nil).
  apply oc_r.
  apply parr_r.
  change (oc bot :: oc bot :: map wn nil) with ((oc bot :: map wn nil) ++ oc bot :: map wn nil).
  eapply mix2_r...
  + apply oc_r.
    apply bot_r.
    apply mix0_r...
  + apply oc_r.
    apply bot_r.
    apply mix0_r...
- nsplit 5...
  + destruct pcut...
  + intros a.
    exists a...
  + destruct pmix0...
  + destruct pmix2...
Qed.

(** Provability in [ll_mix02] is equivalent to adding other stuff in [ll] *)

Lemma mix02_to_ll' {P} : pperm P = true -> forall b0 b2 bp l,
  ll (mk_pfrag P.(pcut) P.(pgax) b0 b2 bp) l -> ll P (wn one :: wn (tens bot bot) :: l).
Proof with myeasy.
intros Hperm b0 b2 bp l pi.
eapply mix0_to_ll...
eapply mix2_to_ll...
apply pi.
Qed.

Lemma ll_to_mix02'_axat {P} : (forall a, Forall atomic (projT2 (pgax P) a)) ->
  pperm P = true -> forall l,
  ll P (wn one :: wn (tens bot bot) :: l) -> ll (mix2add_pfrag (mix0add_pfrag P)) l.
Proof with myeasy.
intros Hgax Hperm l pi.
apply ll_to_mix2_axat...
apply ll_to_mix0_axat...
Qed.

Lemma mix02_to_ll'' {P} : pperm P = true -> forall b0 b2 bp l,
  ll (mk_pfrag P.(pcut) P.(pgax) b0 b2 bp) l -> ll P (wn one :: wn (tens (wn one) bot) :: l).
Proof with myeeasy ; try PCperm_Type_solve.
intros Hperm b0 b2 bp l pi.
eapply (ext_wn_param _ _ _ _ (one :: tens (wn one) bot :: nil)) in pi.
- eapply ex_r...
- intros Hcut...
- simpl ; intros a.
  eapply ex_r ; [ | apply PCperm_Type_app_comm ] ; list_simpl.
  apply wk_r.
  apply wk_r.
  apply gax_r.
- intros Hpmix0 Hpmix0'.
  apply de_r...
  eapply ex_r ; [ | apply PCperm_Type_swap ].
  apply wk_r.
  apply one_r.
- intros _ _ l1 l2 pi1 pi2.
  apply (ex_r _ (wn (tens (wn one) bot) :: (wn one :: l2) ++ l1)) ; [ | rewrite Hperm ]...
  apply co_r.
  apply co_r.
  apply de_r.
  apply (ex_r _ (tens (wn one) bot :: (wn (tens (wn one) bot) :: wn one :: l2)
                                   ++ (wn (tens (wn one) bot) :: l1))) ;
    [ | rewrite Hperm ]...
  apply tens_r.
  + eapply ex_r ; [ apply pi1 | ]...
  + apply bot_r ; eapply ex_r ; [ apply pi2 | rewrite Hperm ]...
Unshelve. assumption.
Qed.

(* Hgax_cut is here only to allow the use of cut_admissible
   the more general result without Hgax_cut should be provable by induction as for [ll_to_mix2] *)
Lemma ll_to_mix02''_axcut {P} : (forall a, Forall atomic (projT2 (pgax P) a)) ->
  (forall a b x l1 l2 l3 l4,
     projT2 (pgax P) a = (l1 ++ dual x :: l2) -> projT2 (pgax P) b = (l3 ++ x :: l4) ->
     { c | projT2 (pgax P) c = l3 ++ l2 ++ l1 ++ l4 }) ->
  pperm P = true -> forall l,
  ll P (wn one :: wn (tens (wn one) bot) :: l) -> ll (mix2add_pfrag (mix0add_pfrag P)) l.
Proof with myeasy.
intros Hgax_at Hgax_cut Hperm l pi.
apply (stronger_pfrag (cutrm_pfrag (cutupd_pfrag (mix2add_pfrag (mix0add_pfrag P)) true))).
{ nsplit 5...
  intros a ; exists a... }
eapply cut_admissible...
eapply stronger_pfrag in pi.
- rewrite <- (app_nil_r l).
  eapply (cut_r _ (wn (tens (wn one) bot))) ; simpl.
  + change nil with (map wn nil).
    apply oc_r.
    apply parr_r.
    change (one :: oc bot :: map wn nil) with ((one :: nil) ++ oc bot :: map wn nil).
    eapply mix2_r...
    * apply oc_r.
      apply bot_r.
      apply mix0_r...
    * apply one_r.
  + rewrite <- app_nil_r.
    eapply cut_r ; [ | | apply pi ] ; simpl...
    change nil with (map wn nil).
    apply oc_r.
    apply bot_r.
    apply mix0_r...
- etransitivity ; [ apply cutupd_pfrag_true| ].
  nsplit 5...
  + intros a ; exists a...
  + apply leb_true.
  + apply leb_true.
Unshelve. reflexivity.
Qed.

(* Hgax_cut is here only to allow the use of cut_admissible
   the more general result without Hgax_cut should be provable by induction as for [ll_to_mix2] *)
Lemma ll_to_mix02'''_axcut {P} : (forall a, Forall atomic (projT2 (pgax P) a)) ->
  (forall a b x l1 l2 l3 l4,
     projT2 (pgax P) a = (l1 ++ dual x :: l2) -> projT2 (pgax P) b = (l3 ++ x :: l4) ->
     { c | projT2 (pgax P) c = l3 ++ l2 ++ l1 ++ l4 }) ->
  pperm P = true -> forall l (l0 : list unit),
  ll P (wn one :: map (fun _ => wn (tens (wn one) bot)) l0 ++ l)  ->
  ll (mix2add_pfrag (mix0add_pfrag P)) l.
Proof with try assumption.
intros Hgax_at Hgax_cut Hperm l l0 pi.
apply ll_to_mix02''_axcut...
revert l pi ; induction l0 ; intros l pi.
- cons2app.
  eapply ex_r ; [ | rewrite Hperm ; apply Permutation_Type_app_comm ].
  simpl ; apply wk_r.
  eapply ex_r ; [ | rewrite Hperm ; apply Permutation_Type_app_comm ]...
- cons2app.
  eapply ex_r ; [ | rewrite Hperm ; apply Permutation_Type_app_comm ].
  simpl ; apply co_r.
  rewrite 2 app_comm_cons.
  eapply ex_r ; [ | rewrite Hperm ; apply Permutation_Type_app_comm ].
  list_simpl ; apply IHl0.
  list_simpl in pi.
  eapply ex_r ; [ apply pi | rewrite Hperm ; PCperm_Type_solve ].
Qed.


(** Provability in [ll_mix02] is equivalent to provability of [ll]
extended with the provability of both [bot :: bot :: nil] and [one :: one :: nil] *)

Lemma mix02_to_ll_one_eq_bot {P} : pcut P = true -> pperm P = true -> forall bc b0 b2 bp l,
  ll (mk_pfrag bc P.(pgax) b0 b2 bp) l ->
    ll (axupd_pfrag P (existT (fun x => x -> list formula) _
                              (fun a => match a with
                                        | inl x => projT2 (pgax P) x
                                        | inr true => one :: one :: nil
                                        | inr false => bot :: bot :: nil
                                        end))) l.
Proof with myeeasy ; try (unfold PCperm_Type ; PCperm_Type_solve).
remember (axupd_pfrag P (existT (fun x => x -> list formula) _
                                (fun a => match a with
                                          | inl x => projT2 (pgax P) x
                                          | inr true => one :: one :: nil
                                          | inr false => bot :: bot :: nil
                                          end))) as P'.
intros fc fp bc b0 b2 bp l pi.
eapply stronger_pfrag in pi.
- eapply mix02_to_ll in pi...
  assert (pcut P' = true) as fc' by (rewrite HeqP' ; simpl ; assumption).
  apply (stronger_pfrag _ P') in pi.
  + assert (ll P' (parr (oc bot) (oc bot) :: map wn nil)) as pi'.
    { apply parr_r.
      change (oc bot :: oc bot :: map wn nil)
        with ((oc bot :: nil) ++ oc bot :: map wn nil).
      eapply (@cut_r _ fc' one).
      - apply bot_r.
        apply oc_r.
        change (bot :: map wn nil) with ((bot :: nil) ++ nil).
        eapply (@cut_r _ fc' bot).
        + apply one_r.
        + assert ({ b | bot :: bot :: nil = projT2 (pgax P') b })
            as [b Hgax] by (rewrite HeqP' ; now (exists (inr false))).
          rewrite Hgax.
          apply gax_r.
      - change (one :: oc bot :: nil)
          with ((one :: nil) ++ oc bot :: map wn nil).
        eapply (@cut_r _ fc' one).
        + apply bot_r.
          apply oc_r.
          change (bot :: map wn nil) with ((bot :: nil) ++ nil).
          eapply (@cut_r _ fc' bot).
          * apply one_r.
          * assert ({ b | bot :: bot :: nil = projT2 (pgax P') b })
              as [b Hgax] by (rewrite HeqP' ; now (exists (inr false))).
            rewrite Hgax.
            apply gax_r.
        + assert ({ b | one :: one :: nil = projT2 (pgax P') b })
            as [b Hgax] by (rewrite HeqP' ; now (exists (inr true))).
          rewrite Hgax.
          apply gax_r. }
    apply oc_r in pi'.
    rewrite <- (app_nil_l l).
    eapply (@cut_r _ fc' (oc (parr (oc bot) (oc bot)))) ; [ simpl ; apply pi | apply pi' ].
  + nsplit 5 ; rewrite HeqP'...
    simpl ; intros a ; exists (inl a)...
- nsplit 5 ; intros ; simpl...
  + rewrite fc.
    destruct bc...
  + exists a...
Qed.

Lemma ll_one_eq_bot_to_mix02 {P} : forall l,
  ll (axupd_pfrag P (existT (fun x => x -> list formula) _
                            (fun a => match a with
                                      | inl x => projT2 (pgax P) x
                                      | inr true => one :: one :: nil
                                      | inr false => bot :: bot :: nil
                                      end))) l
  -> ll (mk_pfrag P.(pcut) P.(pgax) true true P.(pperm)) l.
Proof with myeeasy.
intros l pi.
remember (mk_pfrag P.(pcut) P.(pgax) true true P.(pperm)) as P'.
apply (stronger_pfrag _
  (axupd_pfrag P' (existT (fun x => x -> list formula) _
                          (fun a => match a with
                                    | inl x => projT2 (pgax P) x
                                    | inr true => one :: one :: nil
                                    | inr false => bot :: bot :: nil
                                    end)))) in pi.
- eapply ax_gen...
  clear - HeqP' ; simpl ; intros a.
  destruct a.
  + assert ({ b | projT2 (pgax P) p = projT2 (pgax P') b })
      as [b Hgax] by (rewrite HeqP' ; now exists p).
    rewrite Hgax.
    apply gax_r.
  + destruct b.
    * change (one :: one :: nil) with ((one :: nil) ++ one :: nil).
      rewrite HeqP'.
      apply mix2_r...
      -- apply one_r.
      -- apply one_r.
    * apply bot_r.
      apply bot_r.
      rewrite HeqP'.
      apply mix0_r...
- rewrite HeqP' ; nsplit 5 ; simpl ; intros...
  + exists a...
  + destruct (pmix0 P)...
  + destruct (pmix2 P)...
Qed.


(* llR *)

(** ** Linear logic extended with [R] = [bot]: [llR] *)

(** cut / axioms / mix0 / mix2 / permutation *)
Definition pfrag_llR R :=
  mk_pfrag true (existT (fun x => x -> list formula) _
                        (fun a => match a with
                                  | true => dual R :: nil
                                  | false => R :: one :: nil
                                  end))
             false false true.
(*         cut  axioms
             mix0  mix2  perm  *)

Definition llR R := ll (pfrag_llR R).

Lemma llR1_R2 : forall R1 R2,
  llR R2 (dual R1 :: R2 :: nil) -> llR R2 (dual R2 :: R1 :: nil) ->
    forall l, llR R1 l-> llR R2 l.
Proof with myeeasy.
intros R1 R2 HR1 HR2 l Hll.
induction Hll ; try (now constructor).
- eapply ex_r...
- eapply ex_wn_r...
- eapply cut_r...
- destruct a.
  + rewrite <- (app_nil_l _).
    apply (@cut_r (pfrag_llR R2) eq_refl (dual R2)).
    * rewrite bidual.
      eapply ex_r.
      apply HR1.
      apply PCperm_Type_swap.
    * assert ({ b | dual R2 :: nil = projT2 (pgax (pfrag_llR R2)) b })
        as [b Hgax] by (now exists true).
      rewrite Hgax.
      apply gax_r.
  + eapply (@cut_r (pfrag_llR R2) eq_refl R2) in HR2.
    * eapply ex_r ; [ apply HR2 | ].
      unfold PCperm_Type.
      simpl.
      apply Permutation_Type_sym.
      apply Permutation_Type_cons_app.
      rewrite app_nil_r.
      apply Permutation_Type_refl.
    * assert ({ b | R2 :: one :: nil = projT2 (pgax (pfrag_llR R2)) b })
        as [b Hgax] by (now exists false).
      rewrite Hgax.
      apply gax_r.
Qed.

Lemma ll_to_llR : forall R l, ll_ll l -> llR R l.
Proof with myeeasy.
intros R l pi.
induction pi ; try (now econstructor).
- eapply ex_r...
- eapply ex_wn_r...
Qed.

Lemma subs_llR : forall R C x l, llR R l -> llR (subs C x R) (map (subs C x) l).
Proof with myeeasy.
intros R C x l pi.
apply (subs_ll C x) in pi.
eapply stronger_pfrag in pi...
nsplit 5...
simpl ; intros a.
destruct a ; simpl.
- exists true.
  rewrite subs_dual...
- exists false...
Qed.

Lemma llR_to_ll : forall R l, llR R l-> ll_ll (l ++ wn R :: wn (tens (dual R) bot) :: nil).
Proof with myeasy.
intros R l pi.
apply cut_ll_admissible.
replace (wn R :: wn (tens (dual R) bot) :: nil) with (map wn (map dual (dual R :: parr one R :: nil)))
  by (simpl ; rewrite bidual ; reflexivity).
apply deduction_list...
eapply ax_gen ; [ | | | | | apply pi ]...
simpl ; intros a.
destruct a ; simpl.
- assert ({ b | dual R :: nil = projT2 (pgax (axupd_pfrag (cutupd_pfrag pfrag_ll true)
    (existT (fun x => x -> list formula) (sum _ {k : nat | k < 2})
            (fun a => match a with
                      | inl x => Empty_fun x
                      | inr x => match proj1_sig x with
                                 | 0 => dual R
                                 | 1 => parr one R
                                 | 2 => one
                                 | S (S (S _)) => one
                                 end :: nil
                      end)))) b })
    as [b Hgax] by (now exists (inr (exist _ 0 (le_n_S _ _ (le_S _ _ (le_n 0)))))).
  rewrite Hgax.
  apply gax_r.
- rewrite <- (app_nil_r nil).
  rewrite_all app_comm_cons.
  eapply (cut_r _ (dual (parr one R))).
  + rewrite bidual.
    assert ({ b | parr one R :: nil = projT2 (pgax (axupd_pfrag (cutupd_pfrag pfrag_ll true)
      (existT (fun x => x -> list formula) (sum _ {k : nat | k < 2})
              (fun a => match a with
                        | inl x => Empty_fun x
                        | inr x => match proj1_sig x with
                                   | 0 => dual R
                                   | 1 => parr one R
                                   | 2 => one
                                   | S (S (S _)) => one
                                   end :: nil
                        end)))) b })
      as [b Hgax] by (now exists (inr (exist _ 1 (le_n 2)))).
    erewrite Hgax.
    apply gax_r.
  + apply (ex_r _ (tens (dual R) bot :: (one :: nil) ++ R :: nil)) ; [ | PCperm_Type_solve ].
    apply tens_r.
    * eapply ex_r ; [ | apply PCperm_Type_swap ].
      eapply stronger_pfrag ; [ | apply ax_exp ].
      nsplit 5...
      simpl ; intros a.
      destruct a as [a | a].
      -- destruct a.
      -- destruct a as [n Hlt].
         destruct n ; simpl.
         ++ exists (inr (exist _ 0 Hlt))...
         ++ destruct n ; simpl.
            ** exists (inr (exist _ 1 Hlt))...
            ** exfalso.
               inversion Hlt ; subst.
               inversion H0 ; subst.
               inversion H1.
    * apply bot_r.
      apply one_r.
Unshelve. reflexivity.
Qed.

Lemma llwnR_to_ll : forall R l, llR (wn R) l -> ll_ll (l ++ wn R :: nil).
Proof with myeeasy.
intros R l pi.
apply llR_to_ll in pi.
eapply (ex_r _ _ (wn (tens (dual (wn R)) bot) :: l ++ wn (wn R) :: nil)) in pi ;
  [ | PCperm_Type_solve ].
eapply (cut_ll_r _ nil) in pi.
- eapply (cut_ll_r (wn (wn R))).
  + simpl.
    change (wn R :: nil) with (map wn (R :: nil)).
    apply oc_r ; simpl.
    replace (wn R) with (dual (oc (dual R))) by (simpl ; rewrite bidual ; reflexivity).
    apply ax_exp.
  + eapply ex_r ; [ apply pi | PCperm_Type_solve ].
- simpl ; rewrite bidual.
  change nil with (map wn nil).
  apply oc_r.
  apply parr_r.
  eapply ex_r ; [ apply wk_r ; apply one_r | PCperm_Type_solve ].
Qed.

Lemma ll_wn_wn_to_llR : forall R l, ll_ll (l ++ wn R :: wn (tens (dual R) bot) :: nil) -> llR R l.
Proof with myeasy.
intros R l pi.
apply (ll_to_llR R) in pi.
rewrite <- (app_nil_l l).
eapply (cut_r _ (oc (dual R))).
- rewrite <- (app_nil_l (dual _ :: l)).
  eapply (cut_r _ (oc (parr one R))).
  + simpl ; rewrite bidual ; eapply ex_r ; [apply pi | PCperm_Type_solve ].
  + change nil with (map wn nil).
    apply oc_r.
    apply parr_r.
    apply (ex_r _ (R :: one :: nil)).
    * assert ({ b | R :: one :: nil = projT2 (pgax (pfrag_llR R)) b })
        as [b Hgax] by (now exists false).
      rewrite Hgax.
      apply gax_r.
    * PCperm_Type_solve.
- change nil with (map wn nil).
  apply oc_r.
  assert ({ b | dual R :: map wn nil = projT2 (pgax (pfrag_llR R)) b })
    as [b Hgax] by (now exists true).
  rewrite Hgax.
  apply gax_r.
Unshelve. all : reflexivity.
Qed.

Lemma ll_wn_to_llwnR : forall R l, ll_ll (l ++ wn R :: nil) -> llR (wn R) l.
Proof with myeasy.
intros R l pi.
eapply ll_wn_wn_to_llR.
eapply (ex_r _ (wn (tens (dual (wn R)) bot) :: wn (wn R) :: l)) ;
  [ | PCperm_Type_solve ].
apply wk_r.
apply de_r.
eapply ex_r ; [ apply pi | PCperm_Type_solve ].
Qed.





