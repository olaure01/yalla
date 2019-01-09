(* ll_cut library for yalla *)

(** * Cut elimination for [ll] from cut elimination for [ill] *)


Require Import Arith.
Require Import Lia.

Require Import CyclicPerm_Type.
Require Import List_more.
Require Import List_Type_more.
Require Import Permutation_Type_more.
Require Import Permutation_Type_solve.
Require Import genperm_Type.
Require Import flat_map_Type_more.
Require Import wf_nat_more.

Require Export ll_def.
Require Import ll_mix.
Require Import subs.
Require Import ill_cut.
Require Import nn_def.


(** Ingredients for generating fresh variables *)
Definition a2n := yalla_ax.a2n.
Definition n2a := yalla_ax.n2a.
Definition n2n_a := yalla_ax.n2n_a.


(* TODO probably useless once cut elimination proved directly for LL
          then remove ill_cut / nn_def dependencies *)
Section CutElimTransfer.

Variable P : pfrag.
Hypothesis Hnogax : projT1 (pgax P) -> False.
Hypothesis Hperm : pperm P = true.  (* TODO generalize to the cyclic case *)

Theorem cut_elim_no_mix : pmix0 P = false -> pmix2 P = false -> forall A l1 l2,
ll P (dual A :: l1) -> ll P (A :: l2) -> ll P (l2 ++ l1).
Proof with myeasy.
intros Hmix0 Hmix2.
intros A l1 l2 pi1 pi2.
apply (stronger_pfrag _ _ (cutupd_pfrag_true _)) in pi1.
apply (stronger_pfrag _ _ (cutupd_pfrag_true _)) in pi2.
pose (nat_fresh_of_list a2n ((rev l1 ++ rev l2))) as z.
apply (ll_to_ill_trans (ivar (a2i (n2a z)))) in pi1 ;
  [ | assumption | simpl ; intros f ; rewrite f in Hmix0 ; inversion Hmix0
                 | simpl ; intros f ; rewrite f in Hmix2 ; inversion Hmix2 ].
apply (ll_to_ill_trans (ivar (a2i (n2a z)))) in pi2 ;
  [ | assumption | simpl ; intros f ; rewrite f in Hmix0 ; inversion Hmix0
                 | simpl ; intros f ; rewrite f in Hmix2 ; inversion Hmix2 ].
simpl in pi1 ; simpl in pi2.
apply negR_irr in pi1.
apply negR_irr in pi2.
assert (ipperm (cutupd_ipfrag (p2ipfrag (ivar (a2i (n2a z))) P) true) = true) as Hperm'
  by (simpl ; rewrite Hperm ; reflexivity).
assert (pi0 := trans_dual (ivar (a2i (n2a z))) Hperm' eq_refl A).
rewrite <- (app_nil_l _) in pi0.
eapply (cut_ir _ _ _ _ _ _ pi2) in pi0.
list_simpl in pi0.
eapply (cut_ir _ _ _ _ _ _ pi1) in pi0.
apply cut_admissible_ill in pi0 ; try (intros a ; exfalso ; apply (Hnogax a)).
apply (ill_to_ll i2a) in pi0.
list_simpl in pi0.
apply (subs_ll bot (n2a z)) in pi0.
list_simpl in pi0.
rewrite repl_at_eq in pi0 ; [ | rewrite a2a_i ; reflexivity ].
apply (ax_gen _ P) in pi0...
- rewrite <- app_nil_l in pi0.
  eapply bot_rev_axat in pi0 ; [ | intros a ; exfalso ; apply (Hnogax a) | reflexivity ]...
  list_simpl in pi0.
  apply (ex_r _ (rev l1 ++ rev l2)) ;
    [ | rewrite Hperm ; 
        rewrite <- rev_app_distr ;
        symmetry ; apply Permutation_Type_rev ].
  eapply munit_elim ; [ intros a ; exfalso ; apply (Hnogax a) | exact pi0 | ]...
  rewrite <- ? map_app.
  remember (rev l1 ++ rev l2) as l ; clear.
  assert (HF : Forall (fun x : formula => nat_fresh_of a2n x <= z) l).
  { assert (Hle : nat_fresh_of_list a2n l <= z)
      by (unfold z ; unfold nat_fresh_of_list ; list_simpl ; myeasy).
    clearbody z ; revert Hle ; clear.
    unfold nat_fresh_of_list.
    revert z ; induction l ; intros z Hle ; constructor.
    - simpl in Hle...
    - apply IHl ; simpl in Hle... }
  clearbody z ; revert HF ; induction l ; intros HF ; constructor.
  + rewrite <- (yalla_ax.a2a_n z).
    apply munit_trans.
    rewrite yalla_ax.a2a_n.
    inversion HF ; simpl...
  + apply IHl.
    inversion HF ; subst ; assumption.
- intros a ; exfalso ; apply (Hnogax a).
Unshelve. all: reflexivity.
Qed.

Lemma cut_elim_with_wn : pmix0 P = false -> pmix2 P = false -> forall A l1 l2 l0,
  ll P (dual A :: l1 ++ map wn l0) -> ll P (A :: l2 ++ map wn l0) ->
  ll P (l2 ++ l1 ++ map wn l0).
Proof with myeeasy.
intros Hmix0 Hmix2.
intros A l1 l2 l0 pi1 pi2.
eapply ex_r ; [ | rewrite Hperm ; rewrite app_assoc ; apply Permutation_Type_app_swap ].
apply co_list_r.
eapply ex_r ; [ | rewrite Hperm ; apply Permutation_Type_app_swap ].
list_simpl ; rewrite app_assoc.
eapply cut_elim_no_mix...
eapply ex_r...
rewrite Hperm ; simpl ; perm_Type_solve.
Qed.

End CutElimTransfer.


Section CutElimTransfer2.

Variable P : pfrag.
Hypothesis Hnogax : projT1 (pgax P) -> False.
Hypothesis Hperm : pperm P = true.  (* TODO generalize to the cyclic case *)

Theorem cut_elim_mix0 : pmix0 P = true -> pmix2 P = false -> forall A l1 l2,
  ll P (dual A :: l1) -> ll P (A :: l2) -> ll P (l2 ++ l1).
Proof with myeeasy.
intros Hmix0 Hmix2.
intros A l1 l2 pi1 pi2.
pose (Q := mk_pfrag P.(pcut) P.(pgax) false P.(pmix2) true).
assert (P = mix0add_pfrag Q) as HP.
{ destruct P ; unfold mix0add_pfrag ; simpl.
  simpl in Hmix0 ; rewrite Hmix0.
  simpl in Hperm ; rewrite Hperm... }
rewrite HP in pi1.
apply mix0_to_ll in pi1...
rewrite HP in pi2.
apply mix0_to_ll in pi2...
eapply ex_r in pi1 ; [ | apply Permutation_Type_cons_append ].
rewrite <- app_comm_cons in pi1.
eapply ex_r in pi2 ; [ | apply Permutation_Type_cons_append ].
rewrite <- app_comm_cons in pi2.
rewrite HP.
apply ll_to_mix0...
- intros a ; exfalso ; apply (Hnogax a).
- apply (ex_r _ (l2 ++ l1 ++ map wn (one :: nil))) ; [ | simpl ; perm_Type_solve ].
  eapply cut_elim_with_wn...
Qed.

Theorem cut_elim_mix2 : pmix0 P = false -> pmix2 P = true -> forall A l1 l2,
  ll P (dual A :: l1) -> ll P (A :: l2) -> ll P (l2 ++ l1).
Proof with myeeasy.
intros Hmix0 Hmix2.
intros A l1 l2 pi1 pi2.
pose (Q := mk_pfrag P.(pcut) P.(pgax) P.(pmix0) false true).
assert (P = mix2add_pfrag Q) as HP.
{ destruct P ; unfold mix2add_pfrag ; simpl.
  simpl in Hmix2 ; rewrite Hmix2.
  simpl in Hperm ; rewrite Hperm... }
rewrite HP in pi1.
apply mix2_to_ll in pi1...
rewrite HP in pi2.
apply mix2_to_ll in pi2...
eapply ex_r in pi1 ; [ | apply Permutation_Type_cons_append ].
rewrite <- app_comm_cons in pi1.
eapply ex_r in pi2 ; [ | apply Permutation_Type_cons_append ].
rewrite <- app_comm_cons in pi2.
rewrite HP.
apply ll_to_mix2...
- intros a ; exfalso ; apply (Hnogax a).
- apply (ex_r _ (l2 ++ l1 ++ map wn (tens bot bot :: nil))) ; [ | simpl ; perm_Type_solve ].
  eapply cut_elim_with_wn...
Qed.

Theorem cut_elim_mix02 : pmix0 P = true -> pmix2 P = true -> forall A l1 l2,
  ll P (dual A :: l1) -> ll P (A :: l2) -> ll P (l2 ++ l1).
Proof with myeeasy.
intros Hmix0 Hmix2.
intros A l1 l2 pi1 pi2.
pose (Q := mk_pfrag P.(pcut) P.(pgax) false false true).
assert (P = mix2add_pfrag (mix0add_pfrag Q)) as HP.
{ destruct P ; unfold mix2add_pfrag ; simpl.
  simpl in Hmix0 ; rewrite Hmix0.
  simpl in Hmix2 ; rewrite Hmix2.
  simpl in Hperm ; rewrite Hperm... }
rewrite HP in pi1.
apply (@mix02_to_ll' Q) in pi1...
rewrite HP in pi2.
apply (@mix02_to_ll' Q) in pi2...
eapply ex_r in pi1 ; [ | apply Permutation_Type_cons_append ].
rewrite <- app_comm_cons in pi1.
eapply ex_r in pi1 ; [ | apply Permutation_Type_cons_append ].
list_simpl in pi1.
eapply ex_r in pi2 ; [ | apply Permutation_Type_cons_append ].
rewrite <- app_comm_cons in pi2.
eapply ex_r in pi2 ; [ | apply Permutation_Type_cons_append ].
list_simpl in pi2.
rewrite HP.
apply ll_to_mix02...
- intros a ; exfalso ; apply (Hnogax a).
- apply (ex_r _ (l2 ++ l1 ++ map wn (one :: tens bot bot :: nil))) ; [ | simpl ; perm_Type_solve ].
  eapply cut_elim_with_wn...
Qed.


Theorem cut_elim_perm : forall A l1 l2,
  ll P (dual A :: l1) -> ll P (A :: l2) -> ll P (l2 ++ l1).
Proof with myeasy.
case_eq (pcut P) ; intros Hcut.
- apply cut_r...
- case_eq (pmix0 P) ; case_eq (pmix2 P) ; intros Hmix2 Hmix0.
  + apply cut_elim_mix02...
  + apply cut_elim_mix0...
  + apply cut_elim_mix2...
  + apply cut_elim_no_mix...
Qed.

End CutElimTransfer2.

(*
Theorem cut_elim :
  forall P,
  forall P_gax_atomic : forall a, Forall atomic (projT2 (pgax P) a),
  (forall a l, PCperm_Type (pperm P) (projT2 (pgax P) a) l -> exists b, l = projT2 (pgax P) b) ->
  (forall a b x l1 l2 l3, projT2 (pgax P) a = (dual x :: l1) -> projT2 (pgax P) b = (l2 ++ x :: l3) ->
     exists c, projT2 (pgax P) c = l2 ++ l1 ++ l3) ->
  forall A l1 l2 l3,
  ll P (dual A :: l1) -> ll P (l2 ++ A :: l3) -> ll P (l2 ++ l1 ++ l3).
Proof.
intros P.
case_eq (pperm P).
- intros Hperm Hgax_at Hgax_ex Hgax_cut A l1 l2 l3 pi1 pi2.
  eapply ex_r in pi2 ; [ | rewrite Hperm ; apply Permutation_Type_app_swap ].
  rewrite <- app_comm_cons in pi2.
  eapply ex_r ; [ | rewrite Hperm ; apply Permutation_Type_app_rot ].
  rewrite app_assoc.
  refine (cut_elim_perm _ _ _ _ _ A _ _ _ _) ; try assumption.
  rewrite Hperm ; assumption.
- intros Hperm Hgax_at Hgax_ex Hgax_cut A l1 l2 l3 pi1 pi2.
  refine (cut_elim_cyclic _ _ _ _ _ A _ _ _ _ _) ; try assumption.
  rewrite Hperm ; assumption.
Qed.
*)


Section Cut_Elim_Proof.

Context {P : pfrag}.

Hypothesis P_gax_at : forall a, Forall atomic (projT2 (pgax P) a).

Lemma cut_oc_comm : pcut P = false -> forall n A l1 l2, ll P (l1 ++ wn A :: l2) -> 
  (forall lw (pi0 : ll P (dual A :: map wn lw)), psize pi0 < n -> ll P (l1 ++ map wn lw ++ l2)) ->
  forall l3 l4 (pi1 : ll P (l3 ++ oc (dual A) :: l4)), psize pi1 <= n -> ll P (l1 ++ l4 ++ l3 ++ l2).
Proof with myeasy_perm_Type.
intros P_cutfree n A l1 l2 pi2 ; induction n ; intros IH l3 l4 pi1 Hs ;
  remember (l3 ++ oc (dual A) :: l4) as l ; destruct_ll pi1 f X l Hl Hr HP Hax a ;
  try (exfalso ; simpl in Hs ; clear -Hs ; lia ; fail) ; try inversion Heql ; subst.
- destruct l3 ; inversion Heql ; subst.
  destruct l3 ; inversion H2 ; subst.
  destruct l3 ; inversion H3.
- simpl in Hs.
  apply PCperm_Type_vs_elt_inv in HP.
  destruct HP as [[l3' l4'] Heq HP] ; simpl in Heq ; simpl in HP ; subst.
  assert (PEperm_Type (pperm P) (l1 ++ l4' ++ l3' ++ l2) (l1 ++ l4 ++ l3 ++ l2)) as HP'.
  { apply PEperm_Type_app_head.
    rewrite 2 app_assoc ; apply PEperm_Type_app_tail.
    symmetry... }
  apply PEperm_PCperm_Type in HP'.
  apply (ex_r _ (l1 ++ l4' ++ l3' ++ l2))...
  simpl in Hs ; refine (IHn _ _ _ Hl _)...
  intros ; refine (IH _ pi0 _)...
- symmetry in H0 ; trichot_Type_elt_app_exec H0 ; subst.
  + list_simpl ; rewrite app_assoc.
    eapply ex_wn_r...
    revert Hl Hs ; list_simpl ; intros Hl Hs.
    rewrite (app_assoc l5) ; rewrite (app_assoc _ l0) ; rewrite <- (app_assoc l5).
    refine (IHn _ _ _ Hl _)...
    intros ; refine (IH _ pi0 _)...
  + destruct H2 as [H2 H3] ; simpl in H2 ; decomp_map_Type H2.
    inversion H2.
  + list_simpl ; rewrite 2 app_assoc.
    eapply ex_wn_r...
    revert Hl Hs ; simpl ; rewrite 2 app_assoc ; intros Hl Hs.
    list_simpl ; rewrite (app_assoc l) ; rewrite (app_assoc _ l6).
    refine (IHn _ _ _ Hl _)...
    intros ; refine (IH _ pi0 _)...
- destruct l3 ; inversion H0.
- dichot_Type_elt_app_exec H0 ; subst.
  + list_simpl.
    eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    apply mix2_r...
    eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    simpl in Hs ; refine (IHn _ _ _ Hr _)...
    intros ; refine (IH _ pi0 _)...
  + eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    apply mix2_r...
    eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    simpl in Hs ; refine (IHn _ _ _ Hl _)...
    intros ; refine (IH _ pi0 _)...
- destruct l3 ; inversion H0.
  destruct l3 ; inversion H2.
- destruct l3 ; inversion H0 ; subst.
  eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  apply bot_r...
  eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  simpl in Hs ; refine (IHn _ _ _ Hl _)...
  intros ; refine (IH _ pi0 _)...
- destruct l3 ; inversion H0 ; subst.
  dichot_Type_elt_app_exec H2 ; subst.
  + list_simpl.
    eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    rewrite app_comm_cons ; eapply ex_r ; [ | symmetry ; apply PCperm_Type_app_rot ] ; list_simpl.
    rewrite 3 app_assoc ; apply tens_r...
    list_simpl ; rewrite app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    revert Hr Hs ; simpl ; rewrite (app_comm_cons _ _ B) ; intros Hr Hs.
    refine (IHn _ _ _ Hr _)...
    intros ; refine (IH _ pi0 _)...
  + eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    apply tens_r...
    list_simpl ; rewrite app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    revert Hl Hs ; simpl ; rewrite (app_comm_cons _ _ A0) ; intros Hl Hs.
    refine (IHn _ _ _ Hl _)...
    intros ; refine (IH _ pi0 _)...
- destruct l3 ; inversion H0 ; subst.
  eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  apply parr_r...
  rewrite 2 app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  revert Hl Hs ; simpl ; rewrite (app_comm_cons _ _ B) ; rewrite (app_comm_cons _ _ A0) ; intros Hl Hs.
  simpl in Hs ; refine (IHn _ _ _ Hl _) ; simpl...
  intros ; refine (IH _ pi0 _)...
- destruct l3 ; inversion H0 ; subst.
  eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  apply top_r...
- destruct l3 ; inversion H0 ; subst.
  eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  apply plus_r1...
  rewrite app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  revert Hl Hs ; simpl ; rewrite (app_comm_cons _ _ A0) ; intros Hl Hs.
  simpl in Hs ; refine (IHn _ _ _ Hl _) ; simpl...
  intros ; refine (IH _ pi0 _)...
- destruct l3 ; inversion H0 ; subst.
  eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  apply plus_r2...
  rewrite app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  revert Hl Hs ; simpl ; rewrite (app_comm_cons _ _ A0) ; intros Hl Hs.
  simpl in Hs ; refine (IHn _ _ _ Hl _) ; simpl...
  intros ; refine (IH _ pi0 _)...
- destruct l3 ; inversion H0 ; subst.
  eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  apply with_r...
  + rewrite app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    revert Hl Hs ; simpl ; rewrite (app_comm_cons _ _ A0) ; intros Hl Hs.
    simpl in Hs ; refine (IHn _ _ _ Hl _) ; simpl...
    intros ; refine (IH _ pi0 _)...
  + rewrite app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    revert Hr Hs ; simpl ; rewrite (app_comm_cons _ _ B) ; intros Hr Hs.
    simpl in Hs ; refine (IHn _ _ _ Hr _) ; simpl...
    intros ; refine (IH _ pi0 _)...
- destruct l3 ; inversion H0 ; subst.
  + refine (IH _ _ _)...
  + symmetry in H2 ; decomp_map_Type H2.
    inversion H2.
- destruct l3 ; inversion H0 ; subst.
  eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  apply de_r...
  rewrite app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  revert Hl Hs ; simpl ; rewrite (app_comm_cons _ _ A0) ; intros Hl Hs.
  simpl in Hs ; refine (IHn _ _ _ Hl _) ; simpl...
  intros ; refine (IH _ pi0 _)...
- destruct l3 ; inversion H0 ; subst.
  eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  apply wk_r...
  eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  simpl in Hs ; refine (IHn _ _ _ Hl _) ; simpl...
  intros ; refine (IH _ pi0 _)...
- destruct l3 ; inversion H0 ; subst.
  eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  apply co_r...
  rewrite 2 app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
  revert Hl Hs ; simpl ; rewrite 2 (app_comm_cons _ _ (wn A0)) ; intros Hl Hs.
  simpl in Hs ; refine (IHn _ _ _ Hl _) ; simpl...
  intros ; refine (IH _ pi0 _)...
- rewrite f in P_cutfree ; inversion P_cutfree.
- exfalso.
  assert (Hat := P_gax_at a) ; rewrite H0 in Hat.
  apply Forall_app_inv in Hat ; destruct Hat as [_ Hat] ; inversion Hat.
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
  + destruct (perm_Type_app_flat_map _ (map wn lw) _ _ _ p) as [[L' l''] (Hnil' & HeqL' & HPL')] ;
      simpl in Hnil' ; simpl in HeqL' ; simpl in HPL' ; subst.
    eapply ex_r ; [ | rewrite Hperm ; simpl ; apply HPL' ].
    apply IHpi2...
  + destruct (cperm_Type_app_flat_map _ (map wn lw) _ _ _ p) as [[L' l''] (Hnil' & HeqL' & HPL')] ;
      simpl in Hnil' ; simpl in HeqL' ; simpl in HPL' ; subst.
    eapply ex_r ; [ | rewrite Hperm ; simpl ; apply HPL' ].
    apply IHpi2...
- (* TODO factorize almost identical case in ill_cut.v *)
  app_vs_app_flat_map_inv Heq.
  + app_vs_app_flat_map_inv Heq1.
    * list_simpl ; eapply ex_wn_r...
      rewrite 2 app_assoc.
      apply IHpi2 ; list_simpl...
    * destruct (perm_Type_f_app_flat_map _ wn lw _ _ _ _ p Heq2) as [[L' l'] (Hnil' & HeqL' & HPL')] ;
        simpl in Hnil' ; simpl in HeqL' ; simpl in HPL'.
      rewrite flat_map_app ; list_simpl.
      rewrite (app_assoc l) ; rewrite (app_assoc (map wn lw)) ; rewrite (app_assoc _ _ (l3 ++ _)).
      rewrite <- (app_assoc l).
      replace (l ++ flat_map (app (map wn lw)) L0 ++ map wn lw ++ l0)
         with (l ++ flat_map (app (map wn lw)) (L0 ++ l0 :: nil))
        by (rewrite flat_map_app ; list_simpl ; reflexivity).
      destruct (map_f_flat_map _ wn lw _ _ _ Heq2) as [Lw HeqLw].
      destruct (map_f_flat_map _ wn lw _ _ _ HeqL') as [Lw' HeqLw'].
      assert (Permutation_Type Lw' Lw) as HPw.
      { rewrite HeqLw in HPL' ; rewrite HeqLw' in HPL'.
        apply Permutation_Type_map_inv_inj in HPL' ;
          [ | intros x y Heq ; inversion Heq ; subst ; reflexivity ]... }
      rewrite HeqLw ; apply (ex_wn_r _ _ Lw')...
      rewrite <- HeqLw'.
      induction L' using rev_ind_Type ;
        [ exfalso ; apply Hnil' ; [ intros Heqnil ; destruct L0 ; inversion Heqnil | reflexivity ]
        | clear IHL' ].
      rewrite HeqL' in IHpi2 ; rewrite (app_assoc _ l3 _) in IHpi2 ; rewrite <- (app_assoc _ _ l3) in IHpi2.
      replace (flat_map (cons (wn A)) (L' ++ x :: nil) ++ l3)
         with (flat_map (cons (wn A)) (L' ++ (x ++ l3) :: nil)) in IHpi2
        by (rewrite ? flat_map_app ; list_simpl ; reflexivity).
      list_simpl in IHpi2 ; rewrite <- flat_map_app in IHpi2 ; rewrite app_assoc in IHpi2.
      assert (pi2' := IHpi2 _ _ eq_refl).
      rewrite ? flat_map_app ; list_simpl ; rewrite ? flat_map_app in pi2' ; list_simpl in pi2'...
    * destruct (perm_Type_f_app_flat_map _ wn lw _ _ _ _ p Heq2) as [[L' l'] (Hnil' & HeqL' & HPL')] ;
        simpl in Hnil' ; simpl in HeqL' ; simpl in HPL'.
      rewrite flat_map_app ; list_simpl.
      rewrite (app_assoc l).
      destruct (map_f_flat_map _ wn lw _ _ _ Heq2) as [Lw HeqLw].
      destruct (map_f_flat_map _ wn lw _ _ _ HeqL') as [Lw' HeqLw'].
      assert (Permutation_Type Lw' Lw) as HPw.
      { rewrite HeqLw in HPL' ; rewrite HeqLw' in HPL'.
        apply Permutation_Type_map_inv_inj in HPL' ;
          [ | intros x y Heq ; inversion Heq ; subst ; reflexivity ]... }
      rewrite HeqLw ; apply (ex_wn_r _ _ Lw')...
      rewrite <- HeqLw'.
      rewrite HeqL' in IHpi2 ; list_simpl in IHpi2 ; rewrite <- flat_map_app in IHpi2 ;
        rewrite app_assoc in IHpi2.
      assert (pi2' := IHpi2 _ _ eq_refl).
      rewrite ? flat_map_app ; list_simpl ; rewrite ? flat_map_app in pi2' ; list_simpl in pi2'...
  + app_vs_app_flat_map_inv Heq2.
    * rewrite flat_map_app.
      list_simpl ; rewrite 3 app_assoc ; eapply ex_wn_r...
      rewrite <- 3 app_assoc.
      replace (map wn lw ++ l ++ map wn lw0 ++ l1 ++ flat_map (app (map wn lw)) L1)
         with (flat_map (app (map wn lw)) ((l ++ map wn lw0 ++ l1) :: L1)) by (list_simpl ; reflexivity).
      rewrite <- flat_map_app ; refine (IHpi2 _ _ _)...
      rewrite ? flat_map_app ; list_simpl...
    * destruct (perm_Type_f_app_flat_map _ wn lw _ _ _ _ p Heq1) as [[L' l''] (Hnil' & HeqL' & HPL')] ;
        simpl in Hnil' ; simpl in HeqL' ; simpl in HPL'.
      rewrite ? flat_map_app ; list_simpl ; rewrite ? flat_map_app ; list_simpl.
      rewrite (app_assoc l0) ; rewrite (app_assoc _ _ (l1 ++ _)) ; rewrite (app_assoc _ l1).
      replace (((l0 ++ flat_map (app (map wn lw)) L) ++ map wn lw) ++ l1)
         with (l0 ++ flat_map (app (map wn lw)) (L ++ l1 :: nil))
        by (rewrite flat_map_app ; list_simpl ; reflexivity).
      destruct (map_f_flat_map _ wn lw _ _ _ Heq1) as [Lw HeqLw].
      destruct (map_f_flat_map _ wn lw _ _ _ HeqL') as [Lw' HeqLw'].
      assert (Permutation_Type Lw' Lw) as HPw.
      { rewrite HeqLw in HPL' ; rewrite HeqLw' in HPL'.
        apply Permutation_Type_map_inv_inj in HPL' ;
          [ | intros x y Heq ; inversion Heq ; subst ; reflexivity ]... }
      rewrite HeqLw ; rewrite 3 app_assoc ; apply (ex_wn_r _ _ Lw')...
      rewrite <- HeqLw'.
      induction L' using rev_ind_Type ;
        [ exfalso ; apply Hnil' ; [ intros Heqnil ; destruct L ; inversion Heqnil | reflexivity ]
        | clear IHL' ].
      rewrite HeqL' in IHpi2 ; rewrite (app_assoc _ l3 _) in IHpi2 ; rewrite <- (app_assoc _ _ l3) in IHpi2.
      replace (flat_map (cons (wn A)) (L' ++ x :: nil) ++ l3)
         with (flat_map (cons (wn A)) (L' ++ (x ++ l3) :: nil)) in IHpi2
        by (rewrite ? flat_map_app ; list_simpl ; reflexivity).
      rewrite 2 app_assoc in IHpi2 ; rewrite <- (app_assoc l') in IHpi2.
      replace (flat_map (cons (wn A)) (L0 ++ l :: nil) ++ l'')
         with (flat_map (cons (wn A)) (L0 ++ (l ++ l'') :: nil)) in IHpi2
        by (rewrite ? flat_map_app ; list_simpl ; reflexivity).
      list_simpl in IHpi2 ; rewrite <- 2 flat_map_app in IHpi2.
      assert (pi2' := IHpi2 _ _ eq_refl).
      rewrite ? flat_map_app ; list_simpl ; rewrite ? flat_map_app in pi2' ; list_simpl in pi2'...
    * destruct (perm_Type_f_app_flat_map _ wn lw _ _ _ _ p Heq1) as [[L' l''] (Hnil' & HeqL' & HPL')] ;
        simpl in Hnil' ; simpl in HeqL' ; simpl in HPL'.
      rewrite flat_map_app ; list_simpl.
      rewrite (app_assoc l).
      destruct (map_f_flat_map _ wn lw _ _ _ Heq1) as [Lw HeqLw].
      destruct (map_f_flat_map _ wn lw _ _ _ HeqL') as [Lw' HeqLw'].
      assert (Permutation_Type Lw' Lw) as HPw.
      { rewrite HeqLw in HPL' ; rewrite HeqLw' in HPL'.
        apply Permutation_Type_map_inv_inj in HPL' ;
          [ | intros x y Heq ; inversion Heq ; subst ; reflexivity ]... }
      rewrite flat_map_app ; list_simpl ; rewrite (app_assoc l0).
      rewrite HeqLw ; rewrite 3 app_assoc ; apply (ex_wn_r _ _ Lw')...
      rewrite <- HeqLw'.
      rewrite HeqL' in IHpi2 ; list_simpl in IHpi2 ; rewrite <- flat_map_app in IHpi2.
      replace (flat_map (cons (wn A)) (L0 ++ l :: nil) ++ l'' ++ flat_map (cons (wn A)) (L' ++ L2))
         with (flat_map (cons (wn A)) (L0 ++ (l ++ l'') :: L' ++ L2))
        in IHpi2 by (rewrite ? flat_map_app ; list_simpl ; rewrite ? flat_map_app ; reflexivity).
      assert (pi2' := IHpi2 _ _ eq_refl).
      rewrite ? flat_map_app in pi2' ; list_simpl in pi2' ; rewrite ? flat_map_app in pi2'.
      rewrite ? flat_map_app ; list_simpl...
  + app_vs_flat_map_inv Heq2.
    * rewrite <- (app_nil_l (flat_map _ _)) in Heq1.
      destruct (perm_Type_f_app_flat_map _ wn lw _ _ _ _ p Heq1) as [[L' l''] (Hnil' & HeqL' & HPL')] ;
        simpl in Hnil' ; simpl in HeqL' ; simpl in HPL'.
      rewrite ? flat_map_app ; list_simpl ; rewrite ? flat_map_app ; list_simpl.
      rewrite (app_assoc _ _ (l ++ _)) ; rewrite (app_assoc _ l).
      replace (((flat_map (app (map wn lw)) L) ++ map wn lw) ++ l)
         with (flat_map (app (map wn lw)) (L ++ l :: nil))
        by (rewrite flat_map_app ; list_simpl ; reflexivity).
      destruct (map_f_flat_map _ wn lw _ _ _ Heq1) as [Lw HeqLw] ; list_simpl in HeqLw.
      destruct (map_f_flat_map _ wn lw _ _ _ HeqL') as [Lw' HeqLw'].
      assert (Permutation_Type Lw' Lw) as HPw.
      { rewrite HeqLw in HPL' ; rewrite HeqLw' in HPL'.
        apply Permutation_Type_map_inv_inj in HPL' ;
          [ | intros x y Heq ; inversion Heq ; subst ; reflexivity ]... }
      rewrite HeqLw ; rewrite app_assoc ; apply (ex_wn_r _ _ Lw')...
      rewrite <- HeqLw'.
      induction L' using rev_ind_Type ;
        [ exfalso ; apply Hnil' ; [ intros Heqnil ; destruct L ; inversion Heqnil | reflexivity ]
        | clear IHL' ].
      rewrite HeqL' in IHpi2.
      induction L0 using rev_ind_Type ; [ | clear IHL0 ].
      -- simpl in IHpi2 ; rewrite (app_assoc _ l0 _) in IHpi2 ; rewrite <- (app_assoc _ _ l0) in IHpi2.
         replace (flat_map (cons (wn A)) (L' ++ x :: nil) ++ l0)
            with (flat_map (cons (wn A)) (L' ++ (x ++ l0) :: nil)) in IHpi2
           by (rewrite ? flat_map_app ; list_simpl ; reflexivity).
         rewrite <- ? app_assoc in IHpi2 ; rewrite <- flat_map_app in IHpi2.
         rewrite 2 app_assoc in IHpi2.
         assert (pi2' := IHpi2 _ _ eq_refl).
         rewrite ? flat_map_app ; list_simpl ; rewrite ? flat_map_app in pi2' ; list_simpl in pi2'...
      -- rewrite 3 app_assoc in IHpi2 ; rewrite <- (app_assoc _ _ l'') in IHpi2.
         replace (flat_map (cons (wn A)) (L0 ++ x0 :: nil) ++ l'')
            with (flat_map (cons (wn A)) (L0 ++ (x0 ++ l'') :: nil)) in IHpi2
           by (rewrite ? flat_map_app ; list_simpl ; reflexivity).
         rewrite <- (app_assoc _ _ l0) in IHpi2.
         replace (flat_map (cons (wn A)) (L' ++ x :: nil) ++ l0)
            with (flat_map (cons (wn A)) (L' ++ (x ++ l0) :: nil)) in IHpi2
           by (rewrite ? flat_map_app ; list_simpl ; reflexivity).
         rewrite <- 2 app_assoc in IHpi2 ; rewrite <- 2 flat_map_app in IHpi2.
         assert (pi2' := IHpi2 _ _ eq_refl).
         rewrite ? flat_map_app ; list_simpl ; rewrite ? flat_map_app in pi2' ; list_simpl in pi2'...
    * rewrite <- (app_nil_l (flat_map _ _)) in Heq1.
      destruct (perm_Type_f_app_flat_map _ wn lw _ _ _ _ p Heq1) as [[L' l''] (Hnil' & HeqL' & HPL')] ;
        simpl in Hnil' ; simpl in HeqL' ; simpl in HPL'.
      rewrite ? flat_map_app ; list_simpl ; rewrite ? flat_map_app ; list_simpl.
      destruct (map_f_flat_map _ wn lw _ _ _ Heq1) as [Lw HeqLw] ; list_simpl in HeqLw.
      destruct (map_f_flat_map _ wn lw _ _ _ HeqL') as [Lw' HeqLw'].
      assert (Permutation_Type Lw' Lw) as HPw.
      { rewrite HeqLw in HPL' ; rewrite HeqLw' in HPL'.
        apply Permutation_Type_map_inv_inj in HPL' ;
          [ | intros x y Heq ; inversion Heq ; subst ; reflexivity ]... }
      rewrite HeqLw ; rewrite app_assoc ; apply (ex_wn_r _ _ Lw')...
      rewrite <- HeqLw'.
      rewrite HeqL' in IHpi2.
      induction L0 using rev_ind_Type ; [ | clear IHL0 ].
      -- list_simpl in IHpi2 ; rewrite app_assoc in IHpi2 ; rewrite <- flat_map_app in IHpi2.
         assert (pi2' := IHpi2 _ _ eq_refl).
         rewrite ? flat_map_app ; list_simpl ; rewrite ? flat_map_app in pi2' ; list_simpl in pi2'...
      -- rewrite app_assoc in IHpi2 ; rewrite (app_assoc _ l'') in IHpi2 ;
           rewrite <- (app_assoc _ _ l'') in IHpi2.
         replace (flat_map (cons (wn A)) (L0 ++ x :: nil) ++ l'')
            with (flat_map (cons (wn A)) (L0 ++ (x ++ l'') :: nil)) in IHpi2
           by (rewrite ? flat_map_app ; list_simpl ; reflexivity).
         list_simpl in IHpi2 ; rewrite <- 2 flat_map_app in IHpi2.
         assert (pi2' := IHpi2 _ _ eq_refl).
         rewrite ? flat_map_app ; list_simpl ; rewrite ? flat_map_app in pi2' ; list_simpl in pi2'...
- symmetry in Heq.
  apply app_eq_nil in Heq.
  destruct Heq as [Heq' Heq] ; subst.
  destruct L ; inversion Heq.
  list_simpl ; apply mix0_r...
- app_vs_app_flat_map_inv Heq.
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
  app_vs_app_flat_map_inv H1.
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
    - simpl in Heq ; symmetry in Heq ; decomp_map_Type Heq ; subst.
      inversion Heq3 ; subst ; simpl.
      rewrite Heq5 in IHL ; list_simpl in IHL.
      rewrite app_comm_cons in IHL ; rewrite app_assoc in IHL.
      destruct (IHL _ eq_refl) as [Lw Heq'].
      exists (lw ++ l4 ++ Lw) ; list_simpl ; rewrite <- Heq'... }
  symmetry in H1 ; decomp_map_Type H1 ; subst.
  list_simpl ; rewrite HeqLw ; rewrite <- map_app ; apply oc_r.
  list_simpl in IHpi2 ; simpl in H3 ; rewrite <- H3 in IHpi2.
  list_simpl ; rewrite <- HeqLw ;rewrite app_comm_cons ; apply IHpi2...
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
    apply Forall_app_inv in P_gax_at.
    destruct P_gax_at as [_ Hat].
    inversion Hat ; inversion H1.
Qed.


Hypothesis P_gax_cut : forall a b x l1 l2 l3 l4,
  projT2 (pgax P) a = (l1 ++ dual x :: l2) -> projT2 (pgax P) b = (l3 ++ x :: l4) ->
  { c | projT2 (pgax P) c = l3 ++ l2 ++ l1 ++ l4 }.

Theorem cut_elim : forall A l0 l1 l2,
  ll P (dual A :: l0) -> ll P (l1 ++ A :: l2) -> ll P (l1 ++ l0 ++ l2).
Proof with myeasy_perm_Type.
case_eq (pcut P) ; intros P_cutfree.
{ intros A l0 l1 l2 pi1 pi2.
  apply (ex_r _ _ (A :: l2 ++ l1)) in pi2...
  apply (ex_r _ ((l2 ++ l1) ++ l0))...
  eapply cut_r... }
enough (forall c s A l0 l1 l2 (pi1 : ll P (dual A :: l0)) (pi2 : ll P (l1 ++ A :: l2)),
          s = psize pi1 + psize pi2 -> fsize A <= c -> ll P (l1 ++ l0 ++ l2)) as IH
by (intros A l0 l1 l2 pi1 pi2 ; refine (IH _ _ A _ _ _ pi1 pi2 _ _) ; myeasy_perm_Type).
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
remember (l1 ++ A :: l2) as l ; destruct_ll pi2 f X l Hl Hr HP Hax a.
- (* ax_r *)
  destruct l1 ; inversion Heql ; subst.
  + eapply ex_r...
  + unit_vs_elt_inv H1 ; list_simpl...
- (* ex_r *)
  simpl in IHsize.
  destruct (PCperm_Type_vs_elt_inv _ _ _ _ _ HP) as [[p1 p2] Heq HP'] ; simpl in Heq ; simpl in HP' ; subst.
  apply (PEperm_Type_app_head _ l0) in HP'.
  eapply ex_r ; [ refine (IHsize _ _ _ _ pi1 Hl _ _) | ]...
  apply PEperm_PCperm_Type in HP' ; unfold id in HP' ; simpl in HP'.
  symmetry in HP' ; etransitivity ; [ | etransitivity ; [ apply HP' | ] ]...
- (* ex_wn_r *)
  symmetry in Heql ; trichot_Type_elt_app_exec Heql ; list_simpl ; subst.
  + rewrite 2 app_assoc ; eapply ex_wn_r ; [ | apply HP ] ; rewrite <- 2 app_assoc.
    revert Hl IHsize ; list_simpl ; intros Hl IHsize.
    refine (IHsize _ _ _ _ pi1 Hl _ _)...
  + destruct Heql1 as [Heql1 Heql2] ; subst.
    simpl in Heql1 ; decomp_map_Type Heql1 ; subst ; simpl in HP ; simpl in pi1 ; simpl.
    rewrite app_assoc ; rewrite <- (app_nil_l (map wn l7 ++ l3)).
    simpl in IHsize.
    destruct (Permutation_Type_vs_elt_inv _ _ _ _ HP) as [[lw1 lw2] Heq] ; simpl in Heq ; subst.
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
  dichot_Type_elt_app_exec Heql ; subst.
  + rewrite 2 app_assoc ; apply mix2_r...
    rewrite <- app_assoc ; refine (IHsize _ _ _ _ pi1 Hr _ _) ; simpl...
  + list_simpl ; apply mix2_r...
    refine (IHsize _ _ _ _ pi1 Hl _ _) ; simpl...
- (* one_r *)
  unit_vs_elt_inv Heql ; list_simpl...
  remember (one_r _) as Hone ; clear HeqHone.
  remember (dual one :: l0) as l' ; destruct_ll pi1 f X l Hl2 Hr2 HP Hax a ; try inversion Heql' ;
    simpl in IHsize.
  + (* ex_r *)
    destruct (PCperm_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] Heq HP'] ; simpl in Heq ; simpl in HP' ; subst.
    apply PEperm_PCperm_Type in HP' ; unfold id in HP' ; simpl in HP'.
    eapply ex_r ; [ | etransitivity ; [ apply PCperm_Type_app_comm | symmetry ; apply HP' ] ].
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
    remember (dual bot :: l0) as l' ; destruct_ll pi1 f X l Hl2 Hr2 HP Hax a ; try inversion Heql' ;
      simpl in IHsize.
    * (* ex_r *)
      destruct (PCperm_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] Heq HP'] ; simpl in Heq ; simpl in HP' ; subst.
      apply (PEperm_Type_app_tail _ _ _ l2) in HP'.
      apply PEperm_PCperm_Type in HP' ; unfold id in HP' ; list_simpl in HP'.
      eapply ex_r ; [ | symmetry ; apply HP' ].
      eapply ex_r ; [ | symmetry ; apply PCperm_Type_app_rot ].
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
      -- eapply ex_r ; [ | apply PCperm_Type_app_rot ].
         rewrite app_assoc ; apply mix2_r...
         eapply ex_r ; [ | apply PCperm_Type_app_comm ].
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
    remember (dual (tens A0 B) :: l0) as l' ; destruct_ll pi1 f X l Hl2 Hr2 HP Hax a ; try inversion Heql'.
    * (* ex_r *)
      remember (tens_r _ _ _ _ _ Hl Hr) as Htens ; clear HeqHtens.
      destruct (PCperm_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] Heq HP'] ; simpl in Heq ; simpl in HP' ; subst.
      apply (PEperm_Type_app_tail _ _ _ (l4 ++ l3)) in HP'.
      apply PEperm_PCperm_Type in HP' ; unfold id in HP' ; list_simpl in HP'.
      eapply ex_r ; [ | symmetry ; apply HP' ].
      eapply ex_r ; [ | symmetry ; apply PCperm_Type_app_rot ].
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
      -- eapply ex_r ; [ | apply PCperm_Type_app_rot ].
         rewrite app_assoc ; apply mix2_r...
         eapply ex_r ; [ | apply PCperm_Type_app_comm ].
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
      -- eapply ex_r ; [ | apply PCperm_Type_app_comm ].
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
    dichot_Type_elt_app_exec H1 ; subst.
    * rewrite 2 app_assoc ; apply tens_r...
      revert Hr IHsize ; simpl ; rewrite (app_comm_cons _ _ B) ; intros Hr IHsize.
      rewrite <- app_assoc ; refine (IHsize _ _ _ _ pi1 Hr _ _) ; simpl...
    * list_simpl ; apply tens_r...
      revert Hl IHsize ; simpl ; rewrite (app_comm_cons _ _ A0) ; intros Hl IHsize.
      refine (IHsize _ _ _ _ pi1 Hl _ _) ; simpl...
- (* parr_r *)
  destruct l1 ; inversion Heql ; subst ; list_simpl.
  + (* main case *)
    remember (dual (parr A0 B) :: l0) as l' ; destruct_ll pi1 f X l Hl2 Hr2 HP Hax a ; try inversion Heql'.
    * (* ex_r *)
      remember (parr_r _ _ _ _ Hl) as Hparr ; clear HeqHparr.
      destruct (PCperm_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] Heq HP'] ; simpl in Heq ; simpl in HP' ; subst.
      apply (PEperm_Type_app_tail _ _ _ l2) in HP'.
      apply PEperm_PCperm_Type in HP' ; unfold id in HP' ; list_simpl in HP'.
      eapply ex_r ; [ | symmetry ; apply HP' ].
      eapply ex_r ; [ | symmetry ; apply PCperm_Type_app_rot ].
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
      -- eapply ex_r ; [ | apply PCperm_Type_app_rot ].
         rewrite app_assoc ; apply mix2_r...
         eapply ex_r ; [ | apply PCperm_Type_app_comm ].
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
    remember (dual top :: l0) as l' ; destruct_ll pi1 f X l Hl2 Hr2 HP Hax a ; try inversion Heql'.
    * (* ex_r *)
      remember (top_r _ l2) as Htop ; clear HeqHtop.
      destruct (PCperm_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] Heq HP'] ; simpl in Heq ; simpl in HP' ; subst.
      apply (PEperm_Type_app_tail _ _ _ l2) in HP'.
      apply PEperm_PCperm_Type in HP' ; unfold id in HP' ; list_simpl in HP'.
      eapply ex_r ; [ | symmetry ; apply HP' ].
      eapply ex_r ; [ | symmetry ; apply PCperm_Type_app_rot ].
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
      -- eapply ex_r ; [ | apply PCperm_Type_app_rot ].
         rewrite app_assoc ; apply mix2_r...
         eapply ex_r ; [ | apply PCperm_Type_app_comm ].
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
    remember (dual (aplus A0 B) :: l0) as l' ; destruct_ll pi1 f X l Hl2 Hr2 HP Hax a ; try inversion Heql'.
    * (* ex_r *)
      remember (plus_r1 _ _ _ _ Hl) as Hplus ; clear HeqHplus.
      destruct (PCperm_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] Heq HP'] ; simpl in Heq ; simpl in HP' ; subst.
      apply (PEperm_Type_app_tail _ _ _ l2) in HP'.
      apply PEperm_PCperm_Type in HP' ; unfold id in HP' ; list_simpl in HP'.
      eapply ex_r ; [ | symmetry ; apply HP' ].
      eapply ex_r ; [ | symmetry ; apply PCperm_Type_app_rot ].
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
      -- eapply ex_r ; [ | apply PCperm_Type_app_rot ].
         rewrite app_assoc ; apply mix2_r...
         eapply ex_r ; [ | apply PCperm_Type_app_comm ].
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
    remember (dual (aplus B A0) :: l0) as l' ; destruct_ll pi1 f X l Hl2 Hr2 HP Hax a ; try inversion Heql'.
    * (* ex_r *)
      remember (plus_r2 _ _ _ _ Hl) as Hplus ; clear HeqHplus.
      destruct (PCperm_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] Heq HP'] ; simpl in Heq ; simpl in HP' ; subst.
      apply (PEperm_Type_app_tail _ _ _ l2) in HP'.
      apply PEperm_PCperm_Type in HP' ; unfold id in HP' ; list_simpl in HP'.
      eapply ex_r ; [ | symmetry ; apply HP' ].
      eapply ex_r ; [ | symmetry ; apply PCperm_Type_app_rot ].
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
      -- eapply ex_r ; [ | apply PCperm_Type_app_rot ].
         rewrite app_assoc ; apply mix2_r...
         eapply ex_r ; [ | apply PCperm_Type_app_comm ].
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
    remember (dual (awith A0 B) :: l0) as l' ; destruct_ll pi1 f X l Hl2 Hr2 HP Hax a ; try inversion Heql'.
    * (* ex_r *)
      remember (with_r _ _ _ _ Hl Hr) as Hwith ; clear HeqHwith.
      destruct (PCperm_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] Heq HP'] ; simpl in Heq ; simpl in HP' ; subst.
      apply (PEperm_Type_app_tail _ _ _ l2) in HP'.
      apply PEperm_PCperm_Type in HP' ; unfold id in HP' ; list_simpl in HP'.
      eapply ex_r ; [ | symmetry ; apply HP' ].
      eapply ex_r ; [ | symmetry ; apply PCperm_Type_app_rot ].
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
      -- eapply ex_r ; [ | apply PCperm_Type_app_rot ].
         rewrite app_assoc ; apply mix2_r...
         eapply ex_r ; [ | apply PCperm_Type_app_comm ].
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
    remember (dual (oc A0) :: l0) as l' ; destruct_ll pi1 f X lo Hl2 Hr2 HP Hax a ; try inversion Heql'.
    * (* ex_r *)
      remember (oc_r _ _ _ Hl) as Hoc ; clear HeqHoc.
      destruct (PCperm_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] Heq HP'] ; simpl in Heq ; simpl in HP' ; subst.
      apply (PEperm_Type_app_tail _ _ _ (map wn l)) in HP'.
      apply PEperm_PCperm_Type in HP' ; unfold id in HP' ; list_simpl in HP'.
      eapply ex_r ; [ | symmetry ; apply HP' ].
      eapply ex_r ; [ | symmetry ; apply PCperm_Type_app_rot ].
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
      -- destruct (Permutation_Type_vs_cons_inv _ _ _ HP) as [[lw1 lw2] Heq] ; simpl in Heq ; subst.
         assert (Permutation_Type (lw1 ++ l ++ lw2) (l ++ lw')) as HP'.
         { rewrite <- (app_nil_l (l ++ lw')).
           apply Permutation_Type_app_middle.
           rewrite <- (app_nil_l lw').
           apply (Permutation_Type_app_inv _ _ _ _ (dual A0))... }
         eapply ex_r ; [ | apply PCperm_Type_app_comm ].
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
      -- eapply ex_r ; [ | apply PCperm_Type_app_rot ].
         rewrite app_assoc ; apply mix2_r...
         eapply ex_r ; [ | apply PCperm_Type_app_comm ].
         revert Hr2 IHsize ; simpl ; change (wn (dual A0)) with (dual (oc A0)) ;
           intros Hr2 IHsize.
         revert Hoc IHsize ; rewrite <- (app_nil_l (oc _ :: _)) ; intros Hoc IHsize.
         refine (IHsize _ _ _ _ Hr2 Hoc _ _)...
    * (* oc_r *)
      clear IHsize ; subst.
      rewrite <- (app_nil_l (A0 :: _)) in Hl ; simpl in Hc ; refine (IHcut _ _ _ _ _ Hl2 Hl)...
    * (* wk_r *)
      clear IHsize ; subst.
      eapply ex_r ; [ | apply PCperm_Type_app_comm ].
      apply wk_list_r...
    * (* co_r *)
      clear IHsize ; subst.
      eapply ex_r ; [ | apply PCperm_Type_app_comm ].
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
    symmetry in H1 ; decomp_map_Type H1 ; subst ; simpl in pi1 ; simpl in Hl ; simpl.
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
    remember (dual (wn A0) :: l0) as l' ; destruct_ll pi1 f X l Hl2 Hr2 HP Hax a ; try inversion Heql'.
    * (* ex_r *)
      remember (de_r _ _ _ Hl) as Hde ; clear HeqHde.
      destruct (PCperm_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] Heq HP'] ; simpl in Heq ; simpl in HP' ; subst.
      apply (PEperm_Type_app_tail _ _ _ l2) in HP'.
      apply PEperm_PCperm_Type in HP' ; unfold id in HP' ; list_simpl in HP'.
      eapply ex_r ; [ | symmetry ; apply HP' ].
      eapply ex_r ; [ | symmetry ; apply PCperm_Type_app_rot ].
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
      -- eapply ex_r ; [ | apply PCperm_Type_app_rot ].
         rewrite app_assoc ; apply mix2_r...
         eapply ex_r ; [ | apply PCperm_Type_app_comm ].
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
    remember (dual (wn A0) :: l0) as l' ; destruct_ll pi1 f X l Hl2 Hr2 HP Hax a ; try inversion Heql'.
    * (* ex_r *)
      remember (wk_r _ A0 _ Hl) as Hwk ; clear HeqHwk.
      destruct (PCperm_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] Heq HP'] ; simpl in Heq ; simpl in HP' ; subst.
      apply (PEperm_Type_app_tail _ _ _ l2) in HP'.
      apply PEperm_PCperm_Type in HP' ; unfold id in HP' ; list_simpl in HP'.
      eapply ex_r ; [ | symmetry ; apply HP' ].
      eapply ex_r ; [ | symmetry ; apply PCperm_Type_app_rot ].
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
      -- eapply ex_r ; [ | apply PCperm_Type_app_rot ].
         rewrite app_assoc ; apply mix2_r...
         eapply ex_r ; [ | apply PCperm_Type_app_comm ].
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
    remember (dual (wn A0) :: l0) as l' ; destruct_ll pi1 f X l Hl2 Hr2 HP Hax a ; try inversion Heql'.
    * (* ex_r *)
      remember (co_r _ _ _ Hl) as Hco ; clear HeqHco.
      destruct (PCperm_Type_vs_cons_inv _ _ _ _ HP) as [[p1 p2] Heq HP'] ; simpl in Heq ; simpl in HP' ; subst.
      apply (PEperm_Type_app_tail _ _ _ l2) in HP'.
      apply PEperm_PCperm_Type in HP' ; unfold id in HP' ; list_simpl in HP'.
      eapply ex_r ; [ | symmetry ; apply HP' ].
      eapply ex_r ; [ | symmetry ; apply PCperm_Type_app_rot ].
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
      -- eapply ex_r ; [ | apply PCperm_Type_app_rot ].
         rewrite app_assoc ; apply mix2_r...
         eapply ex_r ; [ | apply PCperm_Type_app_comm ].
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
  assert (atomic A) as Hat.
  { apply Forall_app_inv in P_gax_at ; destruct P_gax_at as [_ P_gax_at2] ; inversion P_gax_at2... }
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
  + apply PCperm_Type_vs_elt_inv in p.
    destruct p as [[l4' l5'] Heq p] ; simpl in Heq ; simpl in p ; subst.
    assert (PEperm_Type (pperm P) (l1 ++ l5' ++ l4' ++ l2) (l1 ++ l5 ++ l4 ++ l2)) as HP'.
    { apply PEperm_Type_app_head.
      rewrite 2 app_assoc ; apply PEperm_Type_app_tail.
      symmetry... }
    apply PEperm_PCperm_Type in HP'.
    apply (ex_r _ (l1 ++ l5' ++ l4' ++ l2))...
    apply IHpi1...
  + symmetry in Heq ; trichot_Type_elt_app_exec Heq ; subst.
    * list_simpl ; rewrite app_assoc.
      eapply ex_wn_r...
      list_simpl.
      rewrite (app_assoc l) ; rewrite (app_assoc _ l3) ; rewrite <- (app_assoc l).
      apply IHpi1 ; list_simpl...
    * destruct Heq1 as [Heq1 Heq2] ; decomp_map_Type Heq1.
      exfalso ; destruct A ; inversion Heq1 ; subst ; inversion Hat.
    * list_simpl ; rewrite 2 app_assoc.
      eapply ex_wn_r...
      list_simpl ; rewrite (app_assoc l0) ; rewrite (app_assoc _ l6).
      apply IHpi1 ; list_simpl...
  + destruct l4 ; inversion Heq.
  + dichot_Type_elt_app_exec Heq ; subst.
    * list_simpl.
      eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
      apply mix2_r...
      eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
      apply IHpi1_2 ; list_simpl...
    * eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
      apply mix2_r...
      eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
      apply IHpi1_1 ; list_simpl...
  + exfalso ; destruct l4 ; inversion Heq.
    * destruct A ; inversion H0 ; subst ; inversion Hat.
    * destruct l4 ; inversion H1.
  + destruct l4 ; inversion Heq ; subst ;
      try (exfalso ; destruct A ; inversion H0 ; subst ; inversion Hat ; fail).
    eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    apply bot_r...
    eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    apply IHpi1 ; list_simpl...
  + destruct l4 ; inversion Heq ; subst ;
      try (exfalso ; destruct A ; inversion H0 ; subst ; inversion Hat ; fail).
    dichot_Type_elt_app_exec H1 ; subst.
    * list_simpl.
      eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
      rewrite app_comm_cons ; eapply ex_r ; [ | symmetry ; apply PCperm_Type_app_rot ] ; list_simpl.
      rewrite 3 app_assoc ; apply tens_r...
      list_simpl ; rewrite app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
      rewrite app_comm_cons ; apply IHpi1_2 ; list_simpl...
    * eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
      apply tens_r...
      list_simpl ; rewrite app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
      rewrite app_comm_cons ; apply IHpi1_1 ; list_simpl...
  + destruct l4 ; inversion Heq ; subst ;
      try (exfalso ; destruct A ; inversion H0 ; subst ; inversion Hat ; fail).
    eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    apply parr_r...
    rewrite 2 app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    rewrite 2 app_comm_cons ; apply IHpi1 ; list_simpl...
  + destruct l4 ; inversion Heq ; subst ;
      try (exfalso ; destruct A ; inversion H0 ; subst ; inversion Hat ; fail).
    eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    apply top_r...
  + destruct l4 ; inversion Heq ; subst ;
      try (exfalso ; destruct A ; inversion H0 ; subst ; inversion Hat ; fail).
    eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    apply plus_r1...
    rewrite app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    rewrite app_comm_cons ; apply IHpi1 ; list_simpl...
  + destruct l4 ; inversion Heq ; subst ;
      try (exfalso ; destruct A ; inversion H0 ; subst ; inversion Hat ; fail).
    eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    apply plus_r2...
    rewrite app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    rewrite app_comm_cons ; apply IHpi1 ; list_simpl...
  + destruct l4 ; inversion Heq ; subst ;
      try (exfalso ; destruct A ; inversion H0 ; subst ; inversion Hat ; fail).
    eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    apply with_r...
    * rewrite app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
      rewrite app_comm_cons ; apply IHpi1_1 ; list_simpl...
    * rewrite app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
      rewrite app_comm_cons ; apply IHpi1_2 ; list_simpl...
  + destruct l4 ; inversion Heq ; subst ;
      try (exfalso ; destruct A ; inversion H0 ; subst ; inversion Hat ; fail).
    exfalso ; symmetry in H1 ; decomp_map_Type H1 ; destruct A ; inversion H1 ; subst ; inversion Hat.
  + destruct l4 ; inversion Heq ; subst ;
      try (exfalso ; destruct A ; inversion H0 ; subst ; inversion Hat ; fail).
    eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    apply de_r...
    rewrite app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    rewrite app_comm_cons ; apply IHpi1 ; list_simpl...
  + destruct l4 ; inversion Heq ; subst ;
      try (exfalso ; destruct A ; inversion H0 ; subst ; inversion Hat ; fail).
    eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    apply wk_r...
    eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    apply IHpi1 ; list_simpl...
  + destruct l4 ; inversion Heq ; subst ;
      try (exfalso ; destruct A ; inversion H0 ; subst ; inversion Hat ; fail).
    eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    apply co_r...
    rewrite 2 app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
    rewrite 2 app_comm_cons ; apply IHpi1 ; list_simpl...
  + rewrite f in P_cutfree ; inversion P_cutfree.
  + destruct (P_gax_cut a0 a _ _ _ _ _ Heq Heql) as [x Hcut].
    rewrite <- Hcut ; apply (gax_r _ x).
Qed.

End Cut_Elim_Proof.



