(* ill_vs_ll library for yalla *)

(** * Comparison between Intuitionistic Linear Logic and Linear Logic *)

Require Import Injective.
Require Import List_more.
Require Import List_Type_more.
Require Import Permutation_Type_more.
Require Import Permutation_Type_solve.
Require Import genperm_Type.

Require Import ll_fragments.
Require Export ill_cut.



(** ** Characterization of [ill] as a fragment of [ll] *)

Section Translation_ll.

(** Embedding of [IAtom] into [Atom] *)
Variable i2a : IAtom -> Atom.

(** *** Embedding of [ill] into [ll] *)

Fixpoint ill2ll A :=
match A with
| ivar x    => var (i2a x)
| ione      => one
| itens A B => tens (ill2ll A) (ill2ll B)
| ilpam A B => parr (ill2ll B) (dual (ill2ll A))
| igen A    => parr (var (i2a atN)) (dual (ill2ll A))
| ilmap A B => parr (dual (ill2ll A)) (ill2ll B)
| ineg A    => parr (dual (ill2ll A)) (var (i2a atN))
| itop      => top
| iwith A B => awith (ill2ll A) (ill2ll B)
| izero     => zero
| iplus A B => aplus (ill2ll A) (ill2ll B)
| ioc A     => oc (ill2ll A)
end.

Lemma ill2ll_map_ioc : forall l,
  map dual (map ill2ll (map ioc l)) = map wn (map dual (map ill2ll l)).
Proof with try (list_simpl ; reflexivity).
induction l...
list_simpl.
rewrite IHl...
Qed.

Lemma ill2ll_map_ioc_inv : forall l1 l2,
  map wn l1 = map dual (map ill2ll l2) ->
    { l2' | l2 = map ioc l2' & l1 = map dual (map ill2ll l2') }.
Proof with try reflexivity.
intros l1 l2 Heq ; revert l1 Heq ; induction l2 ; intros l1 Heq ;
  destruct l1 ; inversion Heq.
- exists nil ; split...
- destruct a ; inversion H0.
  apply IHl2 in H1.
  destruct H1 as [l0 Heq1' Heq'2] ; subst.
  exists (a :: l0) ; split...
Qed.


(** Translation of proof fragments *)
Definition i2pfrag P := {|
  pcut := ipcut P ;
  pgax := existT (fun x => x -> list formula) (projT1 (ipgax P))
          (fun a => ill2ll (snd (projT2 (ipgax P) a))
                    :: rev (map dual (map ill2ll (fst (projT2 (ipgax P) a))))) ;
  pmix0 := false ;
  pmix2 := false ;
  pperm := ipperm P |}.

Lemma cutrm_i2pfrag : forall P,
  cutrm_pfrag (i2pfrag P) = i2pfrag (cutrm_ipfrag P).
Proof.
reflexivity.
Qed.

Proposition ill_to_ll {P} : forall l C, ill P l C ->
  ll (i2pfrag P) (ill2ll C :: rev (map dual (map ill2ll l))).
Proof with myeeasy.
intros l C Hill.
induction Hill ; 
  list_simpl ;
  try list_simpl in IHHill ;
  try list_simpl in IHHill1 ;
  try list_simpl in IHHill2.
- eapply ex_r.
  apply ax_r.
  apply PCperm_Type_swap.
- eapply ex_r...
  hyps_PEperm_Type_unfold ; unfold PCperm_Type ; simpl ; destruct ipperm.
  * apply Permutation_Type_cons...
    apply Permutation_Type_map.
    apply Permutation_Type_map.
    apply Permutation_Type_rev'...
  * subst...
- rewrite_all ill2ll_map_ioc.
  rewrite_all app_comm_cons.
  apply Permutation_Type_rev' in p.
  do 2 eapply Permutation_Type_map in p. 
  eapply ex_wn_r...
- apply one_r.
- rewrite app_comm_cons.
  eapply ex_r ; [ | apply PCperm_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply bot_r.
  eapply ex_r...
  rewrite ? app_comm_cons.
  apply PCperm_Type_app_comm.
- apply tens_r...
- rewrite app_comm_cons.
  eapply ex_r ; [ | apply PCperm_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply parr_r.
  eapply ex_r...
  rewrite ? app_comm_cons.
  apply PCperm_Type_app_comm.
- apply parr_r...
- rewrite app_comm_cons.
  rewrite app_assoc.
  eapply ex_r ; [ | apply PCperm_Type_app_comm ].
  rewrite bidual.
  rewrite ? app_assoc.
  rewrite <- ? app_comm_cons.
  apply tens_r...
  eapply ex_r...
  rewrite ? app_comm_cons.
  apply PCperm_Type_app_comm.
- apply parr_r...
- rewrite app_comm_cons.
  eapply ex_r ; [ | apply PCperm_Type_app_comm ].
  list_simpl.
  change (var (i2a atN) :: map dual (map ill2ll (rev l)))
    with ((var (i2a atN) :: nil) ++ map dual (map ill2ll (rev l))).
  apply tens_r.
  + rewrite bidual...
  + apply ax_r.
- apply parr_r...
  eapply ex_r...
  symmetry.
  rewrite (app_comm_cons _ _ (ill2ll B)).
  apply PCperm_Type_last.
- rewrite app_comm_cons.
  eapply ex_r ; [ | apply PCperm_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  rewrite <- ? app_assoc.
  rewrite bidual.
  apply tens_r...
  eapply ex_r...
  rewrite ? app_comm_cons.
  apply PCperm_Type_app_comm.
- apply parr_r...
  eapply ex_r...
  symmetry.
  rewrite (app_comm_cons _ _ (ill2ll N)).
  apply PCperm_Type_last.
- cons2app.
  eapply ex_r ; [ | apply PCperm_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  rewrite <- ? app_assoc.
  rewrite bidual.
  list_simpl.
  apply tens_r...
  apply ax_r.
- apply top_r.
- apply with_r...
- rewrite ? app_comm_cons.
  eapply ex_r ; [ | apply PCperm_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply plus_r1...
  eapply ex_r...
  rewrite ? app_comm_cons.
  apply PCperm_Type_app_comm.
- rewrite ? app_comm_cons.
  eapply ex_r ; [ | apply PCperm_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply plus_r2...
  eapply ex_r...
  rewrite ? app_comm_cons.
  apply PCperm_Type_app_comm.
- rewrite ? app_comm_cons.
  eapply ex_r ; [ | apply PCperm_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply top_r...
- apply plus_r1...
- apply plus_r2...
- rewrite ? app_comm_cons.
  eapply ex_r ; [ | apply PCperm_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply with_r...
  + eapply ex_r ; [ apply IHHill1 | ].
    rewrite ? app_comm_cons.
    apply PCperm_Type_app_comm.
  + eapply ex_r ; [ apply IHHill2 | ].
    rewrite ? app_comm_cons.
    apply PCperm_Type_app_comm.
- rewrite_all ill2ll_map_ioc.
  apply oc_r...
- rewrite ? app_comm_cons.
  eapply ex_r ; [ | apply PCperm_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply de_r...
  eapply ex_r...
  rewrite ? app_comm_cons.
  apply PCperm_Type_app_comm.
- rewrite app_comm_cons.
  eapply ex_r ; [ | apply PCperm_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply wk_r.
  eapply ex_r...
  rewrite ? app_comm_cons.
  apply PCperm_Type_app_comm.
- rewrite app_comm_cons.
  eapply ex_r ; [ | apply PCperm_Type_app_comm ].
  rewrite <- app_comm_cons.
  apply co_r...
  eapply ex_r...
  rewrite ? app_comm_cons.
  apply PCperm_Type_app_comm.
- rewrite app_comm_cons.
  eapply ex_r ; [ | apply PCperm_Type_app_comm ].
  rewrite <- app_assoc.
  assert (pcut (i2pfrag P) = true) as fc by (now simpl).
  eapply (@cut_r _ fc)...
  eapply ex_r...
  rewrite ? app_comm_cons.
  apply PCperm_Type_app_comm.
- replace (ill2ll (snd (projT2 (ipgax P) a))
   :: map dual (map ill2ll (rev (fst (projT2 (ipgax P) a)))))
  with (projT2 (pgax (i2pfrag P)) a) by (simpl ; rewrite 2 map_rev ; reflexivity).
  apply gax_r.
Qed.

End Translation_ll.



(** ** Conservativity results for [ll] over [ill] *)

Section Conservativity.

(** Embedding of [IAtom] into [Atom] *)
Variable i2a : IAtom -> Atom.
Hypothesis i2a_inj : injective i2a.


(** *** Comparisons between [ll] connectives and [ill] *)

Lemma wn_not_idefin : forall A F,
  ll_mix0 (dual (ill2ll i2a A) :: nil) -> ll_mix0 (oc F :: ill2ll i2a A :: nil)
    -> False.
Proof with myeeasy.
cut (forall A F l2,
  ll_mix0 (dual (ill2ll i2a A) :: nil) ->
  Permutation_Type (oc F :: ill2ll i2a A :: nil) l2 -> ll_mix0 l2 -> False).
{ intros H A F pi1 pi2 ; eapply H... }
induction A ; intros F l2 pi1 HP2 pi2 ; simpl in pi1 ; simpl in HP2.
- remember (covar (i2a i) :: nil) as l1 ; revert Heql1 ;
    clear - pi1 ; induction pi1 ; intros Heql1 ;
    try (now inversion Heql1) ; subst.
  + symmetry in p ; apply Permutation_Type_length_1_inv in p.
    apply IHpi1...
  + destruct l1 ; inversion Heql1 ; destruct lw' ; inversion H0.
    * now symmetry in p ; apply Permutation_Type_nil in p ; subst.
    * now symmetry in p ; apply Permutation_Type_nil in p ; subst.
    * destruct l1 ; inversion H1.
- revert HP2 ; clear - pi2 ; induction pi2 ; intros HP2 ;
    try (now (apply Permutation_Type_length in HP2 ; inversion HP2)) ;
    try (now (apply Permutation_Type_length_2_inv in HP2 ; inversion HP2)).
  + apply IHpi2.
    symmetry in p.
    transitivity l2...
  + apply IHpi2.
    apply (Permutation_Type_map wn) in p.
    perm_Type_solve.
  + apply Permutation_Type_length_2_inv in HP2.
    destruct HP2 ; inversion e.
    destruct l ; inversion H1.
- rewrite <- (app_nil_l (parr _ _ :: _)) in pi1.
  eapply parr_rev_axat in pi1 ;
    [ | intros a ; inversion a | ]...
  list_simpl in pi1.
  assert ((ll_mix0 (oc F :: ill2ll i2a A1 :: nil) * ll_mix0 (ill2ll i2a A2 :: nil))
        + (ll_mix0 (ill2ll i2a A1 :: nil) * ll_mix0 (oc F :: ill2ll i2a A2 :: nil)))
    as [[pi2' pi2''] | [pi2' pi2'']].
  { revert HP2 ; clear - pi2 ; induction pi2 ; intros HP2 ;
      try (now (apply Permutation_Type_length in HP2 ; inversion HP2)) ;
      try (now (apply Permutation_Type_length_2_inv in HP2 ; inversion HP2)).
    - apply IHpi2.
      simpl in p ; perm_Type_solve.
    - apply IHpi2.
      apply (Permutation_Type_map wn) in p.
      perm_Type_solve.
    - apply Permutation_Type_length_2_inv in HP2.
      destruct HP2 ; inversion e ; subst.
      destruct l2 ; inversion H2 ; subst.
      + destruct l1 ; inversion H2 ; subst.
        left ; split...
        eapply ex_r ; [ apply pi2_1 | PCperm_Type_solve ]...
      + apply app_eq_nil in H1 ; destruct H1 ; subst.
        right ; split...
        eapply ex_r ; [ apply pi2_2 | PCperm_Type_solve ]...
    - apply Permutation_Type_length_2_inv in HP2.
      destruct HP2 ; inversion e.
      destruct l ; inversion H1. }
  + eapply cut_mix0_r in pi1 ; [ | rewrite bidual ]...
    eapply IHA1 ; [ apply pi1 | reflexivity | ]...
  + eapply ex_r in pi1 ; [ | apply Permutation_Type_swap ].
    eapply cut_mix0_r in pi1 ; [ | rewrite bidual ]...
    eapply IHA2 ; [ apply pi1 | reflexivity | ]...
- eapply tens_rev_axat in pi1 ;
    [ | intros a ; inversion a | ]...
  cons2app in HP2.
  assert (Heq2 := HP2).
  symmetry in Heq2 ; apply Permutation_Type_vs_elt_inv in Heq2.
  destruct Heq2 as ((l' & l'') & Heq2) ; subst.
  eapply parr_rev_axat in pi2 ;
    [ | intros a ; inversion a | ]...
  destruct pi1 as [pi1' pi1''].
  rewrite bidual in pi1'.
  eapply (cut_mix0_r _ (l' ++ ill2ll i2a A2 :: l'')) in pi1' ;
    [ | eapply ex_r ; [ apply pi2 | PCperm_Type_solve ]].
  eapply IHA2.
  + eassumption.
  + apply Permutation_Type_app_inv in HP2 ; simpl in HP2.
    etransitivity ; [ apply Permutation_Type_swap | ].
    apply Permutation_Type_cons ; [ reflexivity | ]...
  + eapply ex_r ; [ apply pi1' | ].
    PCperm_Type_solve. 
- eapply tens_rev_axat in pi1 ;
    [ | intros a ; inversion a | ]...
  destruct pi1 as [_ pi1'].
  clear - pi1'.
  assert ({ l & Permutation_Type (covar (i2a atN) :: nil) l })
    as [l HP] by (eexists ; reflexivity).
  eapply ex_r in pi1' ; [ | apply HP ].
  revert HP ; induction pi1' ; intros HP ;
    try (now (apply Permutation_Type_length in HP ; inversion HP)) ;
    try (now (apply Permutation_Type_length_1_inv in HP ; inversion HP)).
  + apply IHpi1'.
    simpl in p ; perm_Type_solve.
  + apply IHpi1'.
    apply (Permutation_Type_map wn) in p.
    perm_Type_solve.
- eapply tens_rev_axat in pi1 ;
    [ | intros a ; inversion a | ]...
  cons2app in HP2.
  assert (Heq2 := HP2).
  symmetry in Heq2 ; apply Permutation_Type_vs_elt_inv in Heq2.
  destruct Heq2 as ((l' & l'') & Heq2) ; subst.
  eapply parr_rev_axat in pi2 ;
    [ | intros a ; inversion a | ]...
  destruct pi1 as [pi1' pi1''].
  rewrite bidual in pi1''.
  eapply (cut_mix0_r _ (l' ++ ill2ll i2a A2 :: l'')) in pi1'' ;
    [ | eapply ex_r ; [ apply pi2 | PCperm_Type_solve ]].
  eapply IHA2.
  + eassumption.
  + apply Permutation_Type_app_inv in HP2 ; simpl in HP2.
    etransitivity ; [ apply Permutation_Type_swap | ].
    apply Permutation_Type_cons ; [ reflexivity | ]...
  + eapply ex_r ; [ apply pi1'' | ].
    PCperm_Type_solve.
- eapply tens_rev_axat in pi1 ;
    [ | intros a ; inversion a | ]...
  destruct pi1 as [pi1' _].
  clear - pi1'.
  assert ({ l & Permutation_Type (covar (i2a atN) :: nil) l })
    as [l HP] by (eexists ; reflexivity).
  eapply ex_r in pi1' ; [ | apply HP ].
  revert HP ; induction pi1' ; intros HP ;
    try (now (apply Permutation_Type_length in HP ; inversion HP)) ;
    try (now (apply Permutation_Type_length_1_inv in HP ; inversion HP)).
  + apply IHpi1'.
    simpl in p ; perm_Type_solve.
  + apply IHpi1'.
    apply (Permutation_Type_map wn) in p.
    perm_Type_solve.
- remember (zero :: nil) as l1 ; revert Heql1 ;
    clear - pi1 ; induction pi1 ; intros Heql1 ;
    try (now inversion Heql1) ; subst.
  + symmetry in p ; apply Permutation_Type_length_1_inv in p.
    apply IHpi1...
  + destruct l1 ; inversion Heql1 ; destruct lw' ; inversion H0.
    * now symmetry in p ; apply Permutation_Type_nil in p ; subst.
    * now symmetry in p ; apply Permutation_Type_nil in p ; subst.
    * destruct l1 ; inversion H1.
- eapply plus_rev_axat in pi1 ;
    [ | intros a ; inversion a | ]...
  destruct pi1 as [ pi1 | pi1 ].
  + cons2app in HP2.
    assert (Heq2 := HP2).
    symmetry in Heq2 ; apply Permutation_Type_vs_elt_inv in Heq2.
    destruct Heq2 as ((l' & l'') & Heq2) ; subst.
    eapply with_rev1_noax in pi2 ;
      [ | intros a ; inversion a | ]...
    eapply IHA1.
    * eassumption.
    * apply Permutation_Type_app_inv in HP2 ; simpl in HP2.
      etransitivity ; [ apply Permutation_Type_swap | ].
      apply Permutation_Type_cons ; [ reflexivity | ]...
    * eapply ex_r ; [ apply pi2 | ].
      PCperm_Type_solve.
  + cons2app in HP2.
    assert (Heq2 := HP2).
    symmetry in Heq2 ; apply Permutation_Type_vs_elt_inv in Heq2.
    destruct Heq2 as ((l' & l'') & Heq2) ; subst.
    eapply with_rev2_noax in pi2 ;
      [ | intros a ; inversion a | ]...
    eapply IHA2.
    * eassumption.
    * apply Permutation_Type_app_inv in HP2 ; simpl in HP2.
      etransitivity ; [ apply Permutation_Type_swap | ].
      apply Permutation_Type_cons ; [ reflexivity | ]...
    * eapply ex_r ; [ apply pi2 | ].
      PCperm_Type_solve.
- revert HP2 ; clear - pi2 ; induction pi2 ; intros HP2 ;
    try (now (apply Permutation_Type_length in HP2 ; inversion HP2)) ;
    try (now (apply Permutation_Type_length_2_inv in HP2 ; inversion HP2)).
  + apply IHpi2.
    simpl in p ; perm_Type_solve.
  + apply IHpi2.
    apply (Permutation_Type_map wn) in p ; perm_Type_solve.
  + apply Permutation_Type_length_2_inv in HP2.
    destruct HP2 ; inversion e.
    destruct l ; inversion H1.
- assert (pi0 := pi1).
  eapply with_rev1_noax in pi1 ;
    [ | intros a ; inversion a | rewrite app_nil_l ; reflexivity ]...
  eapply with_rev2_noax in pi0 ;
    [ | intros a ; inversion a | rewrite app_nil_l ; reflexivity ]...
  assert (ll_mix0 (oc F :: ill2ll i2a A1 :: nil)
        + ll_mix0 (oc F :: ill2ll i2a A2 :: nil))
    as [ pi2' | pi2' ].
  { revert HP2 ; clear - pi2 ; induction pi2 ; intros HP2 ;
      try (now (apply Permutation_Type_length in HP2 ; inversion HP2)) ;
      try (now (apply Permutation_Type_length_2_inv in HP2 ; inversion HP2)).
    - apply IHpi2.
      simpl in p ; perm_Type_solve.
    - apply IHpi2.
      apply (Permutation_Type_map wn) in p ; perm_Type_solve.
    - apply Permutation_Type_length_2_inv in HP2.
      destruct HP2 ; inversion e ; subst.
      left.
      eapply ex_r ; [ apply pi2 | PCperm_Type_solve ].
    - apply Permutation_Type_length_2_inv in HP2.
      destruct HP2 ; inversion e ; subst.
      right.
      eapply ex_r ; [ apply pi2 | PCperm_Type_solve ].
    - apply Permutation_Type_length_2_inv in HP2.
      destruct HP2 ; inversion e.
      destruct l ; inversion H1. }
  + eapply IHA1...
  + eapply IHA2...
- revert HP2 ; clear - pi2 ; induction pi2 ; intros HP2 ;
    try (now (apply Permutation_Type_length in HP2 ; inversion HP2)) ;
    try (now (apply Permutation_Type_length_2_inv in HP2 ; inversion HP2)).
  + apply IHpi2.
    simpl in p ; perm_Type_solve.
  + apply IHpi2.
    apply (Permutation_Type_map wn) in p ; perm_Type_solve.
  + apply Permutation_Type_length_2_inv in HP2.
    destruct HP2 ; inversion e ; destruct l ; inversion H1.
Qed.

Lemma bot_not_idefin : forall A,
  ll_mix0 (dual (ill2ll i2a A) :: nil) -> ll_mix0 (one :: ill2ll i2a A :: nil)
    -> False.
Proof with myeeasy.
intros A pi1 pi2.
eapply cut_mix0_r in pi2.
- list_simpl in pi2.
  eapply ex_r in pi2 ; [ | apply Permutation_Type_swap ].
  eapply wn_not_idefin...
- apply bot_r.
  change nil with (map wn nil).
  apply oc_r.
  apply one_r.
Qed.

Lemma wn_one_not_idefin : forall A,
  ll_mix0 (wn one :: dual (ill2ll i2a A) :: nil) ->
  ll_mix0 (oc bot :: ill2ll i2a A :: nil) -> False.
Proof with myeeasy.
intros A pi1 pi2.
eapply cut_mix0_r in pi1.
- list_simpl in pi1.
  eapply wn_not_idefin...
- change nil with (map wn nil).
  apply oc_r.
  apply bot_r.
  apply mix0_r...
Qed.

Lemma oc_bot_not_idefin : forall A,
  ll_ll (oc bot :: dual (ill2ll i2a A) :: nil) ->
  ll_mix0 (wn one :: ill2ll i2a A :: nil) -> False.
Proof with myeeasy.
enough (forall l, ll_ll (map dual (map (ill2ll i2a) l)) ->
          (Forall_Type (fun F => ll_mix0 (ill2ll i2a F :: nil)) l) -> False)
  as Hgen.
{ intros A pi1 pi2.
  eapply cut_ll_r in pi1.
  eapply cut_mix0_r in pi2.
  - change (dual (ill2ll i2a A) :: nil)
      with (map dual (map (ill2ll i2a) (A :: nil))) in pi1.
    rewrite app_nil_r in pi1.
    list_simpl in pi2.
    eapply Hgen...
    constructor ; [ | constructor ]...
  - change nil with (map wn nil).
    apply oc_r.
    apply bot_r.
    apply mix0_r...
  - apply de_r.
    apply one_r. }
intros l pi.
remember (map dual (map (ill2ll i2a) l)) as l0 ; revert l Heql0.
induction pi ; intros l' Heq HF ; subst ;
  try (now inversion f).
- destruct l' ; inversion Heq.
  destruct l' ; inversion Heq.
  destruct i0 ; inversion H3.
- apply PCperm_Type_map_inv in p.
  destruct p as [ l1' Heq HP ] ; subst.
  symmetry in HP.
  apply PCperm_Type_map_inv in HP.
  destruct HP as [ l1'' Heq HP ] ; subst.
  eapply IHpi.
  + reflexivity.
  + eapply Permutation_Type_Forall_Type...
    apply HP.
- decomp_map Heq ; subst.
  decomp_map Heq ; subst.
  destruct (ill2ll_map_ioc_inv _ _ _ Heq3) as [l' ? ?] ; subst.
  rewrite map_map in p.
  apply Permutation_Type_map_inv in p ; destruct p as [l'' ? p] ; subst.
  rewrite <- (map_map _ _ l'') in IHpi.
  rewrite <- ill2ll_map_ioc in IHpi.
  rewrite <- ? map_app in IHpi.
  eapply IHpi ; [ reflexivity | ].
  apply Forall_Type_app_inv in HF ; destruct HF as [HF HF2].
  apply Forall_Type_app_inv in HF2 ; destruct HF2 as [HF2 HF3].
  apply Forall_Type_app...
  apply Forall_Type_app...
  apply (Permutation_Type_map ioc) in p.
  eapply Permutation_Type_Forall_Type...
- destruct l' ; inversion Heq.
  destruct i ; inversion H0.
- destruct l' ; inversion Heq ; subst.
  inversion HF.
  eapply IHpi...
- destruct l' ; inversion Heq.
  decomp_map H1 ; decomp_map H1 ; subst.
  destruct i ; inversion H0 ; subst.
  + inversion HF ; subst.
    simpl in X ; eapply parr_rev_axat in X ;
      [ | intros a ; inversion a | rewrite app_nil_l ; reflexivity ].
    list_simpl in X.
    apply Forall_Type_app_inv in X0 ; destruct X0.
    rewrite bidual in pi1.
    assert (ll_mix0 (ill2ll i2a i1 :: nil)) as pi0.
    { eapply (stronger_pfrag _ pfrag_mix0) in pi1 ;
        [ | nsplit 5 ; myeasy ; intros a ; inversion a ].
      revert pi1 f0 ; clear ; induction l5 ; intros pi HF.
      - assumption.
      - inversion HF ; subst.
        simpl in pi ; eapply ex_r in pi ; [ | apply Permutation_Type_swap ].
        apply (cut_mix0_r _ _ _ pi) in X.
        eapply IHl5... }
    eapply ex_r in X ; [ | apply Permutation_Type_swap ].
    apply (cut_mix0_r _ _ _ X) in pi0.
    apply (IHpi2 (i2 :: l4))...
    constructor...
  + inversion HF ; subst.
    simpl in X ; eapply parr_rev_axat in X ;
      [ | intros a ; inversion a | rewrite app_nil_l ; reflexivity ].
    list_simpl in X.
    apply Forall_Type_app_inv in X0 ; destruct X0.
    rewrite bidual in pi1.
    assert (ll_mix0 (ill2ll i2a i :: nil)) as pi0.
    { eapply (stronger_pfrag _ pfrag_mix0) in pi1 ;
        [ | nsplit 5 ; myeasy ; intros a ; inversion a ].
      revert pi1 f0 ; clear ; induction l5 ; intros pi HF.
      - assumption.
      - inversion HF ; subst.
        simpl in pi ; eapply ex_r in pi ; [ | apply Permutation_Type_swap ].
        apply (cut_mix0_r _ _ _ pi) in X.
        eapply IHl5... }
    eapply ex_r in X ; [ | apply Permutation_Type_swap ].
    apply (cut_mix0_r _ _ _ X) in pi0.
    apply (IHpi2 (ivar atN  :: l4))...
    constructor...
  + inversion HF ; subst.
    simpl in X ; eapply parr_rev_axat in X ;
      [ | intros a ; inversion a | rewrite app_nil_l ; reflexivity ].
    list_simpl in X.
    apply Forall_Type_app_inv in X0 ; destruct X0.
    rewrite bidual in pi2.
    assert (ll_mix0 (ill2ll i2a i1 :: nil)) as pi0.
    { eapply (stronger_pfrag _ pfrag_mix0) in pi2 ;
        [ | nsplit 5 ; myeasy ; intros a ; inversion a ].
      revert pi2 f ; clear ; induction l4 ; intros pi HF.
      - assumption.
      - inversion HF ; subst.
        simpl in pi ; eapply ex_r in pi ; [ | apply Permutation_Type_swap ].
        apply (cut_mix0_r _ _ _ pi) in X.
        eapply IHl4... }
    apply (cut_mix0_r _ _ _ X) in pi0.
    apply (IHpi1 (i2 :: l5))...
    constructor...
  + inversion HF ; subst.
    simpl in X ; eapply parr_rev_axat in X ;
      [ | intros a ; inversion a | rewrite app_nil_l ; reflexivity ].
    list_simpl in X.
    apply Forall_Type_app_inv in X0 ; destruct X0.
    rewrite bidual in pi2.
    assert (ll_mix0 (ill2ll i2a i :: nil)) as pi0.
    { eapply (stronger_pfrag _ pfrag_mix0) in pi2 ;
        [ | nsplit 5 ; myeasy ; intros a ; inversion a ].
      revert pi2 f ; clear ; induction l4 ; intros pi HF.
      - assumption.
      - inversion HF ; subst.
        simpl in pi ; eapply ex_r in pi ; [ | apply Permutation_Type_swap ].
        apply (cut_mix0_r _ _ _ pi) in X.
        eapply IHl4... }
    apply (cut_mix0_r _ _ _ X) in pi0.
    apply (IHpi1 (ivar atN :: l5))...
    constructor...
- destruct l' ; inversion Heq.
  destruct i ; inversion H0 ; subst.
  inversion HF ; subst.
  simpl in X.
  eapply tens_rev_axat in X ; [ | intros a ; inversion a | ]...
  destruct X as [pi1 pi2].
  apply (IHpi (i2 :: i1 :: l'))...
  constructor...
  constructor...
- destruct l' ; inversion Heq.
  destruct i ; inversion H0 ; subst.
  inversion HF ; subst.
  clear - X.
  assert ({ l & Permutation_Type (ill2ll i2a izero :: nil) l }) as [l HP]
    by (eexists ; reflexivity ).
  eapply ex_r in X ; [ | apply HP ].
  revert HP ; clear - X ; induction X ; intros HP ;
    try (now (apply Permutation_Type_length in HP ; inversion HP)) ;
    try (now (apply Permutation_Type_length_1_inv in HP ; inversion HP)).
  + apply IHX.
    simpl in p ; perm_Type_solve.
  + apply IHX.
    apply (Permutation_Type_map wn) in p ; perm_Type_solve.
- destruct l' ; inversion Heq.
  destruct i ; inversion H0 ; subst.
  inversion HF ; subst.
  simpl in X ; rewrite <- (app_nil_l (awith _ _ :: _)) in X.
  eapply with_rev1_noax in X ;
    [ | intros a ; inversion a | ]...
  apply (IHpi (i1 :: l'))...
  constructor...
- destruct l' ; inversion Heq.
  destruct i ; inversion H0 ; subst.
  inversion HF ; subst.
  simpl in X ; rewrite <- (app_nil_l (awith _ _ :: _)) in X.
  eapply with_rev2_noax in X ;
    [ | intros a ; inversion a | ]...
  apply (IHpi (i2 :: l'))...
  constructor...
- destruct l' ; inversion Heq.
  destruct i ; inversion H0 ; subst.
  inversion HF ; subst.
  simpl in X ; eapply plus_rev_axat in X ; [ | intros a ; inversion a | ]...
  destruct X as [pi | pi].
  + apply (IHpi1 (i1 :: l'))...
    constructor...
  + apply (IHpi2 (i2 :: l'))...
    constructor...
- destruct l' ; inversion Heq.
  destruct i ; inversion H0.
- destruct l' ; inversion Heq.
  destruct i ; inversion H0 ; subst.
  inversion HF ; subst.
  simpl in X ; rewrite <- (app_nil_l (oc _ :: _)) in X.
  eapply oc_rev_noax in X ;
    [ | intros a ; inversion a | ]...
  apply (IHpi (i :: l'))...
  constructor...
- destruct l' ; inversion Heq.
  destruct i ; inversion H0 ; subst.
  inversion HF ; subst.
  simpl in X ; rewrite <- (app_nil_l (oc _ :: _)) in X.
  eapply oc_rev_noax in X ;
    [ | intros a ; inversion a | ]...
  apply (IHpi l')...
- destruct l' ; inversion Heq.
  destruct i ; inversion H0 ; subst.
  apply (IHpi (ioc i :: ioc i :: l'))...
  inversion HF ; constructor...
- inversion a.
Qed.


(** ** Characterization of [ill] as a fragment of [ll] *)

(** *** Conservativity with constraints on [izero] *)

(** Constraints on the presence of [izero] for conservativity *)
Inductive zeropos : iformula -> Type :=
| zp_izero   : zeropos izero
| zp_itens_l : forall A B, zeropos A -> zeropos (itens A B)
| zp_itens_r : forall A B, zeropos A -> zeropos (itens B A)
| zp_iwith_l : forall A B, zeropos A -> zeropos (iwith A B)
| zp_iwith_r : forall A B, zeropos A -> zeropos (iwith B A)
| zp_iplus   : forall A B, zeropos A -> zeropos B -> zeropos (iplus A B)
| zp_ioc     : forall A, zeropos A -> zeropos (ioc A).

Lemma zeropos_ilr {P} : forall D, zeropos D -> forall l1 l2 C,
  ill P (l1 ++ D :: l2) C.
Proof with myeeasy.
intros D Hzp ; induction Hzp ; intros l1 l2 C ;
  try now (constructor ; intuition).
apply tens_ilr.
cons2app ; rewrite app_assoc.
apply IHHzp.
Qed.

Lemma ill2ll_zeropos : forall C D, zeropos C -> ill2ll i2a C = ill2ll i2a D ->
  zeropos D.
Proof with try assumption.
intros C D Hz.
revert D ; induction Hz ; intros D Heq ; destruct D ; inversion Heq ;
  try apply IHHz in H0 ; try (now constructor).
- apply zp_itens_r.
  apply IHHz in H1...
- apply zp_iwith_r.
  apply IHHz in H1...
- constructor.
  + apply IHHz1 in H0...
  + apply IHHz2 in H1...
Qed.

Inductive nonzerospos : iformula -> Type :=
| nzsp_ivar  : forall x, nonzerospos (ivar x)
| nzsp_ione  : nonzerospos ione
| nzsp_itens : forall A B, nonzerospos A -> nonzerospos B -> nonzerospos (itens A B)
| nzsp_ilpam : forall A B, nonzerospos A -> nonzerospos B ->
                             (zeropos B -> False) -> nonzerospos (ilpam A B)
| nzsp_igen : forall A, nonzerospos A -> nonzerospos (igen A)
| nzsp_ilmap : forall A B, nonzerospos A -> nonzerospos B ->
                             (zeropos B -> False) -> nonzerospos (ilmap A B)
| nzsp_ineg : forall A, nonzerospos A -> nonzerospos (ineg A)
| nzsp_itop  : nonzerospos itop
| nzsp_iwith : forall A B, nonzerospos A -> nonzerospos B -> nonzerospos (iwith A B)
| nzsp_izero : nonzerospos izero
| nzsp_iplus : forall A B, nonzerospos A -> nonzerospos B -> nonzerospos (iplus A B)
| nzsp_ioc   : forall A, nonzerospos A -> nonzerospos (ioc A).

Definition easyipgax_nzeropos P := forall a,
  (forall D, ill2ll i2a (snd (projT2 (ipgax P) a)) = dual (ill2ll i2a D) ->
     { Zll : _ & zeropos (fst Zll) & D :: (fst (projT2 (ipgax P) a))
                                   = fst (snd Zll) ++ fst Zll :: snd (snd Zll) })
* (forall l C,
     PCperm_Type (ipperm P) (ill2ll i2a (snd (projT2 (ipgax P) a))
                            :: rev (map dual (map (ill2ll i2a) (fst (projT2 (ipgax P) a)))))
                       (ill2ll i2a C :: rev (map dual (map (ill2ll i2a) l)))
       -> ill P l C)
(*     -> { b | fst (projT2 (ipgax P) b) = l & snd (projT2 (ipgax P) b) = C })    *)
* (In_Type N (fst (projT2 (ipgax P) a)) -> False).

Lemma dual_jfragment_zeropos {P} : ipcut P = false -> easyipgax_nzeropos P -> forall l0,
  Forall_Type nonzerospos l0 -> ll (i2pfrag i2a P) (map dual (map (ill2ll i2a) l0)) ->
  { Cll : _ & zeropos (fst Cll) & l0 = fst (snd Cll) ++ fst Cll :: snd (snd Cll) }.
Proof with myeeasy.
intros Hcut Hgax.
intros l0 Hnzsp Hll.
remember (map dual (map (ill2ll i2a) l0)) as l.
revert l0 Hnzsp Heql.
induction Hll ; intros l0 Hnzsp HP.
- exfalso.
  destruct l0 ; inversion HP.
  destruct l0 ; inversion HP.
  destruct i0 ; inversion H3.
- subst.
  rewrite map_map in p.
  apply PCperm_Type_map_inv in p.
  destruct p as [l' Heq HP] ; subst.
  apply PCperm_perm_Type in HP.
  apply (Permutation_Type_Forall_Type _ _ _ HP) in Hnzsp.
  apply IHHll in Hnzsp ; [ | rewrite <- map_map ]...
  destruct Hnzsp as [(C & l1 & l2) Hz Heq] ; unfold id in Heq ; subst.
  unfold id in HP ; apply Permutation_Type_vs_elt_inv in HP.
  destruct HP as ((l' & l'') & HP) ; subst.
  exists (C,(l',l''))...
- decomp_map_Type HP ; subst ; simpl in HP ; simpl in HP3.
  decomp_map_Type HP ; subst ; simpl in HP3.
  apply ill2ll_map_ioc_inv in HP3 ; destruct HP3 as [lw'' ? HP3] ; subst.
  rewrite map_map in p.
  apply Permutation_Type_map_inv in p ; destruct p as [lw''' ? p] ; subst.
  assert (Forall_Type nonzerospos (l1 ++ map ioc lw''' ++ l8)) as HF.
  { apply Forall_Type_app_inv in Hnzsp ; destruct Hnzsp as [HF HF2].
    apply Forall_Type_app_inv in HF2 ; destruct HF2 as [HF2 HF3].
    apply Forall_Type_app...
    apply Forall_Type_app...
    apply (Permutation_Type_map ioc) in p.
    eapply Permutation_Type_Forall_Type... }
  apply IHHll in HF ;
    [ | list_simpl ; rewrite ill2ll_map_ioc ; rewrite <- (map_map _ _ lw''')  ]...
  destruct HF as [(C & l1' & l2') Hz Heq] ; simpl in Heq.
  dichot_Type_elt_app_exec Heq ; subst ; simpl.
  + exists (C,(l1',l ++ map ioc lw'' ++ l8)) ; list_simpl...
  + dichot_Type_elt_app_exec Heq1 ; subst ; simpl.
    * apply (Permutation_Type_map ioc) in p.
      rewrite <- Heq0 in p.
      apply Permutation_Type_vs_elt_inv in p ; destruct p as [llw Heq].
      rewrite Heq ; list_simpl.
      rewrite app_assoc ; exists (C,(l1 ++ fst llw,snd llw ++ l8))...
    * rewrite 2 app_assoc.
      exists (C,((l1 ++ map ioc lw'') ++ l3, l2'))...
- inversion f.
- inversion f.
- destruct l0 ; inversion HP.
  destruct i ; inversion H0.
- rewrite map_map in HP.
  decomp_map_Type HP ; subst.
  rewrite <- map_map in IHHll.
  inversion Hnzsp ; subst.
  apply IHHll in H2...
  destruct H2
    as [(C & l1' & l2') Hzp Heq2] ; subst.
  exists (C,(x :: l1',l2'))...
- rewrite map_map in HP.
  decomp_map_Type HP ; subst.
  destruct x ; inversion HP1 ; subst.
  + rewrite <- map_map in IHHll2.
    assert (Forall_Type nonzerospos (x2 :: l4)) as Hnzsp'.
    { inversion Hnzsp ; subst.
      apply Forall_Type_app_inv in H2.
      destruct H2 as [H2 _].
      inversion H1.
      constructor... }
    apply IHHll2 in Hnzsp'...
    destruct Hnzsp'
      as [(C & l1' & l2') Hzp Heq2] ; subst.
    destruct l1' ; inversion Heq2 ; subst.
    * exfalso.
      inversion Hnzsp ; subst.
      inversion H1.
      apply H5...
    * exists (C,(ilpam x1 i :: l1',l2' ++ l5))...
      list_simpl...
  + assert (Forall_Type nonzerospos (N :: l4)) as Hnzsp'.
    { inversion Hnzsp ; subst.
      apply Forall_Type_app_inv in H2.
      destruct H2 as [H2 _].
      inversion H1.
      constructor...
      constructor. }
    rewrite <- map_map in IHHll2.
    apply IHHll2 in Hnzsp'...
    destruct Hnzsp'
      as [(C & l1' & l2') Hzp Heq2] ; subst.
    destruct l1' ; inversion Heq2 ; subst.
    * exfalso.
      inversion Hzp.
    * exists (C,(igen x :: l1',l2' ++ l5))...
      list_simpl...
  + assert (Forall_Type nonzerospos (x2 :: l5)) as Hnzsp'.
    { inversion Hnzsp ; subst.
      apply Forall_Type_app_inv in H2.
      destruct H2 as [_ H2].
      inversion H1.
      constructor... }
    rewrite <- map_map in IHHll1.
    apply IHHll1 in Hnzsp'...
    destruct Hnzsp'
      as [(C & l1' & l2') Hzp Heq2] ; subst.
    destruct l1' ; inversion Heq2 ; subst.
    * exfalso.
      inversion Hnzsp ; subst.
      inversion H1.
      apply H5...
    * exists (C,(ilmap x1 i :: l4 ++ l1',l2'))...
      list_simpl...
  + assert (Forall_Type nonzerospos (N :: l5)) as Hnzsp'.
    { inversion Hnzsp ; subst.
      apply Forall_Type_app_inv in H2.
      destruct H2 as [_ H2].
      inversion H1.
      constructor...
      constructor. }
    rewrite <- map_map in IHHll1.
    apply IHHll1 in Hnzsp'...
    destruct Hnzsp'
      as [(C & l1' & l2') Hzp Heq2] ; subst.
    destruct l1' ; inversion Heq2 ; subst.
    * exfalso.
      inversion Hzp.
    * exists (C,(ineg x :: l4 ++ l1',l2'))...
      list_simpl...
- rewrite map_map in HP.
  decomp_map_Type HP ; subst.
  destruct x ; inversion HP1 ; subst.
  rewrite <- map_map in IHHll.
  assert (Forall_Type nonzerospos (x2 :: x1 :: l2)) as Hnzsp'.
  { inversion Hnzsp ; subst.
    inversion H1 ; subst.
    constructor...
    constructor... }
  apply IHHll in Hnzsp'...
  destruct Hnzsp'
    as [(C & l1' & l2') Hzp Heq2] ; subst.
  destruct l1' ; inversion Heq2 ; [ | destruct l1' ; inversion Heq2 ] ; subst.
  + exists (itens x1 C,(nil,l2))...
    apply zp_itens_r...
  + exists (itens C i,(nil,l2'))...
    apply zp_itens_l...
  + exists (C,(itens i0 i :: l1',l2'))...
- decomp_map_Type HP ; decomp_map_Type HP ; simpl in HP3 ; subst.
  destruct x0 ; inversion HP1.
  exists (izero,(nil,l3)) ; simpl...
  constructor.
- rewrite map_map in HP.
  decomp_map_Type HP ; subst.
  destruct x ; inversion HP1 ; subst.
  rewrite <- map_map in IHHll.
  assert (Forall_Type nonzerospos (x1 :: l2)) as Hnzsp'.
  { inversion Hnzsp ; subst.
    inversion H1 ; subst.
    constructor... }
  apply IHHll in Hnzsp'...
  destruct Hnzsp'
    as [(C & l1' & l2') Hzp Heq2] ; subst.
  destruct l1' ; inversion Heq2 ; subst.
  + exists (iwith C x2,(nil,l2'))...
    apply zp_iwith_l...
  + exists (C,(iwith i x2 :: l1',l2'))...
- rewrite map_map in HP.
  decomp_map_Type HP ; subst.
  destruct x ; inversion HP1 ; subst.
  rewrite <- map_map in IHHll.
  assert (Forall_Type nonzerospos (x2 :: l2)) as Hnzsp'.
  { inversion Hnzsp ; subst.
    inversion H1 ; subst.
    constructor... }
  apply IHHll in Hnzsp'...
  destruct Hnzsp'
    as [(C & l1' & l2') Hzp Heq2] ; subst.
  destruct l1' ; inversion Heq2 ; subst.
  + exists (iwith x1 C,(nil,l2'))...
    apply zp_iwith_r...
  + exists (C,(iwith x1 i :: l1',l2'))...
- rewrite map_map in HP.
  decomp_map_Type HP ; subst.
  destruct x ; inversion HP1 ; subst.
  rewrite <- map_map in IHHll2.
  assert (Forall_Type nonzerospos (x2 :: l2)) as Hnzsp'.
  { inversion Hnzsp ; subst.
    inversion H1 ; subst.
    constructor... }
  apply IHHll2 in Hnzsp'...
  destruct Hnzsp'
    as [(C & l1' & l2') Hzp Heq2] ; subst.
  destruct l1' ; inversion Heq2 ; subst.
  + assert (Forall_Type nonzerospos (x1 :: l2')) as Hnzsp''.
    { inversion Hnzsp ; subst.
      inversion H1 ; subst.
      constructor... }
    rewrite <- map_map in IHHll1.
    apply IHHll1 in Hnzsp''...
    destruct Hnzsp''
      as [(C' & l1'' & l2'') Hzp' Heq3] ; subst.
    destruct l1'' ; inversion Heq3 ; subst.
    * exists (iplus C' C,(nil,l2''))...
      constructor...
    * exists (C',(iplus i C :: l1'',l2''))...
  + exists (C,(iplus x1 i :: l1',l2'))...
- exfalso.
  destruct l0 ; inversion HP.
  destruct i ; inversion H0.
- rewrite map_map in HP.
  decomp_map_Type HP ; subst.
  destruct x ; inversion HP1 ; subst.
  rewrite <- map_map in IHHll.
  assert (Forall_Type nonzerospos (x :: l2)) as Hnzsp'.
  { inversion Hnzsp ; subst.
    inversion H1 ; subst.
    constructor... }
  apply IHHll in Hnzsp'...
  destruct Hnzsp'
    as [(C & l1' & l2') Hzp Heq2] ; subst.
  destruct l1' ; inversion Heq2 ; subst.
  + exists (ioc C,(nil,l2'))...
    constructor...
  + exists (C,(ioc i :: l1',l2'))...
- rewrite map_map in HP.
  decomp_map_Type HP ; subst.
  rewrite <- map_map in IHHll.
  inversion Hnzsp.
  apply IHHll in H2...
  destruct H2 as [(C & l1' & l2') Hzp Heq2] ; subst.
  exists (C,(x :: l1',l2'))...
- rewrite map_map in HP.
  decomp_map_Type HP ; subst.
  destruct x ; inversion HP1 ; subst.
  assert (Forall_Type nonzerospos (ioc x :: ioc x :: l2)) as Hnzsp'.
  { inversion Hnzsp ; subst ; constructor... }
  rewrite <- (map_map _ _ l2) in IHHll.
  apply IHHll in Hnzsp'...
  destruct Hnzsp'
    as [(C & l1' & l2') Hzp Heq2] ; subst.
  destruct l1' ; inversion Heq2 ; subst.
  + exists (ioc x,(nil,l2))...
  + destruct l1' ; inversion H1 ; subst.
    * exists (ioc x,(nil,l2'))...
    * exists (C,(ioc x :: l1',l2'))...
- simpl in f.
  rewrite f in Hcut.
  inversion Hcut.
- unfold i2pfrag in HP ; simpl in HP.
  destruct l0 ; inversion HP.
  apply (fst (Hgax a)) in H0.
  destruct H0 as [(Z & lz1 & lz2) Hz Heq].
  destruct lz1 ; inversion Heq ; subst.
  + exists (Z,(nil,l0))...
  + list_simpl in H1.
    rewrite H2 in H1 ; list_simpl in H1.
    decomp_map_Type H1.
    apply dual_inj in H1 ; subst.
    simpl in H4 ; decomp_map_Type H4 ; subst.
    apply ill2ll_zeropos in H1...
    rewrite app_comm_cons.
    exists (x0,(i0::l4,l6))...
Qed.

(** Cut-free conservativity *)
Theorem ll_to_ill_nzeropos_cutfree {P} : ipcut P = false -> easyipgax_nzeropos P ->
  forall l, ll (i2pfrag i2a P) l -> forall l0 C, Forall_Type nonzerospos (C :: l0) ->
    PCperm_Type (pperm (i2pfrag i2a P))
                l (ill2ll i2a C :: rev (map dual (map (ill2ll i2a) l0))) ->
      ill P l0 C.
Proof with myeeasy.
intros Hcut Hgax.
intros l Hll ; induction Hll ; intros l0 C Hnzsp HP.
- apply PCperm_Type_length_2_inv in HP.
  destruct HP as [HP | HP] ; inversion HP ; destruct C ; inversion H0.
  destruct l0 using rev_ind_Type ; inversion H1.
  list_simpl in H3 ; inversion H3.
  destruct l0 using rev_ind_Type ; list_simpl in H5 ; inversion H5.
  destruct x ; inversion H4.
  rewrite <- H2 in H6.
  apply i2a_inj in H6 ; subst.
  apply ax_ir.
- apply IHHll...
  etransitivity...
- apply PCperm_Type_vs_cons_inv in HP ; destruct HP as [[l1' l2'] Heq HP].
  simpl in HP ; simpl in Heq ; dichot_Type_elt_app_exec Heq ; subst.
  + apply PEperm_Type_rev in HP ; rewrite rev_involutive in HP ; list_simpl in HP.
    rewrite map_map in HP.
    symmetry in HP ; apply PEperm_Type_map_inv in HP ; destruct HP as [l' Heq HP].
    decomp_map_Type Heq ; subst.
    simpl in Heq2 ; rewrite <- (map_map _ _ l7) in Heq2.
    apply ill2ll_map_ioc_inv in Heq2 ; destruct Heq2 as [l' Heq2 Heq] ; subst.
    symmetry in HP ; eapply ex_ir ; [ | apply HP ] ; simpl.
    rewrite app_assoc.
    apply Permutation_Type_rev' in p ; rewrite Heq in p.
    rewrite map_map in p.
    apply Permutation_Type_map_inv in p ; destruct p as [lw'' Heq' p].
    symmetry in p ; eapply ex_oc_ir...
    apply IHHll...
    * inversion Hnzsp ; subst.
      simpl in HP ; symmetry in HP.
      apply (PEperm_Type_Forall_Type _ _ _ _ HP) in H2.
      apply Forall_Type_app_inv in H2 ; destruct H2 as [HF HF2].
      apply Forall_Type_app_inv in HF2 ; destruct HF2 as [HF2 HF3].
      apply Forall_Type_app_inv in HF3 ; destruct HF3 as [HF3 HF4].
      constructor...
      apply Forall_Type_app ; apply Forall_Type_app...
      symmetry in p ; apply (Permutation_Type_map ioc) in p.
      eapply Permutation_Type_Forall_Type...
    * list_simpl. simpl in HP.
      apply (f_equal (@rev _)) in Heq1 ; rewrite rev_involutive in Heq1 ; subst.
      apply (f_equal (@rev _)) in Heq3 ; rewrite rev_involutive in Heq3 ; subst.
      apply (f_equal (@rev _)) in Heq5 ; rewrite rev_involutive in Heq5 ; subst.
      apply (f_equal (@rev _)) in Heq' ; rewrite rev_involutive in Heq' ; subst.
      list_simpl.
      rewrite <- (map_map _ _ (rev l3)).
      rewrite <- (map_map _ _ (rev l5)).
      rewrite <- (map_map _ _ (rev l8)).
      rewrite <- (map_map _ _ (rev lw'')).
      rewrite ill2ll_map_ioc.
      PCperm_Type_solve.
  + dichot_Type_elt_app_exec Heq1 ; subst ;
      [ exfalso ; decomp_map Heq0 ; destruct C ; inversion Heq0 | ].
    apply PEperm_Type_rev in HP ; rewrite rev_involutive in HP ; list_simpl in HP.
    rewrite map_map in HP.
    symmetry in HP ; apply PEperm_Type_map_inv in HP ; destruct HP as [l' Heq HP].
    decomp_map_Type Heq ; subst.
    simpl in Heq3 ; rewrite <- (map_map _ _ l5) in Heq3.
    apply ill2ll_map_ioc_inv in Heq3 ; destruct Heq3 as [l' Heq3 Heq] ; subst.
    symmetry in HP ; eapply ex_ir ; [ | apply HP ] ; simpl.
    rewrite app_assoc.
    apply Permutation_Type_rev' in p ; rewrite Heq in p.
    rewrite map_map in p.
    apply Permutation_Type_map_inv in p ; destruct p as [lw'' Heq' p].
    list_simpl ; symmetry in p ; eapply ex_oc_ir...
    apply IHHll...
    * inversion Hnzsp ; subst.
      simpl in HP ; symmetry in HP.
      apply (PEperm_Type_Forall_Type _ _ _ _ HP) in H2.
      apply Forall_Type_app_inv in H2 ; destruct H2 as [HF HF2].
      apply Forall_Type_app_inv in HF2 ; destruct HF2 as [HF2 HF3].
      apply Forall_Type_app_inv in HF3 ; destruct HF3 as [HF3 HF4].
      constructor...
      rewrite app_assoc ; apply Forall_Type_app ; apply Forall_Type_app...
      symmetry in p ; apply (Permutation_Type_map ioc) in p.
      eapply Permutation_Type_Forall_Type...
    * list_simpl. simpl in HP.
      apply (f_equal (@rev _)) in Heq1 ; rewrite rev_involutive in Heq1 ; subst.
      apply (f_equal (@rev _)) in Heq2 ; rewrite rev_involutive in Heq2 ; subst.
      apply (f_equal (@rev _)) in Heq5 ; rewrite rev_involutive in Heq5 ; subst.
      apply (f_equal (@rev _)) in Heq' ; rewrite rev_involutive in Heq' ; subst.
      list_simpl.
      rewrite <- (map_map _ _ (rev l2)).
      rewrite <- (map_map _ _ (rev l7)).
      rewrite <- (map_map _ _ (rev l8)).
      rewrite <- (map_map _ _ (rev lw'')).
      rewrite ill2ll_map_ioc.
      PCperm_Type_solve.
- exfalso ; apply PCperm_Type_nil_cons in HP...
- inversion f.
- apply PCperm_Type_length_1_inv in HP.
  inversion HP.
  destruct C ; inversion H0.
  destruct l0 using rev_ind_Type ; list_simpl in H1 ; inversion H1.
  apply one_irr.
- list_simpl in HP.
  symmetry in HP.
  apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq.
  + destruct C ; inversion H0.
  + symmetry in H1.
    decomp_map_Type H1 ; decomp_map_Type H4 ; subst.
    apply (f_equal (@rev _)) in H7.
    rewrite rev_involutive in H7 ; simpl in H4 ; simpl in H6 ; simpl in H8 ; subst.
    destruct x0 ; inversion H1.
    list_simpl.
    apply one_ilr.
    apply IHHll.
    * inversion Hnzsp.
      constructor...
      list_simpl in H3.
      apply Forall_Type_app_inv in H3.
      destruct H3 as [H3l H3r].
      inversion H3r.
      apply Forall_Type_app...
    * list_simpl.
      apply PEperm_PCperm_Type in HP ; unfold id in HP ; simpl in HP.
      PCperm_Type_solve.
- list_simpl in HP.
  symmetry in HP.
  apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq.
  + destruct C ; inversion H0 ; subst.
    list_simpl in HP.
    rewrite map_map in HP.
    apply PEperm_Type_map_inv in HP.
    destruct HP as [l3 Heq' HP].
    rewrite <- map_map in Heq'.
    decomp_map_Type Heq' ; decomp_map_Type Heq' ; simpl in Heq'3 ; simpl in Heq'4 ; subst.
    inversion Hnzsp ; inversion H2 ; subst.
    apply Forall_Type_rev in H3.
    apply (PEperm_Type_Forall_Type _ _ _ _ HP) in H3 ; simpl in H3.
    apply Forall_Type_app_inv in H3.
    destruct H3 as [H3l H3r].
    apply PEperm_Type_rev in HP ; list_simpl in HP ; symmetry in HP.
    eapply ex_ir ; [ | exact HP ].
    apply tens_irr.
    * apply IHHll1.
      -- constructor...
         apply Forall_Type_rev...
      -- list_simpl...
    * apply IHHll2.
      -- constructor...
         apply Forall_Type_rev...
      -- list_simpl...
  + symmetry in H1.
    decomp_map_Type H1 ; decomp_map_Type H4 ; simpl in H4 ; simpl in H6 ; simpl in H8 ; subst.
    inversion Hnzsp ; subst.
    apply Forall_Type_rev in H3.
    rewrite <- H7 in H3.
    apply Forall_Type_app_inv in H3.
    destruct H3 as [H3l H3r].
    inversion H3r ; subst.
    apply (Forall_Type_app _ _ _ H4) in H3l.
    assert ({ pl : _ & 
       PEperm_Type (ipperm P) (l8 ++ l6) (fst pl ++ snd pl) &
       l2 ++ l1 = map dual (map (ill2ll i2a) (fst pl))
                         ++ ill2ll i2a C :: map dual (map (ill2ll i2a) (snd pl)) /\
       (ipperm P = false -> l8 = fst pl /\ l6 = snd pl) }) as  HP0.
    { clear - HP.
      case_eq (ipperm P) ; intros Hperm ; rewrite_all Hperm.
      - apply PEperm_Type_vs_elt_inv in HP.
        destruct HP as [(ll & lr) Heq HP0] ; simpl in HP0.
        rewrite <- 2 map_app in HP0.
        rewrite map_map in HP0.
        symmetry in HP0.
        apply Permutation_Type_map_inv in HP0.
        destruct HP0 as [l3 Heq1 HP].
        rewrite <- map_map in Heq1.
        decomp_map_Type Heq1 ; decomp_map_Type Heq1 ; simpl in Heq4 ; simpl in Heq5 ; subst.
        eexists ; simpl ; [ | split ]...
        intros Hb ; inversion Hb.
      - simpl in HP.
        exists (l8,l6) ; simpl ; [ | split ]...
        intros ; split ; reflexivity. }
    destruct HP0 as [(ll & lr) HP0 (Heq' & HPeq)].
    dichot_Type_elt_app_exec Heq' ; subst.
    * symmetry in Heq'1.
      decomp_map_Type Heq'1 ; decomp_map_Type Heq'1 ;
        simpl in Heq'1 ; simpl in Heq'4 ; simpl in Heq'5 ; subst.
      apply (PEperm_Type_Forall_Type _ _ _ _ HP0) in H3l ; simpl in H3l.
      destruct x0 ; inversion H1 ; inversion H3 ; subst.
      -- simpl in H7.
         apply (f_equal (@rev _)) in H7.
         rewrite rev_involutive in H7 ; subst.
         list_simpl.
         simpl in HP0.
         apply (ex_ir _ (rev ll ++ ilpam x0_1 x0_2 :: rev l10 ++ rev l9)).
         ++ apply lpam_ilr.
            ** apply IHHll1.
               --- constructor...
                   apply Forall_Type_app_inv in H3l.
                   destruct H3l as [_ H3l].
                   apply Forall_Type_app_inv in H3l.
                   destruct H3l as [_ H3l].
                   apply Forall_Type_rev...
               --- rewrite bidual.
                   list_simpl...
            ** apply IHHll2.
               --- constructor...
                   apply Forall_Type_app_inv in H3l.
                   destruct H3l as [H3l' H3l].
                   apply Forall_Type_app_inv in H3l.
                   destruct H3l as [H3l _].
                   apply Forall_Type_rev in H3l'.
                   apply Forall_Type_rev in H3l.
                   apply Forall_Type_app...
                   constructor...
               --- list_simpl.
                   PCperm_Type_solve.
         ++ case_eq (ipperm P) ; intros Hperm ; rewrite_all Hperm.
            ** clear - HP0.
               apply Permutation_Type_rev' in HP0.
               list_simpl in HP0.
               list_simpl.
               apply Permutation_Type_elt.
               symmetry.
               etransitivity ; [ apply Permutation_Type_app_comm | ].
               perm_Type_solve.
            ** destruct (HPeq eq_refl) ; subst.
               list_simpl...
      -- simpl in H7.
         apply (f_equal (@rev _)) in H7.
         rewrite rev_involutive in H7 ; subst.
         list_simpl.
         simpl in HP0.
         apply (ex_ir _ (rev ll ++ igen x0 :: rev l10 ++ rev l9)).
         ++ apply gen_pam_rule.
            ** intros a.
               apply Hgax.
            ** apply IHHll1.
               --- constructor...
                   apply Forall_Type_app_inv in H3l.
                   destruct H3l as [_ H3l].
                   apply Forall_Type_app_inv in H3l.
                   destruct H3l as [_ H3l].
                   apply Forall_Type_rev...
               --- rewrite bidual.
                   list_simpl...
            ** apply IHHll2.
               --- constructor...
                   apply Forall_Type_app_inv in H3l.
                   destruct H3l as [H3l' H3l].
                   apply Forall_Type_app_inv in H3l.
                   destruct H3l as [H3l _].
                   apply Forall_Type_rev in H3l'.
                   apply Forall_Type_rev in H3l.
                   apply Forall_Type_app...
                   constructor...
                   constructor.
               --- list_simpl.
                   PCperm_Type_solve.
         ++ case_eq (ipperm P) ; intros Hperm ; rewrite_all Hperm.
            ** clear - HP0.
               apply Permutation_Type_rev' in HP0.
               list_simpl in HP0.
               list_simpl.
               apply Permutation_Type_elt.
               symmetry.
               etransitivity ; [ apply Permutation_Type_app_comm | ].
               perm_Type_solve.
            ** destruct (HPeq eq_refl) ; subst.
               list_simpl...
      -- simpl in Hll1.
         change (dual (ill2ll i2a x0_2) :: map dual (map (ill2ll i2a) l10))
           with (map dual (map (ill2ll i2a) (x0_2 :: l10))) in Hll1.
         apply dual_jfragment_zeropos in Hll1...
         ++ destruct Hll1 as [(C1 & lz1 & lz2) HzC1 Heq1] ; simpl in Heq1.
            destruct lz1 ; inversion Heq1 ; subst.
            ** contradiction HzC1.
            ** apply (f_equal (@rev _)) in H7.
               rewrite rev_involutive in H7 ; subst.
               simpl in HP0 ; rewrite ? app_assoc in HP0.
               apply PEperm_Type_vs_elt_inv in HP0.
               destruct HP0 as [(ll1 & lr1) HP0 _] ; simpl in HP0.
               dichot_Type_elt_app_exec HP0 ; subst ; list_simpl.
               --- apply zeropos_ilr...
               --- rewrite ? app_comm_cons.
                   rewrite ? app_assoc.
                   apply zeropos_ilr...
         ++ constructor...
            apply Forall_Type_app_inv in H3l.
            destruct H3l as [_ H3l].
            apply Forall_Type_app_inv in H3l.
            destruct H3l as [_ H3l]...
      -- simpl in Hll1.
         change (covar (i2a atN) :: map dual (map (ill2ll i2a) l10))
           with (map dual (map (ill2ll i2a) (N :: l10))) in Hll1.
         apply dual_jfragment_zeropos in Hll1...
         ++ destruct Hll1 as [(C1 & lz1 & lz2) HzC1 Heq1].
            destruct lz1 ; inversion Heq1 ; subst.
            ** inversion HzC1.
            ** apply (f_equal (@rev _)) in H7.
               rewrite rev_involutive in H7 ; subst.
               simpl in HP0 ; rewrite ? app_assoc in HP0.
               apply PEperm_Type_vs_elt_inv in HP0.
               destruct HP0 as [(ll1 & lr1) HP0 _ ].
               dichot_Type_elt_app_exec HP0 ; subst ; list_simpl.
               --- apply zeropos_ilr...
               --- rewrite ? app_comm_cons.
                   rewrite ? app_assoc.
                   apply zeropos_ilr...
         ++ constructor...
            --- constructor.
            --- apply Forall_Type_app_inv in H3l.
                destruct H3l as [_ H3l].
                apply Forall_Type_app_inv in H3l.
                destruct H3l as [_ H3l]...
    * symmetry in Heq'0.
      decomp_map_Type Heq'0 ; decomp_map_Type Heq'0 ;
        simpl in Heq'0 ; simpl in Heq'4 ; simpl in Heq'5 ; subst.
      simpl in HP0 ; simpl in H3l ; simpl in H3r.
      apply (PEperm_Type_Forall_Type _ _ _ _ HP0) in H3l.
      destruct x0 ; inversion H1 ; inversion H3 ; subst.
      -- simpl in Hll2.
         change (dual (ill2ll i2a x0_2) :: map dual (map (ill2ll i2a) l9))
           with (map dual (map (ill2ll i2a) (x0_2 :: l9))) in Hll2.
         apply dual_jfragment_zeropos in Hll2...
         ++ destruct Hll2 as [(C1 & lz1 & lz2) HzC1 Heq1].
            destruct lz1 ; inversion Heq1 ; subst.
            ** contradiction HzC1.
            ** apply (f_equal (@rev _)) in H7.
               rewrite rev_involutive in H7 ; subst.
               list_simpl in HP0.
               apply PEperm_Type_vs_elt_inv in HP0.
               destruct HP0 as [(ll1 & lr1) HP0 _ ].
               dichot_Type_elt_app_exec HP0 ; subst ; list_simpl.
               --- apply zeropos_ilr...
               --- rewrite ? app_comm_cons.
                   rewrite ? app_assoc.
                   apply zeropos_ilr...
         ++ constructor...
            apply Forall_Type_app_inv in H3l.
            destruct H3l as [H3l _].
            apply Forall_Type_app_inv in H3l.
            destruct H3l as [H3l _]...
      -- simpl in Hll2.
         change (covar (i2a atN) :: map dual (map (ill2ll i2a) l9))
           with (map dual (map (ill2ll i2a) (N :: l9))) in Hll2.
         apply dual_jfragment_zeropos in Hll2...
         ++ destruct Hll2 as [(C1 & lz1 & lz2) HzC1 Heq1].
            destruct lz1 ; inversion Heq1 ; subst.
            ** inversion HzC1.
            ** apply (f_equal (@rev _)) in H7.
               rewrite rev_involutive in H7 ; subst.
               list_simpl in HP0.
               apply PEperm_Type_vs_elt_inv in HP0.
               destruct HP0 as [(ll1 & lr1) HP0 _ ].
               dichot_Type_elt_app_exec HP0 ; subst ; list_simpl.
               --- apply zeropos_ilr...
               --- rewrite ? app_comm_cons.
                   rewrite ? app_assoc.
                   apply zeropos_ilr...
         ++ constructor ; [ constructor | ]...
            apply Forall_Type_app_inv in H3l.
            destruct H3l as [H3l _].
            apply Forall_Type_app_inv in H3l.
            destruct H3l as [H3l _]...
      -- simpl in H7.
         apply (f_equal (@rev _)) in H7.
         rewrite rev_involutive in H7 ; subst.
         list_simpl.
         simpl in HP0.
         apply (ex_ir _ (rev l10 ++ rev l9 ++ ilmap x0_1 x0_2 :: rev lr)).
         ++ apply lmap_ilr.
            ** apply IHHll2.
               --- constructor...
                   apply Forall_Type_app_inv in H3l.
                   destruct H3l as [H3l _].
                   apply Forall_Type_app_inv in H3l.
                   destruct H3l as [H3l _].
                   apply Forall_Type_rev...
               --- rewrite bidual.
                   list_simpl...
            ** apply IHHll1.
               --- constructor...
                   apply Forall_Type_app_inv in H3l.
                   destruct H3l as [H3l' H3l].
                   apply Forall_Type_app_inv in H3l'.
                   destruct H3l' as [_ H3l'].
                   apply Forall_Type_rev in H3l'.
                   apply Forall_Type_rev in H3l.
                   apply Forall_Type_app...
                   constructor...
               --- list_simpl.
                   PCperm_Type_solve.
         ++ case_eq (ipperm P) ; intros Hperm ; rewrite_all Hperm.
            ** clear - HP0.
               apply Permutation_Type_rev' in HP0.
               list_simpl in HP0.
               list_simpl.
               rewrite app_assoc.
               apply Permutation_Type_elt.
               etransitivity ; [ apply Permutation_Type_app_comm | ].
               perm_Type_solve.
            ** destruct (HPeq eq_refl) ; subst.
               list_simpl...
      -- simpl in H7.
         apply (f_equal (@rev _)) in H7.
         rewrite rev_involutive in H7 ; subst.
         list_simpl.
         simpl in HP0.
         apply (ex_ir _ (rev l10 ++ rev l9 ++ ineg x0 :: rev lr)).
         ++ apply neg_map_rule.
            ** intros a.
               apply Hgax.
            ** apply IHHll2.
               --- constructor...
                   apply Forall_Type_app_inv in H3l.
                   destruct H3l as [H3l _].
                   apply Forall_Type_app_inv in H3l.
                   destruct H3l as [H3l _].
                   apply Forall_Type_rev...
               --- rewrite bidual.
                   list_simpl...
            ** apply IHHll1.
               --- constructor...
                   apply Forall_Type_app_inv in H3l.
                   destruct H3l as [H3l' H3l].
                   apply Forall_Type_app_inv in H3l'.
                   destruct H3l' as [_ H3l'].
                   apply Forall_Type_rev in H3l'.
                   apply Forall_Type_rev in H3l.
                   apply Forall_Type_app...
                   constructor...
                   constructor.
               --- list_simpl.
                   PCperm_Type_solve.
         ++ case_eq (ipperm P) ; intros Hperm ; rewrite_all Hperm.
            ** clear - HP0.
               apply Permutation_Type_rev' in HP0.
               list_simpl in HP0.
               list_simpl.
               rewrite app_assoc.
               apply Permutation_Type_elt.
               etransitivity ; [ apply Permutation_Type_app_comm | ].
               perm_Type_solve.
            ** destruct (HPeq eq_refl) ; subst.
               list_simpl...
- list_simpl in HP.
  symmetry in HP.
  apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq ; subst.
  + list_simpl in HP.
    rewrite map_map in HP.
    apply PEperm_Type_map_inv in HP.
    destruct HP as [l3 Heq' HP].
    rewrite <- map_map in Heq' ; subst.
    inversion Hnzsp ; subst.
    apply Forall_Type_rev in H3.
    apply (PEperm_Type_Forall_Type _ _ _ _ HP) in H3.
    destruct C ; inversion H0 ; inversion H2 ; subst.
    * apply lpam_irr.
      symmetry in HP.
      apply PEperm_Type_rev in HP.
      rewrite rev_involutive in HP.
      apply (ex_ir _ (rev l3 ++ C1 :: nil)) ; [ | apply PEperm_Type_add_inside ]...
      apply IHHll.
      -- constructor...
         apply Forall_Type_app ; [ | constructor ] ; try constructor...
         apply Forall_Type_rev...
      -- list_simpl...
    * apply gen_irr.
      symmetry in HP.
      apply PEperm_Type_rev in HP.
      rewrite rev_involutive in HP.
      apply (ex_ir _ (rev l3 ++ C :: nil)) ; [ | apply PEperm_Type_app ]...
      apply IHHll.
      -- constructor ; [ constructor | ]...
         apply Forall_Type_app ; [ | constructor ; [ | constructor ] ]...
         apply Forall_Type_rev...
      -- list_simpl ; PCperm_Type_solve.
    * apply lmap_irr.
      symmetry in HP.
      apply PEperm_Type_rev in HP.
      rewrite rev_involutive in HP.
      apply (ex_ir _ (C1 :: rev l3)) ; [ | apply PEperm_Type_cons ]...
      apply IHHll.
      -- constructor...
         constructor...
         apply Forall_Type_rev...
      -- list_simpl ; PCperm_Type_solve.
    * apply neg_irr.
      symmetry in HP.
      apply PEperm_Type_rev in HP.
      rewrite rev_involutive in HP.
      apply (ex_ir _ (C :: rev l3)) ; [ | apply PEperm_Type_cons ]...
      apply IHHll.
      -- constructor ; [ constructor | ]...
         constructor...
         apply Forall_Type_rev...
      -- list_simpl ; PCperm_Type_solve.
  + symmetry in H1.
    decomp_map_Type H1 ; decomp_map_Type H3 ; simpl in H3 ; simpl in H5 ; simpl in H7 ; subst.
    simpl in H6 ; apply (f_equal (@rev _)) in H6.
    rewrite rev_involutive in H6 ; subst.
    destruct x0 ; inversion H1 ; subst.
    list_simpl.
    apply tens_ilr.
    apply IHHll.
    * inversion Hnzsp.
      constructor...
      list_simpl in H3.
      apply Forall_Type_app_inv in H3.
      destruct H3 as [H3l H3r].
      inversion H3r.
      inversion H5 ; subst.
      apply Forall_Type_app...
      constructor...
      constructor...
    * list_simpl.
      rewrite HP ; PCperm_Type_solve.
- list_simpl in HP.
  symmetry in HP.
  apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq ; subst.
  + destruct C ; inversion H0 ; subst.
    apply top_irr.
  + symmetry in H1.
    decomp_map_Type H1 ; decomp_map_Type H3 ; simpl in H3 ; simpl in H5 ; simpl in H7 ; subst.
    apply (f_equal (@rev _)) in H6.
    rewrite rev_involutive in H6 ; subst.
    destruct x0 ; inversion H1 ; subst.
    list_simpl.
    apply zero_ilr.
- list_simpl in HP.
  symmetry in HP.
  apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq ; subst.
  + list_simpl in HP.
    rewrite map_map in HP.
    apply PEperm_Type_map_inv in HP.
    destruct HP as [l3 Heq' HP].
    rewrite <- map_map in Heq' ; subst.
    inversion Hnzsp ; subst.
    apply Forall_Type_rev in H3.
    apply (PEperm_Type_Forall_Type _ _ _ _ HP) in H3.
    destruct C ; inversion H0 ; subst.
    inversion H2 ; subst.
    symmetry in HP.
    apply PEperm_Type_rev in HP.
    rewrite rev_involutive in HP.
    apply (ex_ir _ (rev l3)) ; [ | apply HP ].
    apply plus_irr1.
    apply IHHll.
    * constructor...
      apply Forall_Type_rev...
    * list_simpl...
  + symmetry in H1.
    decomp_map_Type H1 ; decomp_map_Type H3 ; simpl in H3 ; simpl in H5 ; simpl in H7 ; subst.
    apply (f_equal (@rev _)) in H6.
    rewrite rev_involutive in H6 ; subst.
    destruct x0 ; inversion H1 ; subst.
    list_simpl.
    apply with_ilr1.
    apply IHHll.
    * inversion Hnzsp.
      constructor...
      list_simpl in H3.
      apply Forall_Type_app_inv in H3.
      destruct H3 as [H3l H3r].
      inversion H3r.
      inversion H5 ; subst.
      apply Forall_Type_app...
      constructor...
    * list_simpl.
      rewrite HP ; PCperm_Type_solve.
- list_simpl in HP.
  symmetry in HP.
  apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq ; subst.
  + list_simpl in HP.
    rewrite map_map in HP.
    apply PEperm_Type_map_inv in HP.
    destruct HP as [l3 Heq' HP].
    rewrite <- map_map in Heq' ; subst.
    inversion Hnzsp ; subst.
    apply Forall_Type_rev in H3.
    apply (PEperm_Type_Forall_Type _ _ _ _ HP) in H3.
    destruct C ; inversion H0 ; subst.
    inversion H2 ; subst.
    symmetry in HP.
    apply PEperm_Type_rev in HP.
    rewrite rev_involutive in HP.
    apply (ex_ir _ (rev l3)) ; [ | apply HP ].
    apply plus_irr2.
    apply IHHll.
    * constructor...
      apply Forall_Type_rev...
    * list_simpl...
  + symmetry in H1.
    decomp_map_Type H1 ; decomp_map_Type H3 ; simpl in H3 ; simpl in H5 ; simpl in H7 ; subst.
    apply (f_equal (@rev _)) in H6.
    rewrite rev_involutive in H6 ; subst.
    destruct x0 ; inversion H1 ; subst.
    list_simpl.
    apply with_ilr2.
    apply IHHll.
    * inversion Hnzsp.
      constructor...
      list_simpl in H3.
      apply Forall_Type_app_inv in H3.
      destruct H3 as [H3l H3r].
      inversion H3r.
      inversion H5 ; subst.
      apply Forall_Type_app...
      constructor...
    * list_simpl.
      rewrite HP ; PCperm_Type_solve.
- list_simpl in HP.
  symmetry in HP.
  apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq ; subst.
  + list_simpl in HP.
    rewrite map_map in HP.
    apply PEperm_Type_map_inv in HP.
    destruct HP as [l3 Heq' HP].
    rewrite <- map_map in Heq' ; subst.
    inversion Hnzsp ; subst.
    apply Forall_Type_rev in H3.
    apply (PEperm_Type_Forall_Type _ _ _ _ HP) in H3.
    destruct C ; inversion H0 ; subst.
    inversion H2 ; subst.
    symmetry in HP.
    apply PEperm_Type_rev in HP.
    rewrite rev_involutive in HP.
    apply (ex_ir _ (rev l3)) ; [ | apply HP ].
    apply with_irr.
    * apply IHHll1.
      -- constructor...
         apply Forall_Type_rev...
      -- list_simpl...
    * apply IHHll2.
      -- constructor...
         apply Forall_Type_rev...
      -- list_simpl...
  + symmetry in H1.
    decomp_map_Type H1 ; decomp_map_Type H3 ; simpl in H3 ; simpl in H5 ; simpl in H7 ; subst.
    apply (f_equal (@rev _)) in H6.
    rewrite rev_involutive in H6 ; subst.
    destruct x0 ; inversion H1 ; subst.
    list_simpl.
    apply plus_ilr.
    * apply IHHll1.
      -- inversion Hnzsp.
         constructor...
         list_simpl in H3.
         apply Forall_Type_app_inv in H3.
         destruct H3 as [H3l H3r].
         inversion H3r.
         inversion H5 ; subst.
         apply Forall_Type_app...
         constructor...
      -- list_simpl.
         rewrite HP ; PCperm_Type_solve.
    * apply IHHll2.
      -- inversion Hnzsp.
         constructor...
         list_simpl in H3.
         apply Forall_Type_app_inv in H3.
         destruct H3 as [H3l H3r].
         inversion H3r.
         inversion H5 ; subst.
         apply Forall_Type_app...
         constructor...
      -- list_simpl.
         rewrite HP ; PCperm_Type_solve.
- list_simpl in HP.
  symmetry in HP.
  apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq ; subst.
  + list_simpl in HP.
    rewrite map_map in HP.
    apply PEperm_Type_map_inv in HP.
    destruct HP as [l3 Heq' HP].
    rewrite <- (map_map _ _ l3) in Heq'.
    destruct (ill2ll_map_ioc_inv _ _ _ Heq') as [l0' Heq'' _] ; subst.
    inversion Hnzsp ; subst.
    apply Forall_Type_rev in H3.
    apply (PEperm_Type_Forall_Type _ _ _ _ HP) in H3.
    destruct C ; inversion H0 ; subst.
    inversion H2 ; subst.
    symmetry in HP.
    apply PEperm_Type_rev in HP.
    rewrite rev_involutive in HP.
    apply (ex_ir _ (rev (map ioc l0'))) ; [ | apply HP ].
    list_simpl.
    apply oc_irr.
    apply IHHll.
    * constructor...
      apply Forall_Type_rev in H3 ; list_simpl in H3...
    * rewrite Heq'.
      list_simpl...
  + symmetry in H1.
    decomp_map_Type H1 ; decomp_map_Type H3 ; simpl in H3 ; simpl in H5 ; simpl in H7 ; subst.
    destruct x0 ; inversion H1.
- list_simpl in HP.
  symmetry in HP.
  apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq ; subst.
  + destruct C ; inversion H0.
  + symmetry in H1.
    decomp_map_Type H1 ; decomp_map_Type H3 ; simpl in H3 ; simpl in H5 ; simpl in H7 ; subst.
    apply (f_equal (@rev _)) in H6.
    rewrite rev_involutive in H6 ; subst.
    destruct x0 ; inversion H1 ; subst.
    list_simpl.
    apply de_ilr.
    apply IHHll.
    * inversion Hnzsp.
      constructor...
      list_simpl in H3.
      apply Forall_Type_app_inv in H3.
      destruct H3 as [H3l H3r].
      inversion H3r.
      inversion H5 ; subst.
      apply Forall_Type_app...
      constructor...
    * list_simpl.
      rewrite HP ; PCperm_Type_solve.
- list_simpl in HP.
  symmetry in HP.
  apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq ; subst.
  + destruct C ; inversion H0.
  + symmetry in H1.
    decomp_map_Type H1 ; decomp_map_Type H3 ; simpl in H3 ; simpl in H5 ; simpl in H7 ; subst.
    apply (f_equal (@rev _)) in H6.
    rewrite rev_involutive in H6 ; subst.
    destruct x0 ; inversion H1 ; subst.
    list_simpl.
    apply wk_ilr.
    apply IHHll.
    * inversion Hnzsp.
      constructor...
      list_simpl in H3.
      apply Forall_Type_app_inv in H3.
      destruct H3 as [H3l H3r].
      inversion H3r.
      inversion H5 ; subst.
      apply Forall_Type_app...
    * list_simpl.
      apply PEperm_PCperm_Type in HP ; unfold id in HP.
      PCperm_Type_solve.
- list_simpl in HP.
  symmetry in HP.
  apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq ; subst.
  + destruct C ; inversion H0.
  + symmetry in H1.
    decomp_map_Type H1 ; decomp_map_Type H3 ; simpl in H3 ; simpl in H5 ; simpl in H7 ; subst.
    apply (f_equal (@rev _)) in H6.
    rewrite rev_involutive in H6 ; subst.
    destruct x0 ; inversion H1 ; subst.
    list_simpl ; apply co_ilr.
    apply IHHll.
    * inversion Hnzsp ; subst.
      list_simpl in H3 ; apply Forall_Type_app_inv in H3 ; destruct H3 as [HF HF2].
      inversion HF2 ; subst.
      constructor...
      apply Forall_Type_app...
      constructor...
    * apply (PEperm_Type_cons _ (wn (dual (ill2ll i2a x0))) _ eq_refl) in HP.
      apply (PEperm_Type_cons _ (wn (dual (ill2ll i2a x0))) _ eq_refl) in HP.
      apply PEperm_PCperm_Type in HP ; unfold id in HP ; list_simpl in HP.
      etransitivity...
      PCperm_Type_solve.
- simpl in f.
  rewrite Hcut in f.
  inversion f.
- apply (Hgax a)...
Qed.


(** Axiom-free conservativity *)
Proposition ll_to_ill_nzeropos_axfree {P} : (projT1 (ipgax P) -> False) -> forall l,
ll (i2pfrag i2a P) l -> forall l0 C, Forall_Type nonzerospos (C :: l0) ->
  PCperm_Type (pperm (i2pfrag i2a P))
    l (ill2ll i2a C :: rev (map dual (map (ill2ll i2a) l0))) ->
  ill P l0 C.
Proof with myeeasy.
intros P_axfree l pi l0 C Hnz HP.
apply cut_admissible_axfree in pi.
- rewrite cutrm_i2pfrag in pi.
  eapply ll_to_ill_nzeropos_cutfree in pi...
  + eapply (stronger_ipfrag)...
    nsplit 3...
    simpl ; intros.
    exfalso ; intuition.
  + intros a.
    exfalso ; intuition.
- intros Hgax ; intuition.
Qed.


(** *** Conservativity with constraints on the left of [ilpam] *)

(** Constraints on the left of [ilpam] for conservativity *)
Inductive oclike : iformula -> Type :=
| ocl_ivar    : forall X, oclike (ivar X)
| ocl_ione    : oclike ione
| ocl_itens   : forall A B, oclike A -> oclike B -> oclike (itens A B)
| ocl_iwith_l : forall A B, oclike A -> oclike (iwith A B)
| ocl_iwith_r : forall A B, oclike A -> oclike (iwith B A)
| ocl_izero   : oclike izero
| ocl_iplus   : forall A B, oclike A -> oclike B -> oclike (iplus A B)
| ocl_ioc     : forall A, oclike (ioc A).

Inductive oclpam : iformula -> Type :=
| oclm_ivar  : forall x, oclpam (ivar x)
| oclm_ione  : oclpam ione
| oclm_itens : forall A B, oclpam A -> oclpam B -> oclpam (itens A B)
| oclm_ilpam : forall A B, oclike A -> oclpam A -> oclpam B -> oclpam (ilpam A B)
| oclm_igen  : forall A, oclike A -> oclpam A -> oclpam (igen A)
| oclm_ilmap : forall A B, oclike A -> oclpam A -> oclpam B -> oclpam (ilmap A B)
| oclm_ineg  : forall A, oclike A -> oclpam A -> oclpam (ineg A)
| oclm_itop  : oclpam itop
| oclm_iwith : forall A B, oclpam A -> oclpam B -> oclpam (iwith A B)
| oclm_izero : oclpam izero
| oclm_iplus : forall A B, oclpam A -> oclpam B -> oclpam (iplus A B)
| oclm_ioc   : forall A, oclpam A -> oclpam (ioc A).

Definition easyipgax_oclmap P := forall a,
  (forall A, In_Type (dual (ill2ll i2a A)) (map (ill2ll i2a) (fst (projT2 (ipgax P) a))) ->
     oclike A -> False)
* (forall A, ill2ll i2a A = ill2ll i2a (snd (projT2 (ipgax P) a)) -> oclike A -> False)
* (forall l C,
     PCperm_Type (ipperm P) (ill2ll i2a (snd (projT2 (ipgax P) a))
                            :: rev (map dual (map (ill2ll i2a) (fst (projT2 (ipgax P) a)))))
                       (ill2ll i2a C :: rev (map dual (map (ill2ll i2a) l)))
       -> ill P l C)
* (In_Type N (fst (projT2 (ipgax P) a)) -> False).

(** Cut-free conservativity *)
Theorem ll_to_ill_oclpam_cutfree {P} :
  ipperm P = true -> ipcut P = false -> easyipgax_oclmap P ->
  forall l, ll (i2pfrag i2a P) l -> forall l0 l1 C, Forall_Type oclpam (C :: l0) ->
    Forall_Type oclike l1 ->
    PCperm_Type (pperm (i2pfrag i2a P)) l
                (ill2ll i2a C :: map (ill2ll i2a) l1
                  ++ rev (map dual (map (ill2ll i2a) l0))) ->
      ill P l0 C
   *  (l1 <> nil -> forall l2, ill P (l0 ++ l2) C).
Proof with myeeasy.
intros Hperm Hcut Hgax.
intros l Hll ; induction Hll ;
  intros l0 lo C Hoclm Hocl HP ; try (now inversion f).
- apply PCperm_Type_length_2_inv in HP.
  destruct HP as [HP | HP] ; inversion HP ; destruct C ; inversion H0 ; subst.
  destruct lo ; list_simpl in H1 ; inversion H1.
  + induction l0 using rev_ind_Type ; list_simpl in H2 ; inversion H2.
    induction l0 using rev_ind_Type ; list_simpl in H4 ; inversion H4.
    destruct x ; inversion H3.
    apply i2a_inj in H5 ; subst.
    split.
    * apply ax_ir.
    * intros Hnil.
      exfalso.
      apply Hnil...
  + destruct i0 ; inversion H2.
- rewrite HP in p.
  apply IHHll in p...
- assert (PCperm_Type (pperm (i2pfrag i2a P)) (l1 ++ map wn lw ++ l2)
       (ill2ll i2a C :: map (ill2ll i2a) lo ++ rev (map dual (map (ill2ll i2a) l0))))
    as HP'.
  { simpl in HP ; rewrite Hperm in HP ; simpl in HP.
    etransitivity...
    apply (Permutation_Type_map wn) in p.
    simpl ; rewrite Hperm ; simpl ; perm_Type_solve. }
  apply IHHll in HP'...
- apply PCperm_Type_length_1_inv in HP.
  inversion HP ; destruct C ; inversion H0 ; subst.
  destruct lo ; inversion H1.
  induction l0 using rev_ind_Type ; list_simpl in H1 ; inversion H1.
  split.
  + apply one_irr.
  + intros Hnil.
    exfalso.
    apply Hnil...
- symmetry in HP ; apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  symmetry in H1 ; dichot_Type_elt_app_exec H1 ; subst ;
    [ decomp_map_Type H0 ; destruct x ; inversion H0
    | list_simpl in H2 ; decomp_map_Type H2 ; decomp_map_Type H3 ;
        destruct x ; inversion H2 ; destruct x0 ; inversion H3 ] ;
    simpl in H3 ; simpl in H5 ; simpl in H7 ; subst.
  apply (f_equal (@rev _)) in H6 ; list_simpl in H6 ; subst.
  apply PEperm_PCperm_Type in HP ; unfold id in HP.
  assert (HP' := PCperm_Type_trans _ _ _ _ HP (PCperm_Type_app_comm _ _ _)).
  specialize IHHll with (rev l8 ++ rev l6) lo C.
  list_simpl in IHHll ; list_simpl in HP' ; apply IHHll in HP'...
  + destruct HP' as [IH1 IH2] ; split.
    * apply one_ilr...
    * intros Hnil l2.
      list_simpl.
      apply one_ilr.
      rewrite app_assoc.
      apply IH2...
  + inversion Hoclm ; constructor...
    apply Forall_Type_app_inv in H4 ; destruct H4 as [Hl Hr] ;
      apply Forall_Type_app...
    inversion Hr...
- symmetry in HP ; apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  simpl in HP ; rewrite Hperm in HP ; simpl in HP.
  apply Permutation_Type_app_app_inv in HP.
  destruct HP as [[[l3' l3''] [l4' l4'']] [[HP1 HP2] [HP3 HP4]]] ;
    simpl in HP1 ; simpl in HP2 ; simpl in HP3 ; simpl in HP4.
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  + apply Permutation_Type_nil in HP4 ; apply app_eq_nil in HP4 ; destruct HP4 ; subst.
    list_simpl in HP1 ; symmetry in HP1.
    list_simpl in HP2 ; symmetry in HP2.
    apply (@Permutation_Type_trans _ _ _ (l2 ++ l1)) in HP3 ;
      [ | apply Permutation_Type_app ]...
    clear l3' l3'' HP1 HP2.
    apply Permutation_Type_app_app_inv in HP3.
    destruct HP3 as [[[l3' l3''] [l4' l4'']] [[HP1 HP2] [HP3 HP4]]] ;
      simpl in HP1 ; simpl in HP2 ; simpl in HP3 ; simpl in HP4.
    symmetry in HP1 ; apply Permutation_Type_map_inv in HP1.
    destruct HP1 as [l3 Heq1 HP1].
    decomp_map_Type Heq1 ; subst.
    list_simpl in HP2.
    rewrite map_map in HP2.
    symmetry in HP2 ; apply Permutation_Type_map_inv in HP2.
    destruct HP2 as [l3 Heq2 HP2].
    apply Permutation_Type_rev' in HP2.
    rewrite rev_involutive in HP2.
    rewrite <- map_map in Heq2.
    decomp_map_Type Heq2 ; decomp_map_Type Heq2 ; simpl in Heq4 ; simpl in Heq5 ; subst.
    specialize IHHll1 with (rev l9) l5 C1.
    specialize IHHll2 with (rev l8) l4 C2.
    simpl in HP1.
    apply (Permutation_Type_Forall_Type _ _ _ HP1) in Hocl.
    apply Forall_Type_app_inv in Hocl ; destruct Hocl as [Hocl2 Hocl1].
    apply IHHll1 in Hocl1 ; [ apply IHHll2 in Hocl2 | | ].
    * destruct Hocl1 as [IH1 IH2].
      destruct Hocl2 as [IH3 IH4].
      split.
      -- eapply ex_ir ; [ apply tens_irr | ]...
         list_simpl in HP2.
         rewrite Hperm ; simpl ; perm_Type_solve.
      -- intros Hnil lw.
         destruct lo ; [ exfalso ; apply Hnil ; reflexivity | ].
         symmetry in HP1 ; apply Permutation_Type_vs_cons_inv in HP1.
         destruct HP1 as [(ll & lr) Heq3].
         dichot_Type_elt_app_exec Heq3 ; subst.
         ++ assert (ll ++ i :: l <> nil) as Hnil2
              by (clear ; intros H ; destruct ll ; inversion H).
            assert (IH := IH4 Hnil2 lw).
            eapply ex_ir ; [apply tens_irr | ]...
            list_simpl in HP2.
            rewrite Hperm ; simpl ; perm_Type_solve.
         ++ assert (l3 ++ i :: lr <> nil) as Hnil2
              by (clear ; intros H ; destruct l3 ; inversion H).
            assert (IH := IH2 Hnil2 lw).
            eapply ex_ir ; [apply tens_irr | ]...
            list_simpl in HP2.
            rewrite Hperm ; simpl ; perm_Type_solve.
    * inversion Hoclm ; subst.
      inversion H2 ; subst.
      constructor...
      list_simpl in HP2.
      apply (Permutation_Type_Forall_Type _ _ _ HP2) in H3.
      apply Forall_Type_app_inv in H3 ; destruct H3 as [_ H3]...
    * simpl ; rewrite Hperm ; simpl ; perm_Type_solve.
    * inversion Hoclm.
      inversion H2.
      constructor...
      list_simpl in HP2.
      apply (Permutation_Type_Forall_Type _ _ _ HP2) in H3.
      apply Forall_Type_app_inv in H3 ; destruct H3 as [H3 _]...
    * simpl ; rewrite Hperm ; simpl ; perm_Type_solve.
  + dichot_Type_elt_app_exec H1 ; subst.
    * decomp_map_Type H0 ; subst.
      destruct x ; inversion H0 ; subst.
      assert (HP4' := HP4).
      symmetry in HP4' ; apply Permutation_Type_vs_cons_inv in HP4'.
      destruct HP4' as [(ll & lr) Heq'] ; simpl in Heq'.
      apply Permutation_Type_app_app_inv in HP3.
      destruct HP3 as [[[l3l l3r] [l4l l4r]] [[HP3' HP3''] [HP3''' HP3'''']]] ;
        simpl in HP3' ; simpl in HP3'' ; simpl in HP3''' ; simpl in HP3''''.
      symmetry in HP3' ; apply Permutation_Type_map_inv in HP3'.
      destruct HP3' as [l3 Heq'' HP3'].
      decomp_map_Type Heq'' ; subst.
      list_simpl in HP3''.
      rewrite map_map in HP3''.
      symmetry in HP3'' ; apply Permutation_Type_map_inv in HP3''.
      destruct HP3'' as [l3 Heq'' HP3''].
      apply Permutation_Type_rev' in HP3'' ; rewrite rev_involutive in HP3''.
      rewrite <- map_map in Heq''.
      decomp_map_Type Heq'' ; decomp_map_Type Heq'' ;
        simpl in Heq''3 ; simpl in Heq''4 ; subst.
      simpl in HP3''' ; apply (Permutation_Type_app_tail l4') in HP3'''.
      assert (HP1' := Permutation_Type_trans HP1 HP3''').
      simpl in HP3'''' ; apply (Permutation_Type_app_tail l4'') in HP3''''.
      assert (HP2' := Permutation_Type_trans HP2 HP3'''').
      dichot_Type_elt_app_exec Heq' ; subst.
      -- list_simpl in HP4 ; apply Permutation_Type_cons_app_inv in HP4.
         symmetry in HP4 ; apply Permutation_Type_map_inv in HP4.
         destruct HP4 as [l3 Heq' HP].
         decomp_map_Type Heq' ; subst.
         specialize IHHll2 with (rev l11) (x2 :: l7 ++ l10 ++ l14) C.
         assert (Forall_Type oclike (x2 :: l7 ++ l10 ++ l14)) as Hocl'.
         { simpl in HP ; simpl in Hocl.
           apply Forall_Type_app_inv in Hocl ; destruct Hocl as [Hocl2 Hocl1].
           apply (Permutation_Type_Forall_Type _ _ _ HP) in Hocl2.
           inversion Hocl1.
           inversion H2 ; subst.
           constructor...
           simpl in HP3'.
           apply (Permutation_Type_Forall_Type _ _ _ HP3') in H3.
           apply Forall_Type_app_inv in H3 ; destruct H3 ; apply Forall_Type_app...
           rewrite app_assoc in Hocl2.
           apply Forall_Type_app_inv in Hocl2 ; destruct Hocl2... }
         apply IHHll2 in Hocl'.
         ++ destruct Hocl' as [_ Hocl'].
            assert (x2 :: l7 ++ l10 ++ l14 <> nil) as Hnil
              by (intros Hnil ; inversion Hnil).
            split.
            ** eapply Hocl' in Hnil.
               eapply ex_ir ; [ apply Hnil | ].
               simpl in HP3'' ; symmetry in HP3''.
               rewrite Hperm ; simpl ; etransitivity ; [ | apply HP3'' ].
               rewrite rev_app_distr.
               apply Permutation_Type_app_comm.
            ** intros Hnil' l.
               eapply Hocl' in Hnil.
               eapply ex_ir ; [ apply Hnil | ].
               simpl in HP3'' ; symmetry in HP3''.
               apply (Permutation_Type_app_tail l) in HP3''.
               rewrite Hperm ; simpl ; etransitivity ; [ | apply HP3'' ].
               rewrite rev_app_distr.
               rewrite <- app_assoc.
               etransitivity ; [ | apply Permutation_Type_app_rot ].
               etransitivity ; [ | apply Permutation_Type_app_rot ].
               apply Permutation_Type_app_head...
         ++ inversion Hoclm ; constructor...
            simpl in HP3''.
            apply (Permutation_Type_Forall_Type _ _ _ HP3'') in H3.
            list_simpl in H3 ; apply Forall_Type_app_inv in H3 ; apply H3.
         ++ list_simpl ; rewrite Hperm ; simpl.
            perm_Type_solve.
      -- list_simpl in HP4 ; rewrite app_assoc in HP4 ;
           apply Permutation_Type_cons_app_inv in HP4.
         symmetry in HP4 ; apply Permutation_Type_map_inv in HP4.
         destruct HP4 as [l' Heq' HP].
         list_simpl in Heq' ; decomp_map_Type Heq' ; subst.
         specialize IHHll1 with (rev l12) (x1 :: l8 ++ l13 ++ l14) C.
         assert (Forall_Type oclike (x1 :: l8 ++ l13 ++ l14)) as Hocl'.
         { simpl in HP ; simpl in Hocl.
           apply Forall_Type_app_inv in Hocl ; destruct Hocl as [Hocl2 Hocl1].
           apply (Permutation_Type_Forall_Type _ _ _ HP) in Hocl2.
           inversion Hocl1.
           inversion H2 ; subst.
           constructor...
           simpl in HP3'.
           apply (Permutation_Type_Forall_Type _ _ _ HP3') in H3.
           apply Forall_Type_app_inv in H3 ; destruct H3 ; apply Forall_Type_app...
           apply Forall_Type_app_inv in Hocl2 ; destruct Hocl2... }
         apply IHHll1 in Hocl'.
         ++ destruct Hocl' as [_ Hocl'].
            assert (x1 :: l8 ++ l13 ++ l14 <> nil) as Hnil
              by (intros Hnil ; inversion Hnil).
            split.
            ** eapply Hocl' in Hnil.
               eapply ex_ir ; [ apply Hnil | ].
               simpl in HP3'' ; symmetry in HP3''.
               rewrite Hperm ; simpl ; etransitivity ; [ | apply HP3'' ].
               rewrite rev_app_distr ; reflexivity.
            ** intros Hnil' l.
               eapply Hocl' in Hnil.
               eapply ex_ir ; [ apply Hnil | ].
               simpl in HP3'' ; symmetry in HP3''.
               apply (Permutation_Type_app_tail l) in HP3''.
               rewrite Hperm ; simpl ; etransitivity ; [ | apply HP3'' ].
               rewrite rev_app_distr.
               rewrite <- app_assoc.
               apply Permutation_Type_app_head...
         ++ inversion Hoclm ; constructor...
            simpl in HP3''.
            apply (Permutation_Type_Forall_Type _ _ _ HP3'') in H3.
            list_simpl in H3 ; apply Forall_Type_app_inv in H3 ; apply H3.
         ++ list_simpl ; rewrite Hperm ; simpl.
            perm_Type_solve.
    * list_simpl in H2 ; decomp_map_Type H2 ; subst.
      decomp_map_Type H3 ;
        simpl in H1 ; simpl in H3 ; simpl in H4 ; simpl in H5 ; subst.
      apply (f_equal (@rev _)) in H4 ; list_simpl in H4 ; subst.
      destruct x0 ; inversion H2 ; subst.
      -- assert (HP4' := HP4).
         symmetry in HP4' ; apply Permutation_Type_vs_cons_inv in HP4'.
         destruct HP4' as [(l4a & l4b) Heq'] ; simpl in Heq'.
         dichot_Type_elt_app_exec Heq' ; subst.
         ++ simpl in HP3 ; rewrite map_map in HP3.
            symmetry in HP3 ; apply Permutation_Type_map_inv in HP3.
            destruct HP3 as [l3''' Heq' HP3].
            decomp_map_Type Heq' ; subst.
            rewrite <- map_map in HP1.
            rewrite <- map_map in HP2.
            list_simpl in HP4 ; apply Permutation_Type_cons_app_inv in HP4.
            apply Permutation_Type_app_app_inv in HP4.
            destruct HP4 as [[[l3a l3b] [l3c l3d]] [[HP4' HP4''] [HP4''' HP4'''']]] ;
              simpl in HP4' ; simpl in HP4'' ; simpl in HP4''' ; simpl in HP4''''.
            apply Permutation_Type_app_app_inv in HP4''''.
            destruct HP4'''' as [[[l3e l3f] [l3g l3h]] [[HP4a HP4b] [HP4c HP4d]]] ;
              simpl in HP4a ; simpl in HP4b ; simpl in HP4c ; simpl in HP4d.
            simpl in HP1.
            assert (Permutation_Type l2
                     (map dual (map (ill2ll i2a) l4) ++ (l3a ++ l3b)
                       ++ ill2ll i2a C :: l3e ++ l3g))
              as HP' by perm_Type_solve.
            symmetry in HP4' ; apply Permutation_Type_map_inv in HP4'.
            destruct HP4' as [l3' Heq' HP4'].
            decomp_map_Type Heq' ; subst.
            apply (Permutation_Type_app_head l3b) in HP4d.
            assert (HP'' := Permutation_Type_trans HP4'' HP4d).
            rewrite map_map in HP''.
            symmetry in HP'' ; apply Permutation_Type_map_inv in HP''.
            clear HP4'' ; destruct HP'' as [l4' Heq' HP4''].
            decomp_map_Type Heq' ; subst.
            rewrite <- (map_map _ _ l11) in HP'.
            rewrite <- (map_map _ _ l13) in HP'.
            symmetry in HP4c ; apply Permutation_Type_map_inv in HP4c.
            destruct HP4c as [l4' Heq' HP4c].
            decomp_map_Type Heq' ; subst.
            rewrite <- (map_map _ _ l14) in HP4b.
            simpl in HP2 ; simpl in HP4b.
            apply (Permutation_Type_app_head (map dual (map (ill2ll i2a) l6))) in HP4b.
            assert (HP'' := Permutation_Type_trans HP2 HP4b).
            specialize IHHll2 with (rev (x0_2 :: l4 ++ l11 ++ l13)) (l9 ++ l15) C.
            simpl in HP4' ; apply (Permutation_Type_Forall_Type _ _ _ HP4') in Hocl.
            apply Forall_Type_app_inv in Hocl ; destruct Hocl as [Hocl1 Hocl2].
            specialize IHHll1 with (rev (l6 ++ l14)) l16 x0_1.
            simpl in HP4c ; apply (Permutation_Type_Forall_Type _ _ _ HP4c) in Hocl2.
            apply Forall_Type_app_inv in Hocl2 ; destruct Hocl2 as [Hocl2 Hocl3].
            assert (Hocl4 := Forall_Type_app _ _ _ Hocl1 Hocl2).
            apply IHHll2 in Hocl4 ; [ apply IHHll1 in Hocl3 | | ].
            ** split.
               --- destruct Hocl4 as [Hocl4 _].
                   destruct Hocl3 as [Hocl3 _].
                   apply (ex_ir _ (rev (l4 ++ l11 ++ l13) ++
                                     ilpam x0_1 x0_2 :: rev (l6 ++ l14) ++ nil)).
                   +++ apply lpam_ilr...
                   +++ apply Permutation_Type_rev' in HP3 .
                       apply Permutation_Type_rev' in HP4''.
                       list_simpl in HP3 ; list_simpl in HP4''.
                       rewrite Hperm ; list_simpl ; perm_Type_solve.
               --- intros Hnil lw ; destruct lo ; [ contradiction Hnil ; reflexivity | ].
                   apply (Permutation_Type_app_head l9) in HP4c.
                   assert (HP''' := Permutation_Type_trans HP4' HP4c).
                   symmetry in HP''' ; apply Permutation_Type_vs_cons_inv in HP'''.
                   destruct HP''' as [(l4l & l4r) Heq'] ; simpl in Heq'.
                   rewrite app_assoc in Heq'.
                   dichot_Type_elt_app_exec Heq' ; subst.
                   +++ rewrite <- Heq'0 in Hocl4.
                       assert (l4l ++ i :: l0 <> nil) as Hnil'
                         by (intros Hnil' ; destruct l4l ; inversion Hnil').
                       apply (snd Hocl4) with lw in Hnil'.
                       destruct Hocl3 as [Hocl3 _].
                       apply (ex_ir _ (rev (l4 ++ l11 ++ l13) ++
                                         ilpam x0_1 x0_2 :: rev (l6 ++ l14) ++ lw)).
                       *** apply lpam_ilr...
                           eapply ex_ir ; [ apply Hnil' | ].
                           rewrite Hperm ; simpl ; perm_Type_solve.
                       *** apply Permutation_Type_rev' in HP3 .
                           apply Permutation_Type_rev' in HP4''.
                           list_simpl in HP3 ; list_simpl in HP4''.
                           rewrite Hperm ; list_simpl ; perm_Type_solve.
                   +++ assert (l17 ++ i :: l4r <> nil) as Hnil'
                         by (intros Hnil' ; destruct l17 ; inversion Hnil').
                       apply (snd Hocl3) with lw in Hnil'.
                       destruct Hocl4 as [Hocl4 _].
                       apply (ex_ir _ (rev (l4 ++ l11 ++ l13) ++
                                         ilpam x0_1 x0_2 :: (rev (l6 ++ l14) ++ lw) ++ nil)).
                       *** apply lpam_ilr...
                       *** apply Permutation_Type_rev' in HP3 .
                           apply Permutation_Type_rev' in HP4''.
                           list_simpl in HP3 ; list_simpl in HP4''.
                           rewrite Hperm ; list_simpl ; perm_Type_solve.
            ** inversion Hoclm ; subst.
               apply Forall_Type_app_inv in H3 ; destruct H3 as [Hoclm1 Hoclm2].
               inversion Hoclm2 ; subst.
               inversion H3 ; constructor...
               simpl in HP3.
               apply Permutation_Type_rev' in HP3.
               apply (Permutation_Type_Forall_Type _ _ _ HP3) in Hoclm1.
               list_simpl in Hoclm1 ; list_simpl.
               apply Forall_Type_app_inv in Hoclm1 ; destruct Hoclm1.
               simpl in HP4''.
               apply Permutation_Type_rev' in HP4''.
               apply (Permutation_Type_Forall_Type _ _ _ HP4'') in H4.
               list_simpl in H4.
               apply Forall_Type_app_inv in H4 ; destruct H4 ; apply Forall_Type_app...
            ** simpl ; rewrite Hperm ; simpl.
               rewrite bidual.
               perm_Type_solve.
            ** inversion Hoclm ; constructor ; subst...
               list_simpl.
               apply Forall_Type_app_inv in H3 ; destruct H3 as [Hoclm1 Hoclm2].
               inversion Hoclm2 ; subst.
               simpl in HP4''.
               apply Permutation_Type_rev' in HP4''.
               apply (Permutation_Type_Forall_Type _ _ _ HP4'') in H4.
               list_simpl in H4.
               apply Forall_Type_app_inv in H4.
               destruct H4 as [H4l H4r] ; apply Forall_Type_app_inv in H4r.
               apply Forall_Type_app ; [ apply H4r | ].
               apply Forall_Type_app ; [ apply H4r | ].
               simpl in HP3.
               apply Permutation_Type_rev' in HP3.
               apply (Permutation_Type_Forall_Type _ _ _ HP3) in Hoclm1.
               list_simpl in Hoclm1 ; list_simpl.
               apply Forall_Type_app_inv in Hoclm1 ; destruct Hoclm1.
               inversion H3.
               apply Forall_Type_app ; [ | constructor ; [assumption | constructor] ]...
            ** list_simpl ; rewrite Hperm ; simpl.
               perm_Type_solve.
         ++ simpl in HP3 ; rewrite map_map in HP3.
            symmetry in HP3 ; apply Permutation_Type_map_inv in HP3.
            destruct HP3 as [l3''' Heq' HP3].
            decomp_map_Type Heq' ; subst.
            rewrite <- map_map in HP1.
            rewrite <- map_map in HP2.
            rewrite app_assoc in HP4 ; apply Permutation_Type_cons_app_inv in HP4.
            list_simpl in HP4 ; apply Permutation_Type_app_app_inv in HP4.
            destruct HP4 as [[[l3a l3b] [l3c l3d]] [[HP4' HP4''] [HP4''' HP4'''']]] ;
              simpl in HP4' ; simpl in HP4'' ; simpl in HP4''' ; simpl in HP4''''.
            apply Permutation_Type_app_app_inv in HP4''''.
            destruct HP4'''' as [[[l3e l3f] [l3g l3h]] [[HP4a HP4b] [HP4c HP4d]]] ;
              simpl in HP4a ; simpl in HP4b ; simpl in HP4c ; simpl in HP4d.
            symmetry in HP4' ; apply Permutation_Type_map_inv in HP4'.
            destruct HP4' as [l3' Heq' HP4'].
            decomp_map_Type Heq' ; subst.
            apply (Permutation_Type_app_head l3b) in HP4d.
            assert (HP' := Permutation_Type_trans HP4'' HP4d).
            rewrite map_map in HP'.
            symmetry in HP' ; apply Permutation_Type_map_inv in HP'.
            clear HP4'' ; destruct HP' as [l4'' Heq' HP4''].
            decomp_map_Type Heq' ; subst.
            simpl in HP2 ; simpl in HP4a.
            apply (Permutation_Type_app_tail (ill2ll i2a C :: l4b)) in HP4a.
            apply (Permutation_Type_app_head (map dual (map (ill2ll i2a) l6))) in HP4a.
            assert (HP' := Permutation_Type_trans HP2 HP4a).
            rewrite <- (map_map _ _ l13) in HP'. 
            symmetry in HP4c ; apply Permutation_Type_map_inv in HP4c.
            destruct HP4c as [l4'' Heq' HP4c].
            decomp_map_Type Heq' ; subst.
            rewrite <- (map_map _ _ l14) in HP4b.
            simpl in HP4b ; simpl in HP'.
            apply (@Permutation_Type_cons _ (ill2ll i2a C) _ eq_refl) in HP4b.
            apply (Permutation_Type_app_head (map dual (map (ill2ll i2a) l6)
              ++ (map (ill2ll i2a) l15 ++ map dual (map (ill2ll i2a) l13)))) in HP4b.
            rewrite <- app_assoc in HP4b.
            assert (HP'' := Permutation_Type_trans HP' HP4b).
            specialize IHHll1 with (rev (l13 ++ l6 ++ l14)) (x0_1 :: l15 ++ l16) C.
            assert (x0_1 :: l15 ++ l16 <> nil) as Hnil
              by (intros Hnil ; inversion Hnil).
            inversion Hoclm ; subst.
            apply Forall_Type_app_inv in H3 ; destruct H3 as [Hoclm1 Hoclm2].
            inversion Hoclm2 ; subst.
            inversion H3 ; subst.
            simpl in HP4' ; simpl in HP4c.
            apply (Permutation_Type_Forall_Type _ _ _ HP4') in Hocl.
            apply (Permutation_Type_app_head l9) in HP4c.
            apply (Permutation_Type_Forall_Type _ _ _ HP4c) in Hocl.
            apply Forall_Type_app_inv in Hocl ; destruct Hocl as [_ Hocl].
            assert (Hocl' := Forall_Type_cons _ H5 Hocl).
            apply IHHll1 in Hocl' ; [ split | | ].
            ** apply (snd Hocl') with (ilpam x0_1 x0_2 :: rev l4 ++ rev l11) in Hnil.
               eapply ex_ir ; [ apply Hnil | ].
               simpl ; rewrite Hperm ; simpl.
               simpl in HP3.
               apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
               simpl in HP4''.
               apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
               list_simpl ; perm_Type_solve.
            ** intros Hnil' lw.
               apply (snd Hocl') with (ilpam x0_1 x0_2 :: rev l4 ++ rev l11 ++ lw) in Hnil.
               eapply ex_ir ; [ apply Hnil | ].
               simpl ; rewrite Hperm ; simpl.
               simpl in HP3.
               apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
               simpl in HP4''.
               apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
               list_simpl ; perm_Type_solve.
            ** constructor...
               simpl in HP4''.
               apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
               apply (Permutation_Type_Forall_Type _ _ _ HP4'') in H4.
               rewrite app_assoc in H4.
               apply Forall_Type_app_inv in H4 ; destruct H4 as [H4 _].
               apply Forall_Type_app_inv in H4 ; destruct H4 as [H4l H4r].
               simpl in HP3.
               apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
               apply (Permutation_Type_Forall_Type _ _ _ HP3) in Hoclm1.
               list_simpl in Hoclm1 ; apply Forall_Type_app_inv in Hoclm1 ;
                 destruct Hoclm1 as [Hoclm1 _].
               list_simpl.
               apply Forall_Type_app...
               apply Forall_Type_app...
            ** list_simpl ; rewrite Hperm ; simpl.
               rewrite bidual ; perm_Type_solve.
      -- assert (HP4' := HP4).
         symmetry in HP4' ; apply Permutation_Type_vs_cons_inv in HP4'.
         destruct HP4' as [(l4a & l4b) Heq'] ; simpl in Heq'.
         dichot_Type_elt_app_exec Heq' ; subst.
         ++ simpl in HP3 ; rewrite map_map in HP3.
            symmetry in HP3 ; apply Permutation_Type_map_inv in HP3.
            destruct HP3 as [l3''' Heq' HP3].
            decomp_map_Type Heq' ; subst.
            rewrite <- map_map in HP1.
            rewrite <- map_map in HP2.
            list_simpl in HP4 ; apply Permutation_Type_cons_app_inv in HP4.
            apply Permutation_Type_app_app_inv in HP4.
            destruct HP4 as [[[l3a l3b] [l3c l3d]] [[HP4' HP4''] [HP4''' HP4'''']]] ;
              simpl in HP4' ; simpl in HP4'' ; simpl in HP4''' ; simpl in HP4''''.
            apply Permutation_Type_app_app_inv in HP4''''.
            destruct HP4'''' as [[[l3e l3f] [l3g l3h]] [[HP4a HP4b] [HP4c HP4d]]] ;
              simpl in HP4a ; simpl in HP4b ; simpl in HP4c ; simpl in HP4d.
            simpl in HP1.
            assert (Permutation_Type l2
                     (map dual (map (ill2ll i2a) l4) ++ (l3a ++ l3b)
                       ++ ill2ll i2a C :: l3e ++ l3g))
              as HP' by perm_Type_solve.
            symmetry in HP4' ; apply Permutation_Type_map_inv in HP4'.
            destruct HP4' as [l3' Heq' HP4'].
            decomp_map_Type Heq' ; subst.
            apply (Permutation_Type_app_head l3b) in HP4d.
            assert (HP'' := Permutation_Type_trans HP4'' HP4d).
            rewrite map_map in HP''.
            symmetry in HP'' ; apply Permutation_Type_map_inv in HP''.
            clear HP4'' ; destruct HP'' as [l4' Heq' HP4''].
            decomp_map_Type Heq' ; subst.
            rewrite <- (map_map _ _ l11) in HP'.
            rewrite <- (map_map _ _ l13) in HP'.
            symmetry in HP4c ; apply Permutation_Type_map_inv in HP4c.
            destruct HP4c as [l4' Heq' HP4c].
            decomp_map_Type Heq' ; subst.
            rewrite <- (map_map _ _ l14) in HP4b.
            simpl in HP2 ; simpl in HP4b.
            apply (Permutation_Type_app_head (map dual (map (ill2ll i2a) l6))) in HP4b.
            assert (HP'' := Permutation_Type_trans HP2 HP4b).
            specialize IHHll2 with (rev (N :: l4 ++ l11 ++ l13)) (l9 ++ l15) C.
            simpl in HP4' ; apply (Permutation_Type_Forall_Type _ _ _ HP4') in Hocl.
            apply Forall_Type_app_inv in Hocl ; destruct Hocl as [Hocl1 Hocl2].
            specialize IHHll1 with (rev (l6 ++ l14)) l16 x0.
            simpl in HP4c ; apply (Permutation_Type_Forall_Type _ _ _ HP4c) in Hocl2.
            apply Forall_Type_app_inv in Hocl2 ; destruct Hocl2 as [Hocl2 Hocl3].
            assert (Hocl4 := Forall_Type_app _ _ _ Hocl1 Hocl2).
            apply IHHll2 in Hocl4 ; [ apply IHHll1 in Hocl3 | | ].
            ** split.
               --- destruct Hocl4 as [Hocl4 _].
                   destruct Hocl3 as [Hocl3 _].
                   apply (ex_ir _ (rev (l4 ++ l11 ++ l13) ++
                                     igen x0 :: rev (l6 ++ l14) ++ nil)).
                   +++ apply gen_pam_rule...
                       intros a ; apply Hgax.
                   +++ apply Permutation_Type_rev' in HP3 .
                       apply Permutation_Type_rev' in HP4''.
                       list_simpl in HP3 ; list_simpl in HP4''.
                       rewrite Hperm ; list_simpl ; perm_Type_solve.
               --- intros Hnil lw ; destruct lo ; [ contradiction Hnil ; reflexivity | ].
                   apply (Permutation_Type_app_head l9) in HP4c.
                   assert (HP''' := Permutation_Type_trans HP4' HP4c).
                   symmetry in HP''' ; apply Permutation_Type_vs_cons_inv in HP'''.
                   destruct HP''' as [(l4l & l4r) Heq'] ; simpl in Heq'.
                   rewrite app_assoc in Heq'.
                   dichot_Type_elt_app_exec Heq' ; subst.
                   +++ rewrite <- Heq'0 in Hocl4.
                       assert (l4l ++ i :: l0 <> nil) as Hnil'
                         by (intros Hnil' ; destruct l4l ; inversion Hnil').
                       apply (snd Hocl4) with lw in Hnil'.
                       destruct Hocl3 as [Hocl3 _].
                       apply (ex_ir _ (rev (l4 ++ l11 ++ l13) ++
                                         igen x0 :: rev (l6 ++ l14) ++ lw)).
                       *** apply gen_pam_rule...
                           ---- intros a ; apply Hgax.
                           ---- eapply ex_ir ; [ apply Hnil' | ].
                                rewrite Hperm ; simpl ; perm_Type_solve.
                       *** apply Permutation_Type_rev' in HP3 .
                           apply Permutation_Type_rev' in HP4''.
                           list_simpl in HP3 ; list_simpl in HP4''.
                           rewrite Hperm ; list_simpl ; perm_Type_solve.
                   +++ assert (l17 ++ i :: l4r <> nil) as Hnil'
                         by (intros Hnil' ; destruct l17 ; inversion Hnil').
                       apply (snd Hocl3) with lw in Hnil'.
                       destruct Hocl4 as [Hocl4 _].
                       apply (ex_ir _ (rev (l4 ++ l11 ++ l13) ++
                                         igen x0 :: (rev (l6 ++ l14) ++ lw) ++ nil)).
                       *** apply gen_pam_rule...
                           intros a ; apply Hgax.
                       *** apply Permutation_Type_rev' in HP3 .
                           apply Permutation_Type_rev' in HP4''.
                           list_simpl in HP3 ; list_simpl in HP4''.
                           rewrite Hperm ; list_simpl ; perm_Type_solve.
            ** inversion Hoclm ; subst.
               apply Forall_Type_app_inv in H3 ; destruct H3 as [Hoclm1 Hoclm2].
               inversion Hoclm2 ; subst.
               inversion H3 ; constructor...
               simpl in HP3.
               apply Permutation_Type_rev' in HP3.
               apply (Permutation_Type_Forall_Type _ _ _ HP3) in Hoclm1.
               list_simpl in Hoclm1 ; list_simpl.
               apply Forall_Type_app_inv in Hoclm1 ; destruct Hoclm1.
               simpl in HP4''.
               apply Permutation_Type_rev' in HP4''.
               apply (Permutation_Type_Forall_Type _ _ _ HP4'') in H4.
               list_simpl in H4.
               apply Forall_Type_app_inv in H4 ; destruct H4 ; apply Forall_Type_app...
            ** simpl ; rewrite Hperm ; simpl.
               rewrite bidual.
               perm_Type_solve.
            ** inversion Hoclm ; constructor ; subst...
               list_simpl.
               apply Forall_Type_app_inv in H3 ; destruct H3 as [Hoclm1 Hoclm2].
               inversion Hoclm2 ; subst.
               simpl in HP4''.
               apply Permutation_Type_rev' in HP4''.
               apply (Permutation_Type_Forall_Type _ _ _ HP4'') in H4.
               list_simpl in H4.
               apply Forall_Type_app_inv in H4.
               destruct H4 as [H4l H4r] ; apply Forall_Type_app_inv in H4r.
               apply Forall_Type_app ; [ apply H4r | ].
               apply Forall_Type_app ; [ apply H4r | ].
               simpl in HP3.
               apply Permutation_Type_rev' in HP3.
               apply (Permutation_Type_Forall_Type _ _ _ HP3) in Hoclm1.
               list_simpl in Hoclm1 ; list_simpl.
               apply Forall_Type_app_inv in Hoclm1 ; destruct Hoclm1.
               inversion H3.
               apply Forall_Type_app ; [ | constructor ; [ constructor | constructor] ]...
            ** list_simpl ; rewrite Hperm ; simpl.
               perm_Type_solve.
         ++ simpl in HP3 ; rewrite map_map in HP3.
            symmetry in HP3 ; apply Permutation_Type_map_inv in HP3.
            destruct HP3 as [l3''' Heq' HP3].
            decomp_map_Type Heq' ; subst.
            rewrite <- map_map in HP1.
            rewrite <- map_map in HP2.
            rewrite app_assoc in HP4 ; apply Permutation_Type_cons_app_inv in HP4.
            list_simpl in HP4 ; apply Permutation_Type_app_app_inv in HP4.
            destruct HP4 as [[[l3a l3b] [l3c l3d]] [[HP4' HP4''] [HP4''' HP4'''']]] ;
              simpl in HP4' ; simpl in HP4'' ; simpl in HP4''' ; simpl in HP4''''.
            apply Permutation_Type_app_app_inv in HP4''''.
            destruct HP4'''' as [[[l3e l3f] [l3g l3h]] [[HP4a HP4b] [HP4c HP4d]]] ;
              simpl in HP4a ; simpl in HP4b ; simpl in HP4c ; simpl in HP4d.
            symmetry in HP4' ; apply Permutation_Type_map_inv in HP4'.
            destruct HP4' as [l3' Heq' HP4'].
            decomp_map_Type Heq' ; subst.
            apply (Permutation_Type_app_head l3b) in HP4d.
            assert (HP' := Permutation_Type_trans HP4'' HP4d).
            rewrite map_map in HP'.
            symmetry in HP' ; apply Permutation_Type_map_inv in HP'.
            clear HP4'' ; destruct HP' as [l4'' Heq' HP4''].
            decomp_map_Type Heq' ; subst.
            simpl in HP2 ; simpl in HP4a.
            apply (Permutation_Type_app_tail (ill2ll i2a C :: l4b)) in HP4a.
            apply (Permutation_Type_app_head (map dual (map (ill2ll i2a) l6))) in HP4a.
            assert (HP' := Permutation_Type_trans HP2 HP4a).
            rewrite <- (map_map _ _ l13) in HP'. 
            symmetry in HP4c ; apply Permutation_Type_map_inv in HP4c.
            destruct HP4c as [l4'' Heq' HP4c].
            decomp_map_Type Heq' ; subst.
            rewrite <- (map_map _ _ l14) in HP4b.
            simpl in HP4b ; simpl in HP'.
            apply (@Permutation_Type_cons _ (ill2ll i2a C) _ eq_refl) in HP4b.
            apply (Permutation_Type_app_head (map dual (map (ill2ll i2a) l6)
              ++ (map (ill2ll i2a) l15 ++ map dual (map (ill2ll i2a) l13)))) in HP4b.
            rewrite <- app_assoc in HP4b.
            assert (HP'' := Permutation_Type_trans HP' HP4b).
            specialize IHHll1 with (rev (l13 ++ l6 ++ l14)) (x0 :: l15 ++ l16) C.
            assert (x0 :: l15 ++ l16 <> nil) as Hnil
              by (intros Hnil ; inversion Hnil).
            inversion Hoclm ; subst.
            apply Forall_Type_app_inv in H3 ; destruct H3 as [Hoclm1 Hoclm2].
            inversion Hoclm2 ; subst.
            inversion H3 ; subst.
            simpl in HP4' ; simpl in HP4c.
            apply (Permutation_Type_Forall_Type _ _ _ HP4') in Hocl.
            apply (Permutation_Type_app_head l9) in HP4c.
            apply (Permutation_Type_Forall_Type _ _ _ HP4c) in Hocl.
            apply Forall_Type_app_inv in Hocl ; destruct Hocl as [_ Hocl].
            assert (Hocl' := Forall_Type_cons _ H0 Hocl).
            apply IHHll1 in Hocl' ; [ split | | ].
            ** apply (snd Hocl') with (igen x0 :: rev l4 ++ rev l11) in Hnil.
               eapply ex_ir ; [ apply Hnil | ].
               simpl ; rewrite Hperm ; simpl.
               simpl in HP3.
               apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
               simpl in HP4''.
               apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
               list_simpl ; perm_Type_solve.
            ** intros Hnil' lw.
               apply (snd Hocl') with (igen x0 :: rev l4 ++ rev l11 ++ lw) in Hnil.
               eapply ex_ir ; [ apply Hnil | ].
               simpl ; rewrite Hperm ; simpl.
               simpl in HP3.
               apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
               simpl in HP4''.
               apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
               list_simpl ; perm_Type_solve.
            ** constructor...
               simpl in HP4''.
               apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
               apply (Permutation_Type_Forall_Type _ _ _ HP4'') in H4.
               rewrite app_assoc in H4.
               apply Forall_Type_app_inv in H4 ; destruct H4 as [H4 _].
               apply Forall_Type_app_inv in H4 ; destruct H4 as [H4l H4r].
               simpl in HP3.
               apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
               apply (Permutation_Type_Forall_Type _ _ _ HP3) in Hoclm1.
               list_simpl in Hoclm1 ; apply Forall_Type_app_inv in Hoclm1 ;
                 destruct Hoclm1 as [Hoclm1 _].
               list_simpl.
               apply Forall_Type_app...
               apply Forall_Type_app...
            ** list_simpl ; rewrite Hperm ; simpl.
               rewrite bidual ; perm_Type_solve.
      -- assert (HP4' := HP4).
         symmetry in HP4' ; apply Permutation_Type_vs_cons_inv in HP4'.
         destruct HP4' as [(l4a & l4b) Heq'].
         dichot_Type_elt_app_exec Heq' ; subst.
         ++ simpl in HP3 ; rewrite map_map in HP3.
            symmetry in HP3 ; apply Permutation_Type_map_inv in HP3.
            destruct HP3 as [l3''' Heq' HP3].
            decomp_map_Type Heq' ; subst.
            rewrite <- map_map in HP1.
            list_simpl in HP4 ; apply Permutation_Type_cons_app_inv in HP4.
            apply Permutation_Type_app_app_inv in HP4.
            destruct HP4 as [[[l3a l3b] [l3c l3d]] [[HP4' HP4''] [HP4''' HP4'''']]] ;
              simpl in HP4' ; simpl in HP4'' ; simpl in HP4''' ; simpl in HP4''''.
            apply Permutation_Type_app_app_inv in HP4''''.
            destruct HP4'''' as [[[l3e l3f] [l3g l3h]] [[HP4a HP4b] [HP4c HP4d]]] ;
              simpl in HP4a ; simpl in HP4b ; simpl in HP4c ; simpl in HP4d.
            simpl in HP1.
            apply (@Permutation_Type_cons _ (ill2ll i2a C) _ eq_refl) in HP4a.
            apply (Permutation_Type_app HP4''') in HP4a.
            apply (Permutation_Type_app_head (map dual (map (ill2ll i2a) l4))) in HP4a.
            assert (HP' := Permutation_Type_trans HP1 HP4a).
            symmetry in HP4' ; apply Permutation_Type_map_inv in HP4'.
            destruct HP4' as [l3' Heq' HP4'].
            decomp_map_Type Heq' ; subst.
            apply (Permutation_Type_app_head l3b) in HP4d.
            assert (HP'' := Permutation_Type_trans HP4'' HP4d).
            rewrite map_map in HP''.
            symmetry in HP'' ; apply Permutation_Type_map_inv in HP''.
            clear HP4'' ; destruct HP'' as [l4' Heq' HP4''].
            decomp_map_Type Heq' ; subst.
            rewrite <- (map_map _ _ l11) in HP'.
            rewrite <- (map_map _ _ l13) in HP'.
            simpl in HP4c. 
            symmetry in HP4c ; apply Permutation_Type_map_inv in HP4c.
            destruct HP4c as [l4' Heq' HP4c].
            decomp_map_Type Heq' ; subst.
            specialize IHHll2 with (rev (l4 ++ l11 ++ l13)) (x0_1 :: l9 ++ l15) C.
            simpl in HP4' ; apply (Permutation_Type_Forall_Type _ _ _ HP4') in Hocl.
            apply Forall_Type_app_inv in Hocl ; destruct Hocl as [Hocl1 Hocl2].
            simpl in HP4c ; apply (Permutation_Type_Forall_Type _ _ _ HP4c) in Hocl2.
            apply Forall_Type_app_inv in Hocl2 ; destruct Hocl2 as [Hocl2 _].
            assert (Hocl3 := Forall_Type_app _ _ _ Hocl1 Hocl2).
            inversion Hoclm ; subst.
            apply Forall_Type_app_inv in H3 ; destruct H3 as [_ H3].
            inversion H3 ; inversion H4 ; subst.
            assert (Hocl4 := Forall_Type_cons _ H8 Hocl3).
            apply IHHll2 in Hocl4.
            ** assert (x0_1 :: l9 ++ l15 <> nil) as Hnil
                 by (intros Hnil ; inversion Hnil).
               split.
               --- apply (snd Hocl4) with (ilmap x0_1 x0_2 :: rev l6 ++ rev l14) in Hnil.
                   eapply ex_ir ; [ apply Hnil | ].
                   rewrite Hperm ; simpl.
                   apply Permutation_Type_elt.
                   simpl in HP3.
                   apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
                   simpl in HP4''.
                   apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
                   list_simpl ; perm_Type_solve.
               --- intros Hnil' lw.
                   apply (snd Hocl4) with (ilmap x0_1 x0_2 :: lw ++ rev l6 ++ rev l14) in Hnil.
                   eapply ex_ir ; [ apply Hnil | ].
                   rewrite Hperm ; simpl.
                   rewrite <- app_assoc ; rewrite <- app_comm_cons ; apply Permutation_Type_elt.
                   simpl in HP3.
                   apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
                   simpl in HP4''.
                   apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
                   list_simpl ; perm_Type_solve.
            ** constructor...
               simpl in HP4''.
               apply Permutation_Type_rev' in HP4''.
               apply (Permutation_Type_Forall_Type _ _ _ HP4'') in H5.
               list_simpl in H5.
               apply Forall_Type_app_inv in H5 ; destruct H5 as [_ Hoclm1].
               inversion Hoclm ; subst.
               apply Forall_Type_app_inv in H6 ; destruct H6 as [Hoclm2 _].
               simpl in HP3.
               apply Permutation_Type_rev' in HP3.
               apply (Permutation_Type_Forall_Type _ _ _ HP3) in Hoclm2.
               list_simpl in Hoclm2.
               apply Forall_Type_app_inv in Hoclm2 ; destruct Hoclm2 as [_ Hoclm2].
               rewrite rev_app_distr.
               apply Forall_Type_app...
               list_simpl...
            ** simpl ; rewrite Hperm ; list_simpl.
               rewrite bidual ; perm_Type_solve.
         ++ simpl in HP3 ; rewrite map_map in HP3.
            symmetry in HP3 ; apply Permutation_Type_map_inv in HP3.
            destruct HP3 as [l3''' Heq' HP3].
            decomp_map_Type Heq' ; subst.
            rewrite <- map_map in HP1.
            rewrite <- map_map in HP2.
            rewrite app_assoc in HP4 ; apply Permutation_Type_cons_app_inv in HP4.
            apply Permutation_Type_app_app_inv in HP4.
            destruct HP4 as [[[l3a l3b] [l3c l3d]] [[HP4' HP4''] [HP4''' HP4'''']]] ;
              simpl in HP4' ; simpl in HP4'' ; simpl in HP4''' ; simpl in HP4''''.
            apply Permutation_Type_app_app_inv in HP4'''.
            destruct HP4''' as [[[l3e l3f] [l3g l3h]] [[HP4a HP4b] [HP4c HP4d]]] ;
              simpl in HP4a ; simpl in HP4b ; simpl in HP4c ; simpl in HP4d.
            simpl in HP1.
            apply (Permutation_Type_app_head (map dual (map (ill2ll i2a) l4))) in HP4a.
            assert (HP' := Permutation_Type_trans HP1 HP4a).
            symmetry in HP4' ; apply Permutation_Type_map_inv in HP4'.
            destruct HP4' as [l3' Heq' HP4'].
            decomp_map_Type Heq' ; subst.
            apply (Permutation_Type_app_tail l3d) in HP4d.
            assert (HP'' := Permutation_Type_trans HP4'' HP4d).
            rewrite map_map in HP''.
            symmetry in HP'' ; apply Permutation_Type_map_inv in HP''.
            clear HP4'' ; destruct HP'' as [l4'' Heq' HP4''].
            decomp_map_Type Heq' ; subst.
            rewrite <- (map_map _ _ l13) in HP'.
            symmetry in HP4c ; apply Permutation_Type_map_inv in HP4c.
            destruct HP4c as [l4'' Heq' HP4c].
            decomp_map_Type Heq' ; subst.
            rewrite <- (map_map _ _ l14) in HP4b.
            simpl in HP2 ; simpl in HP4'''' ; simpl in HP4b.
            apply (@Permutation_Type_cons _ (ill2ll i2a C) _ eq_refl) in HP4''''.
            apply (Permutation_Type_app HP4b) in HP4''''.
            apply (Permutation_Type_app_head (map dual (map (ill2ll i2a) l6))) in HP4''''.
            assert (HP'' := Permutation_Type_trans HP2 HP4'''').
            specialize IHHll2 with (rev (l4 ++ l13)) l15 x0_1.
            simpl in HP4'.
            apply (Permutation_Type_Forall_Type _ _ _ HP4') in Hocl.
            apply Forall_Type_app_inv in Hocl ; destruct Hocl as [Hocl1 Hocl2].
            rewrite <- (map_map _ _ l12) in HP''. 
            specialize IHHll1 with (rev (x0_2 :: l6 ++ l14 ++ l12)) (l10 ++ l16) C.
            simpl in HP4c.
            apply (Permutation_Type_Forall_Type _ _ _ HP4c) in Hocl1.
            apply Forall_Type_app_inv in Hocl1 ; destruct Hocl1 as [Hocl3 Hocl4].
            assert (Hocl5 := Forall_Type_app _ _ _ Hocl2 Hocl4).
            apply IHHll2 in Hocl3 ; [ apply IHHll1 in Hocl5 | | ].
            ** split.
               --- destruct Hocl5 as [Hocl5 _].
                   destruct Hocl3 as [Hocl3 _].
                   apply (ex_ir _ (nil ++ rev (l4 ++ l13) ++
                                     ilmap x0_1 x0_2 :: rev (l6 ++ l14 ++ l12))).
                   +++ apply lmap_ilr...
                       eapply ex_ir ; [ apply Hocl5 | ].
                       rewrite Hperm ; simpl ; perm_Type_solve.
                   +++ rewrite Hperm ; simpl.
                       simpl in HP3.
                       apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
                       simpl in HP4''.
                       apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
                       list_simpl ; perm_Type_solve.
               --- intros Hnil lw ; destruct lo ; [ contradiction Hnil ; reflexivity | ].
                   apply (Permutation_Type_app_tail l10) in HP4c.
                   assert (HP''' := Permutation_Type_trans HP4' HP4c).
                   symmetry in HP''' ; apply Permutation_Type_vs_cons_inv in HP'''.
                   destruct HP''' as [(l4l & l4r) Heq'].
                   rewrite <- app_assoc in Heq'.
                   dichot_Type_elt_app_exec Heq' ; subst.
                   +++ assert (l4l ++ i :: l <> nil) as Hnil'
                         by (intros Hnil' ; destruct l4l ; inversion Hnil').
                       apply (snd Hocl3) with lw in Hnil'.
                       destruct Hocl5 as [Hocl5 _].
                       apply (ex_ir _ (nil ++ (rev (l4 ++ l13) ++ lw) ++
                                     ilmap x0_1 x0_2 :: rev (l6 ++ l14 ++ l12))).
                       *** apply lmap_ilr...
                           eapply ex_ir ; [ apply Hocl5 | ].
                           rewrite Hperm ; simpl ; perm_Type_solve.
                       *** rewrite Hperm ; simpl.
                           simpl in HP3.
                           apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
                           simpl in HP4''.
                           apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
                           list_simpl ; perm_Type_solve.
                   +++ assert (l17 ++ i :: l4r <> nil) as Hnil'
                         by (intros Hnil' ; destruct l17 ; inversion Hnil').
                       simpl in Heq'2 ; rewrite Heq'2 in Hnil'.
                       assert (l10 ++ l16 <> nil) as Hnil''.
                       { intros Hnil''.
                         apply Hnil'.
                         clear - Hnil''.
                         apply app_eq_nil in Hnil''.
                         destruct Hnil'' ; subst... }
                       apply (snd Hocl5) with lw in Hnil''.
                       destruct Hocl3 as [Hocl3 _].
                       apply (ex_ir _ (lw ++ rev (l4 ++ l13) ++
                                     ilmap x0_1 x0_2 :: rev (l6 ++ l14 ++ l12))).
                       *** apply lmap_ilr...
                           eapply ex_ir ; [ apply Hnil'' | ].
                           rewrite Hperm ; simpl ; perm_Type_solve.
                       *** rewrite Hperm ; simpl.
                           simpl in HP3.
                           apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
                           simpl in HP4''.
                           apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
                           list_simpl ; perm_Type_solve.
            ** inversion Hoclm ; subst.
               apply Forall_Type_app_inv in H3 ; destruct H3 as [Hoclm1 Hoclm2].
               inversion Hoclm2 ; subst.
               inversion H3 ; constructor...
               simpl in HP3.
               apply Permutation_Type_rev' in HP3.
               apply (Permutation_Type_Forall_Type _ _ _ HP3) in Hoclm1.
               apply Forall_Type_rev.
               constructor...
               apply Forall_Type_app.
               --- list_simpl in Hoclm1 ; apply Forall_Type_app_inv in Hoclm1.
                   rewrite <- rev_involutive.
                   apply Forall_Type_rev.
                   apply Hoclm1.
               --- simpl in HP4''.
                   apply Permutation_Type_rev' in HP4''.
                   apply (Permutation_Type_Forall_Type _ _ _ HP4'') in H4.
                   list_simpl in H4 ; apply Forall_Type_app_inv in H4 ; destruct H4 as [H4l H4r].
                   apply Forall_Type_rev in H4l.
                   rewrite rev_involutive in H4l.
                   apply Forall_Type_app...
                   apply Forall_Type_app_inv in H4r ; destruct H4r as [H4r _].
                   apply Forall_Type_rev in H4r.
                   rewrite rev_involutive in H4r...
            ** simpl ; rewrite Hperm ; simpl.
               list_simpl ; perm_Type_solve.
            ** inversion Hoclm ; subst...
               apply Forall_Type_app_inv in H3 ; destruct H3 as [Hoclm1 Hoclm2].
               inversion Hoclm2 ; subst.
               simpl in HP4''.
               apply Permutation_Type_rev' in HP4''.
               apply (Permutation_Type_Forall_Type _ _ _ HP4'') in H4.
               list_simpl in H4.
               apply Forall_Type_app_inv in H4.
               destruct H4 as [H4l H4r] ; apply Forall_Type_app_inv in H4r.
               destruct H4r as [_ H4r].
               inversion H3 ; subst ; constructor...
               list_simpl ; apply Forall_Type_app...
               simpl in HP3.
               apply Permutation_Type_rev' in HP3.
               apply (Permutation_Type_Forall_Type _ _ _ HP3) in Hoclm1.
               list_simpl in Hoclm1 ; apply Forall_Type_app_inv in Hoclm1.
               apply Hoclm1.
            ** list_simpl ; rewrite Hperm ; simpl.
               rewrite bidual ; perm_Type_solve.
      -- assert (HP4' := HP4).
         symmetry in HP4' ; apply Permutation_Type_vs_cons_inv in HP4'.
         destruct HP4' as [(l4a & l4b) Heq'].
         simpl in Heq' ; dichot_Type_elt_app_exec Heq' ; subst.
         ++ simpl in HP3 ; rewrite map_map in HP3.
            symmetry in HP3 ; apply Permutation_Type_map_inv in HP3.
            destruct HP3 as [l3''' Heq' HP3].
            decomp_map_Type Heq' ; subst.
            rewrite <- map_map in HP1.
            list_simpl in HP4 ; apply Permutation_Type_cons_app_inv in HP4.
            apply Permutation_Type_app_app_inv in HP4.
            destruct HP4 as [[[l3a l3b] [l3c l3d]] [[HP4' HP4''] [HP4''' HP4'''']]] ;
              simpl in HP4' ; simpl in HP4'' ; simpl in HP4''' ; simpl in HP4''''.
            apply Permutation_Type_app_app_inv in HP4''''.
            destruct HP4'''' as [[[l3e l3f] [l3g l3h]] [[HP4a HP4b] [HP4c HP4d]]] ;
              simpl in HP4a ; simpl in HP4b ; simpl in HP4c ; simpl in HP4d.
            simpl in HP1 ; simpl in HP4''' ; simpl in HP4a.
            apply (@Permutation_Type_cons _ (ill2ll i2a C) _ eq_refl) in HP4a.
            apply (Permutation_Type_app HP4''') in HP4a.
            apply (Permutation_Type_app_head (map dual (map (ill2ll i2a) l4))) in HP4a.
            assert (HP' := Permutation_Type_trans HP1 HP4a).
            symmetry in HP4' ; apply Permutation_Type_map_inv in HP4'.
            destruct HP4' as [l3' Heq' HP4'].
            decomp_map_Type Heq' ; subst.
            apply (Permutation_Type_app_head l3b) in HP4d.
            assert (HP'' := Permutation_Type_trans HP4'' HP4d).
            rewrite map_map in HP''.
            symmetry in HP'' ; apply Permutation_Type_map_inv in HP''.
            clear HP4'' ; destruct HP'' as [l4' Heq' HP4''].
            decomp_map_Type Heq' ; subst.
            rewrite <- (map_map _ _ l11) in HP'.
            rewrite <- (map_map _ _ l13) in HP'. 
            symmetry in HP4c ; apply Permutation_Type_map_inv in HP4c.
            destruct HP4c as [l4' Heq' HP4c].
            decomp_map_Type Heq' ; subst.
            specialize IHHll2 with (rev (l4 ++ l11 ++ l13)) (x0 :: l9 ++ l15) C.
            simpl in HP4' ; apply (Permutation_Type_Forall_Type _ _ _ HP4') in Hocl.
            apply Forall_Type_app_inv in Hocl ; destruct Hocl as [Hocl1 Hocl2].
            simpl in HP4c ; apply (Permutation_Type_Forall_Type _ _ _ HP4c) in Hocl2.
            apply Forall_Type_app_inv in Hocl2 ; destruct Hocl2 as [Hocl2 _].
            assert (Hocl3 := Forall_Type_app _ _ _ Hocl1 Hocl2).
            inversion Hoclm ; subst.
            apply Forall_Type_app_inv in H3 ; destruct H3 as [_ H3].
            inversion H3 ; inversion H4 ; subst.
            assert (Hocl4 := Forall_Type_cons _ H7 Hocl3).
            apply IHHll2 in Hocl4.
            ** assert (x0 :: l9 ++ l15 <> nil) as Hnil
                 by (intros Hnil ; inversion Hnil).
               split.
               --- apply (snd Hocl4) with (ineg x0 :: rev l6 ++ rev l14) in Hnil.
                   eapply ex_ir ; [ apply Hnil | ].
                   rewrite Hperm ; simpl.
                   apply Permutation_Type_elt.
                   simpl in HP3.
                   apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
                   simpl in HP4''.
                   apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
                   list_simpl ; perm_Type_solve.
               --- intros Hnil' lw.
                   apply (snd Hocl4) with (ineg x0 :: lw ++ rev l6 ++ rev l14) in Hnil.
                   eapply ex_ir ; [ apply Hnil | ].
                   rewrite Hperm ; simpl.
                   rewrite <- app_assoc ; rewrite <- app_comm_cons ; apply Permutation_Type_elt.
                   simpl in HP3.
                   apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
                   simpl in HP4''.
                   apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
                   list_simpl ; perm_Type_solve.
            ** constructor...
               simpl in HP4''.
               apply Permutation_Type_rev' in HP4''.
               apply (Permutation_Type_Forall_Type _ _ _ HP4'') in H5.
               list_simpl in H5.
               apply Forall_Type_app_inv in H5 ; destruct H5 as [_ Hoclm1].
               inversion Hoclm ; subst.
               apply Forall_Type_app_inv in H6 ; destruct H6 as [Hoclm2 _].
               simpl in HP3 ; apply Permutation_Type_rev' in HP3.
               apply (Permutation_Type_Forall_Type _ _ _ HP3) in Hoclm2.
               list_simpl in Hoclm2.
               apply Forall_Type_app_inv in Hoclm2 ; destruct Hoclm2 as [_ Hoclm2].
               rewrite rev_app_distr.
               apply Forall_Type_app...
               list_simpl...
            ** simpl ; rewrite Hperm ; list_simpl.
               rewrite bidual ; perm_Type_solve.
         ++ simpl in HP3 ; rewrite map_map in HP3.
            symmetry in HP3 ; apply Permutation_Type_map_inv in HP3.
            destruct HP3 as [l3''' Heq' HP3].
            decomp_map_Type Heq' ; subst.
            rewrite <- map_map in HP1.
            rewrite <- map_map in HP2.
            rewrite app_assoc in HP4 ; apply Permutation_Type_cons_app_inv in HP4.
            apply Permutation_Type_app_app_inv in HP4.
            destruct HP4 as [[[l3a l3b] [l3c l3d]] [[HP4' HP4''] [HP4''' HP4'''']]] ;
              simpl in HP4' ; simpl in HP4'' ; simpl in HP4''' ; simpl in HP4''''.
            apply Permutation_Type_app_app_inv in HP4'''.
            destruct HP4''' as [[[l3e l3f] [l3g l3h]] [[HP4a HP4b] [HP4c HP4d]]] ;
              simpl in HP4a ; simpl in HP4b ; simpl in HP4c ; simpl in HP4d.
            simpl in HP1 ; simpl in HP4a.
            apply (Permutation_Type_app_head (map dual (map (ill2ll i2a) l4))) in HP4a.
            assert (HP' := Permutation_Type_trans HP1 HP4a).
            symmetry in HP4' ; apply Permutation_Type_map_inv in HP4'.
            destruct HP4' as [l3' Heq' HP4'].
            decomp_map_Type Heq' ; subst.
            apply (Permutation_Type_app_tail l3d) in HP4d.
            assert (HP'' := Permutation_Type_trans HP4'' HP4d).
            rewrite map_map in HP''.
            symmetry in HP'' ; apply Permutation_Type_map_inv in HP''.
            clear HP4'' ; destruct HP'' as [l4'' Heq' HP4''].
            decomp_map_Type Heq' ; subst.
            rewrite <- (map_map _ _ l13) in HP'.
            symmetry in HP4c ; apply Permutation_Type_map_inv in HP4c.
            destruct HP4c as [l4'' Heq' HP4c].
            decomp_map_Type Heq' ; subst.
            rewrite <- (map_map _ _ l14) in HP4b.
            simpl in HP2 ; simpl in HP4'''' ; simpl in HP4b.
            apply (@Permutation_Type_cons _ (ill2ll i2a C) _ eq_refl) in HP4''''.
            apply (Permutation_Type_app HP4b) in HP4''''.
            apply (Permutation_Type_app_head (map dual (map (ill2ll i2a) l6))) in HP4''''.
            assert (HP'' := Permutation_Type_trans HP2 HP4'''').
            specialize IHHll2 with (rev (l4 ++ l13)) l15 x0.
            simpl in HP4' ; apply (Permutation_Type_Forall_Type _ _ _ HP4') in Hocl.
            apply Forall_Type_app_inv in Hocl ; destruct Hocl as [Hocl1 Hocl2].
            rewrite <- (map_map _ _ l12) in HP''. 
            specialize IHHll1 with (rev (ivar atN :: l6 ++ l14 ++ l12)) (l10 ++ l16) C.
            simpl in HP4c ; apply (Permutation_Type_Forall_Type _ _ _ HP4c) in Hocl1.
            apply Forall_Type_app_inv in Hocl1 ; destruct Hocl1 as [Hocl3 Hocl4].
            assert (Hocl5 := Forall_Type_app _ _ _ Hocl2 Hocl4).
            apply IHHll2 in Hocl3 ; [ apply IHHll1 in Hocl5 | | ].
            ** split.
               --- destruct Hocl5 as [Hocl5 _].
                   destruct Hocl3 as [Hocl3 _].
                   apply neg_map_rule with _ (rev l6 ++ rev l14) (rev l12) _ C in Hocl3.
                   +++ eapply ex_ir ; [ apply Hocl3 | ].
                       rewrite Hperm ; simpl.
                       rewrite app_assoc.
                       apply Permutation_Type_elt.
                       simpl in HP3.
                       apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
                       simpl in HP4''.
                       apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
                       list_simpl ; perm_Type_solve.
                   +++ intros a Ha ; apply (snd (Hgax a) Ha).
                   +++ eapply ex_ir ; [ apply Hocl5 | ].
                       rewrite Hperm ; simpl ; perm_Type_solve.
               --- intros Hnil lw ; destruct lo ; [ contradiction Hnil ; reflexivity | ].
                   apply (Permutation_Type_app_tail l10) in HP4c.
                   assert (HP''' := Permutation_Type_trans HP4' HP4c).
                   symmetry in HP''' ; apply Permutation_Type_vs_cons_inv in HP'''.
                   destruct HP''' as [(l4l & l4r) Heq'].
                   rewrite <- app_assoc in Heq'.
                   simpl in Heq' ; dichot_Type_elt_app_exec Heq' ; subst.
                   +++ assert (l4l ++ i :: l <> nil) as Hnil'
                         by (intros Hnil' ; destruct l4l ; inversion Hnil').
                       apply (snd Hocl3) with lw in Hnil'.
                       destruct Hocl5 as [Hocl5 _].
                       apply neg_map_rule with _ (rev l6 ++ rev l14) (rev l12) _ C in Hnil'.
                       *** eapply ex_ir ; [ apply Hnil' | ].
                           rewrite Hperm ; simpl ; list_simpl.
                           rewrite 4 app_assoc.
                           apply Permutation_Type_elt.
                           simpl in HP3.
                           apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
                           simpl in HP4''.
                           apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
                           list_simpl ; perm_Type_solve.
                       *** intros a Ha ; apply (snd (Hgax a) Ha).
                       *** eapply ex_ir ; [ apply Hocl5 | ].
                           rewrite Hperm ; simpl ; perm_Type_solve.
                   +++ assert (l17 ++ i :: l4r <> nil) as Hnil'
                         by (intros Hnil' ; destruct l17 ; inversion Hnil').
                       rewrite Heq'1 in Hnil'.
                       assert (l10 ++ l16 <> nil) as Hnil''.
                       { intros Hnil''.
                         apply Hnil'.
                         clear - Hnil''.
                         apply app_eq_nil in Hnil''.
                         destruct Hnil'' ; subst... }
                       apply (snd Hocl5) with lw in Hnil''.
                       destruct Hocl3 as [Hocl3 _].
                       apply neg_map_rule with _ (rev l6 ++ rev l14) (rev l12 ++ lw) _ C in Hocl3.
                       *** eapply ex_ir ; [ apply Hocl3 | ].
                           rewrite Hperm ; simpl ; list_simpl.
                           rewrite 3 app_assoc.
                           apply Permutation_Type_elt.
                           simpl in HP3.
                           apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
                           simpl in HP4''.
                           apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
                           list_simpl ; perm_Type_solve.
                       *** intros a Ha ; apply (snd (Hgax a) Ha).
                       *** eapply ex_ir ; [ apply Hnil'' | ].
                           rewrite Hperm ; simpl ; perm_Type_solve.
            ** inversion Hoclm ; subst.
               apply Forall_Type_app_inv in H3 ; destruct H3 as [Hoclm1 Hoclm2].
               inversion Hoclm2 ; subst.
               inversion H3 ; constructor...
               simpl in HP3 ; apply Permutation_Type_rev' in HP3.
               apply (Permutation_Type_Forall_Type _ _ _ HP3) in Hoclm1.
               apply Forall_Type_rev.
               constructor ; [ | apply Forall_Type_app ].
               --- constructor.
               --- list_simpl in Hoclm1 ; apply Forall_Type_app_inv in Hoclm1.
                   rewrite <- rev_involutive.
                   apply Forall_Type_rev.
                   apply Hoclm1.
               --- simpl in HP4'' ; apply Permutation_Type_rev' in HP4''.
                   apply (Permutation_Type_Forall_Type _ _ _ HP4'') in H4.
                   list_simpl in H4 ; apply Forall_Type_app_inv in H4 ; destruct H4 as [H4l H4r].
                   apply Forall_Type_rev in H4l.
                   rewrite rev_involutive in H4l.
                   apply Forall_Type_app...
                   apply Forall_Type_app_inv in H4r ; destruct H4r as [H4r _].
                   apply Forall_Type_rev in H4r.
                   rewrite rev_involutive in H4r...
            ** simpl ; rewrite Hperm ; list_simpl ; perm_Type_solve.
            ** inversion Hoclm ; subst...
               apply Forall_Type_app_inv in H3 ; destruct H3 as [Hoclm1 Hoclm2].
               inversion Hoclm2 ; subst.
               simpl in HP4'' ; apply Permutation_Type_rev' in HP4''.
               apply (Permutation_Type_Forall_Type _ _ _ HP4'') in H4.
               list_simpl in H4 ; apply Forall_Type_app_inv in H4 ; destruct H4 as [H4l H4r].
               apply Forall_Type_app_inv in H4r ; destruct H4r as [_ H4r].
               inversion H3 ; subst ; constructor...
               list_simpl ; apply Forall_Type_app...
               simpl in HP3 ; apply Permutation_Type_rev' in HP3.
               apply (Permutation_Type_Forall_Type _ _ _ HP3) in Hoclm1.
               list_simpl in Hoclm1 ; apply Forall_Type_app_inv in Hoclm1.
               apply Hoclm1.
            ** list_simpl ; rewrite Hperm ; simpl.
               rewrite bidual ; perm_Type_solve.
- symmetry in HP ; apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP] ; simpl in Heq ; simpl in HP.
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  + specialize IHHll with (l0 ++ C1 :: nil) lo C2.
    apply IHHll in Hocl.
    * destruct Hocl as [IH1 IH2].
      split.
      -- apply lpam_irr...
      -- intros Hnil l2.
         assert (IH := IH2 Hnil l2).
         list_simpl in IH.
         list_simpl ; apply lpam_irr.
         eapply ex_ir...
         rewrite Hperm ; simpl ; perm_Type_solve.
    * inversion Hoclm ; subst.
      inversion H2 ; subst.
      constructor...
      apply Forall_Type_app...
      constructor...
      constructor.
    * simpl in HP ; rewrite Hperm in HP ; simpl in HP.
      simpl ; rewrite Hperm ; simpl.
      perm_Type_solve.
  + specialize IHHll with (l0 ++ C :: nil) lo N.
    apply IHHll in Hocl.
    * destruct Hocl as [IH1 IH2].
      split.
      -- apply gen_irr...
      -- intros Hnil l2.
         assert (IH := IH2 Hnil l2).
         list_simpl in IH.
         list_simpl ; apply gen_irr.
         eapply ex_ir...
         rewrite Hperm ; list_simpl.
         apply Permutation_Type_app...
         PEperm_Type_solve.
    * inversion Hoclm ; subst.
      inversion H2 ; subst.
      constructor...
      -- constructor.
      -- apply Forall_Type_app...
         constructor ; [ | constructor ]...
    * simpl in HP ; rewrite Hperm in HP ; simpl in HP.
      simpl ; rewrite Hperm ; simpl ; perm_Type_solve.
  + specialize IHHll with (C1 :: l0) lo C2.
    apply IHHll in Hocl.
    * destruct Hocl as [IH1 IH2].
      split.
      -- apply lmap_irr...
      -- intros Hnil l2.
         assert (IH := IH2 Hnil l2).
         list_simpl in IH.
         list_simpl ; apply lmap_irr.
         eapply ex_ir...
    * inversion Hoclm ; subst.
      inversion H2 ; subst.
      constructor...
      constructor...
    * simpl in HP ; rewrite Hperm in HP ; simpl in HP.
      simpl ; rewrite Hperm ; simpl ; perm_Type_solve.
  + specialize IHHll with (C :: l0) lo N.
    apply IHHll in Hocl.
    * destruct Hocl as [IH1 IH2].
      split.
      -- apply neg_irr...
      -- intros Hnil l2.
         assert (IH := IH2 Hnil l2).
         list_simpl in IH.
         list_simpl ; apply neg_irr.
         eapply ex_ir...
    * inversion Hoclm ; subst.
      inversion H2 ; subst.
      constructor...
      -- constructor.
      -- constructor...
    * simpl in HP ; rewrite Hperm in HP ; simpl in HP.
      simpl ; rewrite Hperm ; simpl ; perm_Type_solve.
  + symmetry in H1 ; dichot_Type_elt_app_exec H1 ; subst ;
    [ decomp_map_Type H0 ; destruct x ; inversion H0
    | list_simpl in H2 ; decomp_map_Type H2 ; decomp_map_Type H3 ;
                         destruct x ; inversion H2 ; destruct x0 ; inversion H3 ] ;
      simpl in H3 ; simpl in H5 ; subst.
    * exfalso.
      apply Forall_Type_app_inv in Hocl.
      destruct Hocl as [_ Hocl].
      inversion Hocl.
      inversion H2.
    * exfalso.
      apply Forall_Type_app_inv in Hocl.
      destruct Hocl as [_ Hocl].
      inversion Hocl.
      inversion H2.
    * exfalso.
      apply Forall_Type_app_inv in Hocl.
      destruct Hocl as [_ Hocl].
      inversion Hocl.
      inversion H2.
    * exfalso.
      apply Forall_Type_app_inv in Hocl.
      destruct Hocl as [_ Hocl].
      inversion Hocl.
      inversion H2.
    * apply (f_equal (@rev _)) in H6 ; list_simpl in H6 ; subst.
      apply (@PEperm_Type_cons _ _ _ (dual (ill2ll i2a x0_1)) eq_refl) in HP.
      apply (@PEperm_Type_cons _ _ _ (dual (ill2ll i2a x0_2)) eq_refl) in HP.
      apply PEperm_PCperm_Type in HP ; unfold id in HP.
      rewrite 2 app_comm_cons in HP.
      assert (HP' := PCperm_Type_trans _ _ _ _ HP (PCperm_Type_app_comm _ _ _)).
      specialize IHHll with (rev (x0_2 :: x0_1 :: l8) ++ rev l6) lo C.
      simpl in H7 ; subst.
      list_simpl in IHHll ; list_simpl in HP' ; apply IHHll in HP'...
      -- destruct HP' as [IH1 IH2].
         split.
         ++ apply tens_ilr...
         ++ intros Hnil l2.
            assert (IH := IH2 Hnil l2).
            list_simpl in IH.
            list_simpl ; apply tens_ilr...
      -- inversion Hoclm ; constructor...
         apply Forall_Type_app_inv in H4 ; destruct H4 as [Hl Hr] ; apply Forall_Type_app...
         inversion Hr.
         inversion H6.
         constructor...
         constructor...
- symmetry in HP ; apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  + split ; intros ; apply top_irr.
  + symmetry in H1 ; dichot_Type_elt_app_exec H1 ; subst ;
      [ decomp_map_Type H0 ; destruct x ; inversion H0
      | list_simpl in H2 ; decomp_map_Type H2 ; decomp_map_Type H3 ;
                           destruct x ; inversion H2 ; destruct x0 ; inversion H3 ] ; subst.
    * exfalso.
      apply Forall_Type_app_inv in Hocl ; destruct Hocl as [_ Hocl] ; inversion Hocl.
      inversion H2.
    * apply (f_equal (@rev _)) in H6 ; list_simpl in H6 ; subst.
      split ; intros ; list_simpl ; apply zero_ilr.
- symmetry in HP ; apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  + apply (@PEperm_Type_cons _ _ _ (ill2ll i2a C1) eq_refl) in HP.
    apply PEperm_PCperm_Type in HP ; unfold id in HP.
    rewrite app_comm_cons in HP.
    assert (HP' := PCperm_Type_trans _ _ _ _ HP (PCperm_Type_app_comm _ _ _)).
    specialize IHHll with l0 lo C1.
    list_simpl in IHHll ; list_simpl in HP' ; apply IHHll in HP'...
    * destruct HP' as [IH1 IH2].
      split.
      -- apply plus_irr1...
      -- intros Hnil l2.
         assert (IH := IH2 Hnil l2).
         list_simpl in IH.
         list_simpl ; apply plus_irr1...
    * inversion Hoclm ; subst.
      inversion H2 ; subst.
      constructor...
  + symmetry in H1 ; dichot_Type_elt_app_exec H1 ; subst ;
    [ decomp_map_Type H0 ; destruct x ; inversion H0
    | list_simpl in H2 ; decomp_map_Type H2 ; decomp_map_Type H3 ;
                         destruct x ; inversion H2 ; destruct x0 ; inversion H3 ] ;
      simpl in H3 ; simpl in H5 ; subst.
    * apply (@PEperm_Type_cons _ _ _ (ill2ll i2a x1) eq_refl) in HP.
      apply PEperm_PCperm_Type in HP ; unfold id in HP.
      rewrite app_comm_cons in HP.
      assert (HP' := PCperm_Type_trans _ _ _ _ HP (PCperm_Type_app_comm _ _ _)).
      specialize IHHll with l0 (l3 ++ x1 :: l5) C.
      list_simpl in IHHll ; list_simpl in HP' ; apply IHHll in HP'...
      -- destruct HP' as [IH1 IH2].
         split...
         intros _ l2.
         apply IH2.
         intros Hnil ; destruct l3 ; inversion Hnil.
      -- apply Forall_Type_app_inv in Hocl ; destruct Hocl as [Hocll Hoclr] ; apply Forall_Type_app...
         inversion Hoclr.
         inversion H2.
         constructor...
    * apply (f_equal (@rev _)) in H6 ; list_simpl in H6 ; subst.
      apply (@PEperm_Type_cons _ _ _ (dual (ill2ll i2a x0_1)) eq_refl) in HP.
      apply PEperm_PCperm_Type in HP ; unfold id in HP.
      rewrite app_comm_cons in HP.
      assert (HP' := PCperm_Type_trans _ _ _ _ HP (PCperm_Type_app_comm _ _ _)).
      specialize IHHll with (rev (x0_1 :: l8) ++ rev l6) lo C.
      simpl in H7 ; subst.
      list_simpl in IHHll ; list_simpl in HP' ; apply IHHll in HP'...
      -- destruct HP' as [IH1 IH2].
         split.
         ++ apply with_ilr1...
         ++ intros Hnil l2.
            assert (IH := IH2 Hnil l2).
            list_simpl in IH.
            list_simpl ; apply with_ilr1...
      -- inversion Hoclm ; constructor...
         apply Forall_Type_app_inv in H4 ; destruct H4 as [Hl Hr] ; apply Forall_Type_app...
         inversion Hr.
         inversion H6.
         constructor...
- symmetry in HP ; apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  + apply (@PEperm_Type_cons _ _ _ (ill2ll i2a C2) eq_refl) in HP.
    apply PEperm_PCperm_Type in HP ; unfold id in HP.
    rewrite app_comm_cons in HP.
    assert (HP' := PCperm_Type_trans _ _ _ _ HP (PCperm_Type_app_comm _ _ _)).
    specialize IHHll with l0 lo C2.
    list_simpl in IHHll ; list_simpl in HP' ; apply IHHll in HP'...
    * destruct HP' as [IH1 IH2].
      split.
      -- apply plus_irr2...
      -- intros Hnil l2.
         assert (IH := IH2 Hnil l2).
         list_simpl in IH.
         list_simpl ; apply plus_irr2...
    * inversion Hoclm ; subst.
      inversion H2 ; subst.
      constructor...
  + symmetry in H1 ; dichot_Type_elt_app_exec H1 ; subst ;
    [ decomp_map_Type H0 ; destruct x ; inversion H0
    | list_simpl in H2 ; decomp_map_Type H2 ; decomp_map_Type H3 ;
                         destruct x ; inversion H2 ; destruct x0 ; inversion H3 ] ;
      simpl in H3 ; simpl in H5 ; subst.
    * apply (@PEperm_Type_cons _ _ _ (ill2ll i2a x2) eq_refl) in HP.
      apply PEperm_PCperm_Type in HP ; unfold id in HP.
      rewrite app_comm_cons in HP.
      assert (HP' := PCperm_Type_trans _ _ _ _ HP (PCperm_Type_app_comm _ _ _)).
      specialize IHHll with l0 (l3 ++ x2 :: l5) C.
      list_simpl in IHHll ; list_simpl in HP' ; apply IHHll in HP'...
      -- destruct HP' as [IH1 IH2].
         split...
         intros _ l2.
         apply IH2.
         intros Hnil ; destruct l3 ; inversion Hnil.
      -- apply Forall_Type_app_inv in Hocl ; destruct Hocl as [Hocll Hoclr] ; apply Forall_Type_app...
         inversion Hoclr.
         inversion H2.
         constructor...
    * apply (f_equal (@rev _)) in H6 ; list_simpl in H6 ; subst.
      apply (@PEperm_Type_cons _ _ _ (dual (ill2ll i2a x0_2)) eq_refl) in HP.
      apply PEperm_PCperm_Type in HP ; unfold id in HP.
      rewrite app_comm_cons in HP.
      assert (HP' := PCperm_Type_trans _ _ _ _ HP (PCperm_Type_app_comm _ _ _)).
      specialize IHHll with (rev (x0_2 :: l8) ++ rev l6) lo C.
      simpl in H7 ; subst.
      list_simpl in IHHll ; list_simpl in HP' ; apply IHHll in HP'...
      -- destruct HP' as [IH1 IH2].
         split.
         ++ apply with_ilr2...
         ++ intros Hnil l2.
            assert (IH := IH2 Hnil l2).
            list_simpl in IH.
            list_simpl ; apply with_ilr2...
      -- inversion Hoclm ; constructor...
         apply Forall_Type_app_inv in H4 ; destruct H4 as [Hl Hr] ; apply Forall_Type_app...
         inversion Hr.
         inversion H6.
         constructor...
- symmetry in HP ; apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  + assert (HP1 := HP).
    apply (@PEperm_Type_cons _ _ _ (ill2ll i2a C1) eq_refl) in HP1.
    apply PEperm_PCperm_Type in HP1 ; unfold id in HP1.
    rewrite app_comm_cons in HP1.
    assert (HP1' := PCperm_Type_trans _ _ _ _ HP1 (PCperm_Type_app_comm _ _ _)).
    specialize IHHll1 with l0 lo C1.
    list_simpl in IHHll1 ; list_simpl in HP1' ; apply IHHll1 in HP1'...
    * destruct HP1' as [IH1 IH2].
      apply (@PEperm_Type_cons _ _ _ (ill2ll i2a C2) eq_refl) in HP.
      apply PEperm_PCperm_Type in HP ; unfold id in HP.
      rewrite app_comm_cons in HP.
      assert (HP2' := PCperm_Type_trans _ _ _ _ HP (PCperm_Type_app_comm _ _ _)).
      specialize IHHll2 with l0 lo C2.
      list_simpl in IHHll2 ; list_simpl in HP2' ; apply IHHll2 in HP2'...
      -- destruct HP2' as [IH3 IH4].
         split.
         ++ apply with_irr...
         ++ intros Hnil l2.
            assert (IH := IH2 Hnil l2).
            assert (IH' := IH4 Hnil l2).
            list_simpl in IH ; list_simpl in IH'.
            list_simpl ; apply with_irr...
      -- inversion Hoclm ; subst.
         inversion H2 ; subst.
         constructor...
    * inversion Hoclm ; subst.
      inversion H2 ; subst.
      constructor...
  + symmetry in H1 ; dichot_Type_elt_app_exec H1 ; subst ;
    [ decomp_map_Type H0 ; destruct x ; inversion H0
    | list_simpl in H2 ; decomp_map_Type H2 ; decomp_map_Type H3 ;
                         destruct x ; inversion H2 ; destruct x0 ; inversion H3 ] ;
      simpl in H3 ; simpl in H5 ; subst.
    * apply Forall_Type_app_inv in Hocl ; destruct Hocl as [Hocll Hoclr].
      inversion Hoclr.
      inversion H2.
      -- apply (@PEperm_Type_cons _ _ _ (ill2ll i2a x1) eq_refl) in HP.
         apply PEperm_PCperm_Type in HP ; unfold id in HP.
         rewrite app_comm_cons in HP.
         assert (HP' := PCperm_Type_trans _ _ _ _ HP (PCperm_Type_app_comm _ _ _)).
         specialize IHHll1 with l0 (l3 ++ x1 :: l5) C.
         list_simpl in IHHll1 ; list_simpl in HP' ; apply IHHll1 in HP'...
         ++ destruct HP' as [IH1 IH2].
            split...
            intros _ l2.
            apply IH2.
            intros Hnil ; destruct l3 ; inversion Hnil.
         ++ apply Forall_Type_app...
            constructor...
      -- apply (@PEperm_Type_cons _ _ _ (ill2ll i2a x2) eq_refl) in HP.
         apply PEperm_PCperm_Type in HP ; unfold id in HP.
         rewrite app_comm_cons in HP.
         assert (HP' := PCperm_Type_trans _ _ _ _ HP (PCperm_Type_app_comm _ _ _)).
         specialize IHHll2 with l0 (l3 ++ x2 :: l5) C.
         list_simpl in IHHll2 ; list_simpl in HP' ; apply IHHll2 in HP'...
         ++ destruct HP' as [IH1 IH2].
            split...
            intros _ l2.
            apply IH2.
            intros Hnil ; destruct l3 ; inversion Hnil.
         ++ apply Forall_Type_app...
            constructor...
    * apply (f_equal (@rev _)) in H6 ; list_simpl in H6 ; subst.
      assert (HP1 := HP).
      apply (@PEperm_Type_cons _ _ _ (dual (ill2ll i2a x0_1)) eq_refl) in HP1.
      apply PEperm_PCperm_Type in HP1 ; unfold id in HP1.
      rewrite app_comm_cons in HP1.
      assert (HP1' := PCperm_Type_trans _ _ _ _ HP1 (PCperm_Type_app_comm _ _ _)).
      specialize IHHll1 with (rev (x0_1 :: l8) ++ rev l6) lo C.
      simpl in H7 ; subst.
      list_simpl in IHHll1 ; list_simpl in HP1' ; apply IHHll1 in HP1'...
      -- destruct HP1' as [IH1 IH2].
         apply (@PEperm_Type_cons _ _ _ (dual (ill2ll i2a x0_2)) eq_refl) in HP.
         apply PEperm_PCperm_Type in HP ; unfold id in HP.
         rewrite app_comm_cons in HP.
         assert (HP2' := PCperm_Type_trans _ _ _ _ HP (PCperm_Type_app_comm _ _ _)).
         specialize IHHll2 with (rev (x0_2 :: l8) ++ rev l6) lo C.
         list_simpl in IHHll2 ; list_simpl in HP2' ; apply IHHll2 in HP2'...
         ++ destruct HP2' as [IH3 IH4].
            split.
            ** apply plus_ilr...
            ** intros Hnil l2.
               assert (IH5 := IH2 Hnil l2).
               list_simpl in IH5.
               assert (IH6 := IH4 Hnil l2).
               list_simpl in IH6.
               list_simpl ; apply plus_ilr...
         ++ inversion Hoclm ; constructor...
            apply Forall_Type_app_inv in H4 ; destruct H4 as [Hl Hr] ; apply Forall_Type_app...
            inversion Hr.
            inversion H6.
            constructor...
      -- inversion Hoclm ; constructor...
         apply Forall_Type_app_inv in H4 ; destruct H4 as [Hl Hr] ; apply Forall_Type_app...
         inversion Hr.
         inversion H6.
         constructor...
- symmetry in HP ; apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  + symmetry in HP ; apply PEperm_Type_map_inv in HP.
    destruct HP as [l'' Heq' HPE] ; simpl in Heq'.
    decomp_map_Type Heq'.
    destruct lo ; destruct l4 ; inversion Heq'3 ; subst.
    * split.
      -- list_simpl in Heq'4.
         symmetry in Heq'4.
         apply ill2ll_map_ioc_inv in Heq'4.
         destruct Heq'4 as [l2' Heq' Heq''] ; subst.
         apply (f_equal (@rev _)) in Heq' ; list_simpl in Heq' ; subst.
         specialize IHHll with ((rev (map ioc l2'))) nil C.
         destruct l3 ; inversion Heq'2.
         apply IHHll in Hocl...
         ++ list_simpl in Hocl ; destruct Hocl as [Hocl _].
            apply oc_irr...
         ++ inversion Hoclm ; subst.
            inversion H2 ; subst.
            list_simpl ; constructor...
         ++ etransitivity.
            ** apply PEperm_PCperm_Type.
               list_simpl in HPE.
               apply (PEperm_Type_map wn) in HPE.
               apply PEperm_Type_cons ; [reflexivity | eassumption].
            ** list_simpl ; rewrite ill2ll_map_ioc...
      -- intros Hnil ; contradiction Hnil...
    * exfalso ; destruct i ; inversion H1.
  + exfalso.
    symmetry in H1 ; dichot_Type_elt_app_exec H1 ; subst ;
    [ decomp_map_Type H0 ; destruct x ; inversion H0
    | list_simpl in H2 ; decomp_map_Type H2 ; decomp_map_Type H3 ;
                         destruct x ; inversion H2 ; destruct x0 ; inversion H3 ] ; subst.
    symmetry in HP ; apply PEperm_Type_map_inv in HP.
    destruct HP as [l'' Heq' _] ; simpl in Heq'.
    decomp_map_Type Heq'.
    destruct C ; inversion Heq'1.
- symmetry in HP ; apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  symmetry in H1 ; dichot_Type_elt_app_exec H1 ; subst ;
    [ decomp_map_Type H0 ; destruct x ; inversion H0
    | list_simpl in H2 ; decomp_map_Type H2 ; decomp_map_Type H3 ;
                         destruct x ; inversion H2 ; destruct x0 ; inversion H3 ] ;
      simpl in H3 ; simpl in H5 ; subst.
  apply (f_equal (@rev _)) in H6 ; list_simpl in H6 ; subst.
  apply (@PEperm_Type_cons _ _ _ (dual (ill2ll i2a x0)) eq_refl) in HP.
  apply PEperm_PCperm_Type in HP ; unfold id in HP.
  rewrite app_comm_cons in HP.
  assert (HP' := PCperm_Type_trans _ _ _ _ HP (PCperm_Type_app_comm _ _ _)).
  specialize IHHll with (rev (x0 :: l8) ++ rev l6) lo C.
  simpl in H7 ; subst.
  list_simpl in IHHll ; list_simpl in HP' ; apply IHHll in HP'...
  + destruct HP' as [IH1 IH2].
    split.
    * apply de_ilr...
    * intros Hnil l2.
      assert (IH := IH2 Hnil l2).
      list_simpl in IH.
      list_simpl ; apply de_ilr...
  + inversion Hoclm ; constructor...
    apply Forall_Type_app_inv in H4 ; destruct H4 as [Hl Hr] ; apply Forall_Type_app...
    inversion Hr.
    inversion H6.
    constructor...
- symmetry in HP ; apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  symmetry in H1 ; dichot_Type_elt_app_exec H1 ; subst ;
    [ decomp_map_Type H0 ; destruct x ; inversion H0
    | list_simpl in H2 ; decomp_map_Type H2 ; decomp_map_Type H3 ;
                         destruct x ; inversion H2 ; destruct x0 ; inversion H3 ] ;
      simpl in H3 ; simpl in H5 ; subst.
  apply (f_equal (@rev _)) in H6 ; list_simpl in H6 ; subst.
  apply PEperm_PCperm_Type in HP ; unfold id in HP.
  rewrite app_comm_cons in HP.
  assert (HP' := PCperm_Type_trans _ _ _ _ HP (PCperm_Type_app_comm _ _ _)).
  specialize IHHll with (rev l8 ++ rev l6) lo C.
  simpl in H7 ; subst.
  list_simpl in IHHll ; list_simpl in HP' ; apply IHHll in HP'...
  + destruct HP' as [IH1 IH2].
    split.
    * apply wk_ilr...
    * intros Hnil l2.
      assert (IH := IH2 Hnil l2).
      list_simpl in IH.
      list_simpl ; apply wk_ilr...
  + inversion Hoclm ; constructor...
    apply Forall_Type_app_inv in H4 ; destruct H4 as [Hl Hr] ; apply Forall_Type_app...
    inversion Hr...
- symmetry in HP ; apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  symmetry in H1 ; dichot_Type_elt_app_exec H1 ; subst ;
    [ decomp_map_Type H0 ; destruct x ; inversion H0
    | list_simpl in H2 ; decomp_map_Type H2 ; decomp_map_Type H3 ;
                         destruct x ; inversion H2 ; destruct x0 ; inversion H3 ] ;
      simpl in H3 ; simpl in H5 ; subst.
  simpl in H7 ; subst.
  apply (f_equal (@rev _)) in H6 ; list_simpl in H6 ; subst.
  assert (PCperm_Type (ipperm P) (wn (dual (ill2ll i2a x0)) :: wn (dual (ill2ll i2a x0)) :: l)
         (ill2ll i2a C :: map (ill2ll i2a) lo
          ++ map dual (map (ill2ll i2a) (l6 ++ ioc x0 :: ioc x0 :: l8)))) as HP'.
  { apply (PEperm_Type_cons _ (wn (dual (ill2ll i2a x0))) _ eq_refl) in HP.
    apply (PEperm_Type_cons _ (wn (dual (ill2ll i2a x0))) _ eq_refl) in HP.
    apply PEperm_PCperm_Type in HP.
    unfold id in HP ; simpl in HP.
    etransitivity...
    PCperm_Type_solve. }
  specialize IHHll with (rev (ioc x0 :: ioc x0 :: l8) ++ rev l6) lo C.
  list_simpl in IHHll ; list_simpl in HP' ;  apply IHHll in HP'...
  + destruct HP' as [IH1 IH2].
    split.
    * eapply ex_ir ; [ apply co_ilr | ].
      -- rewrite app_nil_l.
         eapply ex_ir ; [ apply IH1 | ].
         rewrite Hperm ; simpl.
         symmetry ; apply Permutation_Type_cons_app.
         apply Permutation_Type_cons_app.
         reflexivity.
      -- rewrite Hperm ; simpl ; perm_Type_solve.
    * intros Hnil l2.
      assert (IH := IH2 Hnil l2).
      list_simpl in IH.
      eapply ex_ir ; [ apply co_ilr | ].
      -- rewrite app_nil_l.
         eapply ex_ir ; [ apply IH | ].
         rewrite Hperm ; simpl.
         symmetry ; apply Permutation_Type_cons_app.
         apply Permutation_Type_cons_app.
         reflexivity.
      -- rewrite Hperm ; simpl ; perm_Type_solve.
  + inversion Hoclm ; constructor...
    apply Forall_Type_app_inv in H4 ; destruct H4 as [Hl Hr] ; apply Forall_Type_app...
    inversion Hr.
    inversion H6.
    constructor...
- simpl in f ; rewrite f in Hcut ; inversion Hcut.
- destruct lo.
  + apply (snd (fst (Hgax a))) in HP.
    split...
    intros Hnil ; exfalso ; apply Hnil...
  + exfalso.
    inversion Hocl.
    simpl in HP ; rewrite <- (app_nil_l (ill2ll i2a i :: _)) in HP.
    rewrite app_comm_cons in HP.
    apply PCperm_Type_vs_elt_inv in HP ; destruct HP as [(l1,l2) Heq _] ; simpl in Heq.
    destruct l1 ; inversion Heq.
    * symmetry in H4 ; apply (snd (fst (fst (Hgax a))) i)...
    * apply (f_equal (@rev _)) in H5.
      rewrite rev_involutive in H5 ; list_simpl in H5.
      rewrite map_map in H5.
      symmetry in H5 ; decomp_map H5.
      apply (f_equal dual) in H5.
      rewrite bidual in H5.
      apply (f_equal (map (ill2ll i2a))) in H7 ; list_simpl in H7.
      apply (fst (fst (fst (Hgax a))) i)...
      rewrite <- H7 ; rewrite H5.
      apply in_Type_elt.
Qed.

Proposition ll_to_ill_oclpam_axfree {P} : ipperm P = true ->
  (projT1 (ipgax P) -> False) -> forall l,
  ll (i2pfrag i2a P) l -> forall l0 C, Forall_Type oclpam (C :: l0) ->
    Permutation_Type l (ill2ll i2a C :: rev (map dual (map (ill2ll i2a) l0))) ->
      ill P l0 C.
Proof with try eassumption ; try reflexivity.
intros Hperm P_axfree l pi l0 C Hoclm HP.
apply cut_admissible_axfree in pi.
- rewrite cutrm_i2pfrag in pi.
  eapply ll_to_ill_oclpam_cutfree in pi...
  + destruct pi as [pi _].
    eapply (stronger_ipfrag)...
    nsplit 3...
    intros a ; destruct (P_axfree a).
  + intros a ; destruct (P_axfree a).
  + constructor.
  + simpl ; rewrite Hperm ; simpl...
- assumption.
Qed.

End Conservativity.


(** ** Non conservativity of [ll] over [ill]. *)

Section Non_Conservativity.

Variable P : ipfrag.
Hypothesis P_perm : ipperm P = true.
Hypothesis P_cut : ipcut P = false.
Hypothesis P_gax : projT1 (ipgax P) -> False.

Variable i2a : IAtom -> Atom.

Variable x : IAtom.
Variable y : IAtom.
Variable z : IAtom.

(** Counter example from Harold Schellinx *)
Definition cons_counter_ex :=
  ilpam (ilpam (ilpam (ivar x) (ivar y)) izero)
        (itens (ivar x) (ilpam izero (ivar z))).

Lemma counter_haszero : nonzerospos cons_counter_ex -> False.
Proof.
intros Hnzsp.
inversion Hnzsp.
inversion H1.
apply H8.
constructor.
Qed.

Lemma counter_ll_prove :
  ll (i2pfrag i2a P) (ill2ll i2a cons_counter_ex :: nil).
Proof with myeeasy.
simpl.
apply parr_r.
eapply ex_r ; [ | apply PCperm_Type_swap ].
rewrite <- (app_nil_l (tens (var _) _ :: _)).
apply tens_r.
- apply parr_r.
  eapply ex_r ;
    [ | unfold PCperm_Type ; simpl ; rewrite P_perm ;
        symmetry ; apply Permutation_Type_cons_append ].
  eapply ex_r ;
    [ | unfold PCperm_Type ; simpl ; rewrite P_perm ;
        symmetry ; apply Permutation_Type_cons_append ].
  rewrite <- ? app_comm_cons.
  rewrite app_comm_cons.
  apply tens_r.
  + eapply ex_r ; [ apply ax_r | PCperm_Type_solve ].
  + apply parr_r.
    eapply ex_r ;
    [ | unfold PCperm_Type ; simpl ; rewrite P_perm ;
        symmetry ; apply Permutation_Type_cons_append ].
    rewrite <- ? app_comm_cons.
    apply top_r.
- apply top_r.
Qed.

Fact no_at_prove_ill : forall i, ill P nil (ivar i) -> False.
Proof.
intros i pi.
remember (ivar i) as C.
remember nil as l.
revert Heql HeqC.
induction pi ; intros Heql HeqC ; subst ;
  (try now (inversion Heql)) ;
  (try now (inversion HeqC)) ;
  try now (destruct l1 ; inversion Heql) ; subst.
- symmetry in p.
  apply PEperm_Type_nil in p ; subst.
  intuition.
- apply app_eq_nil in Heql ; destruct Heql as [? Heql] ; subst.
  apply app_eq_nil in Heql ; destruct Heql as [Heql ?] ; subst.
  destruct lw' ; inversion Heql ; subst.
  symmetry in p ; apply Permutation_Type_nil in p ; subst.
  intuition.
- destruct l1 ; destruct l0 ; inversion Heql.
- destruct l ; inversion Heql.
- rewrite f in P_cut ; inversion P_cut.
Qed.

Fact no_biat_prove_ill : forall i j, i <> j ->
  ill P (ivar i :: nil) (ivar j) -> False.
Proof with myeasy.
intros i j Ha pi.
remember (ivar j) as C.
remember (ivar i :: nil) as l.
revert Heql HeqC.
induction pi ; intros Heql HeqC ; subst ;
  (try now (inversion Heql)) ;
  (try now (inversion HeqC)) ;
  try now (destruct l1 ; inversion Heql ; destruct l1 ; inversion H1) ; subst...
- inversion HeqC ; inversion Heql ; subst ; intuition.
- symmetry in p.
  apply PEperm_Type_length_1_inv in p ; subst ; intuition.
- destruct l1 ; inversion Heql ; subst.
  + destruct lw' ; inversion H0.
    simpl in H ; subst.
    symmetry in p ; apply Permutation_Type_nil in p ; subst.
    intuition.
  + apply app_eq_nil in H1 ; destruct H1 as [? Heq] ; subst.
    apply app_eq_nil in Heq ; destruct Heq as [Heq ?] ; subst.
    destruct lw' ; inversion Heq.
    symmetry in p ; apply Permutation_Type_nil in p ; subst.
    intuition.
- destruct l1 ; destruct l0 ; inversion Heql ;
    try destruct l0 ; try destruct l1 ; inversion Heql.
- destruct l ; inversion Heql ; subst.
  destruct l ; inversion H1.
- rewrite f in P_cut ; inversion P_cut.
Qed.

Fact no_biat_map_prove_ill : forall i j, i <> j ->
  ill P nil (ilpam (ivar i) (ivar j)) -> False.
Proof with myeasy.
intros i j Ha pi.
remember (ilpam (ivar i) (ivar j)) as C.
remember (nil) as l.
revert Heql HeqC.
induction pi ; intros Heql HeqC ; subst ;
  (try now (inversion Heql)) ;
  (try now (inversion HeqC)) ;
  try now (destruct l1 ; inversion Heql) ; subst...
- symmetry in p.
  apply PEperm_Type_nil in p ; subst.
  intuition.
- apply app_eq_nil in Heql ; destruct Heql as [? Heql] ; subst.
  apply app_eq_nil in Heql ; destruct Heql as [Heql ?] ; subst.
  destruct lw' ; inversion Heql.
  symmetry in p ; apply Permutation_Type_nil in p ; subst.
  intuition.
- inversion HeqC ; subst.
  eapply no_biat_prove_ill ; eassumption.
- destruct l1 ; destruct l0 ; inversion Heql.
- rewrite f in P_cut ; inversion P_cut.
Qed.

(** We need two distinct atoms *)
Hypothesis twoat : x <> y.

Fact pre_pre_counter_ex_ill :
  ill P (ilpam (ilpam (ivar x) (ivar y)) izero :: nil) (ivar x) -> False.
Proof with myeasy.
intros pi.
remember (ilpam (ilpam (ivar x) (ivar y)) izero :: nil) as l.
remember (ivar x) as C.
revert Heql HeqC.
induction pi ; intros Heql HeqC ; subst ;
  (try now (inversion Heql)) ;
  (try now (inversion HeqC)) ;
  try now (destruct l1 ; inversion Heql ; destruct l1 ; inversion H1) ; subst...
- symmetry in p.
  apply PEperm_Type_length_1_inv in p ; subst ; intuition.
- destruct l1 ; inversion Heql ; subst.
  + destruct lw' ; inversion H0.
    simpl in H ; subst.
    symmetry in p ; apply Permutation_Type_nil in p ; subst.
    intuition.
  + apply app_eq_nil in H1 ; destruct H1 as [? Heq] ; subst.
    apply app_eq_nil in Heq ; destruct Heq as [Heq ?] ; subst.
    destruct lw' ; inversion Heq.
    symmetry in p ; apply Permutation_Type_nil in p ; subst.
    intuition.
- destruct l1 ; inversion Heql ; try rewrite app_nil_l in Heql ; subst.
  + apply app_eq_nil in H2.
    destruct H2 ; subst.
    eapply no_biat_map_prove_ill ; eassumption.
  + destruct l1 ; inversion H1.
- destruct l1 ; destruct l0 ; inversion Heql ; 
    try destruct l0 ; try destruct l1 ; inversion H1.
- destruct l ; inversion Heql ; subst.
  destruct l ; inversion H1.
- rewrite f in P_cut ; inversion P_cut.
Qed.

Fact pre_counter_ex_ill :
  @ill P (ilpam (ilpam (ivar x) (ivar y)) izero :: nil)
         (itens (ivar x) (ilpam izero (ivar z))) -> False.
Proof with myeasy.
intros pi.
remember (ilpam (ilpam (ivar x) (ivar y)) izero :: nil) as l.
remember (itens (ivar x) (ilpam izero (ivar z))) as C.
revert Heql HeqC.
induction pi ; intros Heql HeqC ; subst ;
  (try now (inversion Heql)) ;
  (try now (inversion HeqC)) ;
  try now (destruct l1 ; inversion Heql ; destruct l1 ; inversion H1) ; subst...
- symmetry in p.
  apply PEperm_Type_length_1_inv in p ; intuition.
- destruct l1 ; inversion Heql ; subst.
  + destruct lw' ; inversion H0.
    simpl in H ; subst.
    symmetry in p ; apply Permutation_Type_nil in p ; subst.
    intuition.
  + apply app_eq_nil in H1 ; destruct H1 as [? Heq] ; subst.
    apply app_eq_nil in Heq ; destruct Heq as [Heq ?] ; subst.
    destruct lw' ; inversion Heq.
    symmetry in p ; apply Permutation_Type_nil in p ; subst.
    intuition.
- destruct l1 ; inversion Heql ; inversion HeqC ; try rewrite app_nil_l in Heql ; subst.
  + apply no_at_prove_ill in pi1...
  + apply app_eq_nil in H1.
    destruct H1 ; subst.
    apply pre_pre_counter_ex_ill in pi1...
- destruct l1 ; inversion Heql ; subst.
  + apply app_eq_nil in H2.
    destruct H2 ; subst.
    apply no_biat_map_prove_ill in pi1...
  + destruct l1 ; inversion H1.
- destruct l1 ; destruct l0 ; inversion Heql ; 
    try destruct l0 ; try destruct l1 ; inversion H1.
- rewrite f in P_cut ; inversion P_cut.
Qed.

Fact counter_ex_ill : @ill P nil cons_counter_ex -> False.
Proof with myeasy.
intros pi.
remember (cons_counter_ex) as C.
remember (nil) as l.
revert Heql HeqC.
induction pi ; intros Heql HeqC ; subst ;
  (try now (inversion Heql)) ;
  (try now (inversion HeqC)) ;
  try now (destruct l1 ; inversion Heql) ; subst...
- symmetry in p.
  apply PEperm_Type_nil in p ; intuition.
- apply app_eq_nil in Heql ; destruct Heql as [? Heql] ; subst.
  apply app_eq_nil in Heql ; destruct Heql as [Heql ?] ; subst.
  destruct lw' ; inversion Heql.
  symmetry in p ; apply Permutation_Type_nil in p ; subst.
  intuition.
- inversion HeqC ; subst ; apply pre_counter_ex_ill in pi...
- destruct l1 ; destruct l0 ; inversion Heql.
- rewrite f in P_cut ; inversion P_cut.
Qed.

End Non_Conservativity.


