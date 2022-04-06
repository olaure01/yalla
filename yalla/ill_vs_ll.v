(* ill_vs_ll library for yalla *)

(** * Comparison between Intuitionistic Linear Logic and Linear Logic *)

From OLlibs Require Import funtheory infinite List_more
                           Permutation_Type_more Permutation_Type_solve
                           CPermutation_Type GPermutation_Type.
From Yalla Require Import ll_fragments.
From Yalla Require Export ill_prop.

Set Implicit Arguments.


Section Atoms.

Context { atom : InfDecType }.
Context { preiatom : DecType }.
Context { Atoms : IAtom2AtomType atom preiatom }.

Notation iatom := (option preiatom).
Notation formula := (@formula atom).
Notation iformula := (@iformula preiatom).
Notation i2a := IAtom2Atom.

(** ** Characterization of [ill] as a fragment of [ll] *)

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

Lemma ill2ll_map_ioc l : map dual (map ill2ll (map ioc l)) = map wn (map dual (map ill2ll l)).
Proof. induction l as [ | a l IHl ]; [ | list_simpl; rewrite IHl ]; reflexivity. Qed.

Lemma ill2ll_map_ioc_inv l1 l2 : map wn l1 = map dual (map ill2ll l2) ->
  { l2' | l2 = map ioc l2' & l1 = map dual (map ill2ll l2') }.
Proof.
induction l2 in l1 |- *; intros Heq; destruct l1; inversion Heq.
- exists nil; reflexivity.
- destruct a; inversion H0.
  apply IHl2 in H1 as [l0 -> ->].
  exists (a :: l0); reflexivity.
Qed.


(** Translation of proof fragments *)
Definition i2pfrag P := {|
  pcut := ipcut P ;
  pgax := existT (fun x => x -> list formula) (projT1 (ipgax P))
          (fun a => ill2ll (snd (projT2 (ipgax P) a))
                    :: rev (map dual (map ill2ll (fst (projT2 (ipgax P) a))))) ;
  pmix := pmix_none ;
  pperm := ipperm P |}.

Lemma cutrm_i2pfrag P : cutrm_pfrag (i2pfrag P) = i2pfrag (cutrm_ipfrag P).
Proof. reflexivity. Qed.

Proposition ill_to_ll P l C : ill P l C ->
  ll (i2pfrag P) (ill2ll C :: rev (map dual (map ill2ll l))).
Proof.
intros Hill; induction Hill; list_simpl;
  try list_simpl in IHHill; try list_simpl in IHHill1; try list_simpl in IHHill2.
- eapply ex_r, PCPermutation_Type_swap.
  apply ax_r.
- eapply ex_r; [ eassumption | ].
  hyps_GPermutation_Type_unfold; unfold PCPermutation_Type; cbn; destruct ipperm.
  * apply Permutation_Type_cons; [ reflexivity | ].
    do 2 apply Permutation_Type_map.
    apply Permutation_Type_rev'; assumption.
  * subst; reflexivity.
- rewrite_all ill2ll_map_ioc.
  rewrite_all app_comm_cons.
  apply Permutation_Type_rev' in p.
  do 2 eapply Permutation_Type_map in p. 
  eapply ex_wn_r; eassumption.
- apply one_r.
- rewrite app_comm_cons.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply bot_r.
  eapply ex_r; [ eassumption | ].
  rewrite ? app_comm_cons.
  apply PCPermutation_Type_app_comm.
- apply tens_r; assumption.
- rewrite app_comm_cons.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply parr_r.
  eapply ex_r; [ eassumption | ].
  rewrite ? app_comm_cons.
  apply PCPermutation_Type_app_comm.
- apply parr_r; assumption.
- rewrite app_comm_cons, app_assoc.
  eapply ex_r ; [ | apply PCPermutation_Type_app_comm ].
  rewrite bidual, ? app_assoc, <- ? app_comm_cons.
  apply tens_r; [ assumption | ].
  eapply ex_r; [ eassumption | ].
  rewrite ? app_comm_cons.
  apply PCPermutation_Type_app_comm.
- apply parr_r; assumption.
- rewrite app_comm_cons.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  list_simpl.
  change (var (i2a atN) :: map dual (map ill2ll (rev l)))
    with ((var (i2a atN) :: nil) ++ map dual (map ill2ll (rev l))).
  apply tens_r.
  + rewrite bidual; assumption.
  + apply ax_r.
- apply parr_r.
  eapply ex_r; [ eassumption | ].
  symmetry.
  rewrite (app_comm_cons _ _ (ill2ll B)).
  apply PCPermutation_Type_cons_append.
- rewrite app_comm_cons.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  rewrite <- ? app_comm_cons, <- ? app_assoc, bidual.
  apply tens_r; [ | assumption ].
  eapply ex_r; [ eassumption | ].
  rewrite ? app_comm_cons.
  apply PCPermutation_Type_app_comm.
- apply parr_r.
  eapply ex_r; [ eassumption | ].
  symmetry.
  rewrite (app_comm_cons _ _ (ill2ll N)).
  apply PCPermutation_Type_cons_append.
- cons2app.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  rewrite <- ? app_comm_cons, <- ? app_assoc, bidual.
  list_simpl.
  apply tens_r; [ | assumption ].
  apply ax_r.
- apply top_r.
- apply with_r; assumption.
- rewrite ? app_comm_cons.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply plus_r1.
  eapply ex_r; [ eassumption | ].
  rewrite ? app_comm_cons.
  apply PCPermutation_Type_app_comm.
- rewrite ? app_comm_cons.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply plus_r2.
  eapply ex_r; [ eassumption | ].
  rewrite ? app_comm_cons.
  apply PCPermutation_Type_app_comm.
- rewrite ? app_comm_cons.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply top_r.
- apply plus_r1; assumption.
- apply plus_r2; assumption.
- rewrite ? app_comm_cons.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply with_r.
  + eapply ex_r; [ apply IHHill1 | ].
    rewrite ? app_comm_cons.
    apply PCPermutation_Type_app_comm.
  + eapply ex_r; [ apply IHHill2 | ].
    rewrite ? app_comm_cons.
    apply PCPermutation_Type_app_comm.
- rewrite_all ill2ll_map_ioc.
  apply oc_r; assumption.
- rewrite ? app_comm_cons.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply de_r.
  eapply ex_r; [ eassumption | ].
  rewrite ? app_comm_cons.
  apply PCPermutation_Type_app_comm.
- rewrite app_comm_cons.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply wk_r.
  eapply ex_r; [ eassumption | ].
  rewrite ? app_comm_cons.
  apply PCPermutation_Type_app_comm.
- rewrite app_comm_cons.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  rewrite <- app_comm_cons.
  apply co_r.
  eapply ex_r; [ eassumption | ].
  rewrite ? app_comm_cons.
  apply PCPermutation_Type_app_comm.
- rewrite app_comm_cons.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  rewrite <- app_assoc.
  assert (pcut (i2pfrag P) = true) as fc by (now cbn).
  eapply (@cut_r _ _ fc); [ | eassumption ].
  eapply ex_r; [ eassumption | ].
  rewrite ? app_comm_cons.
  apply PCPermutation_Type_app_comm.
- replace (ill2ll (snd (projT2 (ipgax P) a))
   :: map dual (map ill2ll (rev (fst (projT2 (ipgax P) a)))))
  with (projT2 (pgax (i2pfrag P)) a) by (cbn ; rewrite 2 map_rev ; reflexivity).
  apply gax_r.
Qed.


(** ** Non conservativity of [ll] over [ill]. *)

Section Non_Conservativity_Atoms.

Variable x y z : iatom.

(** Counter example from Harold Schellinx *)
Notation cons_counter_ex :=
  (ilpam (ilpam (ilpam (ivar x) (ivar y)) izero)
        (itens (ivar x) (ilpam izero (ivar z)))).

Lemma counter_ll_prove :
  ll_ll (ill2ll cons_counter_ex :: nil).
Proof.
cbn.
apply parr_r.
eapply ex_r ; [ | apply PCPermutation_Type_swap ].
rewrite <- (app_nil_l (tens (var _) _ :: _)).
apply tens_r.
- apply parr_r.
  eapply ex_r ; [ | symmetry ; apply Permutation_Type_cons_append ].
  eapply ex_r ; [ | symmetry ; apply Permutation_Type_cons_append ].
  apply tens_r.
  + eapply ex_r ; [ apply ax_r | GPermutation_Type_solve ].
  + apply parr_r.
    eapply ex_r ; [ | symmetry ; apply Permutation_Type_cons_append ].
    apply top_r.
- apply top_r.
Qed.

Fact no_at_prove_ill : forall i, @ill_ll preiatom nil (ivar i) -> False.
Proof.
intros i pi.
remember (ivar i) as C.
remember nil as l.
revert Heql HeqC.
induction pi ; intros Heql HeqC ; subst ;
  (try now (inversion Heql)) ;
  (try now (inversion HeqC)) ;
  try now (destruct l1 ; inversion Heql).
- symmetry in p.
  apply PEPermutation_Type_nil in p ; subst.
  intuition.
- apply app_eq_nil in Heql ; destruct Heql as [? Heql] ; subst.
  apply app_eq_nil in Heql ; destruct Heql as [Heql ?] ; subst.
  destruct lw' ; inversion Heql ; subst.
  symmetry in p ; apply Permutation_Type_nil in p ; subst.
  intuition.
- destruct l1 ; destruct l0 ; inversion Heql.
- destruct l ; inversion Heql.
Qed.

Fact no_biat_prove_ill : forall i j, i <> j ->
  @ill_ll preiatom (ivar i :: nil) (ivar j) -> False.
Proof.
intros i j Ha pi.
remember (ivar j) as C.
remember (ivar i :: nil) as l.
revert Heql HeqC.
induction pi ; intros Heql HeqC ; subst ;
  (try now (inversion Heql)) ;
  (try now (inversion HeqC)) ;
  try now (destruct l1 ; inversion Heql ; destruct l1 ; inversion H1).
- inversion HeqC ; inversion Heql ; subst ; intuition.
- symmetry in p.
  apply PEPermutation_Type_length_1_inv in p ; subst ; intuition.
- destruct l1 ; inversion Heql ; subst.
  + destruct lw' ; inversion H0.
    cbn in H ; subst.
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
Qed.

Fact no_biat_map_prove_ill : forall i j, i <> j ->
  @ill_ll preiatom nil (ilpam (ivar i) (ivar j)) -> False.
Proof.
intros i j Ha pi.
apply ilpam_rev_noax in pi; [ | intros Hax; inversion Hax ].
eapply no_biat_prove_ill ; eassumption.
Qed.

(** We need two distinct atoms *)
Hypothesis twoat : x <> y.

Fact pre_pre_counter_ex_ill :
  ill_ll (ilpam (ilpam (ivar x) (ivar y)) izero :: nil) (ivar x) -> False.
Proof.
intros pi.
remember (ilpam (ilpam (ivar x) (ivar y)) izero :: nil) as l.
remember (ivar x) as C.
revert Heql HeqC.
induction pi ; intros Heql HeqC ; subst ;
  (try now (inversion Heql)) ;
  (try now (inversion HeqC)) ;
  try now (destruct l1 ; inversion Heql ; destruct l1 ; inversion H1).
- symmetry in p.
  apply PEPermutation_Type_length_1_inv in p ; subst ; intuition.
- destruct l1 ; inversion Heql ; subst.
  + destruct lw' ; inversion H0.
    cbn in H ; subst.
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
Qed.

Fact pre_counter_ex_ill :
  ill_ll (ilpam (ilpam (ivar x) (ivar y)) izero :: nil)
         (itens (ivar x) (ilpam izero (ivar z))) -> False.
Proof.
intros pi.
remember (ilpam (ilpam (ivar x) (ivar y)) izero :: nil) as l.
remember (itens (ivar x) (ilpam izero (ivar z))) as C.
revert Heql HeqC.
induction pi ; intros Heql HeqC ; subst ;
  (try now (inversion Heql)) ;
  (try now (inversion HeqC)) ;
  try now (destruct l1 ; inversion Heql ; destruct l1 ; inversion H1).
- symmetry in p.
  apply PEPermutation_Type_length_1_inv in p ; intuition.
- destruct l1 ; inversion Heql ; subst.
  + destruct lw' ; inversion H0.
    cbn in H ; subst.
    symmetry in p ; apply Permutation_Type_nil in p ; subst.
    intuition.
  + apply app_eq_nil in H1 ; destruct H1 as [? Heq] ; subst.
    apply app_eq_nil in Heq ; destruct Heq as [Heq ?] ; subst.
    destruct lw' ; inversion Heq.
    symmetry in p ; apply Permutation_Type_nil in p ; subst.
    intuition.
- destruct l1 ; inversion Heql ; inversion HeqC ; try rewrite app_nil_l in Heql ; subst.
  + apply (no_at_prove_ill pi1).
  + apply app_eq_nil in H1.
    destruct H1 ; subst.
    apply (pre_pre_counter_ex_ill pi1).
- destruct l1 ; inversion Heql ; subst.
  + apply app_eq_nil in H2.
    destruct H2 ; subst.
    apply (no_biat_map_prove_ill twoat pi1).
  + destruct l1; inversion H1.
- destruct l1, l0; inversion Heql; try destruct l0; try destruct l1; inversion H1.
Qed.

Fact counter_ex_ill : ill_ll nil cons_counter_ex -> False.
Proof.
intros pi.
apply ilpam_rev_noax in pi; [ | intros Hax; inversion Hax ].
apply pre_counter_ex_ill in pi ; assumption.
Qed.

End Non_Conservativity_Atoms.


(** Counter example from Jui-Hsuan Wu *)
Notation cons_counter_ex_atfree :=
 (ilpam (ilpam (ilpam (ilpam (ilpam izero ione) ione) izero) izero) ione).

Lemma counter_atfree_ll_prove :
  ll_ll (ill2ll cons_counter_ex_atfree :: nil).
Proof.
cbn.
apply parr_r.
eapply ex_r ; [ | symmetry ; apply Permutation_Type_cons_append ].
apply tens_r.
- apply parr_r.
  eapply ex_r ; [ | symmetry ; apply Permutation_Type_cons_append ].
  apply tens_r.
  + apply parr_r.
    eapply ex_r ; [ | symmetry ; apply Permutation_Type_cons_append ].
    apply top_r.
  + apply bot_r.
    apply one_r.
- apply top_r.
Qed.

Fact counter_ex_atfree_ill : @ill_ll preiatom nil cons_counter_ex_atfree -> False.
Proof.
intros pi.
apply ilpam_rev_noax in pi; [ | intros Hax; inversion Hax ].
remember (nil ++ ilpam (ilpam (ilpam (ilpam izero ione) ione) izero) izero :: nil) as l.
remember ione as C.
revert Heql HeqC.
induction pi ; intros Heql HeqC ; subst ;
  (try now (inversion Heql)) ;
  (try now (inversion HeqC)) ;
  (try now (destruct l1 ; inversion Heql)) ;
  try now (destruct l1 ; inversion Heql ; destruct l1 ; inversion H1).
- cbn in p ; symmetry in p.
  apply Permutation_Type_length_1_inv in p ; subst.
  apply IHpi; reflexivity.
- apply IHpi; [ | reflexivity ].
  destruct l1 ; inversion Heql.
  + destruct lw' ; inversion H0.
    symmetry in p ; apply Permutation_Type_nil in p ; subst; assumption.
  + apply app_eq_nil in H1.
    destruct H1 as [? H1] ; subst.
    apply app_eq_nil in H1.
    destruct H1 as [H1 ?] ; subst.
    destruct lw' ; inversion H1.
    symmetry in p ; apply Permutation_Type_nil in p ; subst; assumption.
- destruct l1 ; inversion Heql ; subst.
  + apply app_eq_nil in H2 ; destruct H2 ; subst.
    clear - pi1.
    apply ilpam_rev_noax in pi1; [ | intros Hax; inversion Hax ].
    remember (nil ++ ilpam (ilpam izero ione) ione :: nil) as l.
    remember izero as C.
    revert Heql HeqC.
    induction pi1 ; intros Heql HeqC ; subst ;
      (try now (inversion Heql)) ;
      (try now (inversion HeqC)) ;
      (try now (destruct l1 ; inversion Heql)) ;
      try now (destruct l1 ; inversion Heql ; destruct l1 ; inversion H1).
    * cbn in p ; symmetry in p.
      apply Permutation_Type_length_1_inv in p ; subst.
      apply IHpi1; reflexivity.
    * apply IHpi1; [ | reflexivity ].
      destruct l1 ; inversion Heql.
      -- destruct lw' ; inversion H0.
         symmetry in p ; apply Permutation_Type_nil in p ; subst; assumption.
      -- apply app_eq_nil in H1.
         destruct H1 as [? H1] ; subst.
         apply app_eq_nil in H1.
         destruct H1 as [H1 ?] ; subst.
         destruct lw' ; inversion H1.
         symmetry in p ; apply Permutation_Type_nil in p ; subst; assumption.
    * destruct l1 ; inversion Heql ; subst.
      -- apply app_eq_nil in H2 ; destruct H2 ; subst.
         clear - pi1_2.
         remember (nil ++ ione :: nil) as l.
         remember izero as C.
         revert Heql HeqC.
         induction pi1_2 ; intros Heql HeqC ; subst ;
           (try now (inversion Heql)) ;
           (try now (inversion HeqC)) ;
           (try now (destruct l1 ; inversion Heql)) ;
           try now (destruct l1 ; inversion Heql ; destruct l1 ; inversion H1).
         ++ cbn in p ; symmetry in p.
            apply Permutation_Type_length_1_inv in p ; subst.
            apply IHpi1_2; reflexivity.
         ++ apply IHpi1_2; [ | reflexivity ].
            destruct l1 ; inversion Heql.
            ** destruct lw' ; inversion H0.
               symmetry in p ; apply Permutation_Type_nil in p ; subst; assumption.
            ** apply app_eq_nil in H1.
               destruct H1 as [? H1] ; subst.
               apply app_eq_nil in H1.
               destruct H1 as [H1 ?] ; subst.
               destruct lw' ; inversion H1.
               symmetry in p ; apply Permutation_Type_nil in p ; subst; assumption.
         ++ destruct l1 ; inversion Heql ; subst.
            ** clear - pi1_2.
               remember (nil ++ nil) as l.
               remember izero as C.
               revert Heql HeqC.
               induction pi1_2 ; intros Heql HeqC ; subst ;
                 (try now (inversion Heql)) ;
                 (try now (inversion HeqC)) ;
                 (try now (destruct l1 ; inversion Heql)) ;
                 try now (destruct l1 ; inversion Heql ; destruct l1 ; inversion H1).
               --- symmetry in p ; apply Permutation_Type_nil in p ; subst.
                   apply IHpi1_2; reflexivity.
               --- apply app_eq_nil in Heql.
                   destruct Heql as [? Heql] ; subst.
                   apply app_eq_nil in Heql.
                   destruct Heql as [Heql ?] ; subst.
                   destruct lw' ; inversion Heql.
                   symmetry in p ; apply Permutation_Type_nil in p ; subst.
                   apply IHpi1_2; reflexivity.
               --- destruct l1 ; destruct l0 ; inversion Heql.
            ** destruct l1 ; inversion H1.
         ++ destruct l1 ; inversion Heql.
            ** destruct l0 ; inversion H0.
               destruct l0 ; inversion H2.
            ** destruct l1 ; destruct l0 ; inversion H1.
      -- destruct l1 ; inversion H1.
    * destruct l1 ; inversion Heql.
      -- destruct l0 ; inversion H0.
         destruct l0 ; inversion H2.
      -- destruct l1 ; destruct l0 ; inversion H1.
  + destruct l1 ; inversion H1.
- destruct l1 ; inversion Heql.
  + destruct l0 ; inversion H0.
    destruct l0 ; inversion H2.
  + destruct l1 ; destruct l0 ; inversion H1.
Qed.

End Atoms.


(** ** Conservativity results for [ll] over [ill] *)

Section Conservativity_Atoms.

(** Embedding of [IAtom] into [Atom] *)
Context { atom : InfDecType }.
Context { preiatom : DecType }.
Context { Atoms : IAtom2AtomType_inj atom preiatom }.

Notation formula := (@formula atom).
Notation iformula := (@iformula preiatom).
Notation i2a := IAtom2Atom.
Notation i2a_inj := IAtom2Atom_inj.

(** *** Comparisons between [ll] connectives and [ill] *)

Lemma wn_not_idefin A F :
  ll_mix0 (dual (ill2ll A) :: nil) -> ll_mix0 (oc F :: ill2ll A :: nil) -> False.
Proof.
cut (forall l2,
  ll_mix0 (dual (ill2ll A) :: nil) ->
  Permutation_Type (oc F :: ill2ll A :: nil) l2 -> ll_mix0 l2 -> False).
{ intros H pi1 pi2 ; eapply H; try eassumption; reflexivity. }
revert F; induction A; cbn; intros F l2 pi1 HP2 pi2.
- remember (covar (i2a i) :: nil) as l1 ; revert Heql1 ;
    clear - pi1 ; induction pi1 ; intros Heql1 ;
    try (now inversion Heql1) ; subst.
  + symmetry in p; apply Permutation_Type_length_1_inv in p.
    apply IHpi1; assumption.
  + destruct l1 ; inversion Heql1 ; destruct lw' ; inversion H0.
    * now symmetry in p ; apply Permutation_Type_nil in p ; subst.
    * now symmetry in p ; apply Permutation_Type_nil in p ; subst.
    * destruct l1 ; inversion H1.
  + destruct L; try inversion Heql1; try inversion i0.
- revert HP2 ; clear - pi2 ; induction pi2 ; intros HP2 ;
    try (now (apply Permutation_Type_length in HP2 ; inversion HP2)) ;
    try (now (apply Permutation_Type_length_2_inv in HP2 ; inversion HP2)).
  + apply IHpi2.
    symmetry in p.
    transitivity l2; assumption.
  + apply IHpi2.
    apply (Permutation_Type_map wn) in p.
    Permutation_Type_solve.
  + destruct L; try inversion i.
    apply Permutation_Type_sym in HP2.
    apply Permutation_Type_nil_cons in HP2; assumption.
  + apply Permutation_Type_length_2_inv in HP2.
    destruct HP2 ; inversion e.
    destruct l ; inversion H1.
- rewrite <- (app_nil_l (parr _ _ :: _)) in pi1.
  eapply parr_rev in pi1 ; [ | intros a; destruct a ].
  list_simpl in pi1.
  assert ((ll_mix0 (oc F :: ill2ll A1 :: nil) * ll_mix0 (ill2ll A2 :: nil))
        + (ll_mix0 (ill2ll A1 :: nil) * ll_mix0 (oc F :: ill2ll A2 :: nil)))
    as [[pi2' pi2''] | [pi2' pi2'']].
  { revert HP2 ; clear - pi2 ; induction pi2 ; intros HP2 ;
      try (now (apply Permutation_Type_length in HP2 ; inversion HP2)) ;
      try (now (apply Permutation_Type_length_2_inv in HP2 ; inversion HP2)).
    - apply IHpi2.
      cbn in p ; Permutation_Type_solve.
    - apply IHpi2.
      apply (Permutation_Type_map wn) in p.
      Permutation_Type_solve.
    - destruct L; inversion i.
      apply Permutation_Type_sym in HP2.
      apply Permutation_Type_nil_cons in HP2.
      inversion HP2.
    - apply Permutation_Type_length_2_inv in HP2.
      destruct HP2 ; inversion e ; subst.
      destruct l2 ; inversion H2 ; subst.
      + destruct l1 ; inversion H2 ; subst.
        left; split; [ | assumption ].
        eapply ex_r ; [ apply pi2_1 | GPermutation_Type_solve ]; assumption.
      + apply app_eq_nil in H1 ; destruct H1 ; subst.
        right; split; [ assumption | ].
        eapply ex_r ; [ apply pi2_2 | GPermutation_Type_solve ]; assumption.
    - apply Permutation_Type_length_2_inv in HP2.
      destruct HP2 ; inversion e.
      destruct l ; inversion H1. }
  + eapply cut_mix0_r in pi1 ; [ | rewrite bidual; eassumption ].
    eapply IHA1 ; [ apply pi1 | reflexivity | eassumption ].
  + eapply ex_r in pi1 ; [ | apply Permutation_Type_swap ].
    eapply cut_mix0_r in pi1 ; [ | rewrite bidual; eassumption ].
    eapply IHA2 ; [ apply pi1 | reflexivity | eassumption ].
- eapply tens_rev in pi1 ; [ | intros a; destruct a | reflexivity ].
  cons2app in HP2.
  assert (Heq2 := HP2).
  symmetry in Heq2 ; apply Permutation_Type_vs_elt_inv in Heq2.
  destruct Heq2 as ((l' & l'') & Heq2) ; subst.
  eapply parr_rev in pi2 ; [ | intros a; destruct a ].
  destruct pi1 as [pi1' pi1''].
  rewrite bidual in pi1'.
  eapply (@cut_mix0_r _ _ (l' ++ ill2ll A2 :: l'')) in pi1' ;
    [ | eapply ex_r ; [ apply pi2 | GPermutation_Type_solve ]].
  eapply IHA2.
  + eassumption.
  + apply Permutation_Type_app_inv in HP2 ; cbn in HP2.
    apply Permutation_Type_swap.
  + eapply ex_r ; [ apply pi1' | ].
    list_simpl in HP2; cons2app in HP2; apply Permutation_Type_app_inv in HP2.
    list_simpl; etransitivity; [ symmetry; apply Permutation_Type_middle | ].
    symmetry; apply Permutation_Type_cons, HP2; reflexivity.
- eapply tens_rev in pi1 ; [ | intros a; destruct a | reflexivity ].
  destruct pi1 as [_ pi1'].
  clear - pi1'.
  assert ({ l & Permutation_Type (covar (i2a atN) :: nil) l })
    as [l HP] by (eexists ; reflexivity).
  eapply ex_r in pi1' ; [ | apply HP ].
  revert HP ; induction pi1' ; intros HP ;
    try (now (apply Permutation_Type_length in HP ; inversion HP)) ;
    try (now (apply Permutation_Type_length_1_inv in HP ; inversion HP)).
  + apply IHpi1'.
    cbn in p ; Permutation_Type_solve.
  + apply IHpi1'.
    apply (Permutation_Type_map wn) in p.
    Permutation_Type_solve.
  + destruct L; inversion i.
    apply Permutation_Type_sym in HP.
    apply Permutation_Type_nil_cons in HP; assumption.
- eapply tens_rev in pi1 ; [ | intros a; destruct a | reflexivity ].
  cons2app in HP2.
  assert (Heq2 := HP2).
  symmetry in Heq2 ; apply Permutation_Type_vs_elt_inv in Heq2.
  destruct Heq2 as ((l' & l'') & Heq2) ; subst.
  eapply parr_rev in pi2 ; [ | intros a; destruct a ].
  destruct pi1 as [pi1' pi1''].
  rewrite bidual in pi1''.
  eapply (@cut_mix0_r _ _ (l' ++ ill2ll A2 :: l'')) in pi1'' ;
    [ | eapply ex_r ; [ apply pi2 | GPermutation_Type_solve ]].
  eapply IHA2.
  + eassumption.
  + apply Permutation_Type_app_inv in HP2 ; cbn in HP2.
    apply Permutation_Type_swap.
  + eapply ex_r ; [ apply pi1'' | ].
    list_simpl in HP2; cons2app in HP2; apply Permutation_Type_app_inv in HP2.
    list_simpl; etransitivity; [ symmetry; apply Permutation_Type_middle | ].
    symmetry; apply Permutation_Type_cons, HP2; reflexivity.
- eapply tens_rev in pi1 ; [ | intros a; destruct a | reflexivity ].
  destruct pi1 as [pi1' _].
  clear - pi1'.
  assert ({ l & Permutation_Type (covar (i2a atN) :: nil) l })
    as [l HP] by (eexists ; reflexivity).
  eapply ex_r in pi1' ; [ | apply HP ].
  revert HP ; induction pi1' ; intros HP ;
    try (now (apply Permutation_Type_length in HP ; inversion HP)) ;
    try (now (apply Permutation_Type_length_1_inv in HP ; inversion HP)).
  + apply IHpi1'.
    cbn in p ; Permutation_Type_solve.
  + apply IHpi1'.
    apply (Permutation_Type_map wn) in p.
    Permutation_Type_solve.
  + destruct L; inversion i.
    apply Permutation_Type_sym in HP.
    apply Permutation_Type_nil_cons in HP; assumption.
- remember (zero :: nil) as l1 ; revert Heql1 ;
    clear - pi1 ; induction pi1 ; intros Heql1 ;
    try (now inversion Heql1) ; subst.
  + symmetry in p ; apply Permutation_Type_length_1_inv in p.
    apply IHpi1; assumption.
  + destruct l1 ; inversion Heql1 ; destruct lw' ; inversion H0.
    * now symmetry in p ; apply Permutation_Type_nil in p ; subst.
    * now symmetry in p ; apply Permutation_Type_nil in p ; subst.
    * destruct l1 ; inversion H1.
  + destruct L; inversion i; inversion Heql1.
- eapply plus_rev in pi1 ; [ | intros a; destruct a | reflexivity ].
  destruct pi1 as [ pi1 | pi1 ].
  + cons2app in HP2.
    assert (Heq2 := HP2).
    symmetry in Heq2 ; apply Permutation_Type_vs_elt_inv in Heq2.
    destruct Heq2 as ((l' & l'') & Heq2) ; subst.
    eapply with_rev1_noax in pi2 ; [ | intros a; destruct a ].
    eapply IHA1.
    * eassumption.
    * apply Permutation_Type_app_inv in HP2 ; cbn in HP2.
      apply Permutation_Type_swap.
    * eapply ex_r ; [ apply pi2 | ].
      list_simpl in HP2; cons2app in HP2; apply Permutation_Type_app_inv in HP2.
      list_simpl; etransitivity; [ symmetry; apply Permutation_Type_middle | ].
      symmetry; apply Permutation_Type_cons, HP2; reflexivity.
  + cons2app in HP2.
    assert (Heq2 := HP2).
    symmetry in Heq2 ; apply Permutation_Type_vs_elt_inv in Heq2.
    destruct Heq2 as ((l' & l'') & Heq2) ; subst.
    eapply with_rev2_noax in pi2 ; [ | intros a; destruct a ].
    eapply IHA2.
    * eassumption.
    * apply Permutation_Type_app_inv in HP2 ; cbn in HP2.
      apply Permutation_Type_swap.
    * eapply ex_r ; [ apply pi2 | ].
      list_simpl in HP2; cons2app in HP2; apply Permutation_Type_app_inv in HP2.
      list_simpl; etransitivity; [ symmetry; apply Permutation_Type_middle | ].
      symmetry; apply Permutation_Type_cons, HP2; reflexivity.
- revert HP2 ; clear - pi2 ; induction pi2 ; intros HP2 ;
    try (now (apply Permutation_Type_length in HP2 ; inversion HP2)) ;
    try (now (apply Permutation_Type_length_2_inv in HP2 ; inversion HP2)).
  + apply IHpi2.
    cbn in p ; Permutation_Type_solve.
  + apply IHpi2.
    apply (Permutation_Type_map wn) in p ; Permutation_Type_solve.
  + destruct L; inversion i.
    apply Permutation_Type_sym in HP2.
    apply Permutation_Type_nil_cons in HP2; assumption.
  + apply Permutation_Type_length_2_inv in HP2.
    destruct HP2 ; inversion e.
    destruct l ; inversion H1.
- assert (pi0 := pi1).
  rewrite <- (app_nil_l _) in pi1; eapply with_rev1_noax in pi1; [ | intros a; destruct a ].
  rewrite <- (app_nil_l _) in pi0; eapply with_rev2_noax in pi0; [ | intros a; destruct a ].
  assert (ll_mix0 (oc F :: ill2ll A1 :: nil)
        + ll_mix0 (oc F :: ill2ll A2 :: nil))
    as [ pi2' | pi2' ].
  { revert HP2 ; clear - pi2 ; induction pi2 ; intros HP2 ;
      try (now (apply Permutation_Type_length in HP2 ; inversion HP2)) ;
      try (now (apply Permutation_Type_length_2_inv in HP2 ; inversion HP2)).
    - apply IHpi2.
      cbn in p ; Permutation_Type_solve.
    - apply IHpi2.
      apply (Permutation_Type_map wn) in p ; Permutation_Type_solve.
    - destruct L; inversion i.
      apply Permutation_Type_sym in HP2.
      apply Permutation_Type_nil_cons in HP2.
      inversion HP2.
    - apply Permutation_Type_length_2_inv in HP2.
      destruct HP2 ; inversion e ; subst.
      left.
      eapply ex_r ; [ apply pi2 | GPermutation_Type_solve ].
    - apply Permutation_Type_length_2_inv in HP2.
      destruct HP2 ; inversion e ; subst.
      right.
      eapply ex_r ; [ apply pi2 | GPermutation_Type_solve ].
    - apply Permutation_Type_length_2_inv in HP2.
      destruct HP2 ; inversion e.
      destruct l ; inversion H1. }
  + eapply IHA1; try eassumption; reflexivity.
  + eapply IHA2; try eassumption; reflexivity.
- revert HP2 ; clear - pi2 ; induction pi2 ; intros HP2 ;
    try (now (apply Permutation_Type_length in HP2 ; inversion HP2)) ;
    try (now (apply Permutation_Type_length_2_inv in HP2 ; inversion HP2)).
  + apply IHpi2.
    cbn in p; Permutation_Type_solve.
  + apply IHpi2.
    apply (Permutation_Type_map wn) in p; Permutation_Type_solve.
  + destruct L; inversion i.
    apply Permutation_Type_sym in HP2.
    apply Permutation_Type_nil_cons in HP2; assumption.
  + apply Permutation_Type_length_2_inv in HP2.
    destruct HP2; inversion e; destruct l; inversion H1.
Qed.

Lemma bot_not_idefin A :
  ll_mix0 (dual (ill2ll A) :: nil) -> ll_mix0 (one :: ill2ll A :: nil) -> False.
Proof.
intros pi1 pi2.
eapply cut_mix0_r in pi2.
- list_simpl in pi2.
  eapply ex_r in pi2; [ | apply Permutation_Type_swap ].
  eapply wn_not_idefin; eassumption.
- apply bot_r.
  change nil with (map (@wn atom) nil).
  apply oc_r, one_r.
Qed.

Lemma wn_one_not_idefin A :
  ll_mix0 (wn one :: dual (ill2ll A) :: nil) -> ll_mix0 (oc bot :: ill2ll A :: nil) -> False.
Proof.
intros pi1 pi2.
eapply cut_mix0_r in pi1.
- list_simpl in pi1.
  eapply wn_not_idefin; eassumption.
- change nil with (map (@wn atom) nil).
  apply oc_r, bot_r.
  change (map wn nil) with (concat (@nil (list formula))).
  apply mix_r; constructor.
Qed.

Lemma oc_bot_not_idefin A :
  ll_ll (oc bot :: dual (ill2ll A) :: nil) -> ll_mix0 (wn one :: ill2ll A :: nil) -> False.
Proof.
enough (forall l, ll_ll (map dual (map ill2ll l)) ->
          (Forall_inf (fun F => ll_mix0 (ill2ll F :: nil)) l) -> False)
  as Hgen.
{ intros pi1 pi2.
  eapply cut_ll_r in pi1.
  eapply cut_mix0_r in pi2.
  - change (dual (ill2ll A) :: nil)
      with (map dual (map ill2ll (A :: nil))) in pi1.
    rewrite app_nil_r in pi1.
    list_simpl in pi2.
    eapply Hgen; [ eassumption | ].
    constructor; [ eassumption | constructor ].
  - change nil with (map (@wn atom) nil).
    apply oc_r, bot_r.
    change (map wn nil) with (concat (@nil (list formula))).
    apply mix_r; constructor.
  - apply de_r, one_r. }
intros l pi.
remember (map dual (map ill2ll l)) as l0.
revert l Heql0; induction pi; intros l' Heq HF; subst; try (now inversion f).
- destruct l'; inversion Heq.
  destruct l'; inversion Heq.
  destruct i0; inversion H3.
- apply PCPermutation_Type_map_inv in p as [ l1' -> HP ].
  symmetry in HP.
  apply PCPermutation_Type_map_inv in HP as [ l1'' -> HP ].
  eapply IHpi; [ reflexivity | ].
  eapply Permutation_Type_Forall_inf; [ apply HP | eassumption ].
- symmetry in Heq; decomp_map Heq; subst.
  symmetry in Heq; decomp_map Heq; subst.
  symmetry in Heq3.
  destruct (ill2ll_map_ioc_inv _ _ Heq3) as [l' -> ->].
  rewrite map_map in p.
  apply Permutation_Type_map_inv in p as [l'' -> p].
  rewrite <- (map_map _ _ l''), <- ill2ll_map_ioc, <- ? map_app in IHpi.
  eapply IHpi; [ reflexivity | ].
  assert (HF1 := Forall_inf_app_l _ _ HF).
  assert (HF2 := Forall_inf_app_r _ _ HF).
  assert (HF3 := Forall_inf_app_l _ _ HF2).
  assert (HF4 := Forall_inf_app_r _ _ HF2).
  apply Forall_inf_app; [ assumption | ].
  apply Forall_inf_app; [ | assumption ].
  apply (Permutation_Type_map ioc) in p.
  eapply Permutation_Type_Forall_inf; eassumption.
- destruct l'; inversion Heq.
  destruct i; inversion H0.
- destruct l'; inversion Heq; subst.
  inversion HF.
  eapply IHpi; [ reflexivity | eassumption ].
- destruct l'; inversion Heq.
  symmetry in H1; decomp_map H1; symmetry in H1; decomp_map H1; subst.
  destruct i; inversion H0; subst.
  + inversion HF; subst.
    cbn in X; rewrite <- (app_nil_l _) in X; eapply parr_rev in X; [ | intros a; destruct a ].
    list_simpl in X.
    assert (X1 := Forall_inf_app_l _ _ X0).
    assert (X2 := Forall_inf_app_r _ _ X0).
    rewrite bidual in pi1.
    assert (ll_mix0 (ill2ll i1 :: nil)) as pi0.
    { eapply (stronger_pfrag _ pfrag_mix0) in pi1 ;
        [ | repeat split; try reflexivity; intros a; destruct a ].
      revert pi1 X2; clear; induction l5; intros pi HF.
      - assumption.
      - inversion HF; subst.
        cbn in pi; eapply ex_r in pi; [ | apply Permutation_Type_swap ].
        apply (cut_mix0_r pi) in X.
        eapply IHl5; eassumption. }
    eapply ex_r in X; [ | apply Permutation_Type_swap ].
    apply (cut_mix0_r X) in pi0.
    apply (IHpi2 (i2 :: l4)); constructor; assumption.
  + inversion HF; subst.
    cbn in X; rewrite <- (app_nil_l _) in X; eapply parr_rev in X; [ | intros a; destruct a ].
    list_simpl in X.
    assert (X1 := Forall_inf_app_l _ _ X0).
    assert (X2 := Forall_inf_app_r _ _ X0).
    rewrite bidual in pi1.
    assert (ll_mix0 (ill2ll i :: nil)) as pi0.
    { eapply (stronger_pfrag _ pfrag_mix0) in pi1;
        [ | repeat split; try reflexivity; intros a; destruct a ].
      revert pi1 X2; clear; induction l5; intros pi HF.
      - assumption.
      - inversion HF; subst.
        cbn in pi; eapply ex_r in pi; [ | apply Permutation_Type_swap ].
        apply (cut_mix0_r pi) in X.
        eapply IHl5; assumption. }
    eapply ex_r in X; [ | apply Permutation_Type_swap ].
    apply (cut_mix0_r X) in pi0.
    apply (IHpi2 (ivar atN  :: l4)); constructor; assumption.
  + inversion HF; subst.
    cbn in X; rewrite <- (app_nil_l _) in X; eapply parr_rev in X; [ | intros a; destruct a ].
    list_simpl in X.
    assert (X1 := Forall_inf_app_l _ _ X0).
    assert (X2 := Forall_inf_app_r _ _ X0).
    rewrite bidual in pi2.
    assert (ll_mix0 (ill2ll i1 :: nil)) as pi0.
    { eapply (stronger_pfrag _ pfrag_mix0) in pi2;
        [ | repeat split; try reflexivity; intros a; destruct a ].
      revert pi2 X1; clear; induction l4; intros pi HF.
      - assumption.
      - inversion HF; subst.
        cbn in pi; eapply ex_r in pi; [ | apply Permutation_Type_swap ].
        apply (cut_mix0_r pi) in X.
        eapply IHl4; eassumption. }
    apply (cut_mix0_r X) in pi0.
    apply (IHpi1 (i2 :: l5)); constructor; assumption.
  + inversion HF; subst.
    cbn in X; rewrite <- (app_nil_l _) in X; eapply parr_rev in X; [ | intros a; destruct a ].
    list_simpl in X.
    assert (X1 := Forall_inf_app_l _ _ X0).
    assert (X2 := Forall_inf_app_r _ _ X0).
    rewrite bidual in pi2.
    assert (ll_mix0 (ill2ll i :: nil)) as pi0.
    { eapply (stronger_pfrag _ pfrag_mix0) in pi2;
        [ | repeat split; try reflexivity; intros a; destruct a ].
      revert pi2 X1; clear; induction l4; intros pi HF.
      - assumption.
      - inversion HF; subst.
        cbn in pi; eapply ex_r in pi; [ | apply Permutation_Type_swap ].
        apply (cut_mix0_r pi) in X.
        eapply IHl4; eassumption. }
    apply (cut_mix0_r X) in pi0.
    apply (IHpi1 (ivar atN :: l5)); constructor; assumption.
- destruct l'; inversion Heq.
  destruct i; inversion H0; subst.
  inversion HF; subst.
  cbn in X.
  eapply tens_rev in X; [ | intros a; destruct a | reflexivity ].
  destruct X as [pi1 pi2].
  apply (IHpi (i2 :: i1 :: l')); constructor; [ assumption | ].
  constructor; assumption.
- destruct l'; inversion Heq.
  destruct i; inversion H0; subst.
  inversion HF; subst.
  clear - X.
  assert ({ l & Permutation_Type (ill2ll izero :: nil) l }) as [l HP]
    by (eexists; reflexivity).
  eapply ex_r in X; [ | apply HP ].
  revert HP; clear - X; induction X; intros HP;
    try (now apply Permutation_Type_length in HP; inversion HP);
    try (now apply Permutation_Type_length_1_inv in HP; inversion HP).
  + apply IHX.
    cbn in p; Permutation_Type_solve.
  + apply IHX.
    apply (Permutation_Type_map wn) in p; Permutation_Type_solve.
  + destruct L; inversion i.
    apply Permutation_Type_sym in HP.
    apply Permutation_Type_nil_cons in HP; assumption.
- destruct l'; inversion Heq.
  destruct i; inversion H0; subst.
  inversion HF; subst.
  cbn in X; rewrite <- (app_nil_l (awith _ _ :: _)) in X.
  eapply with_rev1_noax in X; [ | intros a; destruct a ].
  apply (IHpi (i1 :: l')); constructor; assumption.
- destruct l'; inversion Heq.
  destruct i; inversion H0; subst.
  inversion HF; subst.
  cbn in X; rewrite <- (app_nil_l (awith _ _ :: _)) in X.
  eapply with_rev2_noax in X; [ | intros a; destruct a ].
  apply (IHpi (i2 :: l')); constructor; assumption.
- destruct l'; inversion Heq.
  destruct i; inversion H0; subst.
  inversion HF; subst.
  cbn in X; eapply plus_rev in X; [ | intros a; destruct a | reflexivity ].
  destruct X as [pi | pi].
  + apply (IHpi1 (i1 :: l')); constructor; assumption.
  + apply (IHpi2 (i2 :: l')); constructor; assumption.
- destruct l'; inversion Heq.
  destruct i; inversion H0.
- destruct l'; inversion Heq.
  destruct i; inversion H0; subst.
  inversion HF; subst.
  cbn in X; rewrite <- (app_nil_l (oc _ :: _)) in X.
  eapply oc_rev_noax in X; [ | intros a; destruct a ].
  apply (IHpi (i :: l')); constructor; assumption.
- destruct l'; inversion Heq.
  destruct i; inversion H0; subst.
  inversion HF; subst.
  cbn in X; rewrite <- (app_nil_l (oc _ :: _)) in X.
  eapply oc_rev_noax in X; [ | intros a; destruct a ].
  apply (IHpi l'); [ reflexivity | assumption ].
- destruct l'; inversion Heq.
  destruct i; inversion H0; subst.
  apply (IHpi (ioc i :: ioc i :: l')); [ reflexivity | ].
  inversion HF; constructor; assumption.
- destruct a.
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

Lemma zeropos_ilr P D : zeropos D -> forall l1 l2 C, ill P (l1 ++ D :: l2) C.
Proof.
intros Hzp; induction Hzp; intros l1 l2 C; try now constructor.
apply tens_ilr.
cons2app; rewrite app_assoc; apply IHHzp.
Qed.

Lemma ill2ll_zeropos C D : zeropos C -> ill2ll C = ill2ll D -> zeropos D.
Proof.
intros Hz; revert D; induction Hz; intros D Heq; destruct D; inversion Heq;
  try apply IHHz in H0; try apply IHHz in H1; try now constructor.
constructor.
- apply IHHz1 in H0; assumption.
- apply IHHz2 in H1; assumption.
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
  (forall D, ill2ll (snd (projT2 (ipgax P) a)) = dual (ill2ll D) ->
     {'(Z, Zl1, Zl2) & zeropos Z
                     & D :: (fst (projT2 (ipgax P) a)) = Zl1 ++ Z :: Zl2 })
* (forall l C,
     PCPermutation_Type (ipperm P) (ill2ll (snd (projT2 (ipgax P) a))
                            :: rev (map dual (map ill2ll (fst (projT2 (ipgax P) a)))))
                       (ill2ll C :: rev (map dual (map ill2ll l)))
       -> ill P l C)
(*     -> { b | fst (projT2 (ipgax P) b) = l & snd (projT2 (ipgax P) b) = C })    *)
* notT (In_inf N (fst (projT2 (ipgax P) a))).

Lemma dual_jfragment_zeropos {P} : ipcut P = false -> easyipgax_nzeropos P -> forall l0,
  Forall_inf nonzerospos l0 -> ll (i2pfrag P) (map dual (map ill2ll l0)) ->
  {'(C, Cl1, Cl2) & zeropos C & l0 = Cl1 ++ C :: Cl2 }.
Proof.
intros Hcut Hgax.
intros l0 Hnzsp Hll.
remember (map dual (map ill2ll l0)) as l.
revert l0 Hnzsp Heql.
induction Hll ; intros l0 Hnzsp HP.
- exfalso.
  destruct l0 ; inversion HP.
  destruct l0 ; inversion HP.
  destruct i0 ; inversion H3.
- subst.
  rewrite map_map in p.
  apply PCPermutation_Type_map_inv in p.
  destruct p as [l' Heq HP] ; subst.
  apply PCPermutation_Permutation_Type in HP.
  apply (Permutation_Type_Forall_inf HP) in Hnzsp.
  apply IHHll in Hnzsp ; [ | rewrite <- map_map; reflexivity ].
  destruct Hnzsp as [[[C l1] l2] Hz Heq] ; unfold id in Heq ; subst.
  unfold id in HP ; apply Permutation_Type_vs_elt_inv in HP.
  destruct HP as ((l' & l'') & HP) ; subst.
  exists (C, l', l''); [ assumption | reflexivity ].
- symmetry in HP; decomp_map_inf HP; subst; cbn in HP, HP3.
  symmetry in HP; decomp_map_inf HP; subst; cbn in HP3.
  symmetry in HP3.
  apply ill2ll_map_ioc_inv in HP3 ; destruct HP3 as [lw'' ? HP3] ; subst.
  rewrite map_map in p.
  apply Permutation_Type_map_inv in p ; destruct p as [lw''' ? p] ; subst.
  assert (Forall_inf nonzerospos (l1 ++ map ioc lw''' ++ l8)) as HF.
  { assert (HF1 := Forall_inf_app_l _ _ Hnzsp).
    assert (HF2 := Forall_inf_app_r _ _ Hnzsp).
    assert (HF3 := Forall_inf_app_l _ _ HF2).
    assert (HF4 := Forall_inf_app_r _ _ HF2).
    apply Forall_inf_app; [ assumption | ].
    apply Forall_inf_app; [ | assumption ].
    apply (Permutation_Type_map ioc) in p.
    eapply Permutation_Type_Forall_inf; [ apply p | assumption ]. }
  apply IHHll in HF ;
    [ | list_simpl ; rewrite ill2ll_map_ioc ; rewrite <- (map_map _ _ lw'''); reflexivity ].
  destruct HF as [[[C l1'] l2'] Hz Heq] ; cbn in Heq.
  dichot_elt_app_inf_exec Heq ; subst ; cbn.
  + exists (C, l1', l ++ map ioc lw'' ++ l8) ; list_simpl; [ assumption | reflexivity ].
  + dichot_elt_app_inf_exec Heq1 ; subst ; cbn.
    * apply (Permutation_Type_map ioc) in p.
      rewrite <- Heq0 in p.
      apply Permutation_Type_vs_elt_inv in p ; destruct p as [(llw1, llw2) Heq].
      rewrite Heq ; list_simpl.
      rewrite app_assoc; exists (C, l1 ++ llw1, llw2 ++ l8); [ assumption | reflexivity ].
    * rewrite 2 app_assoc.
      exists (C, (l1 ++ map ioc lw'') ++ l3, l2'); [ assumption | reflexivity ].
- inversion i.
- destruct l0 ; inversion HP.
  destruct i ; inversion H0.
- rewrite map_map in HP.
  symmetry in HP; decomp_map_inf HP ; subst.
  rewrite <- map_map in IHHll.
  inversion_clear Hnzsp as [ | ? ? ? HF].
  apply IHHll in HF; [ | reflexivity ].
  destruct HF as [[[C l1'] l2'] Hzp ->].
  exists (C, x :: l1', l2'); [ assumption | reflexivity ].
- rewrite map_map in HP.
  symmetry in HP; decomp_map_inf HP ; subst.
  destruct x ; inversion HP1 ; subst.
  + rewrite <- map_map in IHHll2.
    assert (Forall_inf nonzerospos (x2 :: l4)) as Hnzsp'.
    { inversion_clear Hnzsp as [ | ? ? Hnzsp' HF].
      apply Forall_inf_app_l in HF.
      inversion Hnzsp'.
      constructor; assumption. }
    apply IHHll2 in Hnzsp'; [ | reflexivity ].
    destruct Hnzsp' as [[[C l1'] l2'] Hzp Heq2] ; subst.
    destruct l1' ; inversion Heq2 ; subst.
    * exfalso.
      inversion_clear Hnzsp as [ | ? ? Hnzsp' ].
      inversion Hnzsp'.
      apply H0; assumption.
    * exists (C, ilpam x1 i :: l1', l2' ++ l5); [ assumption | list_simpl; reflexivity ].
  + assert (Forall_inf nonzerospos (N :: l4)) as Hnzsp'.
    { inversion_clear Hnzsp as [ | ? ? Hnzsp' HF ].
      apply Forall_inf_app_l in HF.
      inversion Hnzsp'.
      constructor; [ constructor | assumption ]. }
    rewrite <- map_map in IHHll2.
    apply IHHll2 in Hnzsp'; [ | reflexivity ].
    destruct Hnzsp' as [[[C l1'] l2'] Hzp Heq2] ; subst.
    destruct l1' ; inversion Heq2 ; subst.
    * exfalso.
      inversion Hzp.
    * exists (C, igen x :: l1', l2' ++ l5); [ assumption | list_simpl; reflexivity ].
  + assert (Forall_inf nonzerospos (x2 :: l5)) as Hnzsp'.
    { inversion_clear Hnzsp as [ | ? ? Hnzsp' HF ].
      apply Forall_inf_app_r in HF.
      inversion Hnzsp'.
      constructor; assumption. }
    rewrite <- map_map in IHHll1.
    apply IHHll1 in Hnzsp'; [ | reflexivity ].
    destruct Hnzsp' as [[[C l1'] l2'] Hzp Heq2] ; subst.
    destruct l1' ; inversion Heq2 ; subst.
    * exfalso.
      inversion_clear Hnzsp as [ | ? ? Hnzsp' ].
      inversion Hnzsp'.
      apply H0; assumption.
    * exists (C, ilmap x1 i :: l4 ++ l1', l2'); [ assumption | list_simpl; reflexivity ].
  + assert (Forall_inf nonzerospos (N :: l5)) as Hnzsp'.
    { inversion_clear Hnzsp as [ | ? ? Hnzsp' HF ].
      apply Forall_inf_app_r in HF.
      inversion Hnzsp'.
      constructor; [ constructor | assumption ]. }
    rewrite <- map_map in IHHll1.
    apply IHHll1 in Hnzsp'; [ | reflexivity ].
    destruct Hnzsp' as [[[C l1'] l2'] Hzp Heq2] ; subst.
    destruct l1' ; inversion Heq2 ; subst.
    * exfalso.
      inversion Hzp.
    * exists (C, ineg x :: l4 ++ l1', l2'); [ assumption | list_simpl; reflexivity ].
- rewrite map_map in HP.
  symmetry in HP; decomp_map_inf HP ; subst.
  destruct x ; inversion HP1 ; subst.
  rewrite <- map_map in IHHll.
  assert (Forall_inf nonzerospos (x2 :: x1 :: l2)) as Hnzsp'.
  { inversion_clear Hnzsp as [ | ? ? Hnzsp' ].
    inversion_clear Hnzsp'.
    constructor; [ | constructor ]; assumption. }
  apply IHHll in Hnzsp'; [ | reflexivity ].
  destruct Hnzsp' as [[[C l1'] l2'] Hzp Heq2] ; subst.
  destruct l1' ; inversion Heq2 ; [ | destruct l1' ; inversion Heq2 ] ; subst.
  + exists (itens x1 C, nil, l2); [ | reflexivity ].
    apply zp_itens_r; assumption.
  + exists (itens C i, nil, l2'); [ | reflexivity ].
    apply zp_itens_l; assumption.
  + exists (C, itens i0 i :: l1', l2'); [ assumption | reflexivity ].
- symmetry in HP; decomp_map_inf HP ; symmetry in HP; decomp_map_inf HP ; cbn in HP3 ; subst.
  destruct x0 ; inversion HP1.
  exists (izero, nil, l3); cbn; constructor.
- rewrite map_map in HP.
  symmetry in HP; decomp_map_inf HP ; subst.
  destruct x ; inversion HP1 ; subst.
  rewrite <- map_map in IHHll.
  assert (Forall_inf nonzerospos (x1 :: l2)) as Hnzsp'.
  { inversion_clear Hnzsp as [ | ? ? Hnzsp' ].
    inversion_clear Hnzsp'.
    constructor; assumption. }
  apply IHHll in Hnzsp'; [ | reflexivity ].
  destruct Hnzsp' as [[[C l1'] l2'] Hzp Heq2] ; subst.
  destruct l1' ; inversion Heq2 ; subst.
  + exists (iwith C x2, nil, l2'); [ | reflexivity ].
    apply zp_iwith_l; assumption.
  + exists (C, iwith i x2 :: l1', l2'); [ assumption | reflexivity ].
- rewrite map_map in HP.
  symmetry in HP; decomp_map_inf HP ; subst.
  destruct x ; inversion HP1 ; subst.
  rewrite <- map_map in IHHll.
  assert (Forall_inf nonzerospos (x2 :: l2)) as Hnzsp'.
  { inversion_clear Hnzsp as [ | ? ? Hnzsp' ].
    inversion_clear Hnzsp'.
    constructor; assumption. }
  apply IHHll in Hnzsp'; [ | reflexivity ].
  destruct Hnzsp' as [[[C l1'] l2'] Hzp Heq2] ; subst.
  destruct l1' ; inversion Heq2 ; subst.
  + exists (iwith x1 C, nil, l2'); [ | reflexivity ].
    apply zp_iwith_r; assumption.
  + exists (C, iwith x1 i :: l1', l2'); [ assumption | reflexivity ].
- rewrite map_map in HP.
  symmetry in HP; decomp_map_inf HP ; subst.
  destruct x ; inversion HP1 ; subst.
  rewrite <- map_map in IHHll2.
  assert (Forall_inf nonzerospos (x2 :: l2)) as Hnzsp'.
  { inversion_clear Hnzsp as [ | ? ? Hnzsp' ].
    inversion_clear Hnzsp'.
    constructor; assumption. }
  apply IHHll2 in Hnzsp'; [ | reflexivity ].
  destruct Hnzsp' as [[[C l1'] l2'] Hzp Heq2] ; subst.
  destruct l1' ; inversion Heq2 ; subst.
  + assert (Forall_inf nonzerospos (x1 :: l2')) as Hnzsp''.
    { inversion_clear Hnzsp as [ | ? ? Hnzsp' ].
      inversion_clear Hnzsp'.
      constructor; assumption. }
    rewrite <- map_map in IHHll1.
    apply IHHll1 in Hnzsp''; [ | reflexivity ].
    destruct Hnzsp'' as [[[C' l1''] l2''] Hzp' Heq3] ; subst.
    destruct l1'' ; inversion Heq3 ; subst.
    * exists (iplus C' C, nil, l2''); constructor; assumption.
    * exists (C', iplus i C :: l1'', l2''); [ assumption | reflexivity ].
  + exists (C, iplus x1 i :: l1', l2'); [ assumption | reflexivity ].
- exfalso.
  destruct l0 ; inversion HP.
  destruct i ; inversion H0.
- rewrite map_map in HP.
  symmetry in HP; decomp_map_inf HP ; subst.
  destruct x ; inversion HP1 ; subst.
  rewrite <- map_map in IHHll.
  assert (Forall_inf nonzerospos (x :: l2)) as Hnzsp'.
  { inversion_clear Hnzsp as [ | ? ? Hnzsp' ].
    inversion_clear Hnzsp'.
    constructor; assumption. }
  apply IHHll in Hnzsp'; [ | reflexivity ].
  destruct Hnzsp' as [[[C l1'] l2'] Hzp Heq2] ; subst.
  destruct l1' ; inversion Heq2 ; subst.
  + exists (ioc C, nil, l2'); constructor; assumption.
  + exists (C, ioc i :: l1', l2'); [ assumption | reflexivity ].
- rewrite map_map in HP.
  symmetry in HP; decomp_map_inf HP ; subst.
  rewrite <- map_map in IHHll.
  inversion Hnzsp as [ | ? ? ? HF ].
  apply IHHll in HF; [ | reflexivity ].
  destruct HF as [[[C l1'] l2'] Hzp Heq2] ; subst.
  exists (C, x :: l1', l2'); [ assumption | reflexivity ].
- rewrite map_map in HP.
  symmetry in HP; decomp_map_inf HP ; subst.
  destruct x ; inversion HP1 ; subst.
  assert (Forall_inf nonzerospos (ioc x :: ioc x :: l2)) as Hnzsp'.
  { inversion Hnzsp ; subst ; constructor; assumption. }
  rewrite <- (map_map _ _ l2) in IHHll.
  apply IHHll in Hnzsp'; [ | reflexivity ].
  destruct Hnzsp' as [[[C l1'] l2'] Hzp Heq2] ; subst.
  destruct l1' ; inversion Heq2 ; subst.
  + exists (ioc x, nil, l2); [ assumption | reflexivity ].
  + destruct l1' ; inversion H1 ; subst.
    * exists (ioc x, nil, l2'); [ assumption | reflexivity ].
    * exists (C, ioc x :: l1', l2'); [ assumption | reflexivity ].
- cbn in f.
  rewrite f in Hcut.
  inversion Hcut.
- unfold i2pfrag in HP ; cbn in HP.
  destruct l0 ; inversion HP.
  apply (fst (Hgax a)) in H0.
  destruct H0 as [[[Z lz1] lz2] Hz Heq].
  destruct lz1 ; inversion Heq ; subst.
  + exists (Z, nil, l0); [ assumption | reflexivity ].
  + list_simpl in H1.
    rewrite H2 in H1 ; list_simpl in H1.
    symmetry in H1; decomp_map_inf H1.
    apply dual_inj in H1 ; subst.
    cbn in H4 ; symmetry in H4; decomp_map_inf H4 ; subst.
    symmetry in H4.
    apply ill2ll_zeropos in H4; [ | assumption ].
    rewrite app_comm_cons; exists (x, i0 :: l4, l6); [ assumption | reflexivity ].
Qed.

(** Cut-free conservativity *)
Theorem ll_to_ill_nzeropos_cutfree P : ipcut P = false -> easyipgax_nzeropos P ->
  forall l, ll (i2pfrag P) l -> forall l0 C, Forall_inf nonzerospos (C :: l0) ->
    PCPermutation_Type (pperm (i2pfrag P))
                l (ill2ll C :: rev (map dual (map ill2ll l0))) ->
      ill P l0 C.
Proof.
intros Hcut Hgax.
intros l Hll; induction Hll; intros l0 C Hnzsp HP.
- apply PCPermutation_Type_length_2_inv in HP.
  destruct HP as [HP | HP] ; inversion HP ; destruct C ; inversion H0.
  destruct l0 using rev_rect ; inversion H1.
  list_simpl in H3 ; inversion H3.
  destruct l0 using rev_rect ; list_simpl in H5 ; inversion H5.
  destruct x ; inversion H4.
  rewrite <- H2 in H6.
  apply i2a_inj in H6 ; subst.
  apply ax_ir.
- apply IHHll; [ | etransitivity ]; eassumption.
- apply PCPermutation_Type_vs_cons_inv in HP ; destruct HP as [[l1' l2'] HP Heq].
  cbn in HP, Heq ; dichot_elt_app_inf_exec Heq ; subst.
  + apply PEPermutation_Type_rev in HP ; rewrite rev_involutive in HP ; list_simpl in HP.
    rewrite map_map in HP.
    symmetry in HP ; apply PEPermutation_Type_map_inv in HP ; destruct HP as [l' Heq HP].
    symmetry in Heq; decomp_map_inf Heq ; subst.
    cbn in Heq2 ; rewrite <- (map_map _ _ l7) in Heq2.
    symmetry in Heq2.
    apply ill2ll_map_ioc_inv in Heq2 ; destruct Heq2 as [l' Heq2 Heq] ; subst.
    symmetry in HP ; eapply ex_ir ; [ | apply HP ] ; cbn.
    rewrite app_assoc.
    apply Permutation_Type_rev' in p ; rewrite Heq in p.
    rewrite map_map in p.
    apply Permutation_Type_map_inv in p ; destruct p as [lw'' Heq' p].
    symmetry in p ; eapply ex_oc_ir; [ | eassumption ].
    apply IHHll.
    * inversion_clear Hnzsp as [ | ? ? ? HF ].
      cbn in HP ; symmetry in HP.
      apply (PEPermutation_Type_Forall_inf _ _ HP) in HF.
      assert (HF1:= Forall_inf_app_l _ _ HF).
      assert (HF2:= Forall_inf_app_r _ _ HF).
      assert (HF3:= Forall_inf_app_l _ _ HF2).
      assert (HF4:= Forall_inf_app_r _ _ HF2).
      assert (HF5:= Forall_inf_app_l _ _ HF4).
      assert (HF6:= Forall_inf_app_r _ _ HF4).
      constructor; [ assumption | ].
      apply Forall_inf_app ; apply Forall_inf_app; try assumption.
      symmetry in p ; apply (Permutation_Type_map ioc) in p.
      eapply Permutation_Type_Forall_inf; eassumption.
    * list_simpl; cbn in HP.
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
      GPermutation_Type_solve.
  + dichot_elt_app_inf_exec Heq1 ; subst ;
      [ exfalso; symmetry in Heq0; decomp_map Heq0; destruct C; inversion Heq0 | ].
    apply PEPermutation_Type_rev in HP ; rewrite rev_involutive in HP ; list_simpl in HP.
    rewrite map_map in HP.
    symmetry in HP ; apply PEPermutation_Type_map_inv in HP ; destruct HP as [l' Heq HP].
    symmetry in Heq; decomp_map_inf Heq ; subst.
    cbn in Heq3 ; rewrite <- (map_map _ _ l5) in Heq3.
    symmetry in Heq3.
    apply ill2ll_map_ioc_inv in Heq3 ; destruct Heq3 as [l' Heq3 Heq] ; subst.
    symmetry in HP ; eapply ex_ir ; [ | apply HP ] ; cbn.
    rewrite app_assoc.
    apply Permutation_Type_rev' in p ; rewrite Heq in p.
    rewrite map_map in p.
    apply Permutation_Type_map_inv in p ; destruct p as [lw'' Heq' p].
    list_simpl ; symmetry in p ; eapply ex_oc_ir; [ | eassumption ].
    apply IHHll.
    * inversion_clear Hnzsp as [ | ? ? ? HF ].
      cbn in HP ; symmetry in HP.
      apply (PEPermutation_Type_Forall_inf _ _ HP) in HF.
      assert (HF1:= Forall_inf_app_l _ _ HF).
      assert (HF2:= Forall_inf_app_r _ _ HF).
      assert (HF3:= Forall_inf_app_l _ _ HF2).
      assert (HF4:= Forall_inf_app_r _ _ HF2).
      assert (HF5:= Forall_inf_app_l _ _ HF4).
      assert (HF6:= Forall_inf_app_r _ _ HF4).
      constructor; [ assumption | ].
      rewrite app_assoc ; apply Forall_inf_app ; apply Forall_inf_app; try assumption.
      symmetry in p ; apply (Permutation_Type_map ioc) in p.
      eapply Permutation_Type_Forall_inf; eassumption.
    * list_simpl. cbn in HP.
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
      GPermutation_Type_solve.
- inversion i.
- apply PCPermutation_Type_length_1_inv in HP.
  inversion HP.
  destruct C ; inversion H0.
  destruct l0 using rev_rect ; list_simpl in H1 ; inversion H1.
  apply one_irr.
- list_simpl in HP.
  symmetry in HP.
  apply PCPermutation_Type_vs_cons_inv in HP as [(l', l'') HP Heq].
  destruct l'; inversion Heq.
  + destruct C ; inversion H0.
  + decomp_map_inf H1; symmetry in H4; decomp_map_inf H4; subst.
    apply (f_equal (@rev _)) in H7.
    rewrite rev_involutive in H7; subst.
    destruct x0 ; inversion H1.
    list_simpl.
    apply one_ilr.
    apply IHHll.
    * inversion Hnzsp as [ | ? ? ? HF ].
      constructor; [ assumption | ].
      list_simpl in HF.
      assert (H3l := Forall_inf_app_l _ _ HF).
      assert (H3r := Forall_inf_app_r _ _ HF).
      inversion H3r.
      apply Forall_inf_app; assumption.
    * list_simpl.
      apply PEPermutation_PCPermutation_Type in HP ; unfold id in HP ; cbn in HP.
      GPermutation_Type_solve.
- list_simpl in HP.
  symmetry in HP.
  apply PCPermutation_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') HP Heq].
  destruct l' ; inversion Heq.
  + destruct C ; inversion H0 ; subst.
    list_simpl in HP.
    rewrite map_map in HP.
    apply PEPermutation_Type_map_inv in HP.
    destruct HP as [l3 Heq' HP].
    rewrite <- map_map in Heq'; symmetry in Heq'.
    decomp_map_inf Heq'; symmetry in Heq'; decomp_map_inf Heq'; cbn in Heq'3, Heq'4; subst.
    inversion_clear Hnzsp as [ | ? ? Hnzsp' HF ].
    inversion_clear Hnzsp'.
    apply Forall_inf_rev in HF.
    apply (PEPermutation_Type_Forall_inf _ _ HP) in HF; cbn in HF.
    assert (H3l := Forall_inf_app_l _ _ HF).
    assert (H3r := Forall_inf_app_r _ _ HF).
    apply PEPermutation_Type_rev in HP ; list_simpl in HP ; symmetry in HP.
    eapply ex_ir ; [ | exact HP ].
    apply tens_irr.
    * apply IHHll1.
      -- constructor; [ | apply Forall_inf_rev ]; assumption.
      -- list_simpl; reflexivity.
    * apply IHHll2.
      -- constructor; [ | apply Forall_inf_rev ]; assumption.
      -- list_simpl; reflexivity.
  + decomp_map_inf H1; symmetry in H4; decomp_map_inf H4; cbn in H4, H6, H8; subst.
    inversion_clear Hnzsp as [ | ? ? ? HF ].
    apply Forall_inf_rev in HF.
    rewrite <- H7 in HF.
    assert (H3l := Forall_inf_app_l _ _ HF).
    assert (H3r := Forall_inf_app_r _ _ HF).
    inversion H3r as [ | ? ? Hnzsp' HF']; subst.
    apply (Forall_inf_app HF') in H3l.
    assert ({'(ll, lr) & 
       PEPermutation_Type (ipperm P) (l8 ++ l6) (ll ++ lr) &
       l2 ++ l1 = map dual (map ill2ll ll)
                         ++ ill2ll C :: map dual (map ill2ll lr) /\
       (ipperm P = false -> l8 = ll /\ l6 = lr) }) as [(ll & lr) HP0 (Heq' & HPeq)].
    { clear - HP.
      case_eq (ipperm P) ; intros Hperm ; rewrite_all Hperm.
      - apply PEPermutation_Type_vs_elt_inv in HP.
        destruct HP as [(ll & lr) HP0 Heq] ; cbn in HP0.
        rewrite <- 2 map_app in HP0.
        rewrite map_map in HP0.
        symmetry in HP0.
        apply Permutation_Type_map_inv in HP0.
        destruct HP0 as [l3 Heq1 HP].
        rewrite <- map_map in Heq1.
        symmetry in Heq1; decomp_map_inf Heq1 ; symmetry in Heq1; decomp_map_inf Heq1 ;
          cbn in Heq4 ; cbn in Heq5 ; subst.
        exists (l5, l7); [ | split ]; try assumption.
        intros H; inversion H.
      - cbn in HP.
        exists (l8, l6) ; cbn ; [ | split; intros; try split ]; try reflexivity.
        assumption. }
    dichot_elt_app_inf_exec Heq' ; subst.
    * decomp_map_inf Heq'1 ; symmetry in Heq'1; decomp_map_inf Heq'1 ;
        cbn in Heq'1 ; cbn in Heq'4 ; cbn in Heq'5 ; subst.
      apply (PEPermutation_Type_Forall_inf _ _ HP0) in H3l ; cbn in H3l.
      destruct x0 ; inversion Hnzsp'; inversion H1 ; subst.
      -- cbn in H7.
         apply (f_equal (@rev _)) in H7.
         rewrite rev_involutive in H7 ; subst.
         list_simpl.
         cbn in HP0.
         apply (ex_ir _ (rev ll ++ ilpam x0_1 x0_2 :: rev l10 ++ rev l9)).
         ++ apply lpam_ilr.
            ** apply IHHll1.
               --- constructor; [ assumption | ].
                   apply Forall_inf_app_r in H3l.
                   apply Forall_inf_app_r in H3l.
                   apply Forall_inf_rev; assumption.
               --- rewrite bidual; list_simpl; reflexivity.
            ** apply IHHll2.
               --- constructor; [ assumption | ].
                   assert (H3l' := Forall_inf_app_l _ _ H3l).
                   assert (H3l'' := Forall_inf_app_r _ _ H3l).
                   apply Forall_inf_app_l in H3l''.
                   apply Forall_inf_rev in H3l'.
                   apply Forall_inf_rev in H3l''.
                   apply Forall_inf_app; [ assumption | ].
                   constructor; assumption.
               --- list_simpl.
                   GPermutation_Type_solve.
         ++ case_eq (ipperm P) ; intros Hperm ; rewrite_all Hperm.
            ** clear - HP0.
               apply Permutation_Type_rev' in HP0.
               list_simpl in HP0.
               list_simpl.
               apply Permutation_Type_elt.
               symmetry.
               etransitivity ; [ apply Permutation_Type_app_comm | ].
               Permutation_Type_solve.
            ** destruct (HPeq eq_refl) ; subst.
               list_simpl; reflexivity.
      -- cbn in H7.
         apply (f_equal (@rev _)) in H7.
         rewrite rev_involutive in H7 ; subst.
         list_simpl.
         cbn in HP0.
         apply (ex_ir _ (rev ll ++ igen x0 :: rev l10 ++ rev l9)).
         ++ apply gen_pam_rule.
            ** intros a.
               apply Hgax.
            ** apply IHHll1.
               --- constructor; [ assumption | ].
                   apply Forall_inf_app_r in H3l.
                   apply Forall_inf_app_r in H3l.
                   apply Forall_inf_rev; assumption.
               --- rewrite bidual; list_simpl; reflexivity.
            ** apply IHHll2.
               --- constructor; [ assumption | ].
                   assert (H3l' := Forall_inf_app_l _ _ H3l).
                   assert (H3l'' := Forall_inf_app_r _ _ H3l).
                   apply Forall_inf_app_l in H3l''.
                   apply Forall_inf_rev in H3l'.
                   apply Forall_inf_rev in H3l''.
                   apply Forall_inf_app; [ assumption | constructor ]; try assumption.
                   constructor.
               --- list_simpl.
                   GPermutation_Type_solve.
         ++ case_eq (ipperm P) ; intros Hperm ; rewrite_all Hperm.
            ** clear - HP0.
               apply Permutation_Type_rev' in HP0.
               list_simpl in HP0.
               list_simpl.
               apply Permutation_Type_elt.
               symmetry.
               etransitivity ; [ apply Permutation_Type_app_comm | ].
               Permutation_Type_solve.
            ** destruct (HPeq eq_refl); subst.
               list_simpl; reflexivity.
      -- cbn in Hll1.
         change (dual (ill2ll x0_2) :: map dual (map ill2ll l10))
           with (map dual (map ill2ll (x0_2 :: l10))) in Hll1.
         apply dual_jfragment_zeropos in Hll1; try assumption.
         ++ destruct Hll1 as [[[C1 lz1] lz2] HzC1 Heq1] ; cbn in Heq1.
            destruct lz1 ; inversion Heq1 ; subst.
            ** contradiction HzC1.
            ** apply (f_equal (@rev _)) in H7.
               rewrite rev_involutive in H7 ; subst.
               cbn in HP0 ; rewrite ? app_assoc in HP0.
               apply PEPermutation_Type_vs_elt_inv in HP0 as [(ll1, lr1) _ HP0]; cbn in HP0.
               dichot_elt_app_inf_exec HP0 ; subst ; list_simpl.
               --- apply zeropos_ilr; assumption.
               --- rewrite ? app_comm_cons, ? app_assoc; apply zeropos_ilr; assumption.
         ++ constructor; [ assumption | ].
            apply Forall_inf_app_r in H3l.
            apply Forall_inf_app_r in H3l; assumption.
      -- cbn in Hll1.
         change (covar (i2a atN) :: map dual (map ill2ll l10))
           with (map dual (map ill2ll (N :: l10))) in Hll1.
         apply dual_jfragment_zeropos in Hll1; try assumption.
         ++ destruct Hll1 as [[[C1 lz1] lz2] HzC1 Heq1].
            destruct lz1 ; inversion Heq1 ; subst.
            ** inversion HzC1.
            ** apply (f_equal (@rev _)) in H7.
               rewrite rev_involutive in H7 ; subst.
               cbn in HP0 ; rewrite ? app_assoc in HP0.
               apply PEPermutation_Type_vs_elt_inv in HP0 as [(ll1, lr1) _ Heq0].
               dichot_elt_app_inf_exec Heq0 ; subst ; list_simpl.
               --- apply zeropos_ilr; assumption.
               --- rewrite ? app_comm_cons, ? app_assoc; apply zeropos_ilr; assumption.
         ++ constructor.
            --- constructor.
            --- apply Forall_inf_app_r in H3l.
                apply Forall_inf_app_r in H3l; assumption.
    * decomp_map_inf Heq'0; symmetry in Heq'0; decomp_map_inf Heq'0;
        cbn in Heq'0, Heq'4, Heq'5; subst.
      cbn in HP0, H3l, H3r.
      apply (PEPermutation_Type_Forall_inf _ _ HP0) in H3l.
      destruct x0 ; inversion Hnzsp' ; inversion H1 ; subst.
      -- cbn in Hll2.
         change (dual (ill2ll x0_2) :: map dual (map ill2ll l9))
           with (map dual (map ill2ll (x0_2 :: l9))) in Hll2.
         apply dual_jfragment_zeropos in Hll2; try assumption.
         ++ destruct Hll2 as [[[C1 lz1] lz2] HzC1 Heq1].
            destruct lz1 ; inversion Heq1 ; subst.
            ** contradiction HzC1.
            ** apply (f_equal (@rev _)) in H7.
               rewrite rev_involutive in H7 ; subst.
               list_simpl in HP0.
               apply PEPermutation_Type_vs_elt_inv in HP0 as [(ll1, lr1) _ Heq0].
               dichot_elt_app_inf_exec Heq0; subst; list_simpl.
               --- apply zeropos_ilr; assumption.
               --- rewrite ? app_comm_cons, ? app_assoc; apply zeropos_ilr; assumption.
         ++ constructor; [ assumption | ].
            apply Forall_inf_app_l in H3l.
            apply Forall_inf_app_l in H3l; assumption.
      -- cbn in Hll2.
         change (covar (i2a atN) :: map dual (map ill2ll l9))
           with (map dual (map ill2ll (N :: l9))) in Hll2.
         apply dual_jfragment_zeropos in Hll2; try assumption.
         ++ destruct Hll2 as [[[C1 lz1] lz2] HzC1 Heq1].
            destruct lz1 ; inversion Heq1 ; subst.
            ** inversion HzC1.
            ** apply (f_equal (@rev _)) in H7.
               rewrite rev_involutive in H7 ; subst.
               list_simpl in HP0.
               apply PEPermutation_Type_vs_elt_inv in HP0 as [(ll1 & lr1) _ Heq0].
               dichot_elt_app_inf_exec Heq0; subst; list_simpl.
               --- apply zeropos_ilr; assumption.
               --- rewrite ? app_comm_cons, ? app_assoc; apply zeropos_ilr; assumption.
         ++ constructor ; [ constructor | ].
            apply Forall_inf_app_l in H3l.
            apply Forall_inf_app_l in H3l; assumption.
      -- cbn in H7.
         apply (f_equal (@rev _)) in H7.
         rewrite rev_involutive in H7 ; subst.
         list_simpl.
         cbn in HP0.
         apply (ex_ir _ (rev l10 ++ rev l9 ++ ilmap x0_1 x0_2 :: rev lr)).
         ++ apply lmap_ilr.
            ** apply IHHll2.
               --- constructor; [ assumption | ].
                   apply Forall_inf_app_l in H3l.
                   apply Forall_inf_app_l in H3l.
                   apply Forall_inf_rev; assumption.
               --- rewrite bidual; list_simpl; reflexivity.
            ** apply IHHll1.
               --- constructor; [ assumption | ].
                   assert (H3l' := Forall_inf_app_l _ _ H3l).
                   assert (H3l'' := Forall_inf_app_r _ _ H3l).
                   apply Forall_inf_app_r in H3l'.
                   apply Forall_inf_rev in H3l'.
                   apply Forall_inf_rev in H3l''.
                   apply Forall_inf_app; [ assumption | ].
                   constructor; assumption.
               --- list_simpl.
                   GPermutation_Type_solve.
         ++ case_eq (ipperm P) ; intros Hperm ; rewrite_all Hperm.
            ** clear - HP0.
               apply Permutation_Type_rev' in HP0.
               list_simpl in HP0.
               list_simpl.
               rewrite app_assoc.
               apply Permutation_Type_elt.
               etransitivity ; [ apply Permutation_Type_app_comm | ].
               Permutation_Type_solve.
            ** destruct (HPeq eq_refl); subst.
               list_simpl; reflexivity.
      -- cbn in H7.
         apply (f_equal (@rev _)) in H7.
         rewrite rev_involutive in H7 ; subst.
         list_simpl.
         cbn in HP0.
         apply (ex_ir _ (rev l10 ++ rev l9 ++ ineg x0 :: rev lr)).
         ++ apply neg_map_rule.
            ** intros a.
               apply Hgax.
            ** apply IHHll2.
               --- constructor; [ assumption | ].
                   apply Forall_inf_app_l in H3l.
                   apply Forall_inf_app_l in H3l.
                   apply Forall_inf_rev; assumption.
               --- rewrite bidual; list_simpl; reflexivity.
            ** apply IHHll1.
               --- constructor; [ assumption | ].
                   assert (H3l' := Forall_inf_app_l _ _ H3l).
                   assert (H3l'' := Forall_inf_app_r _ _ H3l).
                   apply Forall_inf_app_r in H3l'.
                   apply Forall_inf_rev in H3l'.
                   apply Forall_inf_rev in H3l''.
                   apply Forall_inf_app; [ assumption | ].
                   constructor; [ constructor | assumption ].
               --- list_simpl.
                   GPermutation_Type_solve.
         ++ case_eq (ipperm P) ; intros Hperm ; rewrite_all Hperm.
            ** clear - HP0.
               apply Permutation_Type_rev' in HP0.
               list_simpl in HP0.
               list_simpl.
               rewrite app_assoc.
               apply Permutation_Type_elt.
               etransitivity ; [ apply Permutation_Type_app_comm | ].
               Permutation_Type_solve.
            ** destruct (HPeq eq_refl); subst.
               list_simpl; reflexivity.
- list_simpl in HP.
  symmetry in HP.
  apply PCPermutation_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') HP Heq].
  destruct l'.
  + inversion Heq as [ Heq0 ]; subst.
    list_simpl in HP.
    rewrite map_map in HP.
    apply PEPermutation_Type_map_inv in HP.
    destruct HP as [l3 Heq' HP].
    rewrite <- map_map in Heq' ; subst.
    inversion_clear Hnzsp as [ | ? ? Hnzsp' HF ].
    apply Forall_inf_rev in HF.
    apply (PEPermutation_Type_Forall_inf _ _ HP) in HF.
    destruct C; inversion Hnzsp'; inversion Heq0 ; subst.
    * apply lpam_irr.
      symmetry in HP.
      apply PEPermutation_Type_rev in HP.
      rewrite rev_involutive in HP.
      apply (ex_ir _ (rev l3 ++ C1 :: nil));
        [ | apply PEPermutation_Type_add_inside; [ assumption | reflexivity ] ].
      apply IHHll.
      -- constructor; [ assumption | ].
         apply Forall_inf_app ; [ | constructor ] ; try constructor; [ | assumption ].
         apply Forall_inf_rev; assumption.
      -- list_simpl; reflexivity.
    * apply gen_irr.
      symmetry in HP.
      apply PEPermutation_Type_rev in HP.
      rewrite rev_involutive in HP.
      apply (ex_ir _ (rev l3 ++ C :: nil));
        [ | apply PEPermutation_Type_app; [ assumption | reflexivity ] ].
      apply IHHll.
      -- constructor ; [ constructor | ].
         apply Forall_inf_app ; [ | constructor ; [ | constructor ] ]; [ | assumption ].
         apply Forall_inf_rev; assumption.
      -- list_simpl; GPermutation_Type_solve.
    * apply lmap_irr.
      symmetry in HP.
      apply PEPermutation_Type_rev in HP.
      rewrite rev_involutive in HP.
      apply (ex_ir _ (C1 :: rev l3)) ; [ | apply PEPermutation_Type_cons, HP; reflexivity ].
      apply IHHll.
      -- constructor; [ assumption | constructor; [ assumption | ] ].
         apply Forall_inf_rev; assumption.
      -- list_simpl; GPermutation_Type_solve.
    * apply neg_irr.
      symmetry in HP.
      apply PEPermutation_Type_rev in HP.
      rewrite rev_involutive in HP.
      apply (ex_ir _ (C :: rev l3)) ; [ | apply PEPermutation_Type_cons, HP; reflexivity ].
      apply IHHll.
      -- constructor; [ constructor | ].
         constructor; [ assumption | ].
         apply Forall_inf_rev; assumption.
      -- list_simpl; GPermutation_Type_solve.
  + inversion Heq as [[Heq0 Heq1]]; subst.
    decomp_map_inf Heq1; symmetry in Heq3; decomp_map_inf Heq3; cbn in Heq3, Heq5, Heq7 ; subst.
    cbn in Heq6 ; apply (f_equal (@rev _)) in Heq6.
    rewrite rev_involutive in Heq6 ; subst.
    destruct x0; inversion Heq1; subst.
    list_simpl.
    apply tens_ilr.
    apply IHHll.
    * inversion Hnzsp as [ | ? ? ? HF ].
      constructor; [ assumption | ].
      list_simpl in HF.
      assert (H3l := Forall_inf_app_l _ _ HF).
      assert (H3r := Forall_inf_app_r _ _ HF).
      inversion H3r as [ | ? ? Hnzsp' ].
      inversion_clear Hnzsp'.
      apply Forall_inf_app; [ assumption | ].
      constructor; [ | constructor ]; assumption.
    * list_simpl.
      rewrite HP; GPermutation_Type_solve.
- list_simpl in HP.
  symmetry in HP.
  apply PCPermutation_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') HP Heq].
  destruct l' ; inversion Heq ; subst.
  + destruct C ; inversion H0 ; subst.
    apply top_irr.
  + decomp_map_inf H1; symmetry in H3; decomp_map_inf H3; cbn in H3, H5, H7; subst.
    apply (f_equal (@rev _)) in H6.
    rewrite rev_involutive in H6 ; subst.
    destruct x0 ; inversion H1 ; subst.
    list_simpl.
    apply zero_ilr.
- list_simpl in HP.
  symmetry in HP.
  apply PCPermutation_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') HP Heq].
  destruct l' ; inversion Heq ; subst.
  + list_simpl in HP.
    rewrite map_map in HP.
    apply PEPermutation_Type_map_inv in HP.
    destruct HP as [l3 Heq' HP].
    rewrite <- map_map in Heq' ; subst.
    inversion_clear Hnzsp as [ | ? ? Hnzsp' HF].
    apply Forall_inf_rev in HF.
    apply (PEPermutation_Type_Forall_inf _ _ HP) in HF.
    destruct C; inversion H0; subst.
    inversion Hnzsp'; subst.
    symmetry in HP.
    apply PEPermutation_Type_rev in HP.
    rewrite rev_involutive in HP.
    apply (ex_ir _ (rev l3)) ; [ | apply HP ].
    apply plus_irr1.
    apply IHHll.
    * constructor; [ assumption | ].
      apply Forall_inf_rev; assumption.
    * list_simpl; reflexivity.
  + decomp_map_inf H1; symmetry in H3; decomp_map_inf H3; cbn in H3, H5, H7; subst.
    apply (f_equal (@rev _)) in H6.
    rewrite rev_involutive in H6 ; subst.
    destruct x0 ; inversion H1 ; subst.
    list_simpl.
    apply with_ilr1.
    apply IHHll.
    * inversion Hnzsp as [ | ? ? ? HF ].
      constructor; [ assumption | ].
      list_simpl in HF.
      assert (H3l := Forall_inf_app_l _ _ HF).
      assert (H3r := Forall_inf_app_r _ _ HF).
      inversion H3r as [ | ? ? Hnzsp' ].
      inversion_clear Hnzsp'.
      apply Forall_inf_app; [ assumption | ].
      constructor; assumption.
    * list_simpl.
      rewrite HP ; GPermutation_Type_solve.
- list_simpl in HP.
  symmetry in HP.
  apply PCPermutation_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') HP Heq].
  destruct l' ; inversion Heq ; subst.
  + list_simpl in HP.
    rewrite map_map in HP.
    apply PEPermutation_Type_map_inv in HP.
    destruct HP as [l3 Heq' HP].
    rewrite <- map_map in Heq' ; subst.
    inversion_clear Hnzsp as [ | ? ? Hnzsp' HF ].
    apply Forall_inf_rev in HF.
    apply (PEPermutation_Type_Forall_inf _ _ HP) in HF.
    destruct C; inversion H0; subst.
    inversion_clear Hnzsp'.
    symmetry in HP.
    apply PEPermutation_Type_rev in HP.
    rewrite rev_involutive in HP.
    apply (ex_ir _ (rev l3)) ; [ | apply HP ].
    apply plus_irr2.
    apply IHHll.
    * constructor; [ assumption | ].
      apply Forall_inf_rev; assumption.
    * list_simpl; reflexivity.
  + decomp_map_inf H1; symmetry in H3; decomp_map_inf H3; cbn in H3, H5, H7; subst.
    apply (f_equal (@rev _)) in H6.
    rewrite rev_involutive in H6 ; subst.
    destruct x0 ; inversion H1 ; subst.
    list_simpl.
    apply with_ilr2.
    apply IHHll.
    * inversion Hnzsp as [ | ? ? ? HF ].
      constructor; [ assumption | ].
      list_simpl in HF.
      assert (H3l := Forall_inf_app_l _ _ HF).
      assert (H3r := Forall_inf_app_r _ _ HF).
      inversion H3r as [ | ? ? Hnzsp' ].
      inversion_clear Hnzsp'.
      apply Forall_inf_app; [ | constructor ]; assumption.
    * list_simpl.
      rewrite HP; GPermutation_Type_solve.
- list_simpl in HP.
  symmetry in HP.
  apply PCPermutation_Type_vs_cons_inv in HP as [(l', l'') HP Heq].
  destruct l' ; inversion Heq ; subst.
  + list_simpl in HP.
    rewrite map_map in HP.
    apply PEPermutation_Type_map_inv in HP.
    destruct HP as [l3 Heq' HP].
    rewrite <- map_map in Heq' ; subst.
    inversion_clear Hnzsp as [ | ? ? Hnzsp' HF ].
    apply Forall_inf_rev in HF.
    apply (PEPermutation_Type_Forall_inf _ _ HP) in HF.
    destruct C; inversion H0; subst.
    inversion_clear Hnzsp'.
    symmetry in HP.
    apply PEPermutation_Type_rev in HP.
    rewrite rev_involutive in HP.
    apply (ex_ir _ (rev l3)) ; [ | apply HP ].
    apply with_irr.
    * apply IHHll1.
      -- constructor; [ assumption | ].
         apply Forall_inf_rev; assumption.
      -- list_simpl; reflexivity.
    * apply IHHll2.
      -- constructor; [ assumption | ].
         apply Forall_inf_rev; assumption.
      -- list_simpl; reflexivity.
  + decomp_map_inf H1; symmetry in H3; decomp_map_inf H3; cbn in H3, H5, H7; subst.
    apply (f_equal (@rev _)) in H6.
    rewrite rev_involutive in H6 ; subst.
    destruct x0 ; inversion H1 ; subst.
    list_simpl.
    apply plus_ilr.
    * apply IHHll1.
      -- inversion Hnzsp as [ | ? ? ? HF ].
         constructor; [ assumption | ].
         list_simpl in HF.
         assert (H3l := Forall_inf_app_l _ _ HF).
         assert (H3r := Forall_inf_app_r _ _ HF).
         inversion H3r as [ | ? ? Hnzsp' ].
         inversion_clear Hnzsp'.
         apply Forall_inf_app; [ | constructor ]; assumption.
      -- list_simpl.
         rewrite HP ; GPermutation_Type_solve.
    * apply IHHll2.
      -- inversion Hnzsp as [ | ? ? ? HF ].
         constructor; [ assumption | ].
         list_simpl in HF.
         assert (H3l := Forall_inf_app_l _ _ HF).
         assert (H3r := Forall_inf_app_r _ _ HF).
         inversion H3r as [ | ? ? Hnzsp' ].
         inversion_clear Hnzsp'.
         apply Forall_inf_app; [ | constructor ]; assumption.
      -- list_simpl.
         rewrite HP ; GPermutation_Type_solve.
- list_simpl in HP.
  symmetry in HP.
  apply PCPermutation_Type_vs_cons_inv in HP as [(l', l'') HP Heq].
  destruct l' ; inversion Heq ; subst.
  + list_simpl in HP.
    rewrite map_map in HP.
    apply PEPermutation_Type_map_inv in HP.
    destruct HP as [l3 Heq' HP].
    rewrite <- (map_map _ _ l3) in Heq'.
    destruct (ill2ll_map_ioc_inv _ _ Heq') as [l0' Heq'' _] ; subst.
    inversion_clear Hnzsp as [ | ? ? Hnzsp' HF ].
    apply Forall_inf_rev in HF.
    apply (PEPermutation_Type_Forall_inf _ _ HP) in HF.
    destruct C ; inversion H0 ; subst.
    inversion_clear Hnzsp'.
    symmetry in HP.
    apply PEPermutation_Type_rev in HP.
    rewrite rev_involutive in HP.
    apply (ex_ir _ (rev (map ioc l0'))) ; [ | apply HP ].
    list_simpl.
    apply oc_irr.
    apply IHHll.
    * constructor; [ assumption | ].
      apply Forall_inf_rev in HF; list_simpl in HF; assumption.
    * rewrite Heq'; list_simpl; reflexivity.
  + decomp_map_inf H1; symmetry in H3; decomp_map_inf H3; cbn in H3, H5, H7; subst.
    destruct x0 ; inversion H1.
- list_simpl in HP.
  symmetry in HP.
  apply PCPermutation_Type_vs_cons_inv in HP as [(l', l'') HP Heq].
  destruct l' ; inversion Heq ; subst.
  + destruct C ; inversion H0.
  + decomp_map_inf H1; symmetry in H3; decomp_map_inf H3; cbn in H3, H5, H7; subst.
    apply (f_equal (@rev _)) in H6.
    rewrite rev_involutive in H6 ; subst.
    destruct x0 ; inversion H1 ; subst.
    list_simpl.
    apply de_ilr.
    apply IHHll.
    * inversion Hnzsp as [ | ? ? ? HF ].
      constructor; [ assumption | ].
      list_simpl in HF.
      assert (H3l := Forall_inf_app_l _ _ HF).
      assert (H3r := Forall_inf_app_r _ _ HF).
      inversion H3r as [ | ? ? Hnzsp' ].
      inversion_clear Hnzsp'.
      apply Forall_inf_app; [ | constructor ]; assumption.
    * list_simpl.
      rewrite HP ; GPermutation_Type_solve.
- list_simpl in HP.
  symmetry in HP.
  apply PCPermutation_Type_vs_cons_inv in HP as [(l', l'') HP Heq].
  destruct l' ; inversion Heq ; subst.
  + destruct C ; inversion H0.
  + decomp_map_inf H1; symmetry in H3; decomp_map_inf H3; cbn in H3, H5, H7 ; subst.
    apply (f_equal (@rev _)) in H6.
    rewrite rev_involutive in H6 ; subst.
    destruct x0 ; inversion H1 ; subst.
    list_simpl.
    apply wk_ilr.
    apply IHHll.
    * inversion Hnzsp as [ | ? ? ? HF ].
      constructor; [ assumption | ].
      list_simpl in HF.
      assert (H3l := Forall_inf_app_l _ _ HF).
      assert (H3r := Forall_inf_app_r _ _ HF).
      inversion H3r as [ | ? ? Hnzsp' ].
      inversion_clear Hnzsp'.
      apply Forall_inf_app; assumption.
    * list_simpl.
      apply PEPermutation_PCPermutation_Type in HP ; unfold id in HP.
      GPermutation_Type_solve.
- list_simpl in HP.
  symmetry in HP.
  apply PCPermutation_Type_vs_cons_inv in HP as [(l', l'') HP Heq].
  destruct l' ; inversion Heq ; subst.
  + destruct C ; inversion H0.
  + decomp_map_inf H1; symmetry in H3; decomp_map_inf H3; cbn in H3, H5, H7; subst.
    apply (f_equal (@rev _)) in H6.
    rewrite rev_involutive in H6 ; subst.
    destruct x0 ; inversion H1 ; subst.
    list_simpl ; apply co_ilr.
    apply IHHll.
    * inversion_clear Hnzsp as [ | ? ? ? HF ].
      list_simpl in HF.
      assert (HF1 := Forall_inf_app_l _ _ HF).
      assert (HF2 := Forall_inf_app_r _ _ HF).
      inversion HF2; subst.
      constructor; [ assumption | ].
      apply Forall_inf_app; [ | constructor ]; assumption.
    * apply (@PEPermutation_Type_cons _ _ _ (wn (dual (ill2ll x0))) eq_refl) in HP.
      apply (@PEPermutation_Type_cons _ _ _ (wn (dual (ill2ll x0))) eq_refl) in HP.
      apply PEPermutation_PCPermutation_Type in HP ; unfold id in HP ; list_simpl in HP.
      etransitivity; try eassumption.
      GPermutation_Type_solve.
- cbn in f.
  rewrite Hcut in f.
  inversion f.
- apply (Hgax a); assumption.
Qed.


(** Axiom-free conservativity *)
Proposition ll_to_ill_nzeropos_axfree {P} : (projT1 (ipgax P) -> False) -> forall l,
ll (i2pfrag P) l -> forall l0 C, Forall_inf nonzerospos (C :: l0) ->
  PCPermutation_Type (pperm (i2pfrag P))
    l (ill2ll C :: rev (map dual (map ill2ll l0))) ->
  ill P l0 C.
Proof.
intros P_axfree l pi l0 C Hnz HP.
apply cut_admissible_axfree in pi; [ | assumption ].
rewrite cutrm_i2pfrag in pi.
eapply ll_to_ill_nzeropos_cutfree in pi; try eassumption.
- eapply (stronger_ipfrag); [ | eassumption ].
  repeat split; [ | reflexivity ].
  cbn; intros; exfalso; auto.
- reflexivity.
- intros a; exfalso; auto.
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
  (forall A,
     In_inf (dual (ill2ll A)) (map ill2ll (fst (projT2 (ipgax P) a))) ->
     oclike A -> False)
* (forall A, ill2ll A = ill2ll (snd (projT2 (ipgax P) a)) -> oclike A -> False)
* (forall l C,
     PCPermutation_Type (ipperm P) (ill2ll (snd (projT2 (ipgax P) a))
                         :: rev (map dual (map ill2ll (fst (projT2 (ipgax P) a)))))
                       (ill2ll C :: rev (map dual (map ill2ll l)))
       -> ill P l C)
* notT (In_inf N (fst (projT2 (ipgax P) a))).

(** Cut-free conservativity *)
Theorem ll_to_ill_oclpam_cutfree {P} :
  ipperm P = true -> ipcut P = false -> easyipgax_oclmap P ->
  forall l, ll (i2pfrag P) l -> forall l0 l1 C, Forall_inf oclpam (C :: l0) ->
    Forall_inf oclike l1 ->
    PCPermutation_Type (pperm (i2pfrag P)) l
                (ill2ll C :: map ill2ll l1
                  ++ rev (map dual (map ill2ll l0))) ->
      ill P l0 C
   *  (l1 <> nil -> forall l2, ill P (l0 ++ l2) C).
Proof.
intros Hperm Hcut Hgax.
intros l Hll ; induction Hll ;
  intros l0 lo C Hoclm Hocl HP ; try (now inversion f).
- apply PCPermutation_Type_length_2_inv in HP.
  destruct HP as [HP | HP] ; inversion HP ; destruct C ; inversion H0 ; subst.
  destruct lo ; list_simpl in H1 ; inversion H1.
  + induction l0 using rev_rect ; list_simpl in H2 ; inversion H2.
    induction l0 using rev_rect ; list_simpl in H4 ; inversion H4.
    destruct x ; inversion H3.
    apply i2a_inj in H5 ; subst.
    split.
    * apply ax_ir.
    * intros Hnil.
      exfalso.
      apply Hnil; reflexivity.
  + destruct i0 ; inversion H2.
- rewrite HP in p.
  apply IHHll in p; assumption.
- assert (PCPermutation_Type (pperm (i2pfrag P)) (l1 ++ map wn lw ++ l2)
       (ill2ll C :: map ill2ll lo ++ rev (map dual (map ill2ll l0))))
    as HP'.
  { cbn in HP ; rewrite Hperm in HP ; cbn in HP.
    apply (Permutation_Type_map wn) in p.
    cbn ; rewrite Hperm ; cbn ; Permutation_Type_solve. }
  apply IHHll in HP'; assumption.
- apply PCPermutation_Type_length_1_inv in HP.
  inversion HP ; destruct C ; inversion H0 ; subst.
  destruct lo ; inversion H1.
  induction l0 using rev_rect ; list_simpl in H1 ; inversion H1.
  split.
  + apply one_irr.
  + intros Hnil.
    contradiction Hnil; reflexivity.
- symmetry in HP ; apply PCPermutation_Type_vs_cons_inv in HP as [(l', l'') HP Heq].
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  symmetry in H1 ; dichot_elt_app_inf_exec H1 ; subst.
  { symmetry in H0; decomp_map_inf H0 ; destruct x ; inversion H0. }
  list_simpl in H2; symmetry in H2; decomp_map_inf H2.
  symmetry in H3; decomp_map_inf H3;
    destruct x; inversion H2; destruct x0; inversion H3; cbn in H3, H5, H7; subst.
  apply (f_equal (@rev _)) in H6 ; list_simpl in H6 ; subst.
  apply PEPermutation_PCPermutation_Type in HP ; unfold id in HP.
  assert (HP' := PCPermutation_Type_trans _ _ _ _ HP (PCPermutation_Type_app_comm _ _ _)).
  specialize IHHll with (rev l8 ++ rev l6) lo C.
  list_simpl in IHHll ; list_simpl in HP' ; apply IHHll in HP'; try assumption.
  + destruct HP' as [IH1 IH2] ; split.
    * apply one_ilr; assumption.
    * intros Hnil l2.
      list_simpl.
      apply one_ilr.
      rewrite app_assoc.
      apply IH2; assumption.
  + inversion Hoclm as [ | ? ? ? HF ] ; constructor; try assumption.
    assert (Hl := Forall_inf_app_l _ _ HF).
    assert (Hr := Forall_inf_app_r _ _ HF).
    apply Forall_inf_app; try assumption.
    inversion Hr; assumption.
- symmetry in HP; apply PCPermutation_Type_vs_cons_inv in HP as [(l', l'') HP Heq].
  cbn in HP ; rewrite Hperm in HP ; cbn in HP.
  apply Permutation_Type_app_app_inv in HP as [[[[l3' l3''] l4'] l4''] [[HP1 HP2] [HP3 HP4]]];
    cbn in HP1 ; cbn in HP2 ; cbn in HP3 ; cbn in HP4.
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  + apply Permutation_Type_nil in HP4 ; apply app_eq_nil in HP4 ; destruct HP4 ; subst.
    list_simpl in HP1 ; symmetry in HP1.
    list_simpl in HP2 ; symmetry in HP2.
    apply (@Permutation_Type_trans _ _ _ (l2 ++ l1)) in HP3 ;
      [ | apply Permutation_Type_app ]; try assumption.
    clear l3' l3'' HP1 HP2.
    apply Permutation_Type_app_app_inv in HP3.
    destruct HP3 as [[[[l3' l3''] l4'] l4''] [[HP1 HP2] [HP3 HP4]]] ;
      cbn in HP1 ; cbn in HP2 ; cbn in HP3 ; cbn in HP4.
    symmetry in HP1 ; apply Permutation_Type_map_inv in HP1.
    destruct HP1 as [l3 Heq1 HP1].
    symmetry in Heq1; decomp_map_inf Heq1 ; subst.
    list_simpl in HP2.
    rewrite map_map in HP2.
    symmetry in HP2 ; apply Permutation_Type_map_inv in HP2.
    destruct HP2 as [l3 Heq2 HP2].
    apply Permutation_Type_rev' in HP2.
    rewrite rev_involutive in HP2.
    rewrite <- map_map in Heq2.
    symmetry in Heq2; decomp_map_inf Heq2;
      symmetry in Heq2; decomp_map_inf Heq2 ; cbn in Heq4 ; cbn in Heq5 ; subst.
    specialize IHHll1 with (rev l9) l5 C1.
    specialize IHHll2 with (rev l8) l4 C2.
    cbn in HP1.
    apply (Permutation_Type_Forall_inf HP1) in Hocl.
    assert (Hocl2 := Forall_inf_app_l _ _ Hocl).
    assert (Hocl1 := Forall_inf_app_r _ _ Hocl).
    apply IHHll1 in Hocl1 ; [ apply IHHll2 in Hocl2 | | ].
    * destruct Hocl1 as [IH1 IH2].
      destruct Hocl2 as [IH3 IH4].
      split.
      -- eapply ex_ir ; [ apply tens_irr; eassumption | ].
         list_simpl in HP2.
         rewrite Hperm ; cbn ; Permutation_Type_solve.
      -- intros Hnil lw.
         destruct lo ; [ exfalso ; apply Hnil ; reflexivity | ].
         symmetry in HP1 ; apply Permutation_Type_vs_cons_inv in HP1.
         destruct HP1 as [(ll & lr) Heq3].
         dichot_elt_app_inf_exec Heq3 ; subst.
         ++ assert (ll ++ i :: l <> nil) as Hnil2
              by (clear ; intros H ; destruct ll ; inversion H).
            assert (IH := IH4 Hnil2 lw).
            eapply ex_ir ; [apply tens_irr; eassumption | ].
            list_simpl in HP2.
            rewrite Hperm ; cbn ; Permutation_Type_solve.
         ++ assert (l3 ++ i :: lr <> nil) as Hnil2
              by (clear ; intros H ; destruct l3 ; inversion H).
            assert (IH := IH2 Hnil2 lw).
            eapply ex_ir ; [apply tens_irr; eassumption | ].
            list_simpl in HP2.
            rewrite Hperm ; cbn ; Permutation_Type_solve.
    * inversion_clear Hoclm as [ | ? ? Hoclm' HF ].
      inversion_clear Hoclm'.
      constructor; try assumption.
      list_simpl in HP2.
      apply (Permutation_Type_Forall_inf HP2) in HF.
      apply Forall_inf_app_r in HF; assumption.
    * now cbn ; rewrite Hperm ; list_simpl; apply Permutation_Type_cons.
    * inversion Hoclm as [ | ? ? Hoclm' HF ].
      inversion Hoclm'.
      constructor; try assumption.
      list_simpl in HP2.
      apply (Permutation_Type_Forall_inf HP2) in HF.
      apply Forall_inf_app_l in HF; assumption.
    * now cbn ; rewrite Hperm ; list_simpl; apply Permutation_Type_cons.
  + dichot_elt_app_inf_exec H1 ; subst.
    * symmetry in H0; decomp_map_inf H0 ; subst.
      destruct x ; inversion H0 ; subst.
      assert (HP4' := HP4).
      symmetry in HP4' ; apply Permutation_Type_vs_cons_inv in HP4'.
      destruct HP4' as [(ll & lr) Heq'] ; cbn in Heq'.
      apply Permutation_Type_app_app_inv in HP3.
      destruct HP3 as [[[[l3l l3r] l4l] l4r] [[HP3' HP3''] [HP3''' HP3'''']]] ;
        cbn in HP3' ; cbn in HP3'' ; cbn in HP3''' ; cbn in HP3''''.
      symmetry in HP3' ; apply Permutation_Type_map_inv in HP3'.
      destruct HP3' as [l3 Heq'' HP3'].
      symmetry in Heq''; decomp_map_inf Heq'' ; subst.
      list_simpl in HP3''.
      rewrite map_map in HP3''.
      symmetry in HP3'' ; apply Permutation_Type_map_inv in HP3''.
      destruct HP3'' as [l3 Heq'' HP3''].
      apply Permutation_Type_rev' in HP3'' ; rewrite rev_involutive in HP3''.
      rewrite <- map_map in Heq''.
      symmetry in Heq''; decomp_map_inf Heq''; symmetry in Heq''; decomp_map_inf Heq'' ;
        cbn in Heq''3 ; cbn in Heq''4 ; subst.
      cbn in HP3''' ; apply (Permutation_Type_app_tail l4') in HP3'''.
      assert (HP1' := Permutation_Type_trans HP1 HP3''').
      cbn in HP3'''' ; apply (Permutation_Type_app_tail l4'') in HP3''''.
      assert (HP2' := Permutation_Type_trans HP2 HP3'''').
      dichot_elt_app_inf_exec Heq' ; subst.
      -- list_simpl in HP4 ; apply Permutation_Type_cons_app_inv in HP4.
         symmetry in HP4 ; apply Permutation_Type_map_inv in HP4.
         destruct HP4 as [l3 Heq' HP].
         symmetry in Heq'; decomp_map_inf Heq' ; subst.
         specialize IHHll2 with (rev l11) (x2 :: l7 ++ l10 ++ l14) C.
         assert (Forall_inf oclike (x2 :: l7 ++ l10 ++ l14)) as Hocl'.
         { cbn in HP ; cbn in Hocl.
           assert (Hocl2 := Forall_inf_app_l _ _ Hocl).
           assert (Hocl1 := Forall_inf_app_r _ _ Hocl).
           apply (Permutation_Type_Forall_inf HP) in Hocl2.
           inversion Hocl1 as [ | ? ? Hocl1' HF ].
           inversion_clear Hocl1'.
           constructor; try assumption.
           cbn in HP3'.
           apply (Permutation_Type_Forall_inf HP3') in HF.
           assert (HF1 := Forall_inf_app_l _ _ HF).
           assert (HF2 := Forall_inf_app_r _ _ HF).
           apply Forall_inf_app; try assumption.
           rewrite app_assoc in Hocl2.
           assert (Hocl3 := Forall_inf_app_l _ _ Hocl2).
           assert (Hocl4 := Forall_inf_app_r _ _ Hocl2); assumption. }
         apply IHHll2 in Hocl'.
         ++ destruct Hocl' as [_ Hocl'].
            assert (x2 :: l7 ++ l10 ++ l14 <> nil) as Hnil
              by (intros Hnil ; inversion Hnil).
            split.
            ** eapply Hocl' in Hnil.
               eapply ex_ir ; [ apply Hnil | ].
               cbn in HP3'' ; symmetry in HP3''.
               rewrite Hperm ; cbn ; etransitivity ; [ | apply HP3'' ].
               rewrite rev_app_distr.
               apply Permutation_Type_app_comm.
            ** intros Hnil' l.
               eapply Hocl' in Hnil.
               eapply ex_ir ; [ apply Hnil | ].
               cbn in HP3'' ; symmetry in HP3''.
               apply (Permutation_Type_app_tail l) in HP3''.
               rewrite Hperm ; cbn ; etransitivity ; [ | apply HP3'' ].
               rewrite rev_app_distr.
               rewrite <- app_assoc.
               etransitivity ; [ apply Permutation_Type_app_rot | apply Permutation_Type_app_rot ].
         ++ inversion Hoclm as [ | ? ? ? HF ]; constructor; try assumption.
            cbn in HP3''.
            apply (Permutation_Type_Forall_inf HP3'') in HF.
            list_simpl in HF; apply Forall_inf_app_r in HF; apply HF.
         ++ list_simpl ; rewrite Hperm ; cbn.
            cons2app; rewrite <- (app_comm_cons _ _ (ill2ll x2)); apply Permutation_Type_cons_app.
            list_simpl; etransitivity; [ apply HP1' | Permutation_Type_solve ].
      -- list_simpl in HP4 ; rewrite app_assoc in HP4 ;
           apply Permutation_Type_cons_app_inv in HP4.
         symmetry in HP4 ; apply Permutation_Type_map_inv in HP4.
         destruct HP4 as [l' Heq' HP].
         list_simpl in Heq'; symmetry in Heq'; decomp_map_inf Heq' ; subst.
         specialize IHHll1 with (rev l12) (x1 :: l8 ++ l13 ++ l14) C.
         assert (Forall_inf oclike (x1 :: l8 ++ l13 ++ l14)) as Hocl'.
         { cbn in HP ; cbn in Hocl.
           assert (Hocl2 := Forall_inf_app_l _ _ Hocl).
           assert (Hocl1 := Forall_inf_app_r _ _ Hocl).
           apply (Permutation_Type_Forall_inf HP) in Hocl2.
           inversion Hocl1 as [ | ? ? Hocl1' HF ].
           inversion_clear Hocl1'.
           constructor; try assumption.
           cbn in HP3'.
           apply (Permutation_Type_Forall_inf HP3') in HF.
           apply Forall_inf_app_r in HF; apply Forall_inf_app; try assumption.
           apply Forall_inf_app_r in Hocl2; assumption. }
         apply IHHll1 in Hocl'.
         ++ destruct Hocl' as [_ Hocl'].
            assert (x1 :: l8 ++ l13 ++ l14 <> nil) as Hnil
              by (intros Hnil ; inversion Hnil).
            split.
            ** eapply Hocl' in Hnil.
               eapply ex_ir ; [ apply Hnil | ].
               cbn in HP3'' ; symmetry in HP3''.
               rewrite Hperm ; cbn ; etransitivity ; [ | apply HP3'' ].
               rewrite rev_app_distr ; reflexivity.
            ** intros Hnil' l.
               eapply Hocl' in Hnil.
               eapply ex_ir ; [ apply Hnil | ].
               cbn in HP3'' ; symmetry in HP3''.
               apply (Permutation_Type_app_tail l) in HP3''.
               rewrite Hperm ; cbn ; etransitivity ; [ | apply HP3'' ].
               rewrite rev_app_distr, <- app_assoc; reflexivity.
         ++ inversion Hoclm as [ | ? ? ? HF ]; constructor; try assumption.
            cbn in HP3''.
            apply (Permutation_Type_Forall_inf HP3'') in HF.
            list_simpl in HF; apply Forall_inf_app_l in HF; apply HF.
         ++ list_simpl ; rewrite Hperm ; cbn.
            cons2app; rewrite <- (app_comm_cons _ _ (ill2ll x1)); apply Permutation_Type_cons_app.
            list_simpl; etransitivity; [ apply HP2' | Permutation_Type_solve ].
    * list_simpl in H2 ; symmetry in H2; decomp_map_inf H2 ; subst.
      symmetry in H3; decomp_map_inf H3 ;
        cbn in H1 ; cbn in H3 ; cbn in H4 ; cbn in H5 ; subst.
      apply (f_equal (@rev _)) in H4 ; list_simpl in H4 ; subst.
      destruct x0 ; inversion H2 ; subst.
      -- assert (HP4' := HP4).
         symmetry in HP4' ; apply Permutation_Type_vs_cons_inv in HP4'.
         destruct HP4' as [(l4a & l4b) Heq'] ; cbn in Heq'.
         dichot_elt_app_inf_exec Heq' ; subst.
         ++ cbn in HP3 ; rewrite map_map in HP3.
            symmetry in HP3 ; apply Permutation_Type_map_inv in HP3.
            destruct HP3 as [l3''' Heq' HP3].
            symmetry in Heq'; decomp_map_inf Heq' ; subst.
            rewrite <- map_map in HP1.
            rewrite <- map_map in HP2.
            list_simpl in HP4 ; apply Permutation_Type_cons_app_inv in HP4.
            apply Permutation_Type_app_app_inv in HP4.
            destruct HP4 as [[[[l3a l3b] l3c] l3d] [[HP4' HP4''] [HP4''' HP4'''']]] ;
              cbn in HP4' ; cbn in HP4'' ; cbn in HP4''' ; cbn in HP4''''.
            apply Permutation_Type_app_app_inv in HP4''''.
            destruct HP4'''' as [[[[l3e l3f] l3g] l3h] [[HP4a HP4b] [HP4c HP4d]]] ;
              cbn in HP4a ; cbn in HP4b ; cbn in HP4c ; cbn in HP4d.
            cbn in HP1.
            assert (Permutation_Type l2
                     (map dual (map ill2ll l4) ++ (l3a ++ l3b)
                       ++ ill2ll C :: l3e ++ l3g))
              as HP'.
            { etransitivity; [ apply HP1 | ].
              apply Permutation_Type_app_head.
              apply Permutation_Type_app; Permutation_Type_solve. }
            symmetry in HP4' ; apply Permutation_Type_map_inv in HP4'.
            destruct HP4' as [l3' Heq' HP4'].
            symmetry in Heq'; decomp_map_inf Heq' ; subst.
            apply (Permutation_Type_app_head l3b) in HP4d.
            assert (HP'' := Permutation_Type_trans HP4'' HP4d).
            rewrite map_map in HP''.
            symmetry in HP'' ; apply Permutation_Type_map_inv in HP''.
            clear HP4'' ; destruct HP'' as [l4' Heq' HP4''].
            symmetry in Heq'; decomp_map_inf Heq' ; subst.
            rewrite <- (map_map _ _ l11) in HP'.
            rewrite <- (map_map _ _ l13) in HP'.
            symmetry in HP4c ; apply Permutation_Type_map_inv in HP4c.
            destruct HP4c as [l4' Heq' HP4c].
            symmetry in Heq'; decomp_map_inf Heq' ; subst.
            rewrite <- (map_map _ _ l14) in HP4b.
            cbn in HP2 ; cbn in HP4b.
            apply (Permutation_Type_app_head (map dual (map ill2ll l6))) in HP4b.
            assert (HP'' := Permutation_Type_trans HP2 HP4b).
            specialize IHHll2 with (rev (x0_2 :: l4 ++ l11 ++ l13)) (l9 ++ l15) C.
            cbn in HP4' ; apply (Permutation_Type_Forall_inf HP4') in Hocl.
            assert (Hocl1 := Forall_inf_app_l _ _ Hocl).
            assert (Hocl2 := Forall_inf_app_r _ _ Hocl).
            specialize IHHll1 with (rev (l6 ++ l14)) l16 x0_1.
            cbn in HP4c ; apply (Permutation_Type_Forall_inf HP4c) in Hocl2.
            assert (Hocl2' := Forall_inf_app_l _ _ Hocl2).
            assert (Hocl3 := Forall_inf_app_r _ _ Hocl2).
            assert (Hocl4 := Forall_inf_app Hocl1 Hocl2').
            apply IHHll2 in Hocl4 ; [ apply IHHll1 in Hocl3 | | ].
            ** split.
               --- destruct Hocl4 as [Hocl4 _].
                   destruct Hocl3 as [Hocl3 _].
                   apply (ex_ir _ (rev (l4 ++ l11 ++ l13) ++
                                     ilpam x0_1 x0_2 :: rev (l6 ++ l14) ++ nil)).
                   +++ apply lpam_ilr; assumption.
                   +++ apply Permutation_Type_rev' in HP3 .
                       apply Permutation_Type_rev' in HP4''.
                       list_simpl in HP3 ; list_simpl in HP4''.
                       rewrite Hperm ; list_simpl ; Permutation_Type_solve.
               --- intros Hnil lw ; destruct lo ; [ contradiction Hnil ; reflexivity | ].
                   apply (Permutation_Type_app_head l9) in HP4c.
                   assert (HP''' := Permutation_Type_trans HP4' HP4c).
                   symmetry in HP''' ; apply Permutation_Type_vs_cons_inv in HP'''.
                   destruct HP''' as [(l4l & l4r) Heq'] ; cbn in Heq'.
                   rewrite app_assoc in Heq'.
                   dichot_elt_app_inf_exec Heq' ; subst.
                   +++ rewrite <- Heq'0 in Hocl4.
                       assert (l4l ++ i :: l0 <> nil) as Hnil'
                         by (intros Hnil' ; destruct l4l ; inversion Hnil').
                       apply (snd Hocl4) with lw in Hnil'.
                       destruct Hocl3 as [Hocl3 _].
                       apply (ex_ir _ (rev (l4 ++ l11 ++ l13) ++
                                         ilpam x0_1 x0_2 :: rev (l6 ++ l14) ++ lw)).
                       *** apply lpam_ilr; try assumption.
                           eapply ex_ir ; [ apply Hnil' | ].
                           rewrite Hperm ; cbn ; Permutation_Type_solve.
                       *** apply Permutation_Type_rev' in HP3 .
                           apply Permutation_Type_rev' in HP4''.
                           list_simpl in HP3 ; list_simpl in HP4''.
                           rewrite Hperm ; list_simpl ; Permutation_Type_solve.
                   +++ assert (l17 ++ i :: l4r <> nil) as Hnil'
                         by (intros Hnil' ; destruct l17 ; inversion Hnil').
                       apply (snd Hocl3) with lw in Hnil'.
                       destruct Hocl4 as [Hocl4 _].
                       apply (ex_ir _ (rev (l4 ++ l11 ++ l13) ++
                                      ilpam x0_1 x0_2 :: (rev (l6 ++ l14) ++ lw) ++ nil)).
                       *** apply lpam_ilr; assumption.
                       *** apply Permutation_Type_rev' in HP3 .
                           apply Permutation_Type_rev' in HP4''.
                           list_simpl in HP3 ; list_simpl in HP4''.
                           rewrite Hperm ; list_simpl ; Permutation_Type_solve.
            ** inversion_clear Hoclm as [ | ? ? ? HF ].
               assert (Hoclm1 := Forall_inf_app_l _ _ HF).
               assert (Hoclm2 := Forall_inf_app_r _ _ HF).
               inversion_clear Hoclm2 as [ | ? ? Hoclm3 HF'].
               inversion Hoclm3; constructor; try assumption.
               cbn in HP3.
               apply Permutation_Type_rev' in HP3.
               apply (Permutation_Type_Forall_inf HP3) in Hoclm1.
               list_simpl in Hoclm1 ; list_simpl.
               assert (Hoclm1' := Forall_inf_app_l _ _ Hoclm1).
               assert (Hoclm2' := Forall_inf_app_r _ _ Hoclm1).
               cbn in HP4''.
               apply Permutation_Type_rev' in HP4''.
               apply (Permutation_Type_Forall_inf HP4'') in HF'.
               list_simpl in HF'.
               apply Forall_inf_app_l in HF'; apply Forall_inf_app; assumption.
            ** cbn ; rewrite Hperm ; cbn.
               rewrite bidual.
               now list_simpl; apply Permutation_Type_cons; try Permutation_Type_solve.
            ** inversion_clear Hoclm as [ | ? ? ? HF ]; constructor; try assumption.
               list_simpl.
               assert (Hoclm1 := Forall_inf_app_l _ _ HF).
               assert (Hoclm2 := Forall_inf_app_r _ _ HF).
               inversion_clear Hoclm2 as [ | ? ? Hoclm2' HF' ].
               cbn in HP4''.
               apply Permutation_Type_rev' in HP4''.
               apply (Permutation_Type_Forall_inf HP4'') in HF'.
               list_simpl in HF'.
               apply Forall_inf_app_r in HF'.
               assert (H4l := Forall_inf_app_l _ _ HF').
               assert (H4r := Forall_inf_app_r _ _ HF').
               apply Forall_inf_app ; [ apply H4l | ].
               apply Forall_inf_app ; [ apply H4r | ].
               cbn in HP3.
               apply Permutation_Type_rev' in HP3.
               apply (Permutation_Type_Forall_inf HP3) in Hoclm1.
               list_simpl in Hoclm1; list_simpl.
               apply Forall_inf_app_r in Hoclm1.
               inversion Hoclm2'.
               apply Forall_inf_app ; [ | constructor ; [assumption | constructor] ]; assumption.
            ** list_simpl ; rewrite Hperm ; cbn.
               rewrite app_comm_cons, 2 app_assoc; apply Permutation_Type_cons_app.
               Permutation_Type_solve.
         ++ cbn in HP3 ; rewrite map_map in HP3.
            symmetry in HP3 ; apply Permutation_Type_map_inv in HP3.
            destruct HP3 as [l3''' Heq' HP3].
            symmetry in Heq'; decomp_map_inf Heq' ; subst.
            rewrite <- map_map in HP1.
            rewrite <- map_map in HP2.
            rewrite app_assoc in HP4 ; apply Permutation_Type_cons_app_inv in HP4.
            list_simpl in HP4 ; apply Permutation_Type_app_app_inv in HP4.
            destruct HP4 as [[[[l3a l3b] l3c] l3d] [[HP4' HP4''] [HP4''' HP4'''']]] ;
              cbn in HP4' ; cbn in HP4'' ; cbn in HP4''' ; cbn in HP4''''.
            apply Permutation_Type_app_app_inv in HP4''''.
            destruct HP4'''' as [[[[l3e l3f] l3g] l3h] [[HP4a HP4b] [HP4c HP4d]]] ;
              cbn in HP4a ; cbn in HP4b ; cbn in HP4c ; cbn in HP4d.
            symmetry in HP4' ; apply Permutation_Type_map_inv in HP4'.
            destruct HP4' as [l3' Heq' HP4'].
            symmetry in Heq'; decomp_map_inf Heq' ; subst.
            apply (Permutation_Type_app_head l3b) in HP4d.
            assert (HP' := Permutation_Type_trans HP4'' HP4d).
            rewrite map_map in HP'.
            symmetry in HP' ; apply Permutation_Type_map_inv in HP'.
            clear HP4'' ; destruct HP' as [l4'' Heq' HP4''].
            symmetry in Heq'; decomp_map_inf Heq' ; subst.
            cbn in HP2 ; cbn in HP4a.
            apply (Permutation_Type_app_tail (ill2ll C :: l4b)) in HP4a.
            apply (Permutation_Type_app_head (map dual (map ill2ll l6))) in HP4a.
            assert (HP' := Permutation_Type_trans HP2 HP4a).
            rewrite <- (map_map _ _ l13) in HP'.
            symmetry in HP4c ; apply Permutation_Type_map_inv in HP4c.
            destruct HP4c as [l4'' Heq' HP4c].
            symmetry in Heq'; decomp_map_inf Heq' ; subst.
            rewrite <- (map_map _ _ l14) in HP4b.
            cbn in HP4b ; cbn in HP'.
            apply (@Permutation_Type_cons _ (ill2ll C) _ eq_refl) in HP4b.
            apply (Permutation_Type_app_head (map dual (map ill2ll l6)
              ++ (map ill2ll l15 ++ map dual (map ill2ll l13)))) in HP4b.
            rewrite <- app_assoc in HP4b.
            assert (HP'' := Permutation_Type_trans HP' HP4b).
            specialize IHHll1 with (rev (l13 ++ l6 ++ l14)) (x0_1 :: l15 ++ l16) C.
            assert (x0_1 :: l15 ++ l16 <> nil) as Hnil
              by (intros Hnil ; inversion Hnil).
            inversion_clear Hoclm as [ | ? ? ? HF ].
            assert (Hoclm1 := Forall_inf_app_l _ _ HF).
            assert (Hoclm2 := Forall_inf_app_r _ _ HF).
            inversion_clear Hoclm2 as [ | ? ? Hoclm2' ].
            inversion_clear Hoclm2'.
            cbn in HP4' ; cbn in HP4c.
            apply (Permutation_Type_Forall_inf HP4') in Hocl.
            apply (Permutation_Type_app_head l9) in HP4c.
            apply (Permutation_Type_Forall_inf HP4c) in Hocl.
            apply Forall_inf_app_r in Hocl.
            assert (Hocl' := Forall_inf_cons _ X1 Hocl).
            apply IHHll1 in Hocl' ; [ split | | ].
            ** apply (snd Hocl') with (ilpam x0_1 x0_2 :: rev l4 ++ rev l11) in Hnil.
               eapply ex_ir ; [ apply Hnil | ].
               cbn ; rewrite Hperm ; cbn.
               cbn in HP3.
               apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
               cbn in HP4''.
               apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
               list_simpl ; Permutation_Type_solve.
            ** intros Hnil' lw.
               apply (snd Hocl') with (ilpam x0_1 x0_2 :: rev l4 ++ rev l11 ++ lw) in Hnil.
               eapply ex_ir ; [ apply Hnil | ].
               cbn ; rewrite Hperm ; cbn.
               cbn in HP3.
               apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
               cbn in HP4''.
               apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
               list_simpl ; Permutation_Type_solve.
            ** constructor; try assumption.
               cbn in HP4''.
               apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
               apply (Permutation_Type_Forall_inf HP4'') in X0.
               rewrite app_assoc in X0.
               apply Forall_inf_app_l in X0.
               assert (H4l := Forall_inf_app_l _ _ X0).
               assert (H4r := Forall_inf_app_r _ _ X0).
               cbn in HP3.
               apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
               apply (Permutation_Type_Forall_inf HP3) in Hoclm1.
               list_simpl in Hoclm1 ; apply Forall_inf_app_l in Hoclm1.
               list_simpl.
               apply Forall_inf_app; try assumption.
               apply Forall_inf_app; assumption.
            ** list_simpl ; rewrite Hperm ; cbn.
               rewrite bidual ; list_simpl.
               cons2app; rewrite <- (app_comm_cons _ _ (ill2ll x0_1));
                 apply Permutation_Type_cons_app.
               list_simpl; etransitivity; [ apply HP'' | Permutation_Type_solve ].
      -- assert (HP4' := HP4).
         symmetry in HP4' ; apply Permutation_Type_vs_cons_inv in HP4'.
         destruct HP4' as [(l4a & l4b) Heq'] ; cbn in Heq'.
         dichot_elt_app_inf_exec Heq' ; subst.
         ++ cbn in HP3 ; rewrite map_map in HP3.
            symmetry in HP3; apply Permutation_Type_map_inv in HP3 as [l3''' Heq' HP3].
            symmetry in Heq'; decomp_map_inf Heq'; subst.
            rewrite <- map_map in HP1.
            rewrite <- map_map in HP2.
            list_simpl in HP4 ; apply Permutation_Type_cons_app_inv in HP4.
            apply Permutation_Type_app_app_inv in HP4.
            destruct HP4 as [[[[l3a l3b] l3c] l3d] [[HP4' HP4''] [HP4''' HP4'''']]] ;
              cbn in HP4' ; cbn in HP4'' ; cbn in HP4''' ; cbn in HP4''''.
            apply Permutation_Type_app_app_inv in HP4''''.
            destruct HP4'''' as [[[[l3e l3f] l3g] l3h] [[HP4a HP4b] [HP4c HP4d]]] ;
              cbn in HP4a ; cbn in HP4b ; cbn in HP4c ; cbn in HP4d.
            cbn in HP1.
            assert (Permutation_Type l2
                     (map dual (map ill2ll l4) ++ (l3a ++ l3b)
                       ++ ill2ll C :: l3e ++ l3g)) as HP'.
            { etransitivity; [ apply HP1 | ].
              apply Permutation_Type_app_head, Permutation_Type_app; auto. }
            symmetry in HP4' ; apply Permutation_Type_map_inv in HP4'.
            destruct HP4' as [l3' Heq' HP4'].
            symmetry in Heq'; decomp_map_inf Heq' ; subst.
            apply (Permutation_Type_app_head l3b) in HP4d.
            assert (HP'' := Permutation_Type_trans HP4'' HP4d).
            rewrite map_map in HP''.
            symmetry in HP'' ; apply Permutation_Type_map_inv in HP''.
            clear HP4'' ; destruct HP'' as [l4' Heq' HP4''].
            symmetry in Heq'; decomp_map_inf Heq' ; subst.
            rewrite <- (map_map _ _ l11) in HP'.
            rewrite <- (map_map _ _ l13) in HP'.
            symmetry in HP4c ; apply Permutation_Type_map_inv in HP4c.
            destruct HP4c as [l4' Heq' HP4c].
            symmetry in Heq'; decomp_map_inf Heq' ; subst.
            rewrite <- (map_map _ _ l14) in HP4b.
            cbn in HP2 ; cbn in HP4b.
            apply (Permutation_Type_app_head (map dual (map ill2ll l6))) in HP4b.
            assert (HP'' := Permutation_Type_trans HP2 HP4b).
            specialize IHHll2 with (rev (N :: l4 ++ l11 ++ l13)) (l9 ++ l15) C.
            cbn in HP4' ; apply (Permutation_Type_Forall_inf HP4') in Hocl.
            assert (Hocl1 := Forall_inf_app_l _ _ Hocl).
            assert (Hocl2 := Forall_inf_app_r _ _ Hocl).
            specialize IHHll1 with (rev (l6 ++ l14)) l16 x0.
            cbn in HP4c ; apply (Permutation_Type_Forall_inf HP4c) in Hocl2.
            assert (Hocl2' := Forall_inf_app_l _ _ Hocl2).
            assert (Hocl3 := Forall_inf_app_r _ _ Hocl2).
            assert (Hocl4 := Forall_inf_app Hocl1 Hocl2').
            apply IHHll2 in Hocl4 ; [ apply IHHll1 in Hocl3 | | ].
            ** split.
               --- destruct Hocl4 as [Hocl4 _].
                   destruct Hocl3 as [Hocl3 _].
                   apply (ex_ir _ (rev (l4 ++ l11 ++ l13) ++
                                     igen x0 :: rev (l6 ++ l14) ++ nil)).
                   +++ apply gen_pam_rule; try assumption.
                       intros a; apply Hgax.
                   +++ apply Permutation_Type_rev' in HP3 .
                       apply Permutation_Type_rev' in HP4''.
                       list_simpl in HP3 ; list_simpl in HP4''.
                       rewrite Hperm ; list_simpl ; Permutation_Type_solve.
               --- intros Hnil lw ; destruct lo ; [ contradiction Hnil ; reflexivity | ].
                   apply (Permutation_Type_app_head l9) in HP4c.
                   assert (HP''' := Permutation_Type_trans HP4' HP4c).
                   symmetry in HP''' ; apply Permutation_Type_vs_cons_inv in HP'''.
                   destruct HP''' as [(l4l & l4r) Heq'] ; cbn in Heq'.
                   rewrite app_assoc in Heq'.
                   dichot_elt_app_inf_exec Heq' ; subst.
                   +++ rewrite <- Heq'0 in Hocl4.
                       assert (l4l ++ i :: l0 <> nil) as Hnil'
                         by (intros Hnil' ; destruct l4l ; inversion Hnil').
                       apply (snd Hocl4) with lw in Hnil'.
                       destruct Hocl3 as [Hocl3 _].
                       apply (ex_ir _ (rev (l4 ++ l11 ++ l13) ++
                                         igen x0 :: rev (l6 ++ l14) ++ lw)).
                       *** apply gen_pam_rule; try assumption.
                           ---- intros a ; apply Hgax.
                           ---- eapply ex_ir ; [ apply Hnil' | ].
                                rewrite Hperm ; cbn ; Permutation_Type_solve.
                       *** apply Permutation_Type_rev' in HP3 .
                           apply Permutation_Type_rev' in HP4''.
                           list_simpl in HP3 ; list_simpl in HP4''.
                           rewrite Hperm ; list_simpl ; Permutation_Type_solve.
                   +++ assert (l17 ++ i :: l4r <> nil) as Hnil'
                         by (intros Hnil' ; destruct l17 ; inversion Hnil').
                       apply (snd Hocl3) with lw in Hnil'.
                       destruct Hocl4 as [Hocl4 _].
                       apply (ex_ir _ (rev (l4 ++ l11 ++ l13) ++
                                         igen x0 :: (rev (l6 ++ l14) ++ lw) ++ nil)).
                       *** apply gen_pam_rule; try assumption.
                           intros a ; apply Hgax.
                       *** apply Permutation_Type_rev' in HP3 .
                           apply Permutation_Type_rev' in HP4''.
                           list_simpl in HP3 ; list_simpl in HP4''.
                           rewrite Hperm ; list_simpl ; Permutation_Type_solve.
            ** inversion_clear Hoclm as [ | ? ? ? HF ].
               assert (Hoclm1 := Forall_inf_app_l _ _ HF).
               assert (Hoclm2 := Forall_inf_app_r _ _ HF).
               inversion_clear Hoclm2 as [ | ? ? Hoclm2' HF' ].
               inversion Hoclm2'; constructor; try assumption.
               cbn in HP3.
               apply Permutation_Type_rev' in HP3.
               apply (Permutation_Type_Forall_inf HP3) in Hoclm1.
               list_simpl in Hoclm1 ; list_simpl.
               assert (Hoclm1' := Forall_inf_app_l _ _ Hoclm1).
               assert (Hoclm1'' := Forall_inf_app_r _ _ Hoclm1).
               cbn in HP4''.
               apply Permutation_Type_rev' in HP4''.
               apply (Permutation_Type_Forall_inf HP4'') in HF'.
               list_simpl in HF'.
               apply Forall_inf_app_l in HF'; apply Forall_inf_app; assumption.
            ** cbn ; rewrite Hperm ; cbn.
               rewrite bidual; list_simpl.
               apply Permutation_Type_cons; auto.
               etransitivity; [ apply HP'' | Permutation_Type_solve ].
            ** inversion_clear Hoclm as [ | ? ? ? HF ]; constructor; try assumption.
               list_simpl.
               assert (Hoclm1 := Forall_inf_app_l _ _ HF).
               assert (Hoclm2 := Forall_inf_app_r _ _ HF).
               inversion_clear Hoclm2 as [ | ? ? Hoclm2' HF' ].
               cbn in HP4''.
               apply Permutation_Type_rev' in HP4''.
               apply (Permutation_Type_Forall_inf HP4'') in HF'.
               list_simpl in HF'.
               assert (H4l := Forall_inf_app_l _ _ HF').
               assert (H4r := Forall_inf_app_r _ _ HF').
               assert (H4r1 := Forall_inf_app_l _ _ H4r).
               assert (H4r2 := Forall_inf_app_r _ _ H4r).
               apply Forall_inf_app ; [ apply H4r1 | ].
               apply Forall_inf_app ; [ apply H4r2 | ].
               cbn in HP3.
               apply Permutation_Type_rev' in HP3.
               apply (Permutation_Type_Forall_inf HP3) in Hoclm1.
               list_simpl in Hoclm1 ; list_simpl.
               apply Forall_inf_app_r in Hoclm1.
               inversion Hoclm2'.
               apply Forall_inf_app ; [ | constructor ; [ constructor | constructor] ]; assumption.
            ** list_simpl ; rewrite Hperm ; cbn.
               rewrite app_comm_cons, 2 app_assoc; apply Permutation_Type_cons_app.
               Permutation_Type_solve.
         ++ cbn in HP3 ; rewrite map_map in HP3.
            symmetry in HP3 ; apply Permutation_Type_map_inv in HP3.
            destruct HP3 as [l3''' Heq' HP3].
            symmetry in Heq'; decomp_map_inf Heq' ; subst.
            rewrite <- map_map in HP1.
            rewrite <- map_map in HP2.
            rewrite app_assoc in HP4 ; apply Permutation_Type_cons_app_inv in HP4.
            list_simpl in HP4 ; apply Permutation_Type_app_app_inv in HP4.
            destruct HP4 as [[[[l3a l3b] l3c] l3d] [[HP4' HP4''] [HP4''' HP4'''']]] ;
              cbn in HP4' ; cbn in HP4'' ; cbn in HP4''' ; cbn in HP4''''.
            apply Permutation_Type_app_app_inv in HP4''''.
            destruct HP4'''' as [[[[l3e l3f] l3g] l3h] [[HP4a HP4b] [HP4c HP4d]]] ;
              cbn in HP4a ; cbn in HP4b ; cbn in HP4c ; cbn in HP4d.
            symmetry in HP4' ; apply Permutation_Type_map_inv in HP4'.
            destruct HP4' as [l3' Heq' HP4'].
            symmetry in Heq'; decomp_map_inf Heq' ; subst.
            apply (Permutation_Type_app_head l3b) in HP4d.
            assert (HP' := Permutation_Type_trans HP4'' HP4d).
            rewrite map_map in HP'.
            symmetry in HP' ; apply Permutation_Type_map_inv in HP'.
            clear HP4'' ; destruct HP' as [l4'' Heq' HP4''].
            symmetry in Heq'; decomp_map_inf Heq' ; subst.
            cbn in HP2 ; cbn in HP4a.
            apply (Permutation_Type_app_tail (ill2ll C :: l4b)) in HP4a.
            apply (Permutation_Type_app_head (map dual (map ill2ll l6))) in HP4a.
            assert (HP' := Permutation_Type_trans HP2 HP4a).
            rewrite <- (map_map _ _ l13) in HP'. 
            symmetry in HP4c ; apply Permutation_Type_map_inv in HP4c.
            destruct HP4c as [l4'' Heq' HP4c].
            symmetry in Heq'; decomp_map_inf Heq' ; subst.
            rewrite <- (map_map _ _ l14) in HP4b.
            cbn in HP4b ; cbn in HP'.
            apply (@Permutation_Type_cons _ (ill2ll C) _ eq_refl) in HP4b.
            apply (Permutation_Type_app_head (map dual (map ill2ll l6)
              ++ (map ill2ll l15 ++ map dual (map ill2ll l13)))) in HP4b.
            rewrite <- app_assoc in HP4b.
            assert (HP'' := Permutation_Type_trans HP' HP4b).
            specialize IHHll1 with (rev (l13 ++ l6 ++ l14)) (x0 :: l15 ++ l16) C.
            assert (x0 :: l15 ++ l16 <> nil) as Hnil
              by (intros Hnil ; inversion Hnil).
            inversion_clear Hoclm as [ | ? ? ? HF ].
            assert (Hoclm1 := Forall_inf_app_l _ _ HF).
            assert (Hoclm2 := Forall_inf_app_r _ _ HF).
            inversion_clear Hoclm2 as [ | ? ? Hoclm2' HF' ].
            inversion_clear Hoclm2'.
            cbn in HP4' ; cbn in HP4c.
            apply (Permutation_Type_Forall_inf HP4') in Hocl.
            apply (Permutation_Type_app_head l9) in HP4c.
            apply (Permutation_Type_Forall_inf HP4c) in Hocl.
            apply Forall_inf_app_r in Hocl.
            assert (Hocl' := Forall_inf_cons _ X0 Hocl).
            apply IHHll1 in Hocl' ; [ split | | ].
            ** apply (snd Hocl') with (igen x0 :: rev l4 ++ rev l11) in Hnil.
               eapply ex_ir ; [ apply Hnil | ].
               cbn ; rewrite Hperm ; cbn.
               cbn in HP3.
               apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
               cbn in HP4''.
               apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
               list_simpl ; Permutation_Type_solve.
            ** intros Hnil' lw.
               apply (snd Hocl') with (igen x0 :: rev l4 ++ rev l11 ++ lw) in Hnil.
               eapply ex_ir ; [ apply Hnil | ].
               cbn ; rewrite Hperm ; cbn.
               cbn in HP3.
               apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
               cbn in HP4''.
               apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
               list_simpl ; Permutation_Type_solve.
            ** constructor; try assumption.
               cbn in HP4''.
               apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
               apply (Permutation_Type_Forall_inf HP4'') in HF'.
               rewrite app_assoc in HF'.
               apply Forall_inf_app_l in HF'.
               assert (H4l := Forall_inf_app_l _ _ HF').
               assert (H4r := Forall_inf_app_r _ _ HF').
               cbn in HP3.
               apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
               apply (Permutation_Type_Forall_inf HP3) in Hoclm1.
               list_simpl in Hoclm1 ; apply Forall_inf_app_l in Hoclm1.
               list_simpl.
               apply Forall_inf_app; [ assumption | ].
               apply Forall_inf_app; assumption.
            ** list_simpl ; rewrite Hperm ; cbn.
               rewrite bidual; list_simpl.
               cons2app; rewrite <- (app_comm_cons _ _ (ill2ll x0)).
               apply Permutation_Type_cons_app.
               etransitivity; [ apply HP'' | ].
               cons2app; rewrite ? app_assoc; apply Permutation_Type_app_tail.
               Permutation_Type_solve.
      -- assert (HP4' := HP4).
         symmetry in HP4' ; apply Permutation_Type_vs_cons_inv in HP4'.
         destruct HP4' as [(l4a & l4b) Heq'].
         dichot_elt_app_inf_exec Heq' ; subst.
         ++ cbn in HP3 ; rewrite map_map in HP3.
            symmetry in HP3 ; apply Permutation_Type_map_inv in HP3 as [l3''' Heq' HP3].
            symmetry in Heq'; decomp_map_inf Heq'; subst.
            rewrite <- map_map in HP1.
            list_simpl in HP4 ; apply Permutation_Type_cons_app_inv in HP4.
            apply Permutation_Type_app_app_inv in HP4.
            destruct HP4 as [[[[l3a l3b] l3c] l3d] [[HP4' HP4''] [HP4''' HP4'''']]] ;
              cbn in HP4' ; cbn in HP4'' ; cbn in HP4''' ; cbn in HP4''''.
            apply Permutation_Type_app_app_inv in HP4''''.
            destruct HP4'''' as [[[[l3e l3f] l3g] l3h] [[HP4a HP4b] [HP4c HP4d]]] ;
              cbn in HP4a ; cbn in HP4b ; cbn in HP4c ; cbn in HP4d.
            cbn in HP1.
            apply (@Permutation_Type_cons _ (ill2ll C) _ eq_refl) in HP4a.
            apply (Permutation_Type_app HP4''') in HP4a.
            apply (Permutation_Type_app_head (map dual (map ill2ll l4))) in HP4a.
            assert (HP' := Permutation_Type_trans HP1 HP4a).
            symmetry in HP4' ; apply Permutation_Type_map_inv in HP4'.
            destruct HP4' as [l3' Heq' HP4'].
            symmetry in Heq'; decomp_map_inf Heq' ; subst.
            apply (Permutation_Type_app_head l3b) in HP4d.
            assert (HP'' := Permutation_Type_trans HP4'' HP4d).
            rewrite map_map in HP''.
            symmetry in HP'' ; apply Permutation_Type_map_inv in HP''.
            clear HP4'' ; destruct HP'' as [l4' Heq' HP4''].
            symmetry in Heq'; decomp_map_inf Heq' ; subst.
            rewrite <- (map_map _ _ l11) in HP'.
            rewrite <- (map_map _ _ l13) in HP'.
            cbn in HP4c. 
            symmetry in HP4c; apply Permutation_Type_map_inv in HP4c as [l4' Heq' HP4c].
            symmetry in Heq'; decomp_map_inf Heq'; subst.
            specialize IHHll2 with (rev (l4 ++ l11 ++ l13)) (x0_1 :: l9 ++ l15) C.
            cbn in HP4' ; apply (Permutation_Type_Forall_inf HP4') in Hocl.
            assert (Hocl1 := Forall_inf_app_l _ _ Hocl).
            assert (Hocl2 := Forall_inf_app_r _ _ Hocl).
            cbn in HP4c ; apply (Permutation_Type_Forall_inf HP4c) in Hocl2.
            apply Forall_inf_app_l in Hocl2.
            assert (Hocl3 := Forall_inf_app Hocl1 Hocl2).
            inversion Hoclm as [ | ? ? ? HF ].
            apply Forall_inf_app_r in HF.
            inversion HF as [ | ? ? Hoclm' HF']; inversion_clear Hoclm'.
            assert (Hocl4 := Forall_inf_cons _ X0 Hocl3).
            apply IHHll2 in Hocl4.
            ** assert (x0_1 :: l9 ++ l15 <> nil) as Hnil
                 by (intros Hnil ; inversion Hnil).
               split.
               --- apply (snd Hocl4) with (ilmap x0_1 x0_2 :: rev l6 ++ rev l14) in Hnil.
                   eapply ex_ir ; [ apply Hnil | ].
                   rewrite Hperm ; cbn.
                   apply Permutation_Type_elt.
                   cbn in HP3.
                   apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
                   cbn in HP4''.
                   apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
                   list_simpl ; Permutation_Type_solve.
               --- intros Hnil' lw.
                   apply (snd Hocl4) with (ilmap x0_1 x0_2 :: lw ++ rev l6 ++ rev l14)
                     in Hnil.
                   eapply ex_ir ; [ apply Hnil | ].
                   rewrite Hperm ; cbn.
                   rewrite <- app_assoc ; rewrite <- app_comm_cons ;
                     apply Permutation_Type_elt.
                   cbn in HP3.
                   apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
                   cbn in HP4''.
                   apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
                   list_simpl ; Permutation_Type_solve.
            ** constructor; try assumption.
               cbn in HP4''.
               apply Permutation_Type_rev' in HP4''.
               apply (Permutation_Type_Forall_inf HP4'') in HF'.
               list_simpl in HF'.
               apply Forall_inf_app_r in HF' as Hoclm1.
               inversion Hoclm as [ | ? ? ? HF'' ].
               apply Forall_inf_app_l in HF'' as Hoclm2.
               cbn in HP3.
               apply Permutation_Type_rev' in HP3.
               apply (Permutation_Type_Forall_inf HP3) in Hoclm2.
               list_simpl in Hoclm2.
               apply Forall_inf_app_r in Hoclm2.
               rewrite rev_app_distr.
               apply Forall_inf_app; list_simpl; assumption.
            ** cbn ; rewrite Hperm ; list_simpl.
               rewrite bidual; list_simpl.
               cons2app; rewrite <- (app_comm_cons _ _ (ill2ll x0_1));
                 apply Permutation_Type_cons_app.
               Permutation_Type_solve.
         ++ cbn in HP3 ; rewrite map_map in HP3.
            symmetry in HP3 ; apply Permutation_Type_map_inv in HP3 as [l3''' Heq' HP3].
            symmetry in Heq'; decomp_map_inf Heq'; subst.
            rewrite <- map_map in HP1.
            rewrite <- map_map in HP2.
            rewrite app_assoc in HP4 ; apply Permutation_Type_cons_app_inv in HP4.
            apply Permutation_Type_app_app_inv in HP4.
            destruct HP4 as [[[[l3a l3b] l3c] l3d] [[HP4' HP4''] [HP4''' HP4'''']]] ;
              cbn in HP4' ; cbn in HP4'' ; cbn in HP4''' ; cbn in HP4''''.
            apply Permutation_Type_app_app_inv in HP4'''.
            destruct HP4''' as [[[[l3e l3f] l3g] l3h] [[HP4a HP4b] [HP4c HP4d]]] ;
              cbn in HP4a ; cbn in HP4b ; cbn in HP4c ; cbn in HP4d.
            cbn in HP1.
            apply (Permutation_Type_app_head (map dual (map ill2ll l4))) in HP4a.
            assert (HP' := Permutation_Type_trans HP1 HP4a).
            symmetry in HP4' ; apply Permutation_Type_map_inv in HP4'.
            destruct HP4' as [l3' Heq' HP4'].
            symmetry in Heq'; decomp_map_inf Heq' ; subst.
            apply (Permutation_Type_app_tail l3d) in HP4d.
            assert (HP'' := Permutation_Type_trans HP4'' HP4d).
            rewrite map_map in HP''.
            symmetry in HP'' ; apply Permutation_Type_map_inv in HP''.
            clear HP4'' ; destruct HP'' as [l4'' Heq' HP4''].
            symmetry in Heq'; decomp_map_inf Heq' ; subst.
            rewrite <- (map_map _ _ l13) in HP'.
            symmetry in HP4c ; apply Permutation_Type_map_inv in HP4c.
            destruct HP4c as [l4'' Heq' HP4c].
            symmetry in Heq'; decomp_map_inf Heq' ; subst.
            rewrite <- (map_map _ _ l14) in HP4b.
            cbn in HP2 ; cbn in HP4'''' ; cbn in HP4b.
            apply (@Permutation_Type_cons _ (ill2ll C) _ eq_refl) in HP4''''.
            apply (Permutation_Type_app HP4b) in HP4''''.
            apply (Permutation_Type_app_head (map dual (map ill2ll l6))) in HP4''''.
            assert (HP'' := Permutation_Type_trans HP2 HP4'''').
            specialize IHHll2 with (rev (l4 ++ l13)) l15 x0_1.
            cbn in HP4'.
            apply (Permutation_Type_Forall_inf HP4') in Hocl.
            assert (Hocl1 := Forall_inf_app_l _ _ Hocl).
            assert (Hocl2 := Forall_inf_app_r _ _ Hocl).
            rewrite <- (map_map _ _ l12) in HP''.
            specialize IHHll1 with (rev (x0_2 :: l6 ++ l14 ++ l12)) (l10 ++ l16) C.
            cbn in HP4c.
            apply (Permutation_Type_Forall_inf HP4c) in Hocl1.
            assert (Hocl3 := Forall_inf_app_l _ _ Hocl1).
            assert (Hocl4 := Forall_inf_app_r _ _ Hocl1).
            assert (Hocl5 := Forall_inf_app Hocl2 Hocl4).
            apply IHHll2 in Hocl3 ; [ apply IHHll1 in Hocl5 | | ].
            ** split.
               --- destruct Hocl5 as [Hocl5 _].
                   destruct Hocl3 as [Hocl3 _].
                   apply (ex_ir _ (nil ++ rev (l4 ++ l13) ++
                                     ilmap x0_1 x0_2 :: rev (l6 ++ l14 ++ l12))).
                   +++ apply lmap_ilr; try assumption.
                       eapply ex_ir ; [ apply Hocl5 | ].
                       rewrite Hperm ; cbn ; Permutation_Type_solve.
                   +++ rewrite Hperm ; cbn.
                       cbn in HP3.
                       apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
                       cbn in HP4''.
                       apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
                       list_simpl ; Permutation_Type_solve.
               --- intros Hnil lw ; destruct lo ; [ contradiction Hnil ; reflexivity | ].
                   apply (Permutation_Type_app_tail l10) in HP4c.
                   assert (HP''' := Permutation_Type_trans HP4' HP4c).
                   symmetry in HP''' ; apply Permutation_Type_vs_cons_inv in HP'''.
                   destruct HP''' as [(l4l & l4r) Heq'].
                   rewrite <- app_assoc in Heq'.
                   dichot_elt_app_inf_exec Heq' ; subst.
                   +++ assert (l4l ++ i :: l <> nil) as Hnil'
                         by (intros Hnil' ; destruct l4l ; inversion Hnil').
                       apply (snd Hocl3) with lw in Hnil'.
                       destruct Hocl5 as [Hocl5 _].
                       apply (ex_ir _ (nil ++ (rev (l4 ++ l13) ++ lw) ++
                                     ilmap x0_1 x0_2 :: rev (l6 ++ l14 ++ l12))).
                       *** apply lmap_ilr; try assumption.
                           eapply ex_ir ; [ apply Hocl5 | ].
                           rewrite Hperm ; cbn ; Permutation_Type_solve.
                       *** rewrite Hperm ; cbn.
                           cbn in HP3.
                           apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
                           cbn in HP4''.
                           apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
                           list_simpl ; Permutation_Type_solve.
                   +++ assert (l17 ++ i :: l4r <> nil) as Hnil'
                         by (intros Hnil'; destruct l17; inversion Hnil').
                       rewrite Heq'1 in Hnil'.
                       assert (l10 ++ l16 <> nil) as Hnil''.
                       { intros Hnil''.
                         apply Hnil'.
                         clear - Hnil''.
                         apply app_eq_nil in Hnil''.
                         destruct Hnil''; subst; reflexivity. }
                       apply (snd Hocl5) with lw in Hnil''.
                       destruct Hocl3 as [Hocl3 _].
                       apply (ex_ir _ (lw ++ rev (l4 ++ l13) ++
                                     ilmap x0_1 x0_2 :: rev (l6 ++ l14 ++ l12))).
                       *** apply lmap_ilr; try assumption.
                           eapply ex_ir ; [ apply Hnil'' | ].
                           rewrite Hperm ; cbn ; Permutation_Type_solve.
                       *** rewrite Hperm ; cbn.
                           cbn in HP3.
                           apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
                           cbn in HP4''.
                           apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
                           list_simpl ; Permutation_Type_solve.
            ** inversion_clear Hoclm as [ | ? ? ? HF ].
               assert (Hoclm1 := Forall_inf_app_l _ _ HF).
               assert (Hoclm2 := Forall_inf_app_r _ _ HF).
               inversion_clear Hoclm2 as [ | ? ? Hoclm2' HF' ].
               inversion Hoclm2'; constructor; try assumption.
               cbn in HP3.
               apply Permutation_Type_rev' in HP3.
               apply (Permutation_Type_Forall_inf HP3) in Hoclm1.
               apply Forall_inf_rev.
               constructor; try assumption.
               apply Forall_inf_app.
               --- list_simpl in Hoclm1 ; apply Forall_inf_app_l in Hoclm1.
                   rewrite <- rev_involutive.
                   apply Forall_inf_rev.
                   apply Hoclm1.
               --- cbn in HP4''.
                   apply Permutation_Type_rev' in HP4''.
                   apply (Permutation_Type_Forall_inf HP4'') in HF'.
                   list_simpl in HF'.
                   assert (H4l := Forall_inf_app_l _ _ HF').
                   assert (H4r := Forall_inf_app_r _ _ HF').
                   apply Forall_inf_rev in H4l.
                   rewrite rev_involutive in H4l.
                   apply Forall_inf_app; [ | assumption ].
                   apply Forall_inf_app_l in H4r.
                   apply Forall_inf_rev in H4r.
                   rewrite rev_involutive in H4r; assumption.
            ** cbn ; rewrite Hperm ; cbn; list_simpl.
               rewrite app_comm_cons, 2 app_assoc; apply Permutation_Type_cons_app.
               list_simpl ; Permutation_Type_solve.
            ** inversion_clear Hoclm as [ | ? ? ? HF ].
               assert (Hoclm1 := Forall_inf_app_l _ _ HF).
               assert (Hoclm2 := Forall_inf_app_r _ _ HF).
               inversion_clear Hoclm2 as [ | ? ?  Hoclm2' HF' ].
               cbn in HP4''.
               apply Permutation_Type_rev' in HP4''.
               apply (Permutation_Type_Forall_inf HP4'') in HF'.
               list_simpl in HF'.
               assert (H4l := Forall_inf_app_l _ _ HF').
               assert (H4r := Forall_inf_app_r _ _ HF').
               apply Forall_inf_app_r in H4r.
               inversion_clear Hoclm2'; constructor; try assumption.
               list_simpl; apply Forall_inf_app; try assumption.
               cbn in HP3.
               apply Permutation_Type_rev' in HP3.
               apply (Permutation_Type_Forall_inf HP3) in Hoclm1.
               list_simpl in Hoclm1; apply Forall_inf_app_r in Hoclm1.
               apply Hoclm1.
            ** list_simpl ; rewrite Hperm ; cbn.
               rewrite bidual; list_simpl.
               apply Permutation_Type_cons; auto.
               Permutation_Type_solve.
      -- assert (HP4' := HP4).
         symmetry in HP4' ; apply Permutation_Type_vs_cons_inv in HP4'.
         destruct HP4' as [(l4a & l4b) Heq'].
         cbn in Heq' ; dichot_elt_app_inf_exec Heq' ; subst.
         ++ cbn in HP3 ; rewrite map_map in HP3.
            symmetry in HP3 ; apply Permutation_Type_map_inv in HP3.
            destruct HP3 as [l3''' Heq' HP3].
            symmetry in Heq'; decomp_map_inf Heq' ; subst.
            rewrite <- map_map in HP1.
            list_simpl in HP4 ; apply Permutation_Type_cons_app_inv in HP4.
            apply Permutation_Type_app_app_inv in HP4.
            destruct HP4 as [[[[l3a l3b] l3c] l3d] [[HP4' HP4''] [HP4''' HP4'''']]] ;
              cbn in HP4' ; cbn in HP4'' ; cbn in HP4''' ; cbn in HP4''''.
            apply Permutation_Type_app_app_inv in HP4''''.
            destruct HP4'''' as [[[[l3e l3f] l3g] l3h] [[HP4a HP4b] [HP4c HP4d]]] ;
              cbn in HP4a ; cbn in HP4b ; cbn in HP4c ; cbn in HP4d.
            cbn in HP1 ; cbn in HP4''' ; cbn in HP4a.
            apply (@Permutation_Type_cons _ (ill2ll C) _ eq_refl) in HP4a.
            apply (Permutation_Type_app HP4''') in HP4a.
            apply (Permutation_Type_app_head (map dual (map ill2ll l4))) in HP4a.
            assert (HP' := Permutation_Type_trans HP1 HP4a).
            symmetry in HP4' ; apply Permutation_Type_map_inv in HP4'.
            destruct HP4' as [l3' Heq' HP4'].
            symmetry in Heq'; decomp_map_inf Heq' ; subst.
            apply (Permutation_Type_app_head l3b) in HP4d.
            assert (HP'' := Permutation_Type_trans HP4'' HP4d).
            rewrite map_map in HP''.
            symmetry in HP'' ; apply Permutation_Type_map_inv in HP''.
            clear HP4''; destruct HP'' as [l4' Heq' HP4''].
            symmetry in Heq'; decomp_map_inf Heq'; subst.
            rewrite <- (map_map _ _ l11) in HP'.
            rewrite <- (map_map _ _ l13) in HP'.
            symmetry in HP4c; apply Permutation_Type_map_inv in HP4c as [l4' Heq' HP4c].
            symmetry in Heq'; decomp_map_inf Heq'; subst.
            specialize IHHll2 with (rev (l4 ++ l11 ++ l13)) (x0 :: l9 ++ l15) C.
            cbn in HP4' ; apply (Permutation_Type_Forall_inf HP4') in Hocl.
            assert (Hocl1 := Forall_inf_app_l _ _ Hocl).
            assert (Hocl2 := Forall_inf_app_r _ _ Hocl).
            cbn in HP4c ; apply (Permutation_Type_Forall_inf HP4c) in Hocl2.
            apply Forall_inf_app_l in Hocl2.
            assert (Hocl3 := Forall_inf_app Hocl1 Hocl2).
            inversion_clear Hoclm as [ | ? ? ? HF ].
            assert (HF'' := Forall_inf_app_l _ _ HF).
            apply Forall_inf_app_r in HF.
            inversion HF as [ | ? ? Hoclm' HF' ]; inversion_clear Hoclm'.
            assert (Hocl4 := Forall_inf_cons _ X0 Hocl3).
            apply IHHll2 in Hocl4.
            ** assert (x0 :: l9 ++ l15 <> nil) as Hnil
                 by (intros Hnil ; inversion Hnil).
               split.
               --- apply (snd Hocl4) with (ineg x0 :: rev l6 ++ rev l14) in Hnil.
                   eapply ex_ir ; [ apply Hnil | ].
                   rewrite Hperm ; cbn.
                   apply Permutation_Type_elt.
                   cbn in HP3.
                   apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
                   cbn in HP4''.
                   apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
                   list_simpl ; Permutation_Type_solve.
               --- intros Hnil' lw.
                   apply (snd Hocl4) with (ineg x0 :: lw ++ rev l6 ++ rev l14) in Hnil.
                   eapply ex_ir ; [ apply Hnil | ].
                   rewrite Hperm ; cbn.
                   rewrite <- app_assoc ; rewrite <- app_comm_cons ;
                     apply Permutation_Type_elt.
                   cbn in HP3.
                   apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
                   cbn in HP4''.
                   apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
                   list_simpl ; Permutation_Type_solve.
            ** constructor; try assumption.
               cbn in HP4''.
               apply Permutation_Type_rev' in HP4''.
               apply (Permutation_Type_Forall_inf HP4'') in HF'.
               list_simpl in HF'.
               apply Forall_inf_app_r in HF' as Hoclm1.
               cbn in HP3 ; apply Permutation_Type_rev' in HP3.
               apply (Permutation_Type_Forall_inf HP3) in HF''.
               list_simpl in HF''.
               apply Forall_inf_app_r in HF''.
               rewrite rev_app_distr.
               apply Forall_inf_app; list_simpl; assumption.
            ** cbn ; rewrite Hperm ; list_simpl.
               rewrite bidual; list_simpl.
               cons2app; rewrite <- (app_comm_cons _ _ (ill2ll x0));
                 apply Permutation_Type_cons_app.
               Permutation_Type_solve.
         ++ cbn in HP3 ; rewrite map_map in HP3.
            symmetry in HP3; apply Permutation_Type_map_inv in HP3 as [l3''' Heq' HP3].
            symmetry in Heq'; decomp_map_inf Heq'; subst.
            rewrite <- map_map in HP1.
            rewrite <- map_map in HP2.
            rewrite app_assoc in HP4 ; apply Permutation_Type_cons_app_inv in HP4.
            apply Permutation_Type_app_app_inv in HP4.
            destruct HP4 as [[[[l3a l3b] l3c] l3d] [[HP4' HP4''] [HP4''' HP4'''']]] ;
              cbn in HP4' ; cbn in HP4'' ; cbn in HP4''' ; cbn in HP4''''.
            apply Permutation_Type_app_app_inv in HP4'''.
            destruct HP4''' as [[[[l3e l3f] l3g] l3h] [[HP4a HP4b] [HP4c HP4d]]] ;
              cbn in HP4a ; cbn in HP4b ; cbn in HP4c ; cbn in HP4d.
            cbn in HP1 ; cbn in HP4a.
            apply (Permutation_Type_app_head (map dual (map ill2ll l4))) in HP4a.
            assert (HP' := Permutation_Type_trans HP1 HP4a).
            symmetry in HP4'; apply Permutation_Type_map_inv in HP4' as [l3' Heq' HP4'].
            symmetry in Heq'; decomp_map_inf Heq'; subst.
            apply (Permutation_Type_app_tail l3d) in HP4d.
            assert (HP'' := Permutation_Type_trans HP4'' HP4d).
            rewrite map_map in HP''.
            symmetry in HP''; apply Permutation_Type_map_inv in HP''.
            clear HP4''; destruct HP'' as [l4'' Heq' HP4''].
            symmetry in Heq'; decomp_map_inf Heq'; subst.
            rewrite <- (map_map _ _ l13) in HP'.
            symmetry in HP4c ; apply Permutation_Type_map_inv in HP4c.
            destruct HP4c as [l4'' Heq' HP4c].
            symmetry in Heq'; decomp_map_inf Heq' ; subst.
            rewrite <- (map_map _ _ l14) in HP4b.
            cbn in HP2 ; cbn in HP4'''' ; cbn in HP4b.
            apply (@Permutation_Type_cons _ (ill2ll C) _ eq_refl) in HP4''''.
            apply (Permutation_Type_app HP4b) in HP4''''.
            apply (Permutation_Type_app_head (map dual (map ill2ll l6))) in HP4''''.
            assert (HP'' := Permutation_Type_trans HP2 HP4'''').
            specialize IHHll2 with (rev (l4 ++ l13)) l15 x0.
            cbn in HP4' ; apply (Permutation_Type_Forall_inf HP4') in Hocl.
            assert (Hocl1 := Forall_inf_app_l _ _ Hocl).
            assert (Hocl2 := Forall_inf_app_r _ _ Hocl).
            rewrite <- (map_map _ _ l12) in HP''. 
            specialize IHHll1 with (rev (ivar atN :: l6 ++ l14 ++ l12)) (l10 ++ l16) C.
            cbn in HP4c ; apply (Permutation_Type_Forall_inf HP4c) in Hocl1.
            assert (Hocl3 := Forall_inf_app_l _ _ Hocl1).
            assert (Hocl4 := Forall_inf_app_r _ _ Hocl1).
            assert (Hocl5 := Forall_inf_app Hocl2 Hocl4).
            apply IHHll2 in Hocl3; [ apply IHHll1 in Hocl5 | | ].
            ** split.
               --- destruct Hocl5 as [Hocl5 _].
                   destruct Hocl3 as [Hocl3 _].
                   apply neg_map_rule with _ (rev l6 ++ rev l14) (rev l12) _ C in Hocl3.
                   +++ eapply ex_ir; [ apply Hocl3 | ].
                       rewrite Hperm; cbn.
                       rewrite app_assoc.
                       apply Permutation_Type_elt.
                       cbn in HP3.
                       apply Permutation_Type_rev' in HP3; list_simpl in HP3.
                       cbn in HP4''.
                       apply Permutation_Type_rev' in HP4''; list_simpl in HP4''.
                       list_simpl; Permutation_Type_solve.
                   +++ intros a Ha; apply (snd (Hgax a) Ha).
                   +++ eapply ex_ir; [ apply Hocl5 | ].
                       rewrite Hperm; cbn; Permutation_Type_solve.
               --- intros Hnil lw; destruct lo; [ contradiction Hnil; reflexivity | ].
                   apply (Permutation_Type_app_tail l10) in HP4c.
                   assert (HP''' := Permutation_Type_trans HP4' HP4c).
                   symmetry in HP'''.
                   apply Permutation_Type_vs_cons_inv in HP''' as [(l4l & l4r) Heq'].
                   rewrite <- app_assoc in Heq'.
                   cbn in Heq'; dichot_elt_app_inf_exec Heq'; subst.
                   +++ assert (l4l ++ i :: l <> nil) as Hnil'
                         by (intros Hnil'; destruct l4l; inversion Hnil').
                       apply (snd Hocl3) with lw in Hnil'.
                       destruct Hocl5 as [Hocl5 _].
                       apply neg_map_rule with _ (rev l6 ++ rev l14) (rev l12) _ C in Hnil'.
                       *** eapply ex_ir ; [ apply Hnil' | ].
                           rewrite Hperm ; cbn ; list_simpl.
                           rewrite 4 app_assoc.
                           apply Permutation_Type_elt.
                           cbn in HP3.
                           apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
                           cbn in HP4''.
                           apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
                           list_simpl ; Permutation_Type_solve.
                       *** intros a Ha ; apply (snd (Hgax a) Ha).
                       *** eapply ex_ir ; [ apply Hocl5 | ].
                           rewrite Hperm ; cbn ; Permutation_Type_solve.
                   +++ assert (l17 ++ i :: l4r <> nil) as Hnil'
                         by (intros Hnil'; destruct l17; inversion Hnil').
                       rewrite Heq'1 in Hnil'.
                       assert (l10 ++ l16 <> nil) as Hnil''.
                       { intros Hnil''.
                         apply Hnil'.
                         clear - Hnil''.
                         apply app_eq_nil in Hnil''.
                         destruct Hnil''; subst; reflexivity. }
                       apply (snd Hocl5) with lw in Hnil''.
                       destruct Hocl3 as [Hocl3 _].
                       apply neg_map_rule with _ (rev l6 ++ rev l14) (rev l12 ++ lw) _ C in Hocl3.
                       *** eapply ex_ir ; [ apply Hocl3 | ].
                           rewrite Hperm ; cbn ; list_simpl.
                           rewrite 3 app_assoc.
                           apply Permutation_Type_elt.
                           cbn in HP3.
                           apply Permutation_Type_rev' in HP3 ; list_simpl in HP3.
                           cbn in HP4''.
                           apply Permutation_Type_rev' in HP4'' ; list_simpl in HP4''.
                           list_simpl ; Permutation_Type_solve.
                       *** intros a Ha ; apply (snd (Hgax a) Ha).
                       *** eapply ex_ir ; [ apply Hnil'' | ].
                           rewrite Hperm ; cbn ; Permutation_Type_solve.
            ** inversion_clear Hoclm as [ | ? ? ? HF ].
               assert (Hoclm1 := Forall_inf_app_l _ _ HF).
               assert (Hoclm2 := Forall_inf_app_r _ _ HF).
               inversion_clear Hoclm2 as [ | ? ? Hoclm2' HF' ].
               inversion Hoclm2'; constructor; try assumption.
               cbn in HP3 ; apply Permutation_Type_rev' in HP3.
               apply (Permutation_Type_Forall_inf HP3) in Hoclm1.
               apply Forall_inf_rev.
               constructor ; [ | apply Forall_inf_app ].
               --- constructor.
               --- list_simpl in Hoclm1 ; apply Forall_inf_app_l in Hoclm1.
                   rewrite <- rev_involutive.
                   apply Forall_inf_rev.
                   apply Hoclm1.
               --- cbn in HP4'' ; apply Permutation_Type_rev' in HP4''.
                   apply (Permutation_Type_Forall_inf HP4'') in HF'.
                   list_simpl in HF'.
                   assert (H4l := Forall_inf_app_l _ _ HF').
                   assert (H4r := Forall_inf_app_r _ _ HF').
                   apply Forall_inf_rev in H4l.
                   rewrite rev_involutive in H4l.
                   apply Forall_inf_app; [ | assumption ].
                   apply Forall_inf_app_l in H4r.
                   apply Forall_inf_rev in H4r.
                   rewrite rev_involutive in H4r; assumption.
            ** cbn ; rewrite Hperm ; list_simpl.
               rewrite app_comm_cons, 2 app_assoc; apply Permutation_Type_cons_app.
               Permutation_Type_solve.
            ** inversion_clear Hoclm as [ | ? ? ? HF ].
               assert (Hoclm1 := Forall_inf_app_l _ _ HF).
               assert (Hoclm2 := Forall_inf_app_r _ _ HF).
               inversion_clear Hoclm2 as [ | ? ? Hoclm2' HF' ].
               cbn in HP4''; apply Permutation_Type_rev' in HP4''.
               apply (Permutation_Type_Forall_inf HP4'') in HF'.
               list_simpl in HF'.
               assert (H4l := Forall_inf_app_l _ _ HF').
               assert (H4r := Forall_inf_app_r _ _ HF').
               apply Forall_inf_app_r in H4r.
               inversion_clear Hoclm2'; constructor; try assumption.
               list_simpl ; apply Forall_inf_app; try assumption.
               cbn in HP3 ; apply Permutation_Type_rev' in HP3.
               apply (Permutation_Type_Forall_inf HP3) in Hoclm1.
               list_simpl in Hoclm1 ; apply Forall_inf_app_r in Hoclm1.
               apply Hoclm1.
            ** list_simpl ; rewrite Hperm ; cbn.
               rewrite bidual.
               apply Permutation_Type_cons; auto.
               Permutation_Type_solve.
- symmetry in HP; apply PCPermutation_Type_vs_cons_inv in HP as [(l', l'') HP Heq]; cbn in Heq, HP.
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  + specialize IHHll with (l0 ++ C1 :: nil) lo C2.
    apply IHHll in Hocl.
    * destruct Hocl as [IH1 IH2].
      split.
      -- apply lpam_irr; assumption.
      -- intros Hnil l2.
         assert (IH := IH2 Hnil l2).
         list_simpl in IH.
         list_simpl ; apply lpam_irr.
         eapply ex_ir; [ eassumption | ].
         rewrite Hperm ; cbn ; Permutation_Type_solve.
    * inversion_clear Hoclm as [ | ? ?  Hoclm' ].
      inversion_clear Hoclm'.
      constructor; try assumption.
      apply Forall_inf_app; [ assumption | ].
      constructor; [ assumption | constructor ].
    * cbn in HP ; rewrite Hperm in HP ; cbn in HP.
      cbn ; rewrite Hperm ; cbn.
      apply Permutation_Type_cons; auto; list_simpl.
      apply Permutation_Type_cons_app.
      Permutation_Type_solve.
  + specialize IHHll with (l0 ++ C :: nil) lo N.
    apply IHHll in Hocl.
    * destruct Hocl as [IH1 IH2].
      split.
      -- apply gen_irr; assumption.
      -- intros Hnil l2.
         assert (IH := IH2 Hnil l2).
         list_simpl in IH.
         list_simpl ; apply gen_irr.
         eapply ex_ir; [ eassumption | ].
         rewrite Hperm ; list_simpl.
         apply Permutation_Type_app_head.
         GPermutation_Type_solve.
    * inversion_clear Hoclm as [ | ? ? Hoclm' ].
      inversion_clear Hoclm'.
      constructor; try assumption.
      -- constructor.
      -- apply Forall_inf_app; try assumption.
         constructor ; [ | constructor ]; assumption.
    * cbn in HP ; rewrite Hperm in HP ; cbn in HP.
      cbn ; rewrite Hperm ; cbn.
      apply Permutation_Type_cons; auto; list_simpl.
      apply Permutation_Type_cons_app.
      Permutation_Type_solve.
  + specialize IHHll with (C1 :: l0) lo C2.
    apply IHHll in Hocl.
    * destruct Hocl as [IH1 IH2].
      split.
      -- apply lmap_irr; assumption.
      -- intros Hnil l2.
         assert (IH := IH2 Hnil l2).
         list_simpl in IH.
         list_simpl ; apply lmap_irr; assumption.
    * inversion_clear Hoclm as [ | ? ? Hoclm' ].
      inversion_clear Hoclm'.
      constructor; [ assumption | ].
      constructor; assumption.
    * cbn in HP ; rewrite Hperm in HP ; cbn in HP.
      cbn ; rewrite Hperm ; cbn.
      rewrite app_comm_cons, app_assoc; apply Permutation_Type_cons_app.
      apply Permutation_Type_cons; auto.
  + specialize IHHll with (C :: l0) lo N.
    apply IHHll in Hocl.
    * destruct Hocl as [IH1 IH2].
      split.
      -- apply neg_irr; assumption.
      -- intros Hnil l2.
         assert (IH := IH2 Hnil l2).
         list_simpl in IH.
         list_simpl ; apply neg_irr; assumption.
    * inversion_clear Hoclm as [ | ? ? Hoclm' ].
      inversion_clear Hoclm'.
      constructor; try assumption.
      -- constructor.
      -- constructor; assumption.
    * cbn in HP ; rewrite Hperm in HP ; cbn in HP.
      cbn ; rewrite Hperm ; cbn.
      rewrite app_comm_cons, app_assoc; apply Permutation_Type_cons_app.
      apply Permutation_Type_cons; auto.
  + symmetry in H1 ; dichot_elt_app_inf_exec H1 ; subst;
    [ symmetry in H0; decomp_map_inf H0 ; destruct x ; inversion H0
    | list_simpl in H2 ; symmetry in H2; decomp_map_inf H2 ; symmetry in H3; decomp_map_inf H3 ;
                         destruct x ; inversion H2 ; destruct x0 ; inversion H3 ] ;
      cbn in H3 ; cbn in H5 ; subst.
    * exfalso.
      apply Forall_inf_app_r in Hocl.
      inversion Hocl as [ | ? ? Hocl'].
      inversion Hocl'.
    * exfalso.
      apply Forall_inf_app_r in Hocl.
      inversion Hocl as [ | ? ? Hocl'].
      inversion Hocl'.
    * exfalso.
      apply Forall_inf_app_r in Hocl.
      inversion Hocl as [ | ? ? Hocl'].
      inversion Hocl'.
    * exfalso.
      apply Forall_inf_app_r in Hocl.
      inversion Hocl as [ | ? ? Hocl'].
      inversion Hocl'.
    * apply (f_equal (@rev _)) in H6 ; list_simpl in H6 ; subst.
      apply (@PEPermutation_Type_cons _ _ _ (dual (ill2ll x0_1)) eq_refl) in HP.
      apply (@PEPermutation_Type_cons _ _ _ (dual (ill2ll x0_2)) eq_refl) in HP.
      apply PEPermutation_PCPermutation_Type in HP ; unfold id in HP.
      rewrite 2 app_comm_cons in HP.
      assert (HP' := PCPermutation_Type_trans _ _ _ _ HP (PCPermutation_Type_app_comm _ _ _)).
      specialize IHHll with (rev (x0_2 :: x0_1 :: l8) ++ rev l6) lo C.
      list_simpl in IHHll ; list_simpl in HP' ; apply IHHll in HP'; try assumption.
      -- destruct HP' as [IH1 IH2].
         split.
         ++ apply tens_ilr; assumption.
         ++ intros Hnil l2.
            assert (IH := IH2 Hnil l2).
            list_simpl in IH.
            list_simpl ; apply tens_ilr; assumption.
      -- inversion Hoclm as [ | ? ? ? HF ]; constructor; try assumption.
         assert (Hl := Forall_inf_app_l _ _ HF).
         assert (Hr := Forall_inf_app_r _ _ HF).
         apply Forall_inf_app; [ assumption | ].
         inversion Hr as [ | ? ? Hr' ].
         inversion Hr'.
         constructor; [ | constructor ]; assumption.
- symmetry in HP; apply PCPermutation_Type_vs_cons_inv in HP as [(l', l'') HP Heq].
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  + split ; intros ; apply top_irr.
  + symmetry in H1 ; dichot_elt_app_inf_exec H1 ; subst ;
      [ symmetry in H0; decomp_map_inf H0 ; destruct x ; inversion H0
      | list_simpl in H2 ; symmetry in H2; decomp_map_inf H2 ; symmetry in H3; decomp_map_inf H3 ;
                           destruct x ; inversion H2 ; destruct x0 ; inversion H3 ] ; subst.
    * exfalso.
      apply Forall_inf_app_r in Hocl; inversion Hocl as [ | ? ?  Hocl' ].
      inversion Hocl'.
    * apply (f_equal (@rev _)) in H6 ; list_simpl in H6 ; subst.
      split ; intros ; list_simpl ; apply zero_ilr.
- symmetry in HP; apply PCPermutation_Type_vs_cons_inv in HP as [(l', l'') HP Heq].
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  + apply (@PEPermutation_Type_cons _ _ _ (ill2ll C1) eq_refl) in HP.
    apply PEPermutation_PCPermutation_Type in HP ; unfold id in HP.
    rewrite app_comm_cons in HP.
    assert (HP' := PCPermutation_Type_trans _ _ _ _ HP (PCPermutation_Type_app_comm _ _ _)).
    specialize IHHll with l0 lo C1.
    list_simpl in IHHll ; list_simpl in HP' ; apply IHHll in HP'; try assumption.
    * destruct HP' as [IH1 IH2].
      split.
      -- apply plus_irr1; assumption.
      -- intros Hnil l2.
         assert (IH := IH2 Hnil l2).
         list_simpl in IH.
         list_simpl ; apply plus_irr1; assumption.
    * inversion_clear Hoclm as [ | ? ? Hoclm' ].
      inversion_clear Hoclm'.
      constructor; assumption.
  + symmetry in H1 ; dichot_elt_app_inf_exec H1 ; subst ;
    [ symmetry in H0; decomp_map_inf H0 ; destruct x ; inversion H0
    | list_simpl in H2 ; symmetry in H2; decomp_map_inf H2 ; symmetry in H3; decomp_map_inf H3 ;
                         destruct x ; inversion H2 ; destruct x0 ; inversion H3 ] ;
      cbn in H3 ; cbn in H5 ; subst.
    * apply (@PEPermutation_Type_cons _ _ _ (ill2ll x1) eq_refl) in HP.
      apply PEPermutation_PCPermutation_Type in HP ; unfold id in HP.
      rewrite app_comm_cons in HP.
      assert (HP' := PCPermutation_Type_trans _ _ _ _ HP (PCPermutation_Type_app_comm _ _ _)).
      specialize IHHll with l0 (l3 ++ x1 :: l5) C.
      list_simpl in IHHll ; list_simpl in HP' ; apply IHHll in HP'; try assumption.
      -- destruct HP' as [IH1 IH2].
         split; try assumption.
         intros _ l2.
         apply IH2.
         intros Hnil ; destruct l3 ; inversion Hnil.
      -- assert (Hocll := Forall_inf_app_l _ _ Hocl).
         assert (Hoclr := Forall_inf_app_r _ _ Hocl).
         apply Forall_inf_app; [ assumption | ].
         inversion Hoclr as [ | ? ? Hocl'].
         inversion Hocl'.
         constructor; assumption.
    * apply (f_equal (@rev _)) in H6 ; list_simpl in H6 ; subst.
      apply (@PEPermutation_Type_cons _ _ _ (dual (ill2ll x0_1)) eq_refl) in HP.
      apply PEPermutation_PCPermutation_Type in HP ; unfold id in HP.
      rewrite app_comm_cons in HP.
      assert (HP' := PCPermutation_Type_trans _ _ _ _ HP (PCPermutation_Type_app_comm _ _ _)).
      specialize IHHll with (rev (x0_1 :: l8) ++ rev l6) lo C.
      list_simpl in IHHll ; list_simpl in HP' ; apply IHHll in HP'; try assumption.
      -- destruct HP' as [IH1 IH2].
         split.
         ++ apply with_ilr1; assumption.
         ++ intros Hnil l2.
            assert (IH := IH2 Hnil l2).
            list_simpl in IH.
            list_simpl ; apply with_ilr1; assumption.
      -- inversion_clear Hoclm as [ | ? ? ? HF ]; constructor; try assumption.
         assert (Hl := Forall_inf_app_l _ _ HF).
         assert (Hr := Forall_inf_app_r _ _ HF).
         apply Forall_inf_app; [ assumption | ].
         inversion Hr as [ | ? ? Hr' ].
         inversion Hr'.
         constructor; assumption.
- symmetry in HP; apply PCPermutation_Type_vs_cons_inv in HP as [(l', l'') HP Heq].
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  + apply (@PEPermutation_Type_cons _ _ _ (ill2ll C2) eq_refl) in HP.
    apply PEPermutation_PCPermutation_Type in HP ; unfold id in HP.
    rewrite app_comm_cons in HP.
    assert (HP' := PCPermutation_Type_trans _ _ _ _ HP (PCPermutation_Type_app_comm _ _ _)).
    specialize IHHll with l0 lo C2.
    list_simpl in IHHll ; list_simpl in HP' ; apply IHHll in HP'; try assumption.
    * destruct HP' as [IH1 IH2].
      split.
      -- apply plus_irr2; assumption.
      -- intros Hnil l2.
         assert (IH := IH2 Hnil l2).
         list_simpl in IH.
         list_simpl ; apply plus_irr2; assumption.
    * inversion_clear Hoclm as [ | ? ? Hoclm' ].
      inversion_clear Hoclm'.
      constructor; assumption.
  + symmetry in H1 ; dichot_elt_app_inf_exec H1 ; subst ;
    [ symmetry in H0; decomp_map_inf H0 ; destruct x ; inversion H0
    | list_simpl in H2 ; symmetry in H2; decomp_map_inf H2 ; symmetry in H3; decomp_map_inf H3 ;
                         destruct x ; inversion H2 ; destruct x0 ; inversion H3 ] ;
      cbn in H3 ; cbn in H5 ; subst.
    * apply (@PEPermutation_Type_cons _ _ _ (ill2ll x2) eq_refl) in HP.
      apply PEPermutation_PCPermutation_Type in HP ; unfold id in HP.
      rewrite app_comm_cons in HP.
      assert (HP' := PCPermutation_Type_trans _ _ _ _ HP (PCPermutation_Type_app_comm _ _ _)).
      specialize IHHll with l0 (l3 ++ x2 :: l5) C.
      list_simpl in IHHll ; list_simpl in HP' ; apply IHHll in HP'; try assumption.
      -- destruct HP' as [IH1 IH2].
         split; try assumption.
         intros _ l2.
         apply IH2.
         intros Hnil ; destruct l3 ; inversion Hnil.
      -- assert (Hocll := Forall_inf_app_l _ _ Hocl).
         assert (Hoclr := Forall_inf_app_r _ _ Hocl).
         apply Forall_inf_app; [ assumption | ].
         inversion Hoclr as [ | ? ?  Hoclr' ].
         inversion Hoclr'.
         constructor; assumption.
    * apply (f_equal (@rev _)) in H6 ; list_simpl in H6 ; subst.
      apply (@PEPermutation_Type_cons _ _ _ (dual (ill2ll x0_2)) eq_refl) in HP.
      apply PEPermutation_PCPermutation_Type in HP ; unfold id in HP.
      rewrite app_comm_cons in HP.
      assert (HP' := PCPermutation_Type_trans _ _ _ _ HP (PCPermutation_Type_app_comm _ _ _)).
      specialize IHHll with (rev (x0_2 :: l8) ++ rev l6) lo C.
      list_simpl in IHHll ; list_simpl in HP' ; apply IHHll in HP'; try assumption.
      -- destruct HP' as [IH1 IH2].
         split.
         ++ apply with_ilr2; assumption.
         ++ intros Hnil l2.
            assert (IH := IH2 Hnil l2).
            list_simpl in IH.
            list_simpl ; apply with_ilr2; assumption.
      -- inversion_clear Hoclm as [ | ? ? ? HF ]; constructor; try assumption.
         assert (Hl := Forall_inf_app_l _ _ HF).
         assert (Hr := Forall_inf_app_r _ _ HF).
         apply Forall_inf_app; [ assumption | ].
         inversion Hr as [ | ? ? Hr' ].
         inversion Hr'.
         constructor; assumption.
- symmetry in HP; apply PCPermutation_Type_vs_cons_inv in HP as [(l', l'') HP Heq].
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  + assert (HP1 := HP).
    apply (@PEPermutation_Type_cons _ _ _ (ill2ll C1) eq_refl) in HP1.
    apply PEPermutation_PCPermutation_Type in HP1 ; unfold id in HP1.
    rewrite app_comm_cons in HP1.
    assert (HP1' := PCPermutation_Type_trans _ _ _ _ HP1 (PCPermutation_Type_app_comm _ _ _)).
    specialize IHHll1 with l0 lo C1.
    list_simpl in IHHll1 ; list_simpl in HP1' ; apply IHHll1 in HP1'; try assumption.
    * destruct HP1' as [IH1 IH2].
      apply (@PEPermutation_Type_cons _ _ _ (ill2ll C2) eq_refl) in HP.
      apply PEPermutation_PCPermutation_Type in HP ; unfold id in HP.
      rewrite app_comm_cons in HP.
      assert (HP2' := PCPermutation_Type_trans _ _ _ _ HP (PCPermutation_Type_app_comm _ _ _)).
      specialize IHHll2 with l0 lo C2.
      list_simpl in IHHll2 ; list_simpl in HP2' ; apply IHHll2 in HP2'; try assumption.
      -- destruct HP2' as [IH3 IH4].
         split.
         ++ apply with_irr; assumption.
         ++ intros Hnil l2.
            assert (IH := IH2 Hnil l2).
            assert (IH' := IH4 Hnil l2).
            list_simpl in IH ; list_simpl in IH'.
            list_simpl ; apply with_irr; assumption.
      -- inversion_clear Hoclm as [ | ? ? Hoclm' ].
         inversion_clear Hoclm'.
         constructor; assumption.
    * inversion_clear Hoclm as [ | ? ? Hoclm' ].
      inversion_clear Hoclm'.
      constructor; assumption.
  + symmetry in H1 ; dichot_elt_app_inf_exec H1 ; subst ;
    [ symmetry in H0; decomp_map_inf H0 ; destruct x ; inversion H0
    | list_simpl in H2 ; symmetry in H2; decomp_map_inf H2 ; symmetry in H3; decomp_map_inf H3 ;
                         destruct x ; inversion H2 ; destruct x0 ; inversion H3 ] ;
      cbn in H3 ; cbn in H5 ; subst.
    * assert (Hocll := Forall_inf_app_l _ _ Hocl).
      assert (Hoclr := Forall_inf_app_r _ _ Hocl).
      inversion Hoclr as [ | ? ? Hoclr' ].
      inversion Hoclr'.
      -- apply (@PEPermutation_Type_cons _ _ _ (ill2ll x1) eq_refl) in HP.
         apply PEPermutation_PCPermutation_Type in HP ; unfold id in HP.
         rewrite app_comm_cons in HP.
         assert (HP' := PCPermutation_Type_trans _ _ _ _ HP (PCPermutation_Type_app_comm _ _ _)).
         specialize IHHll1 with l0 (l3 ++ x1 :: l5) C.
         list_simpl in IHHll1 ; list_simpl in HP' ; apply IHHll1 in HP'; try assumption.
         ++ destruct HP' as [IH1 IH2].
            split; try assumption.
            intros _ l2.
            apply IH2.
            intros Hnil ; destruct l3 ; inversion Hnil.
         ++ apply Forall_inf_app; [ | constructor ]; assumption.
      -- apply (@PEPermutation_Type_cons _ _ _ (ill2ll x2) eq_refl) in HP.
         apply PEPermutation_PCPermutation_Type in HP ; unfold id in HP.
         rewrite app_comm_cons in HP.
         assert (HP' := PCPermutation_Type_trans _ _ _ _ HP (PCPermutation_Type_app_comm _ _ _)).
         specialize IHHll2 with l0 (l3 ++ x2 :: l5) C.
         list_simpl in IHHll2 ; list_simpl in HP' ; apply IHHll2 in HP'; try assumption.
         ++ destruct HP' as [IH1 IH2].
            split; try assumption.
            intros _ l2.
            apply IH2.
            intros Hnil ; destruct l3 ; inversion Hnil.
         ++ apply Forall_inf_app; [ | constructor ]; assumption.
    * apply (f_equal (@rev _)) in H6 ; list_simpl in H6 ; subst.
      assert (HP1 := HP).
      apply (@PEPermutation_Type_cons _ _ _ (dual (ill2ll x0_1)) eq_refl) in HP1.
      apply PEPermutation_PCPermutation_Type in HP1 ; unfold id in HP1.
      rewrite app_comm_cons in HP1.
      assert (HP1' := PCPermutation_Type_trans _ _ _ _ HP1 (PCPermutation_Type_app_comm _ _ _)).
      specialize IHHll1 with (rev (x0_1 :: l8) ++ rev l6) lo C.
      list_simpl in IHHll1 ; list_simpl in HP1' ; apply IHHll1 in HP1'; try assumption.
      -- destruct HP1' as [IH1 IH2].
         apply (@PEPermutation_Type_cons _ _ _ (dual (ill2ll x0_2)) eq_refl) in HP.
         apply PEPermutation_PCPermutation_Type in HP ; unfold id in HP.
         rewrite app_comm_cons in HP.
         assert (HP2' := PCPermutation_Type_trans _ _ _ _ HP (PCPermutation_Type_app_comm _ _ _)).
         specialize IHHll2 with (rev (x0_2 :: l8) ++ rev l6) lo C.
         list_simpl in IHHll2 ; list_simpl in HP2' ; apply IHHll2 in HP2'; try assumption.
         ++ destruct HP2' as [IH3 IH4].
            split.
            ** apply plus_ilr; assumption.
            ** intros Hnil l2.
               assert (IH5 := IH2 Hnil l2).
               list_simpl in IH5.
               assert (IH6 := IH4 Hnil l2).
               list_simpl in IH6.
               list_simpl ; apply plus_ilr; assumption.
         ++ inversion Hoclm as [ | ? ? ? HF]; constructor; try assumption.
            assert (Hl := Forall_inf_app_l _ _ HF).
            assert (Hr := Forall_inf_app_r _ _ HF).
            apply Forall_inf_app; [ assumption | ].
            inversion Hr as [ | ? ? Hr' ].
            inversion Hr'.
            constructor; assumption.
      -- inversion Hoclm as [ | ? ? ? HF ]; constructor; try assumption.
         assert (Hl := Forall_inf_app_l _ _ HF).
         assert (Hr := Forall_inf_app_r _ _ HF).
         apply Forall_inf_app; [ assumption | ].
         inversion Hr as [ | ? ? Hr' ].
         inversion Hr'.
         constructor; assumption.
- symmetry in HP; apply PCPermutation_Type_vs_cons_inv in HP as [(l', l'') HP Heq].
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  + symmetry in HP ; apply PEPermutation_Type_map_inv in HP.
    destruct HP as [l'' Heq' HPE] ; cbn in Heq'.
    symmetry in Heq'; decomp_map_inf Heq'.
    destruct lo ; destruct l4 ; inversion Heq'3 ; subst.
    * split.
      -- list_simpl in Heq'4.
         apply ill2ll_map_ioc_inv in Heq'4.
         destruct Heq'4 as [l2' Heq' Heq''] ; subst.
         apply (f_equal (@rev _)) in Heq' ; list_simpl in Heq' ; subst.
         specialize IHHll with ((rev (map ioc l2'))) nil C.
         destruct l3 ; inversion Heq'2.
         apply IHHll in Hocl; try assumption.
         ++ list_simpl in Hocl ; destruct Hocl as [Hocl _].
            apply oc_irr; assumption.
         ++ inversion_clear Hoclm as [ | ? ? Hoclm' ].
            inversion_clear Hoclm'.
            list_simpl ; constructor; assumption.
         ++ etransitivity.
            ** apply PEPermutation_PCPermutation_Type.
               list_simpl in HPE.
               apply (PEPermutation_Type_map _ wn) in HPE.
               apply PEPermutation_Type_cons ; [reflexivity | eassumption].
            ** list_simpl; rewrite ill2ll_map_ioc; reflexivity.
      -- intros Hnil; contradiction Hnil; reflexivity.
    * exfalso ; destruct i ; inversion H1.
  + exfalso.
    symmetry in H1 ; dichot_elt_app_inf_exec H1 ; subst ;
    [ symmetry in H0; decomp_map_inf H0 ; destruct x ; inversion H0
    | list_simpl in H2 ; symmetry in H2; decomp_map_inf H2 ; symmetry in H3; decomp_map_inf H3 ;
                         destruct x ; inversion H2 ; destruct x0 ; inversion H3 ] ; subst.
    symmetry in HP ; apply PEPermutation_Type_map_inv in HP.
    destruct HP as [l'' Heq' _] ; cbn in Heq'.
    symmetry in Heq'; decomp_map_inf Heq'.
    destruct C ; inversion Heq'1.
- symmetry in HP; apply PCPermutation_Type_vs_cons_inv in HP as [(l', l'') HP Heq].
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  symmetry in H1 ; dichot_elt_app_inf_exec H1 ; subst ;
    [ symmetry in H0; decomp_map_inf H0 ; destruct x ; inversion H0
    | list_simpl in H2 ; symmetry in H2; decomp_map_inf H2 ; symmetry in H3; decomp_map_inf H3 ;
                         destruct x ; inversion H2 ; destruct x0 ; inversion H3 ] ;
      cbn in H3 ; cbn in H5 ; subst.
  apply (f_equal (@rev _)) in H6 ; list_simpl in H6 ; subst.
  apply (@PEPermutation_Type_cons _ _ _ (dual (ill2ll x0)) eq_refl) in HP.
  apply PEPermutation_PCPermutation_Type in HP ; unfold id in HP.
  rewrite app_comm_cons in HP.
  assert (HP' := PCPermutation_Type_trans _ _ _ _ HP (PCPermutation_Type_app_comm _ _ _)).
  specialize IHHll with (rev (x0 :: l8) ++ rev l6) lo C.
  list_simpl in IHHll ; list_simpl in HP' ; apply IHHll in HP'; try assumption.
  + destruct HP' as [IH1 IH2].
    split.
    * apply de_ilr; assumption.
    * intros Hnil l2.
      assert (IH := IH2 Hnil l2).
      list_simpl in IH.
      list_simpl ; apply de_ilr; assumption.
  + inversion Hoclm as [ | ? ? ? HF ]; constructor; try assumption.
    assert (Hl := Forall_inf_app_l _ _ HF).
    assert (Hr := Forall_inf_app_r _ _ HF).
    apply Forall_inf_app; [ assumption | ].
    inversion Hr as [ | ? ? Hr' ].
    inversion Hr'.
    constructor; assumption.
- symmetry in HP; apply PCPermutation_Type_vs_cons_inv in HP as [(l', l'') HP Heq].
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  symmetry in H1 ; dichot_elt_app_inf_exec H1 ; subst ;
    [ symmetry in H0; decomp_map_inf H0 ; destruct x ; inversion H0
    | list_simpl in H2 ; symmetry in H2; decomp_map_inf H2 ; symmetry in H3; decomp_map_inf H3 ;
                         destruct x ; inversion H2 ; destruct x0 ; inversion H3 ] ;
      cbn in H3 ; cbn in H5 ; subst.
  apply (f_equal (@rev _)) in H6 ; list_simpl in H6 ; subst.
  apply PEPermutation_PCPermutation_Type in HP ; unfold id in HP.
  rewrite app_comm_cons in HP.
  assert (HP' := PCPermutation_Type_trans _ _ _ _ HP (PCPermutation_Type_app_comm _ _ _)).
  specialize IHHll with (rev l8 ++ rev l6) lo C.
  list_simpl in IHHll ; list_simpl in HP' ; apply IHHll in HP'; try assumption.
  + destruct HP' as [IH1 IH2].
    split.
    * apply wk_ilr; assumption.
    * intros Hnil l2.
      assert (IH := IH2 Hnil l2).
      list_simpl in IH.
      list_simpl ; apply wk_ilr; assumption.
  + inversion Hoclm as [ | ? ? ? HF ]; constructor; try assumption.
    assert (Hl := Forall_inf_app_l _ _ HF).
    assert (Hr := Forall_inf_app_r _ _ HF).
    apply Forall_inf_app; [ assumption | ].
    inversion Hr; assumption.
- symmetry in HP; apply PCPermutation_Type_vs_cons_inv in HP as [(l', l'') HP Heq].
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  symmetry in H1 ; dichot_elt_app_inf_exec H1 ; subst ;
    [ symmetry in H0; decomp_map_inf H0 ; destruct x ; inversion H0
    | list_simpl in H2 ; symmetry in H2; decomp_map_inf H2 ; symmetry in H3; decomp_map_inf H3 ;
                         destruct x ; inversion H2 ; destruct x0 ; inversion H3 ] ;
      cbn in H3 ; cbn in H5 ; subst.
  apply (f_equal (@rev _)) in H6 ; list_simpl in H6 ; subst.
  assert (PCPermutation_Type (ipperm P) (wn (dual (ill2ll x0)) :: wn (dual (ill2ll x0)) :: l)
         (ill2ll C :: map ill2ll lo
          ++ map dual (map ill2ll (l6 ++ ioc x0 :: ioc x0 :: l8)))) as HP'.
  { apply (@PEPermutation_Type_cons _ _ _ (wn (dual (ill2ll x0))) eq_refl) in HP.
    apply (@PEPermutation_Type_cons _ _ _ (wn (dual (ill2ll x0))) eq_refl) in HP.
    apply PEPermutation_PCPermutation_Type in HP.
    unfold id in HP ; cbn in HP.
    etransitivity; [ apply HP | ].
    GPermutation_Type_solve. }
  specialize IHHll with (rev (ioc x0 :: ioc x0 :: l8) ++ rev l6) lo C.
  list_simpl in IHHll ; list_simpl in HP' ;  apply IHHll in HP'; try assumption.
  + destruct HP' as [IH1 IH2].
    split.
    * eapply ex_ir ; [ apply co_ilr | ].
      -- rewrite app_nil_l.
         eapply ex_ir ; [ apply IH1 | ].
         rewrite Hperm ; cbn.
         symmetry ; apply Permutation_Type_cons_app.
         apply Permutation_Type_cons_app.
         reflexivity.
      -- rewrite Hperm ; cbn ; Permutation_Type_solve.
    * intros Hnil l2.
      assert (IH := IH2 Hnil l2).
      list_simpl in IH.
      eapply ex_ir ; [ apply co_ilr | ].
      -- rewrite app_nil_l.
         eapply ex_ir ; [ apply IH | ].
         rewrite Hperm ; cbn.
         symmetry ; apply Permutation_Type_cons_app.
         apply Permutation_Type_cons_app.
         reflexivity.
      -- rewrite Hperm ; cbn ; Permutation_Type_solve.
  + inversion Hoclm as [ | ? ? ? HF ]; constructor; try assumption.
    assert (Hl := Forall_inf_app_l _ _ HF).
    assert (Hr := Forall_inf_app_r _ _ HF).
    apply Forall_inf_app; [ assumption | ].
    inversion Hr as [ | ? ? Hr' ].
    inversion Hr'.
    constructor; assumption.
- cbn in f; rewrite f in Hcut; inversion Hcut.
- destruct lo.
  + apply (snd (fst (Hgax a))) in HP.
    split; [ assumption | ].
    intros Hnil; contradiction Hnil; reflexivity.
  + exfalso.
    inversion_clear Hocl as [ | ? ? ? HF ].
    cbn in HP ; rewrite <- (app_nil_l (ill2ll i :: _)) in HP.
    rewrite app_comm_cons in HP.
    apply PCPermutation_Type_vs_elt_inv in HP; destruct HP as [(l1,l2) _ Heq]; cbn in Heq.
    destruct l1; inversion Heq as [[Heq' Heq'']].
    * symmetry in Heq'; apply (snd (fst (fst (Hgax a))) i); assumption.
    * apply (f_equal (@rev _)) in Heq''.
      rewrite rev_involutive in Heq''; list_simpl in Heq''.
      rewrite map_map in Heq''.
      decomp_map Heq''.
      apply (f_equal dual) in Heq''3.
      rewrite bidual in Heq''3.
      apply (f_equal (map ill2ll)) in Heq''; list_simpl in Heq''.
      apply (fst (fst (fst (Hgax a))) i); [ | assumption ].
      rewrite <- Heq'', Heq''3.
      apply in_inf_elt.
Qed.

Proposition ll_to_ill_oclpam_axfree P : ipperm P = true ->
  (projT1 (ipgax P) -> False) -> forall l,
  ll (i2pfrag P) l -> forall l0 C, Forall_inf oclpam (C :: l0) ->
    Permutation_Type l (ill2ll C :: rev (map dual (map ill2ll l0))) ->
      ill P l0 C.
Proof.
intros Hperm P_axfree l pi l0 C Hoclm HP.
apply cut_admissible_axfree in pi; [ | assumption ].
rewrite cutrm_i2pfrag in pi.
eapply ll_to_ill_oclpam_cutfree in pi; try eassumption.
- destruct pi as [pi _].
  eapply (stronger_ipfrag); [ | eassumption ].
  repeat split; [ | reflexivity ].
  intros a; destruct (P_axfree a).
- reflexivity.
- intros a; destruct (P_axfree a).
- constructor.
- cbn; rewrite Hperm; cbn; assumption.
Qed.

End Conservativity_Atoms.
