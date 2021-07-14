(* nn_prop library for yalla *)


(** * Parametric negative translation from [ll] into [ill]. *)
(** Properties relying on cut admissibility *)

From OLlibs Require Import funtheory infinite List_more Dependent_Forall_Type
                           Permutation_Type GPermutation_Type.
From Yalla Require Import subs ll_fragments bbb.
From Yalla Require Export nn_def.


Section Atoms.

Context {atom : DecType} {preiatom : InfDecType} {Atoms : Atom2IAtomType_self atom preiatom}.

Notation atom_inf := (@atom_inf _ _ Atoms).
Notation formula := (@formula atom_inf).
Notation iformula := (@iformula preiatom).
Notation unill := (@unill _ _ Atoms).
Notation trans := (@trans _ _ Atoms).
Notation i2a := (@i2a _ _ Atoms).
Notation a2i := (@a2i _ _ Atoms).
Notation ll_to_ill_trans := (@ll_to_ill_trans _ _ Atoms).
Notation p2ipfrag := (@p2ipfrag _ _ Atoms).

Section RTranslation.

(** We fix the parameter [R] of the translation. *)

Variable R : iformula.

(** In [llR] (where [bot] is equivalent to [R]),
  [A] is implied by the dual of its translation. *)
Lemma back_to_llR : forall A,
  llR (unill R) (unill (trans R A) :: A :: nil).
Proof with myeeasy ; try ((try rewrite a2a_i) ; GPermutation_Type_solve).
induction A ; simpl ; rewrite ? bidual.
- apply parr_r.
  unfold IAtom2Atom, iatom2atom; rewrite a2a_i.
  apply (ex_r ((covar c :: var c :: nil) ++ unill R :: nil))...
  eapply (@cut_r _ (pfrag_llR (unill R)) eq_refl (dual one)).
  + apply (ex_r (unill R :: one :: nil))...
    apply (@gax_r _ (pfrag_llR (unill R)) false).
  + apply bot_r.
    apply ax_r.
- unfold IAtom2Atom, iatom2atom; rewrite a2a_i.
  apply (ex_r (covar c :: var c :: nil))...
  apply ax_r...
- eapply parr_r.
  apply bot_r.
  apply (@gax_r _ (pfrag_llR (unill R)) false).
- apply (ex_r (bot :: one :: nil))...
  apply bot_r.
  apply one_r.
- assert (Hax := @ax_exp _ (pfrag_llR (unill R)) (unill R)).
  apply parr_r.
  apply parr_r.
  change (tens (dual (unill R)) (unill (trans R A2)) ::
  tens (dual (unill R)) (unill (trans R A1)) :: unill R :: tens A1 A2 :: nil)
    with (tens (dual (unill R)) (unill (trans R A2)) ::  
    (tens (dual (unill R)) (unill (trans R A1)) :: unill R :: tens A1 A2 :: nil) ++ nil).
  apply tens_r.
  + apply (@gax_r _ (pfrag_llR (unill R)) true).
  + apply (ex_r (tens (dual (unill R)) (unill (trans R A1))
             :: (unill (trans R A2) :: tens A1 A2 :: nil) ++ (unill R :: nil)))...
    2:{ list_simpl.
        transitivity ((tens (dual (unill R)) (unill (trans R A1))
              :: (unill (trans R A2) :: unill R :: tens A1 A2 :: nil)))...
        - apply Permutation_Type_cons...
          apply Permutation_Type_cons...
        - apply Permutation_Type_swap. }
    apply tens_r.
    -- eapply ex_r ; [ | apply Permutation_Type_swap ]...
    -- apply (ex_r (tens A1 A2 ::
             (unill (trans R A2) :: nil) ++ unill (trans R A1) :: nil))...
       2:{ list_simpl.
           etransitivity; [ apply Permutation_Type_cons_append | ].
           apply Permutation_Type_swap. }
       apply tens_r.
       ++ eapply ex_r ; [ apply IHA1 | ]...
       ++ eapply ex_r ; [ apply IHA2 | ]...
- apply (ex_r (parr A1 A2 ::
                 tens (unill (trans R A2)) (unill (trans R A1)) :: nil))...
  apply parr_r.
  apply (ex_r (tens (unill (trans R A2)) (unill (trans R A1))
                  :: (A1 :: nil) ++ (A2 :: nil)))...
  apply tens_r...
- apply parr_r.
  apply top_r.
- eapply ex_r ; [ | apply Permutation_Type_swap ].
  eapply top_r.
- assert (Hax := @ax_exp _ (pfrag_llR (unill R)) (unill R)).
  apply parr_r.
  apply with_r.
  + apply (ex_r (tens (dual (unill R)) (unill (trans R A1)) ::
                    (aplus A1 A2 :: nil) ++ unill R :: nil))...
    apply tens_r.
    * eapply ex_r ; [ | apply Permutation_Type_swap ]...
    * eapply ex_r ; [ | apply Permutation_Type_swap ].
      apply plus_r1.
      eapply ex_r ; [ | apply Permutation_Type_swap ]...
  + apply (ex_r (tens (dual (unill R)) (unill (trans R A2)) ::
                    (aplus A1 A2 :: nil) ++ unill R :: nil))...
    apply tens_r...
    * eapply ex_r ; [ | apply Permutation_Type_swap ]...
    * eapply ex_r ; [ | apply Permutation_Type_swap ].
      apply plus_r2.
      eapply ex_r ; [ | apply Permutation_Type_swap ]...
- assert (Hax := @ax_exp _ (pfrag_llR (unill R)) (unill R)).
  eapply ex_r ; [ | apply Permutation_Type_swap ].
  apply with_r.
  + eapply ex_r ; [ | apply Permutation_Type_swap ].
    apply plus_r1...
  + eapply ex_r ; [ | apply Permutation_Type_swap ].
    apply plus_r2...
- apply parr_r.
  apply (ex_r ((oc A ::
                  map wn (tens (dual (unill R)) (unill (trans R A)) :: nil))
                  ++ unill R :: nil)) ; [idtac | cbn]...
  apply (@cut_r _ (pfrag_llR (unill R)) eq_refl (dual one)).
  + apply (ex_r (unill R :: one :: nil))...
    apply (@gax_r _ (pfrag_llR (unill R)) false).
  + apply bot_r.
    apply oc_r; cbn.
    apply (ex_r ((wn (tens (dual (unill R)) (unill (trans R A))) :: nil)
                     ++ (A :: nil) ++ nil))...
    apply de_r.
    apply tens_r...
    apply (@gax_r _ (pfrag_llR (unill R)) true).
- assert (Hax := @ax_exp _ (pfrag_llR (unill R)) (unill R)).
  change (wn A :: nil) with (map wn (A :: nil)).
  apply oc_r ; cbn.
  apply parr_r.
  apply (ex_r (tens (dual (unill R)) (unill (trans R A)) :: (wn A :: nil) ++ unill R :: nil))...
  apply tens_r.
  + eapply ex_r...
  + apply (ex_r (wn A :: unill (trans R A) :: nil))...
    apply de_r...
    eapply ex_r; [ | apply Permutation_Type_swap ]...
Qed.

(** The previous lemma comes with the following result from the [ll_fragments] library:
<<
Lemma ll_to_llR : forall R l, ll_ll l -> llR R l.
>> to deduce: *)

(** A sequent whose translation is provable in [ill] was provable in [llR]. *)
Lemma ill_trans_to_llR : forall l,  ill_ll (map (trans R) l) R -> llR (unill R) l.
Proof with myeeasy ; try GPermutation_Type_solve.
intros l Hill.
apply (@ill_to_ll _ _ iatom2atom) in Hill.
apply (stronger_pfrag _ (mk_pfrag true NoAxioms pmix_none true))
  in Hill.
- eapply cut_admissible_axfree in Hill.
  + apply (ll_to_llR (unill R)) in Hill.
    assert (forall l',
      llR (unill R) (l' ++ map dual (map unill (map (trans R) (rev l))))
        -> llR (unill R) (l' ++ rev l)) as Hll.
    { clear.
      induction l using rev_rect ; intros...
      assert (Hb := back_to_llR x).
      rewrite rev_unit in X.
      apply (ex_r _ (dual (unill (trans R x))
               :: l' ++ map dual (map unill (map (trans R) (rev l))))) in X...
      apply (@cut_r _ _ (eq_refl (pcut (pfrag_llR (unill R)))) _ _ _ X) in Hb.
      rewrite rev_unit.
      change (x :: rev l) with ((x :: nil) ++ rev l).
      rewrite app_assoc.
      eapply IHl.
      eapply ex_r... }
    assert (llR (unill R) (dual (unill R) :: nil)) as HR
      by (apply (@gax_r _ (pfrag_llR (unill R)) true)).
    apply (@cut_r _ _ (eq_refl (pcut (pfrag_llR (unill R)))) _ _ _ HR) in Hill.
    rewrite app_nil_r in Hill.
    rewrite <- (app_nil_l (rev _)) in Hill.
    rewrite <- ? map_rev in Hill.
    apply Hll in Hill.
    eapply ex_r ; [ apply Hill | ].
    symmetry.
    apply Permutation_Type_rev.
  + intros Hax ; inversion Hax.
- nsplit 4 ; myeasy.
  intros Hax ; inversion Hax.
Qed.


(** *** Sufficient condition on [R] for embedding [llR] into [ill_ll]

extension of [ll_to_ill_trans] *)

(** Elementary intuitionistic formulas *)
Inductive ielem : iformula -> Type :=
| ie_ivar : forall X, X <> atN -> ielem (ivar X)
| ie_ione : ielem ione
| ie_itens : forall A B, ielem A -> ielem B -> ielem (itens A B)
| ie_izero : ielem izero
| ie_iplus : forall A B, ielem A -> ielem B -> ielem (iplus A B)
| ie_itop : ielem itop.

Lemma ie_ie : forall A, ielem A ->
  ill_ll (A :: nil) (negR R (trans R (unill A))).
Proof with try now (apply ax_exp_ill).
induction A ; intros Hgfn ; inversion Hgfn ;
  cbn ; unfold trans.
- unfold IAtom2Atom; rewrite (i2i_not_atN _ H0).
  apply negR_irr.
  apply negR_ilr...
  reflexivity.
- apply negR_irr.
  apply negR_ilr...
  reflexivity.
- apply IHA1 in X.
  apply IHA2 in X0.
  apply negR_irr.
  apply negR_ilr ; [ reflexivity | | ]...
  rewrite <- (app_nil_l _).
  apply tens_ilr.
  list_simpl ; cons2app.
  apply tens_irr ; eassumption.
- apply negR_irr.
  rewrite <- (app_nil_l _).
  apply zero_ilr.
- rewrite <- (app_nil_l _).
  apply zero_ilr.
- apply IHA1 in X.
  apply IHA2 in X0.
  apply negR_irr.
  apply negR_ilr ; [ reflexivity | | ]...
  rewrite <- (app_nil_l _).
  apply plus_ilr ; constructor ; eassumption.
Qed.

Lemma ie_dual : forall A, ielem A ->
  ill_ll (trans R (dual (unill A)) :: nil) A.
Proof with try now (apply ax_exp_ill).
induction A ; intros Hgfn ; inversion Hgfn ;
  cbn ; unfold trans...
- unfold IAtom2Atom; rewrite (i2i_not_atN _ H0)...
- apply IHA1 in X.
  apply IHA2 in X0.
  rewrite <- (app_nil_l _).
  apply tens_ilr.
  list_simpl.
  cons2app.
  apply tens_irr ; eassumption.
- apply top_irr.
- apply IHA1 in X.
  apply IHA2 in X0.
  rewrite <- (app_nil_l _).
  apply plus_ilr ; constructor ; eassumption.
Qed.

End RTranslation.


Lemma ie_ie_diag : forall A, ielem A ->
  ill_ll (trans A (unill A) :: A :: nil) A.
Proof.
intros A Hgfn.
eapply ex_ir ; [ | apply Permutation_Type_swap ].
cons2app.
rewrite <- (app_nil_l _).
eapply cut_ir_axfree.
- intros a ; destruct a.
- apply ie_ie.
  assumption.
- apply negR_ilr ; try apply ax_exp_ill.
  reflexivity.
Qed.

Lemma ie_dual_diag : forall A, ielem A ->
  ill_ll (trans A (dual (unill A)) :: nil) A.
Proof.
intros A ; apply ie_dual.
Qed.

Proposition llR_ie_to_ill_trans : forall R l, ielem R ->
  llR (unill R) l -> ill_ll (map (trans R) l) R.
Proof with myeeasy ; try GPermutation_Type_solve.
intros R l Hie Hll.
assert (Hax := @ax_exp_ill _ ipfrag_ill R).
rewrite <- (app_nil_l (R :: _)) in Hax.
induction Hll ; 
  (try now (apply Hmix0)) ;
  (try now (rewrite map_app ; eapply Hmix2)) ;
  (try now (apply P_axfree in H ; inversion H)) ;
  (try now (inversion f)) ;
  cbn.
- eapply ex_ir.
  + eapply lmap_ilr ; [ | apply Hax ].
    eapply (ax_ir _ (a2i X)).
  + GPermutation_Type_solve.
- eapply ex_ir...
  apply Permutation_Type_map...
- list_simpl in IHHll ; rewrite trans_wn in IHHll.
  list_simpl ; rewrite trans_wn.
  eapply Permutation_Type_map in p.
  eapply ex_oc_ir...
- rewrite <- (app_nil_l _).
  rewrite <- (app_nil_l _).
  apply lmap_ilr...
  apply one_irr.
- rewrite <- (app_nil_l (ione :: _)).
  apply one_ilr...
- apply negR_irr in IHHll1.
  apply negR_irr in IHHll2.
  apply (tens_irr _ _ _ _ _ IHHll1) in IHHll2.
  apply (lmap_ilr _ _ _ _ _ _ _ IHHll2) in Hax.
  apply (ex_ir _ _ _ _ Hax)...
- rewrite <- (app_nil_l (itens _ _ :: _)).
  apply tens_ilr.
  eapply ex_ir...
- rewrite <- (app_nil_l (izero :: _)).
  apply zero_ilr.
- apply negR_irr in IHHll.
  apply (plus_irr1 _ _ (negR R (trans R B))) in IHHll.
  apply (lmap_ilr _ _ _ _ _ _ _ IHHll) in Hax.
  apply (ex_ir _ _ _ _ Hax)...
- apply negR_irr in IHHll.
  apply (plus_irr2 _ _ (negR R (trans R B))) in IHHll.
  apply (lmap_ilr _ _ _ _ _ _ _ IHHll) in Hax.
  apply (ex_ir _ _ _ _ Hax)...
- rewrite <- (app_nil_l (iplus _ _ :: _)).
  apply plus_ilr...
- cbn in IHHll ; rewrite map_map in IHHll.
  cbn in IHHll ; rewrite <- map_map in IHHll.
  apply negR_irr in IHHll.
  apply oc_irr in IHHll.
  apply negR_ilr...
  eapply ex_ir...
  list_simpl...
  rewrite ? map_map...
- rewrite <- (app_nil_l (ioc _ :: _)).
  apply de_ilr...
  eapply ex_ir ; [ | apply Permutation_Type_middle ].
  apply negR_ilr...
  apply negR_irr.
  eapply ex_ir...
- rewrite <- (app_nil_l (ioc _ :: _)).
  apply wk_ilr...
- rewrite <- (app_nil_l (ioc _ :: _)).
  change nil with (map (@ioc preiatom) nil).
  rewrite <- (app_nil_l (map _ _ ++ _)).
  apply co_ilr.
  eapply ex_ir...
- apply negR_irr in IHHll1.
  apply negR_irr in IHHll2.
  apply (stronger_ipfrag _ (cutupd_ipfrag ipfrag_ill true) (cutupd_ipfrag_true _)) in IHHll1.
  apply (stronger_ipfrag _ (cutupd_ipfrag ipfrag_ill true) (cutupd_ipfrag_true _)) in IHHll2.
  assert (pi0 := @trans_dual _ _ _ R (cutupd_ipfrag ipfrag_ill true) eq_refl eq_refl A).
  rewrite <- (app_nil_l _) in pi0.
  eapply (cut_ir _ _ _ _ _ _ IHHll2) in pi0.
  list_simpl in pi0.
  eapply (cut_ir _ _ _ _ _ _ IHHll1) in pi0.
  unfold ill_ll ;  change ipfrag_ill with (@cutrm_ipfrag preiatom (cutupd_ipfrag ipfrag_ill true)).
  apply cut_admissible_ill_axfree ; [ intros a ; destruct a | ].
  eapply ex_ir...
- destruct a ; subst.
  + apply ie_dual_diag...
  + cbn.
    eapply ex_ir ; [ | apply Permutation_Type_swap ].
    rewrite <- 2 (app_nil_l (negR _ _ :: _)).
    apply lmap_ilr...
    * apply one_irr.
    * eapply ex_ir.
      -- apply ie_ie_diag...
      -- GPermutation_Type_solve.
Unshelve. all : reflexivity.
Qed.


(** ** Study of the case [R = bot] *)

(** Given a sequent, the following 3 statements are equivalent:
 - the translation of the sequent is provable in [ill] for any [R];
 - the sequent is provable in [llR bot];
 - the sequent is provable in [ll].
*)

Theorem ill_trans_to_llR_bot : forall l : list formula,
  (forall R, ill_ll (map (trans R) l) R) -> llR bot l.
Proof with myeeasy ; try GPermutation_Type_solve.
intros l Hill.
remember (fresh_of_list l) as z.
specialize Hill with (ivar (a2i z)).
apply ill_trans_to_llR in Hill...
apply (subs_llR _ bot z) in Hill ; subst.
cbn in Hill.
rewrite repl_at_eq in Hill.
- change (proj1_sig (nat_injective_choice atom (self_injective_nat atom Atom_self_inj)) (flat_map atom_list l))
   with  (fresh_of_list l) in Hill.
  rewrite (@subs_fresh_list atom_inf) in Hill...
- apply a2a_i.
Qed.

Theorem llR_bot_to_ll : forall l, llR bot l -> @ll_ll atom_inf l.
Proof with myeeasy.
intros l HR.
induction HR ;
  (try now (inversion f)) ;
  try now constructor.
- eapply ex_r...
- eapply ex_wn_r...
- eapply cut_ll_r...
- destruct a.
  + apply one_r.
  + apply bot_r.
    apply one_r.
Qed.

Theorem ll_ll_to_ill_trans : forall R (l : list formula),
  ll_ll l -> ill_ll (map (trans R) l) R.
Proof.
intros R l Hll.
apply (ll_to_ill_trans R) in Hll ; myeasy.
- eapply stronger_ipfrag ; [ | apply Hll ].
  nsplit 3 ; myeasy.
  intros a ; destruct a.
- intros L eqpmix; inversion eqpmix.
Qed.


(** ** Study of the case [R = one] *)

(** Given a sequent, the following 3 statements are equivalent:
 - the translation of the sequent is provable in [ill] for parameter [ione];
 - the sequent is provable in [llR one];
 - the sequent is provable in [ll_mix02].
*)

Lemma ill_trans_to_llR_one : forall l : list formula,
  ill_ll (map (trans ione) l) ione -> llR one l.
Proof.
apply ill_trans_to_llR.
Qed.

Theorem llR_one_to_ll_mix02 : forall l, llR one l -> @ll_mix02 atom_inf l.
Proof with myeeasy.
intros l pi.
induction pi ; try now constructor.
- eapply ex_r...
- eapply ex_wn_r...
- eapply cut_mix02_r...
- destruct a ; cbn.
  + apply bot_r.
    change nil with (concat (@nil (list formula))).
    apply mix_r...
    apply Forall_inf_nil.
  + change (one :: one :: nil) with (concat ((@one atom :: nil) :: (one :: nil) :: nil)).
    apply mix_r...
    repeat (apply Forall_inf_cons; try apply one_r)...
    apply Forall_inf_nil.
Qed.

Theorem ll_mix02_to_ill_trans : forall l : list formula,
  ll_mix02 l -> ill_ll (map (trans ione) l) ione.
Proof with myeeasy.
intros l Hll.
apply (ll_to_ill_trans ione) in Hll ; myeasy.
- eapply stronger_ipfrag ; [ | apply Hll ].
  nsplit 3 ; myeasy.
  intros a ; destruct a.
- intros L eqpmix FL FLind.
  destruct L.
  { apply one_irr. }
  destruct L.
  { inversion eqpmix. }
  destruct L.
  { cbn.
    rewrite app_nil_r.
    assert (ill (p2ipfrag ione (@pfrag_mix02 atom_inf)) (map (trans ione) l0) ione).
    { assert (In_inf l0 (l0 :: l1 :: nil)) as Hin.
      { left... }
      apply (In_Forall_inf_in _ FL) in Hin as [pi Hin].
      refine (Dependent_Forall_inf_forall_formula _ _ FLind Hin). }
    assert (ill (p2ipfrag ione (@pfrag_mix02 atom_inf)) (map (trans ione) l1) ione).
    { assert (In_inf l1 (l0 :: l1 :: nil)) as Hin.
      { right; left... }
      apply (In_Forall_inf_in _ FL) in Hin as [pi Hin].
      refine (Dependent_Forall_inf_forall_formula _ _ FLind Hin). }
    rewrite map_app.
    rewrite <- (app_nil_l (map _ l0 ++ map _ l1)).
    rewrite <- (app_nil_r (map _ l0 ++ map _ l1)).
    eapply cut_ir_axfree.
    + intros a ; destruct a.
    + apply tens_irr...
    + apply tens_ilr.
      apply one_ilr.
      apply one_ilr.
      apply one_irr. }
    inversion eqpmix.
Qed.

(** ** Study of the case [R = zero] *)

(** Given a sequent, the following 2 statements are equivalent:
 - the translation of the sequent is provable in [ill] for parameter [izero];
 - the sequent is provable in [llR zero].
*)

Lemma ill_trans_to_llR_zero : forall l : list formula,
  ill_ll (map (trans izero) l) izero -> llR zero l.
Proof.
apply ill_trans_to_llR.
Qed.

Lemma llR_zero_to_ill_trans : forall l : list formula,
  llR zero l -> ill_ll (map (trans izero) l) izero.
Proof with myeeasy.
intros l pi.
eapply llR_ie_to_ill_trans...
constructor.
Qed.

(** Moreover in these systems, the general weakening rule is admissible. *)
Lemma aff_to_ill_trans : forall l A,
  ill_ll (map (trans izero) l) izero -> ill_ll (map (trans izero) (A :: l)) izero.
Proof with myeeasy.
intros l A Hll.
cbn.
cons2app.
rewrite <- (app_nil_r (map _ _)).
eapply cut_ir_axfree ; try (now (intros a ; destruct a))...
apply zero_ilr.
Qed.


(** ** Study of the case [R = wn one] *)

(** Given a sequent, the following 3 statements are equivalent:
 - the translation of the sequent is provable in [ill] for any parameter [R] such that [R] is provable in [ill];
 - the sequent is provable in [llR (wn one)];
 - the sequent is provable in [ll_mix0].
*)

Theorem ill_trans_to_llR_wn_one : forall l : list formula,
  (forall R, ill_ll nil R -> ill_ll (map (trans R) l) R) -> llR (wn one) l.
Proof with myeeasy ; try GPermutation_Type_solve.
intros l Hill.
remember (fresh_of_list l) as z.
assert (ill_ll nil (ilpam (ioc (ivar (a2i z))) (ivar (a2i z))))
  as Hz.
{ apply lpam_irr.
  apply de_ilr.
  apply ax_ir. }
specialize Hill with (ilpam (ioc (ivar (a2i z))) (ivar (a2i z))).
assert (Hz2 := Hz).
apply Hill in Hz2 ; clear Hill.
apply ill_trans_to_llR in Hz2...
apply (subs_llR _ bot z) in Hz2 ; subst.
simpl in Hz2; unfold IAtom2Atom in Hz2; rewrite a2a_i, repl_at_eq in Hz2...
eapply (llR1_R2 _ (wn one)) in Hz2.
- change (proj1_sig (nat_injective_choice atom (self_injective_nat atom Atom_self_inj)) (flat_map atom_list l))
   with  (fresh_of_list l) in Hz2.
  rewrite (@subs_fresh_list atom_inf) in Hz2...
- cbn.
  rewrite <- (app_nil_l (wn _ :: _)).
  apply tens_r.
  + change (wn one :: nil) with (map (@wn atom) (one :: nil)).
    apply oc_r ; cbn.
    apply bot_r.
    apply de_r.
    apply one_r.
  + apply one_r.
- cbn.
  apply (ex_r (parr bot (wn one) :: oc bot :: nil))...
  apply parr_r.
  apply bot_r.
  change (oc bot) with (@dual atom (wn one)).
  apply ax_exp.
Qed.

Theorem llR_wn_one_to_ll_mix0 : forall l, llR (wn one) l -> @ll_mix0 atom_inf l.
Proof with myeeasy.
intros l pi.
induction pi ; try now constructor.
- eapply ex_r...
- eapply ex_wn_r...
- eapply cut_mix0_r...
- destruct a ; cbn.
  + change nil with (map (@wn atom) nil).
    apply oc_r.
    apply bot_r.
    change (map wn nil) with (concat (@nil (list formula))).
    apply mix_r...
    apply Forall_inf_nil.
  + apply wk_r.
    apply one_r.
Qed.

Theorem ll_mix0_to_ill_trans : forall R (l : list formula),
  ill_ll nil R -> ll_mix0 l -> ill_ll (map (trans R) l) R.
Proof with myeeasy.
intros R l HR Hll.
apply (stronger_pfrag _ (cutupd_pfrag pfrag_mix0 true)) in Hll.
- apply (ll_to_ill_trans R) in Hll ; myeasy.
  + unfold ill_ll ; change ipfrag_ill with (@cutrm_ipfrag preiatom (cutupd_ipfrag ipfrag_ill true)).
    apply cut_admissible_ill_axfree ; [ intros a ; destruct a | ].
    eapply stronger_ipfrag ; [ | apply Hll ].
    nsplit 3...
    intros a ; destruct a.
  + intros L eqpmix FL FLind.
    destruct L; try now inversion eqpmix.
    cbn.
    eapply stronger_ipfrag ; [ | apply HR ].
    nsplit 3...
    intros a ; destruct a.
- nsplit 4...
  intros a ; destruct a.
Qed.

(** ** Study of the case [R = oc bot] *)

(** Given a sequent, the following 3 statements are equivalent:
 - the translation of the sequent is provable in [ill] for any parameter [ioc R];
 - the sequent is provable in [llR (oc bot)];
 - the sequent is provable in [ll_bbb].
*)

Theorem ill_trans_to_llR_oc_bot : forall l : list formula,
  (forall R, ill_ll (map (trans (ioc R)) l) (ioc R)) ->
  llR (oc bot) l.
Proof with myeeasy ; try GPermutation_Type_solve.
intros l Hill.
remember (fresh_of_list l) as z.
specialize Hill with (ivar (a2i z)).
apply ill_trans_to_llR in Hill...
apply (subs_llR _ bot z) in Hill ; subst.
simpl in Hill; unfold IAtom2Atom in Hill; rewrite a2a_i, repl_at_eq in Hill...
change (proj1_sig (nat_injective_choice atom (self_injective_nat atom Atom_self_inj)) (flat_map atom_list l))
   with  (fresh_of_list l) in Hill.
rewrite (@subs_fresh_list atom_inf) in Hill...
Qed.

Theorem llR_oc_bot_to_ll_bbb : forall l, llR (oc bot) l -> @ll_bbb atom_inf l.
Proof.
apply bb_to_bbb.
Qed.

Lemma ll_mix02_to_ill_trans_gen : forall R (l : list formula),
 ll_mix02 l -> ill_ll (ioc R :: map (trans (ioc R)) l) (ioc R).
Proof with myeeasy.
intros R l Hll.
change (ioc R :: map (trans _) l)
  with (map ioc (R :: nil) ++ map (trans (ioc R)) l).
apply (stronger_pfrag _ (cutupd_pfrag pfrag_mix02 true)) in Hll.
- eapply (ll_to_ill_trans_gen (ioc R) _ _ (R :: nil)) in Hll ; myeasy.
  + unfold ill_ll ; change ipfrag_ill with (@cutrm_ipfrag preiatom (cutupd_ipfrag ipfrag_ill true)).
    apply cut_admissible_ill_axfree ; [ intros a ; destruct a | ].
    eapply stronger_ipfrag ; [ | apply Hll ].
    nsplit 3...
    intros a ; destruct a.
  + intros L eqpmix FL FLind.
    destruct L.
    { intros ; apply ax_exp_ill. }
    destruct L.
    { inversion eqpmix. }
    destruct L.
    { assert (ill (p2ipfrag (ioc R) (cutupd_pfrag (@pfrag_mix02 atom_inf) true))
               (map ioc (R :: nil) ++ map (trans (ioc R)) l0) (ioc R)).
      { assert (In_inf l0 (l0 :: l1 :: nil)) as Hin.
        { left... }
        apply (In_Forall_inf_in _ FL) in Hin as [pi Hin].
        refine (Dependent_Forall_inf_forall_formula _ _ FLind Hin). }
    assert (ill (p2ipfrag (ioc R) (cutupd_pfrag (@pfrag_mix02 atom_inf) true))
               (map ioc (R :: nil) ++ map (trans (ioc R)) l1) (ioc R)).
      { assert (In_inf l1 (l0 :: l1 :: nil)) as Hin.
        { right; left... }
        apply (In_Forall_inf_in _ FL) in Hin as [pi Hin].
        refine (Dependent_Forall_inf_forall_formula _ _ FLind Hin). }
      cbn.
      rewrite app_nil_r.
      rewrite map_app.
      rewrite <- (app_nil_l (ioc R :: _)).
      rewrite <- (app_nil_r (map _ l1)).
      rewrite app_comm_cons.
      rewrite (app_assoc _ (map _ l1)).
      eapply (cut_ir _ (itens (ioc R) (ioc R))).
      - rewrite <- 2 (app_nil_l (ioc R :: _)).
        rewrite <- ? app_assoc.
        change nil with (map (@ioc preiatom) nil) at 2.
        apply co_ilr.
        eapply ex_ir.
        + apply tens_irr ; [ apply X | apply X0 ].
        + GPermutation_Type_solve.
      - apply tens_ilr.
        apply wk_ilr.
        apply ax_exp_ill. }
    inversion eqpmix.
- nsplit 4...
  intros a ; destruct a.
Unshelve. all: reflexivity.
Qed.

Theorem ll_bbb_to_ill_trans : forall R (l : list formula),
  ll_bbb l -> ill_ll (map (trans (ioc R)) l) (ioc R).
Proof with myeeasy ; try GPermutation_Type_solve ; try now (apply ax_exp_ill).
intros R l Hll.
induction Hll ; (try now (inversion f)) ; cbn.
- eapply ex_ir.
  + eapply lmap_ilr ; [ | ].
    * eapply (ax_ir _ (a2i X)).
    * rewrite app_nil_l...
  + GPermutation_Type_solve.
- eapply ex_ir...
  apply Permutation_Type_map...
- apply (ll_mix02_to_ill_trans_gen R) in l.
  rewrite <- (app_nil_l (ioc _ :: _)) in l.
  rewrite map_app.
  rewrite <- (app_nil_r (map _ l1)).
  eapply (cut_ir_axfree) ; [ intros a ; destruct a | | ]...
  eapply ex_ir ; [ | apply Permutation_Type_app_comm ]...
- apply negR_ilr...
  apply one_irr.
- rewrite <- (app_nil_l (ione :: _)).
  apply one_ilr...
- apply negR_ilr...
  list_simpl.
  eapply ex_ir ; [ | apply Permutation_Type_app_comm ].
  apply tens_irr ; apply negR_irr ; eapply ex_ir.
  + apply IHHll1.
  + GPermutation_Type_solve.
  + apply IHHll2.
  + GPermutation_Type_solve.
- rewrite <- (app_nil_l (itens _ _ :: _)).
  apply tens_ilr.
  eapply ex_ir...
- rewrite <- (app_nil_l (izero :: _)).
  apply zero_ilr.
- apply negR_ilr...
  apply plus_irr1 ; apply negR_irr ; eapply ex_ir...
- apply negR_ilr...
  apply plus_irr2 ; apply negR_irr ; eapply ex_ir...
- rewrite <- (app_nil_r (map _ _)).
  rewrite <- (app_nil_l (iplus _ _ :: _)).
  apply plus_ilr ; eapply ex_ir ; [ apply IHHll1 | | apply IHHll2 | ]...
- apply negR_ilr...
  rewrite map_map ; cbn.
  rewrite <- map_map.
  cbn in IHHll ; rewrite map_map in IHHll.
  cbn in IHHll ; rewrite <- map_map in IHHll.
  apply oc_irr.
  apply negR_irr.
  eapply ex_ir...
- rewrite <- (app_nil_l (ioc _ :: _)).
  apply de_ilr...
  list_simpl.
  apply negR_ilr...
  apply negR_irr...
- rewrite <- (app_nil_l (ioc _ :: _)).
  apply wk_ilr...
- rewrite <- 2 (app_nil_l (ioc _ :: _)).
  change nil with (map (@ioc preiatom) nil).
  apply co_ilr.
  eapply ex_ir...
Qed.

(** The following result is the converse of [bb_to_bbb] proved in the [bbb] library *)

Theorem bbb_to_bb : forall l, ll_bbb l -> @llR atom_inf (oc bot) l.
Proof.
intros l pi.
apply ill_trans_to_llR_oc_bot.
intros R.
apply ll_bbb_to_ill_trans ; eassumption.
Qed.

End Atoms.
