(** * Parametric negative translation from [ll] into [ill]. *)
(** Properties relying on cut admissibility *)

From OLlibs Require Import funtheory infinite List_more Dependent_Forall_Type Permutation_Type GPermutation_Type.
From Yalla Require Import subs ll_fragments bbb.
From Yalla Require Export nn_def.

Set Default Proof Using "Type".
Set Implicit Arguments.


Section Atoms.

Context {atom : DecType} {preiatom : InfDecType} {Atoms : Atom2IAtomType_self atom preiatom}.

Notation atom_inf := (@atom_inf _ _ Atoms).
Notation formula := (@formula atom_inf).
Notation iformula := (@iformula preiatom).
Notation ill2ll := (@ill2ll _ _ iatom2atom_fin).
Notation unill := (@unill _ _ Atoms).
Notation trans := (@trans _ _ Atoms).
Notation i2a := (@i2a _ _ Atoms).
Notation a2i := (@a2i _ _ Atoms).
Arguments ll_to_ill_trans_gen {_ _ _} R {P} _ [l].
Arguments ll_to_ill_trans {_ _ _} R {P} _ [l].
Notation ll_to_ill_trans := (@ll_to_ill_trans _ _ Atoms).
Notation p2ipfrag := (@p2ipfrag _ _ Atoms).

Section RTranslation.

(** We fix the parameter [R] of the translation. *)

Variable R : iformula.

(** In [llR] (where [bot] is equivalent to [R]),
  [A] is implied by the dual of its translation. *)
Lemma back_to_llR A : llR (unill R) (unill (trans R A) :: A :: nil).
Proof.
induction A; cbn; rewrite ? bidual.
- apply parr_r.
  destruct (bijective_inverse Atom2PreIAtom_bij) as [f Hr1 Hr2]. rewrite (Hr2 c).
  apply (ex_r ((covar c :: var c :: nil) ++ unill R :: nil));
    [ | apply Permutation_Type_cons, Permutation_Type_swap; reflexivity ].
  eapply (@cut_r _ (pfrag_llR (unill R)) (dual one) eq_refl).
  + apply (ex_r (unill R :: one :: nil)); [ | apply Permutation_Type_swap ].
    apply (@gax_r _ (pfrag_llR (unill R)) false).
  + apply bot_r, ax_r.
- destruct (bijective_inverse Atom2PreIAtom_bij) as [f Hr1 Hr2].  rewrite (Hr2 c).
  apply (ex_r (covar c :: var c :: nil)); [ | apply Permutation_Type_swap ].
  apply ax_r.
- apply parr_r, bot_r.
  apply (@gax_r _ (pfrag_llR (unill R)) false).
- apply (ex_r (bot :: one :: nil)); [ | apply Permutation_Type_swap ].
  apply bot_r, one_r.
- assert (Hax := @ax_exp _ (pfrag_llR (unill R)) (unill R)).
  apply parr_r, parr_r.
  change (tens (dual (unill R)) (unill (trans R A2)) ::
            tens (dual (unill R)) (unill (trans R A1)) :: unill R :: tens A1 A2 :: nil)
    with (tens (dual (unill R)) (unill (trans R A2)) ::  
            (tens (dual (unill R)) (unill (trans R A1)) :: unill R :: tens A1 A2 :: nil) ++ nil).
  apply tens_r.
  + apply (@gax_r _ (pfrag_llR (unill R)) true).
  + apply (ex_r (tens (dual (unill R)) (unill (trans R A1))
             :: (unill (trans R A2) :: tens A1 A2 :: nil) ++ (unill R :: nil))).
    2:{ list_simpl.
        transitivity ((tens (dual (unill R)) (unill (trans R A1))
              :: (unill (trans R A2) :: unill R :: tens A1 A2 :: nil))).
        - apply Permutation_Type_cons, Permutation_Type_cons, Permutation_Type_swap; reflexivity.
        - apply Permutation_Type_swap. }
    apply tens_r.
    -- eapply ex_r; [ eassumption | apply Permutation_Type_swap ].
    -- apply (ex_r (tens A1 A2 ::
               (unill (trans R A2) :: nil) ++ unill (trans R A1) :: nil));
         [ | etransitivity; [ apply Permutation_Type_cons_append | apply Permutation_Type_swap ] ].
       apply tens_r.
       ++ eapply ex_r; [ apply IHA1 | apply Permutation_Type_swap ].
       ++ eapply ex_r; [ apply IHA2 | apply Permutation_Type_swap ].
- apply (ex_r (parr A1 A2 ::
          tens (unill (trans R A2)) (unill (trans R A1)) :: nil)); [ | apply Permutation_Type_swap ].
  apply parr_r.
  apply (ex_r (tens (unill (trans R A2)) (unill (trans R A1))
                  :: (A1 :: nil) ++ (A2 :: nil)));
    [ | etransitivity; [ apply Permutation_Type_middle
                       | apply Permutation_Type_cons, Permutation_Type_swap; reflexivity ] ].
  apply tens_r; assumption.
- apply parr_r, top_r.
- eapply ex_r; [ apply top_r | apply Permutation_Type_swap ].
- assert (Hax := @ax_exp _ (pfrag_llR (unill R)) (unill R)).
  apply parr_r, with_r.
  + apply (ex_r (tens (dual (unill R)) (unill (trans R A1)) ::
                    (aplus A1 A2 :: nil) ++ unill R :: nil));
      [ | apply Permutation_Type_cons, Permutation_Type_swap; reflexivity ].
    apply tens_r.
    * eapply ex_r; [ eassumption | apply Permutation_Type_swap ].
    * eapply ex_r; [ | apply Permutation_Type_swap ].
      apply plus_r1.
      eapply ex_r; [ | apply Permutation_Type_swap ]; assumption.
  + apply (ex_r (tens (dual (unill R)) (unill (trans R A2)) ::
                    (aplus A1 A2 :: nil) ++ unill R :: nil));
      [ | apply Permutation_Type_cons, Permutation_Type_swap; reflexivity ].
    apply tens_r.
    * eapply ex_r; [ eassumption | apply Permutation_Type_swap ].
    * eapply ex_r; [ | apply Permutation_Type_swap ].
      apply plus_r2.
      eapply ex_r; [ | apply Permutation_Type_swap ]; assumption.
- assert (Hax := @ax_exp _ (pfrag_llR (unill R)) (unill R)).
  eapply ex_r; [ | apply Permutation_Type_swap ].
  apply with_r.
  + eapply ex_r; [ | apply Permutation_Type_swap ].
    apply plus_r1; assumption.
  + eapply ex_r; [ | apply Permutation_Type_swap ].
    apply plus_r2; assumption.
- apply parr_r.
  apply (ex_r ((oc A ::
                  map wn (tens (dual (unill R)) (unill (trans R A)) :: nil))
                  ++ unill R :: nil));
    [ | etransitivity; [ apply Permutation_Type_middle
                       | apply Permutation_Type_cons, Permutation_Type_swap; reflexivity ] ].
  apply (@cut_r _ (pfrag_llR (unill R)) (dual one) eq_refl).
  + apply (ex_r (unill R :: one :: nil)); [ | apply Permutation_Type_swap ].
    apply (@gax_r _ (pfrag_llR (unill R)) false).
  + apply bot_r, oc_r.
    apply (ex_r ((wn (tens (dual (unill R)) (unill (trans R A))) :: nil)
                     ++ (A :: nil) ++ nil)); [ | apply Permutation_Type_swap ].
    apply de_r, tens_r.
    * apply (@gax_r _ (pfrag_llR (unill R)) true).
    * assumption.
- assert (Hax := @ax_exp _ (pfrag_llR (unill R)) (unill R)).
  change (wn A :: nil) with (map wn (A :: nil)).
  apply oc_r, parr_r.
  apply (ex_r (tens (dual (unill R)) (unill (trans R A)) :: (wn A :: nil) ++ unill R :: nil));
    [ | apply Permutation_Type_cons, Permutation_Type_swap; reflexivity ].
  apply tens_r.
  + eapply ex_r; [ eassumption | apply Permutation_Type_swap ].
  + apply (ex_r (wn A :: unill (trans R A) :: nil)); [ | apply Permutation_Type_swap ].
    apply de_r.
    eapply ex_r; [ | apply Permutation_Type_swap ]; assumption.
Qed.

(** The previous lemma comes with the following result from the [ll_fragments] library:
[Lemma ll_to_llR R l : ll_ll l -> llR R l.] to deduce: *)

(** A sequent whose translation is provable in [ill] was provable in [llR]. *)
Lemma ill_trans_to_llR l : ill_ll (map (trans R) l) R -> llR (unill R) l.
Proof.
intros Hill%(@ill_to_ll _ _ iatom2atom_fin)%cut_admissible_axfree; [ | intros [] ].
apply (stronger_pfrag _ pfrag_ll) in Hill; [ | repeat split; intros [] ].
apply (ll_to_llR (unill R)) in Hill.
assert (forall C, pcut (pfrag_llR (unill R)) C = true) as Hcut by (intro; reflexivity).
assert (forall l',
  llR (unill R) (l' ++ map dual (map unill (map (trans R) (rev l))))
    -> llR (unill R) (l' ++ rev l)) as Hll.
{ clear - Hcut.
  induction l using rev_rect; intros; [ assumption | ].
  assert (Hb := back_to_llR x).
  rewrite rev_unit in X.
  apply (ex_r _ (dual (unill (trans R x))
           :: l' ++ map dual (map unill (map (trans R) (rev l))))) in X;
    [ | symmetry; apply Permutation_Type_middle ].
  apply (cut_r _ (Hcut _) X) in Hb.
  rewrite rev_unit. change (x :: rev l) with ((x :: nil) ++ rev l). rewrite app_assoc.
  apply IHl.
  eapply ex_r; [ eassumption | list_simpl; apply Permutation_Type_middle ]. }
assert (llR (unill R) (dual (unill R) :: nil)) as HR by apply (@gax_r _ (pfrag_llR (unill R)) true).
apply (cut_r _ (Hcut _) HR) in Hill.
rewrite app_nil_r, <- (app_nil_l (rev _)), <- ? map_rev in Hill. apply Hll in Hill.
eapply ex_r; [ apply Hill | symmetry; apply Permutation_Type_rev ].
Qed.


(** *** Sufficient condition on [R] for embedding [llR] into [ill_ll]

extension of [ll_to_ill_trans] *)

(** Elementary intuitionistic formulas *)
Inductive ielem : iformula -> Type :=
| ie_ivar X : X <> atN -> ielem (ivar X)
| ie_ione : ielem ione
| ie_itens A B : ielem A -> ielem B -> ielem (itens A B)
| ie_izero : ielem izero
| ie_iplus A B : ielem A -> ielem B -> ielem (iplus A B)
| ie_itop : ielem itop.

Lemma ie_ie A : ielem A -> ill_ll (A :: nil) (negR R (trans R (unill A))).
Proof.
induction A; intros Hgfn; inversion Hgfn; cbn; unfold trans.
- unfold IAtom2Atom; rewrite (i2i_not_atN H0).
  apply negR_irr, negR_ilr_head, ax_exp_ill. reflexivity.
- apply negR_irr, negR_ilr_head, ax_exp_ill. reflexivity.
- apply IHA1 in X.
  apply IHA2 in X0.
  apply negR_irr, negR_ilr_head; [ reflexivity | ].
  rewrite <- (app_nil_l _). apply tens_ilr.
  list_simpl. cons2app. apply tens_irr; assumption.
- apply negR_irr. rewrite <- (app_nil_l _). apply zero_ilr.
- rewrite <- (app_nil_l _). apply zero_ilr.
- apply IHA1 in X.
  apply IHA2 in X0.
  apply negR_irr, negR_ilr_head; [ reflexivity | ].
  rewrite <- (app_nil_l _). apply plus_ilr; constructor; assumption.
Qed.

Lemma ie_dual A : ielem A -> ill_ll (trans R (dual (unill A)) :: nil) A.
Proof.
induction A; intros Hgfn; inversion Hgfn; cbn; unfold trans; try now apply ax_exp_ill.
- unfold IAtom2Atom; rewrite (i2i_not_atN H0); apply ax_exp_ill.
- apply IHA1 in X.
  apply IHA2 in X0.
  rewrite <- (app_nil_l _). apply tens_ilr.
  list_simpl; cons2app. apply tens_irr; assumption.
- apply top_irr.
- apply IHA1 in X.
  apply IHA2 in X0.
  rewrite <- (app_nil_l _). apply plus_ilr; constructor; assumption.
Qed.

End RTranslation.


Lemma ie_ie_diag A : ielem A -> ill_ll (trans A (unill A) :: A :: nil) A.
Proof.
intros Hgfn.
eapply ex_ir; [ | apply Permutation_Type_swap ].
cons2app. rewrite <- (app_nil_l _). eapply cut_ir_axfree.
- intros [].
- apply ie_ie. assumption.
- apply negR_ilr_head; [ reflexivity | ]. apply ax_exp_ill.
Qed.

Lemma ie_dual_diag  A : ielem A -> ill_ll (trans A (dual (unill A)) :: nil) A.
Proof. apply ie_dual. Qed.

Lemma llR_ie_to_ill_trans R l : ielem R -> llR (unill R) l -> ill_ll (map (trans R) l) R.
Proof.
intros Hie Hll.
assert (Hax := @ax_exp_ill _ ipfrag_ill R). rewrite <- (app_nil_l (R :: _)) in Hax.
induction Hll; cbn.
- cons2app. rewrite <- (app_nil_l _).
  apply lmap_ilr; [ apply (ax_ir (a2i X)) | assumption ].
- eapply ex_ir; [ eassumption | ].
  apply Permutation_Type_map. assumption.
- list_simpl in IHHll. rewrite trans_wn in IHHll.
  list_simpl. rewrite trans_wn.
  eapply Permutation_Type_map in p.
  eapply ex_oc_ir; eassumption.
- discriminate f.
- rewrite <- 2 (app_nil_l _). apply lmap_ilr; [ apply one_irr | assumption ].
- rewrite <- (app_nil_l (ione :: _)). apply one_ilr. assumption.
- apply negR_irr in IHHll1.
  apply negR_irr in IHHll2.
  apply (tens_irr _ _ _ _ IHHll1) in IHHll2.
  apply (lmap_ilr _ _ _ _ _ _ IHHll2) in Hax.
  apply (ex_ir _ _ _ Hax).
  fold (map (trans R)). list_simpl.
  symmetry. etransitivity; [ apply Permutation_Type_cons, Permutation_Type_app_comm; reflexivity | ].
  rewrite ? app_assoc. apply Permutation_Type_cons_append.
- rewrite <- (app_nil_l (itens _ _ :: _)). apply tens_ilr.
  eapply ex_ir; [ eassumption | apply Permutation_Type_swap ].
- rewrite <- (app_nil_l (izero :: _)). apply zero_ilr.
- apply negR_irr in IHHll.
  apply (plus_irr1 _ (negR R (trans R B))) in IHHll.
  apply (lmap_ilr _ _ _ _ _ _ IHHll) in Hax.
  apply (ex_ir _ _ _ Hax).
  fold (map (trans R)). list_simpl.
  symmetry. apply Permutation_Type_cons_append.
- apply negR_irr in IHHll.
  apply (plus_irr2 _ (negR R (trans R B))) in IHHll.
  apply (lmap_ilr _ _ _ _ _ _ IHHll) in Hax.
  apply (ex_ir _ _ _ Hax).
  fold (map (trans R)). list_simpl. symmetry. apply Permutation_Type_cons_append.
- rewrite <- (app_nil_l (iplus _ _ :: _)). apply plus_ilr; assumption.
- cbn in IHHll. rewrite map_map in IHHll. cbn in IHHll. rewrite <- map_map in IHHll.
  apply negR_irr, oc_irr in IHHll.
  list_simpl in IHHll. rewrite ? map_map in IHHll.
  apply negR_ilr_head; [ reflexivity | rewrite ? map_map; assumption ].
- rewrite <- (app_nil_l (ioc _ :: _)). apply de_ilr, negR_ilr_head, negR_irr, IHHll. reflexivity.
- rewrite <- (app_nil_l (ioc _ :: _)). apply wk_ilr. assumption.
- rewrite <- (app_nil_l (ioc _ :: _)).
  change nil with (map (@ioc preiatom) nil). rewrite <- (app_nil_l (map _ _ ++ _)).
  apply co_ilr. assumption.
- apply negR_irr in IHHll1.
  apply negR_irr in IHHll2.
  apply (@stronger_ipfrag _ _ (cutupd_ipfrag ipfrag_ill ipcut_all) (cutupd_ipfrag_true _)) in IHHll1.
  apply (@stronger_ipfrag _ _ (cutupd_ipfrag ipfrag_ill ipcut_all) (cutupd_ipfrag_true _)) in IHHll2.
  assert (full_icut (cutupd_ipfrag (@ipfrag_ill preiatom) ipcut_all)) as Hcut by (intro; reflexivity).
  assert (pi0 := @trans_dual _ _ _ R (cutupd_ipfrag ipfrag_ill ipcut_all) eq_refl Hcut A).
  rewrite <- (app_nil_l _) in pi0.
  apply (cut_ir _ (Hcut _) IHHll2) in pi0.
  list_simpl in pi0. apply (cut_ir _ (Hcut _) IHHll1) in pi0.
  unfold ill_ll. change ipfrag_ill with (@cutrm_ipfrag preiatom (cutupd_ipfrag ipfrag_ill ipcut_all)).
  apply cut_admissible_ill_axfree; [ intros [] | ].
  fold (map (trans R)) in pi0. list_simpl in pi0. list_simpl. assumption.
- destruct a.
  + apply ie_dual_diag; assumption.
  + cbn. eapply ex_ir; [ | apply Permutation_Type_swap ].
    rewrite <- 2 (app_nil_l (negR _ _ :: _)). apply lmap_ilr.
    * apply one_irr.
    * eapply ex_ir; [ | apply Permutation_Type_swap ].
      apply ie_ie_diag. assumption.
Qed.


(** ** Study of the case [R = bot] *)

(** Given a sequent, the following 3 statements are equivalent:
 - the translation of the sequent is provable in [ill] for any [R];
 - the sequent is provable in [llR bot];
 - the sequent is provable in [ll].
*)

Lemma ill_trans_to_llR_bot (l : list formula) : (forall R, ill_ll (map (trans R) l) R) -> llR bot l.
Proof.
intro Hill. remember (fresh_of_list l) as z eqn:Heqz.
specialize Hill with (ivar (a2i z)).
apply ill_trans_to_llR in Hill.
apply (subs_llR bot z) in Hill. simpl subs in Hill.
change (proj1_sig (nat_injective_choice atom (self_injective_nat atom Atom_self_inj))
                    (flat_map atom_list l))
    with (fresh_of_list l) in Hill.
destruct (bijective_inverse Atom2PreIAtom_bij) as [f Hr1 Hr2]. rewrite (Hr2 z), Heqz in Hill.
rewrite repl_at_eq, (@subs_fresh_list atom_inf) in Hill. assumption.
Qed.

Lemma llR_bot_to_ll (l : list formula) : llR bot l -> ll_ll l.
Proof.
intro HR. induction HR; try discriminate f; try (constructor; assumption); try (econstructor; eassumption).
- eapply cut_ll_r; eassumption.
- destruct a; [ | apply bot_r ]; apply one_r.
Qed.

Lemma ll_ll_to_ill_trans R (l : list formula) : ll_ll l -> ill_ll (map (trans R) l) R.
Proof.
intros Hll%(ll_to_ill_trans R).
- apply cut_ill_admissible.
  eapply stronger_ipfrag, Hll.
  repeat split. intros [].
- reflexivity.
- intros ? [=].
Qed.

Lemma cut_admissible_ll_from_ill (l : list formula) : ll ((cutupd_pfrag pfrag_ll pcut_all)) l -> ll_ll l.
Proof.
remember (fresh (flat_map atom_list l)) as x eqn:Heqx. intro pi.
apply (ex_r (rev l)); [ |  symmetry; apply Permutation_Type_rev ].
rewrite <- app_nil_l. apply bot_rev; [ intros [] | ]. rewrite app_nil_l.
apply munit_elim
  with (l1 := map (subs bot x)
                  (ill2ll (ivar (a2i x)) :: rev (map dual (map ill2ll (map (trans (ivar (a2i x))) l))))).
- intros [].
- eapply (stronger_pfrag (axupd_pfrag pfrag_ll _)), subs_ll.
  + repeat split. intros [].
  + reflexivity.
  + eapply stronger_pfrag; [ eapply i2pfrag_ill_ll | ].
    apply ill_to_ll, cut_ill_admissible.
    apply (@stronger_ipfrag _ (p2ipfrag (ivar (a2i x)) (cutupd_pfrag (@pfrag_ll atom_inf) pcut_all))).
    { repeat split. intros []. }
    apply (ll_to_ill_trans (ivar (a2i x))), pi.
    * reflexivity.
    * intros ? [=].
- cbn. constructor.
  + destruct (bijective_inverse Atom2PreIAtom_bij) as [f Hr1 Hr2]. rewrite (Hr2 x), repl_at_eq.
    apply musmp_bot.
  + clear pi. rewrite map_rev. apply Forall2_inf_rev.
    assert (Forall (fun A => ~ In x (atom_list A)) l) as Hf.
    { assert (Hf := fresh_spec (flat_map atom_list l)). rewrite <- Heqx in Hf.
      clear Heqx. induction l as [|A l IHl]; constructor.
      - intro Hin. apply Hf. apply in_or_app. left. assumption.
      - apply IHl. intro Hin. apply Hf. cbn. apply in_or_app. right. assumption. }
    clear Heqx. rewrite ? map_map.
    induction l as [|C l IHl]; constructor.
    * apply munit_trans. inversion Hf. assumption.
    * apply IHl. inversion Hf. assumption.
Qed.


(** ** Study of the case [R = one] *)

(** Given a sequent, the following 3 statements are equivalent:
 - the translation of the sequent is provable in [ill] for parameter [ione];
 - the sequent is provable in [llR one];
 - the sequent is provable in [ll_mix02].
*)

Lemma ill_trans_to_llR_one (l : list formula) : ill_ll (map (trans ione) l) ione -> llR one l.
Proof. apply ill_trans_to_llR. Qed.

Lemma llR_one_to_ll_mix02 (l : list formula) : llR one l -> ll_mix02 l.
Proof.
intros pi. induction pi; try (econstructor; eassumption).
- discriminate f.
- eapply cut_mix02_r; eassumption.
- destruct a; cbn.
  + apply bot_r.
    change nil with (concat (@nil (list formula))).
    apply mix_r; constructor.
  + change (one :: one :: nil) with (concat ((@one atom :: nil) :: (one :: nil) :: nil)).
    apply mix_r; [ reflexivity | ].
    repeat (apply Forall_inf_cons; try apply one_r).
    apply Forall_inf_nil.
Qed.

Lemma ll_mix02_to_ill_trans (l : list formula) : ll_mix02 l -> ill_ll (map (trans ione) l) ione.
Proof.
intros Hll%(ll_to_ill_trans ione).
- apply cut_ill_admissible.
  eapply stronger_ipfrag; [ | apply Hll ].
  repeat split. intros [].
- reflexivity.
- intros L eqpmix FL FLind.
  destruct L; [ apply one_irr | ].
  destruct L; [ inversion eqpmix | ].
  destruct L; [ | inversion eqpmix ].
  cbn; rewrite app_nil_r.
  assert (ill (p2ipfrag ione (@pfrag_mix02 atom_inf)) (map (trans ione) l0) ione).
  { assert (In_inf l0 (l0 :: l1 :: nil)) as Hin by apply in_inf_eq.
    apply (In_Forall_inf_in _ FL) in Hin as [pi Hin].
    refine (Dependent_Forall_inf_forall_formula _ _ FLind Hin). }
  assert (ill (p2ipfrag ione (@pfrag_mix02 atom_inf)) (map (trans ione) l1) ione).
  { assert (In_inf l1 (l0 :: l1 :: nil)) as Hin by (right; apply in_inf_eq).
    apply (In_Forall_inf_in _ FL) in Hin as [pi Hin].
    refine (Dependent_Forall_inf_forall_formula _ _ FLind Hin). }
  rewrite map_app, <- (app_nil_l (map _ l0 ++ map _ l1)), <- (app_nil_r (map _ l0 ++ map _ l1)).
  eapply cut_ir_axfree.
  + intros [].
  + apply tens_irr; eassumption.
  + apply tens_ilr, one_ilr, one_ilr, one_irr.
Qed.

(** ** Study of the case [R = zero] *)

(** Given a sequent, the following 2 statements are equivalent:
 - the translation of the sequent is provable in [ill] for parameter [izero];
 - the sequent is provable in [llR zero].
*)

Lemma ill_trans_to_llR_zero (l : list formula) : ill_ll (map (trans izero) l) izero -> llR zero l.
Proof. apply ill_trans_to_llR. Qed.

Lemma llR_zero_to_ill_trans (l : list formula) : llR zero l -> ill_ll (map (trans izero) l) izero.
Proof. intros pi; apply llR_ie_to_ill_trans; [ constructor | assumption ]. Qed.

(** Moreover in these systems, the general weakening rule is admissible. *)
Lemma aff_to_ill_trans l A : ill_ll (map (trans izero) l) izero ->
  ill_ll (map (trans izero) (A :: l)) izero.
Proof.
intros Hll. cbn. cons2app.
rewrite <- (app_nil_r (map _ _)).
eapply cut_ir_axfree, zero_ilr; [ intros [] | eassumption ].
Qed.


(** ** Study of the case [R = wn one] *)

(** Given a sequent, the following 3 statements are equivalent:
 - the translation of the sequent is provable in [ill] for any parameter [R] such that [R] is provable in [ill];
 - the sequent is provable in [llR (wn one)];
 - the sequent is provable in [ll_mix0].
*)

Lemma ill_trans_to_llR_wn_one (l : list formula) :
  (forall R, ill_ll nil R -> ill_ll (map (trans R) l) R) -> llR (wn one) l.
Proof.
intros Hill.
remember (fresh_of_list l) as z.
assert (ill_ll nil (ilpam (ioc (ivar (a2i z))) (ivar (a2i z)))) as Hz
  by apply lpam_irr, de_ilr, ax_ir.
specialize Hill with (ilpam (ioc (ivar (a2i z))) (ivar (a2i z))).
assert (Hz2 := Hz).
apply Hill in Hz2. clear Hill.
apply ill_trans_to_llR in Hz2.
apply (subs_llR bot z) in Hz2. subst.
simpl subs in Hz2. destruct (bijective_inverse Atom2PreIAtom_bij) as [f Hr1 Hr2]. rewrite Hr2, repl_at_eq in Hz2.
change (proj1_sig (nat_injective_choice atom (self_injective_nat atom Atom_self_inj))
                    (flat_map atom_list l))
   with  (fresh_of_list l) in Hz2.
eapply (@llR1_R2 _ _ (wn one)) in Hz2.
- rewrite (@subs_fresh_list atom_inf) in Hz2. assumption.
- cbn. rewrite <- (app_nil_l (wn _ :: _)). apply tens_r.
  + change (wn one :: nil) with (map (@wn atom) (one :: nil)).
    apply oc_r, bot_r, de_r, one_r.
  + apply one_r.
- apply (ex_r (parr bot (wn one) :: oc bot :: nil)); [ | apply Permutation_Type_swap ].
  apply parr_r, bot_r.
  change (oc bot) with (@dual atom (wn one)). apply ax_exp.
Qed.

Lemma llR_wn_one_to_ll_mix0 (l : list formula) : llR (wn one) l -> ll_mix0 l.
Proof.
intros pi. induction pi; (try now constructor); try (econstructor; eassumption).
- eapply cut_mix0_r; eassumption.
- destruct a; cbn.
  + change nil with (map (@wn atom) nil). apply oc_r, bot_r.
    change (map wn nil) with (concat (@nil (list formula))). apply mix_r; constructor.
  + apply wk_r, one_r.
Qed.

Lemma ll_mix0_to_ill_trans R (l : list formula) : ill_ll nil R -> ll_mix0 l -> ill_ll (map (trans R) l) R.
Proof.
intros HR Hll%(stronger_pfrag _ (cutupd_pfrag pfrag_mix0 pcut_all)).
- apply (ll_to_ill_trans R) in Hll.
  + unfold ill_ll. change ipfrag_ill with (@cutrm_ipfrag preiatom (cutupd_ipfrag ipfrag_ill ipcut_all)).
    apply cut_admissible_ill_axfree; [ intros [] | ].
    eapply stronger_ipfrag; [ | apply Hll ].
    repeat split. intros [].
  + reflexivity.
  + intros L eqpmix FL FLind.
    destruct L; try (discriminate eqpmix).
    cbn. eapply stronger_ipfrag; [ | apply HR ].
    repeat split. intros [].
- now repeat split.
Qed.

(** ** Study of the case [R = oc bot] *)

(** Given a sequent, the following 3 statements are equivalent:
 - the translation of the sequent is provable in [ill] for any parameter [ioc R];
 - the sequent is provable in [llR (oc bot)];
 - the sequent is provable in [ll_bbb].
*)

Lemma ill_trans_to_llR_oc_bot (l : list formula) : (forall R, ill_ll (map (trans (ioc R)) l) (ioc R)) ->
  llR (oc bot) l.
Proof.
intros Hill.
remember (fresh_of_list l) as z.
specialize Hill with (ivar (a2i z)).
apply ill_trans_to_llR in Hill.
apply (subs_llR bot z) in Hill. subst.
simpl subs in Hill. destruct (bijective_inverse Atom2PreIAtom_bij) as [f Hr1 Hr2].
rewrite Hr2, repl_at_eq in Hill.
change (proj1_sig (nat_injective_choice atom (self_injective_nat atom Atom_self_inj))
                  (flat_map atom_list l))
   with  (fresh_of_list l) in Hill.
rewrite (@subs_fresh_list atom_inf) in Hill. assumption.
Qed.

Lemma llR_oc_bot_to_ll_bbb (l : list formula) : llR (oc bot) l -> ll_bbb l.
Proof. apply bb_to_bbb. Qed.

Lemma ll_mix02_to_ill_trans_gen R (l : list formula) : ll_mix02 l ->
  ill_ll (ioc R :: map (trans (ioc R)) l) (ioc R).
Proof.
intros Hll.
change (ioc R :: map (trans _) l)
  with (map ioc (R :: nil) ++ map (trans (ioc R)) l).
apply (stronger_pfrag _ (cutupd_pfrag pfrag_mix02 pcut_all)) in Hll.
- assert (@pperm atom_inf (cutupd_pfrag pfrag_mix02 pcut_all) = true) as Hperm by reflexivity.
  apply (ll_to_ill_trans_gen (ioc R) Hperm (R :: nil)) in Hll.
  + unfold ill_ll. change ipfrag_ill with (@cutrm_ipfrag preiatom (cutupd_ipfrag ipfrag_ill ipcut_all)).
    apply cut_admissible_ill_axfree; [ intros [] | ].
    eapply stronger_ipfrag; [ | apply Hll ].
    repeat split. intros [].
  + intros L eqpmix FL FLind.
    destruct L; [ intros; apply ax_exp_ill | ].
    destruct L; [ discriminate eqpmix | ].
    destruct L; [ | discriminate eqpmix ].
    assert (ill (p2ipfrag (ioc R) (cutupd_pfrag (@pfrag_mix02 atom_inf) pcut_all))
                (map ioc (R :: nil) ++ map (trans (ioc R)) l0) (ioc R)).
    { assert (In_inf l0 (l0 :: l1 :: nil)) as Hin by apply in_inf_eq.
      apply (In_Forall_inf_in _ FL) in Hin as [pi Hin].
      apply (Dependent_Forall_inf_forall_formula _ _ FLind Hin). }
    assert (ill (p2ipfrag (ioc R) (cutupd_pfrag (@pfrag_mix02 atom_inf) pcut_all))
                (map ioc (R :: nil) ++ map (trans (ioc R)) l1) (ioc R)).
    { assert (In_inf l1 (l0 :: l1 :: nil)) as Hin by (right; apply in_inf_eq).
      apply (In_Forall_inf_in _ FL) in Hin as [pi Hin].
      apply (Dependent_Forall_inf_forall_formula _ _ FLind Hin). }
    cbn. rewrite app_nil_r, map_app, <- (app_nil_l (ioc R :: _)), <- (app_nil_r (map _ l1)).
    rewrite app_comm_cons, (app_assoc _ (map _ l1)).
    assert (forall C, ipcut (p2ipfrag (ioc R) (cutupd_pfrag (@pfrag_mix02 atom_inf) pcut_all)) C = true)
      as Hcut by reflexivity.
    apply (cut_ir (itens (ioc R) (ioc R)) (Hcut _)).
    * rewrite <- 2 (app_nil_l (ioc R :: _)), <- ? app_assoc.
      change nil with (map (@ioc preiatom) nil) at 2.
      apply co_ilr.
      eapply ex_ir.
      -- apply tens_irr; [ apply X | apply X0 ].
      -- symmetry. apply Permutation_Type_cons, Permutation_Type_middle. reflexivity.
    * apply tens_ilr, wk_ilr, ax_exp_ill.
- now repeat split.
Qed.

Lemma ll_bbb_to_ill_trans R (l : list formula) : ll_bbb l -> ill_ll (map (trans (ioc R)) l) (ioc R).
Proof.
intro Hll. induction Hll; try discriminate f; cbn.
- cons2app. rewrite <- (app_nil_l _). apply lmap_ilr.
  + apply (ax_ir (a2i X)).
  + rewrite app_nil_l. apply ax_exp_ill.
- eapply ex_ir; [ eassumption | apply Permutation_Type_map; assumption ].
- apply (ll_mix02_to_ill_trans_gen R) in l.
  rewrite <- (app_nil_l (ioc _ :: _)) in l.
  rewrite map_app, <- (app_nil_r (map _ l1)).
  eapply (cut_ir_axfree); [ intros [] | eassumption | ].
  eapply ex_ir; [ | apply Permutation_Type_app_comm ]; assumption.
- apply negR_ilr_head, one_irr. reflexivity.
- rewrite <- (app_nil_l (ione :: _)). apply one_ilr. assumption.
- apply negR_ilr_head; [ reflexivity | ].
  list_simpl. eapply ex_ir; [ | apply Permutation_Type_app_comm ].
  list_simpl in IHHll1. list_simpl in IHHll2.
  apply tens_irr; apply negR_irr; assumption.
- rewrite <- (app_nil_l (itens _ _ :: _)). apply tens_ilr.
  eapply ex_ir; [ eassumption | apply Permutation_Type_swap ].
- rewrite <- (app_nil_l (izero :: _)). apply zero_ilr.
- apply negR_ilr_head, plus_irr1, negR_irr, IHHll. reflexivity.
- apply negR_ilr_head, plus_irr2, negR_irr, IHHll. reflexivity.
- rewrite <- (app_nil_r (map _ _)), <- (app_nil_l (iplus _ _ :: _)).
  list_simpl in IHHll1. list_simpl in IHHll2.
  apply plus_ilr; list_simpl; [ apply IHHll1 | apply IHHll2 ].
- apply negR_ilr_head; [ reflexivity | ].
  rewrite map_map. cbn. rewrite <- map_map.
  cbn in IHHll. rewrite map_map in IHHll. cbn in IHHll. rewrite <- map_map in IHHll.
  apply oc_irr, negR_irr. assumption.
- rewrite <- (app_nil_l (ioc _ :: _)). apply de_ilr.
  list_simpl. apply negR_ilr_head, negR_irr, IHHll. reflexivity.
- rewrite <- (app_nil_l (ioc _ :: _)). apply wk_ilr. assumption.
- rewrite <- 2 (app_nil_l (ioc _ :: _)). change nil with (map (@ioc preiatom) nil). apply co_ilr. assumption.
Qed.

(** The following result is the converse of [bb_to_bbb] proved in bbb.v *)

Lemma bbb_to_bb (l : list formula) : ll_bbb l -> llR (oc bot) l.
Proof. intro pi. apply ill_trans_to_llR_oc_bot. intro. apply ll_bbb_to_ill_trans, pi. Qed.

End Atoms.
