(* nn_foc file for yalla library *)

(** * Focusing by Polarized Translation *)

From Coq Require Import CMorphisms.
From OLlibs Require Import funtheory infinite List_more
                           Permutation_Type_more GPermutation_Type.
From Yalla Require Import ll_fragments llfoc tl nn_prop.

Set Implicit Arguments.


Section Atoms.

Context { atom : DecType }.
Context { preiatom : InfDecType }.
Context { tatom : DecType }.
Context { Atoms : AtomIAtomTAtomType atom preiatom tatom }.

Notation atom_inf := (@atom_inf _ _ AtomIAtomTAtom_Atom2IAtom).
Notation formula := (@formula atom_inf).
Notation iformula := (@iformula preiatom).
Notation tformula := (@tformula tatom).
Notation a2i := (@a2i _ _ AtomIAtomTAtom_Atom2IAtom).
Notation t2i := (@t2i atom_inf _ _ AtomIAtomTAtom_TAtom).
Notation ill_ll := (@ill_ll preiatom).
Notation tl2ill := (@tl2ill atom_inf _ _ AtomIAtomTAtom_TAtom).
Notation trans := (@trans _ _ AtomIAtomTAtom_Atom2IAtom).

Definition a2t X :=
  proj1_sig (sig_of_sig2 (bijective_inverse TAtom2PreIAtom_bij)) (Atom2PreIAtom X).
Lemma a2t_inj : injective a2t.
Proof.
unfold a2t; apply compose_injective.
- apply bijective_injective.
  apply Atom2PreIAtom_bij.
- destruct (bijective_inverse TAtom2PreIAtom_bij).
  now apply section_injective with TAtom2PreIAtom.
Qed.
Lemma a2i_a2i a : t2i (a2t a) = a2i a.
Proof.
unfold t2i, a2t, a2i; f_equal.
destruct (bijective_inverse TAtom2PreIAtom_bij) as [f Hf1 Hf2]; cbn.
now rewrite Hf1.
Qed.


(** ** Polarized Translation *)

Fixpoint ptrans C :=
match C with
| var x => tvar (a2t x)
| one => tone
| tens A B => ttens (ptrans A) (ptrans B)
| zero => tzero
| aplus A B => tplus (ptrans A) (ptrans B)
| oc A => toc (tneg (ntrans A))
| covar x => tneg (tvar (a2t x))
| bot => tneg tone
| parr A B => tneg (ttens (ntrans B) (ntrans A))
| top => tneg (tzero)
| awith A B => tneg (tplus (ntrans A) (ntrans B))
| wn A => tneg (toc (tneg (ptrans A)))
end
with ntrans C :=
match C with
| var x => tneg (tvar (a2t x))
| one => tneg tone
| tens A B => tneg (ttens (ptrans A) (ptrans B))
| zero => tneg tzero
| aplus A B => tneg (tplus (ptrans A) (ptrans B))
| oc A => tneg (toc (tneg (ntrans A)))
| covar x => tvar (a2t x)
| bot => tone
| parr A B => ttens (ntrans B) (ntrans A)
| top => tzero
| awith A B => tplus (ntrans A) (ntrans B)
| wn A => toc (tneg (ptrans A))
end.

Lemma pntrans_neg (A : formula) :
   (aformula A -> ptrans A = tneg (ntrans A))
/\ (sformula A -> ntrans A = tneg (ptrans A)).
Proof. induction A ; (split; intros Hpol; inversion Hpol); reflexivity. Qed.

Lemma pntrans_dual A : ptrans (dual A) = ntrans A /\ ntrans (dual A) = ptrans A.
Proof.
induction A; cbn;
  try (destruct IHA as [IHAl IHAr]);
  try (destruct IHA1 as [IHA1l IHA1r]);
  try (destruct IHA2 as [IHA2l IHA2r]);
  rewrite ? IHAl, ? IHAr, ? IHA1l, ? IHA1r, ? IHA2l, ? IHA2r;
  split; reflexivity.
Qed.

Lemma ntrans_map_toc l : map ntrans (map wn l) = map toc (map tneg (map ptrans l)).
Proof. induction l as [ | a l IHl ]; [ | cbn; rewrite IHl ]; reflexivity. Qed.

Lemma ntrans_map_toc_inv l1 l2 : map toc l1 = map ntrans l2 ->
  { l2' | l2 = map wn l2' & l1 = map tneg (map ptrans l2') }.
Proof.
induction l1 in l2 |- *; intros Heq; destruct l2; inversion Heq.
- exists nil; reflexivity.
- apply IHl1 in H1.
  destruct f; inversion H0.
  destruct H1 as [l2' -> ->].
  exists (f :: l2'); reflexivity.
Qed.

Lemma pntrans_to_trans (A : formula) : ill_ll (tl2ill (ntrans A) :: nil) (trans N A) ->
  ill_ll (negR N (trans N A) :: tl2ill (tneg (ptrans A)) :: nil) N.
Proof.
intros pi.
destruct (polarity A).
- apply negR_ilr; [ reflexivity | | ].
  + apply ax_ir.
  + rewrite <- (proj2 (pntrans_neg _)); assumption.
- rewrite (proj1 (pntrans_neg _)); [ | assumption ].
  cons2app.
  apply neg_ilr, neg_irr.
  eapply ex_ir; [ | apply Permutation_Type_swap ].
  apply negR_ilr; [ reflexivity | | assumption ].
  apply ax_ir.
Qed.

Lemma ntrans_to_trans A : ill_ll (tl2ill (ntrans A) :: nil) (trans N A).
Proof.
induction A; simpl.
- apply negR_irr.
  cons2app.
  apply neg_ilr.
  rewrite a2i_a2i.
  apply ax_ir.
- rewrite a2i_a2i.
  apply ax_ir.
- apply negR_irr.
  cons2app.
  apply neg_ilr.
  rewrite <- (app_nil_l _).
  apply one_ilr.
  apply one_irr.
- rewrite <- (app_nil_l _).
  apply one_ilr.
  apply one_irr.
- apply negR_irr.
  assert (H' := @ineg_to_ilmap _ ipfrag_ill
                  (itens (tl2ill (ptrans A1)) (tl2ill (ptrans A2)))).
  cons2app.
  refine (cut_ir_axfree _ _ _ _ _ _ H' _) ; [ intros a ; destruct a | ].
  unfold ill_ll ; change ipfrag_ill with (@cutrm_ipfrag preiatom (cutupd_ipfrag ipfrag_ill true)).
  apply cut_admissible_ill_axfree ; [ intros a ; destruct a | ].
  apply neg_tens_propag; [ reflexivity | reflexivity | | ].
  + apply pntrans_to_trans in IHA1.
    cons2app in IHA1.
    assert (H1 := @ilmap_to_ineg _ ipfrag_ill (tl2ill (ptrans A1))).
    apply (stronger_ipfrag _ (cutupd_ipfrag ipfrag_ill true) (cutupd_ipfrag_true _)) in H1.
    apply (stronger_ipfrag _ (cutupd_ipfrag ipfrag_ill true) (cutupd_ipfrag_true _)) in IHA1.
    refine (cut_ir _ _ _ _ _ _ H1 IHA1); reflexivity.
  + apply pntrans_to_trans in IHA2.
    cons2app in IHA2.
    assert (H2 := @ilmap_to_ineg _ ipfrag_ill (tl2ill (ptrans A2))).
    apply (stronger_ipfrag _ (cutupd_ipfrag ipfrag_ill true) (cutupd_ipfrag_true _)) in H2.
    apply (stronger_ipfrag _ (cutupd_ipfrag ipfrag_ill true) (cutupd_ipfrag_true _)) in IHA2.
    refine (cut_ir _ _ _ _ _ _ H2 IHA2); reflexivity.
- rewrite <- (app_nil_l _).
  apply tens_ilr.
  list_simpl.
  cons2app.
  apply tens_irr; assumption.
- apply negR_irr.
  rewrite <- (app_nil_l _).
  apply zero_ilr.
- rewrite <- (app_nil_l _).
  apply zero_ilr.
- apply negR_irr.
  assert (H' := @ineg_to_ilmap _ ipfrag_ill
                  (iplus (tl2ill (ptrans A1)) (tl2ill (ptrans A2)))).
  cons2app.
  refine (cut_ir_axfree _ _ _ _ _ _ H' _) ; [ intros a ; destruct a | ].
  unfold ill_ll ; change ipfrag_ill with (@cutrm_ipfrag preiatom (cutupd_ipfrag ipfrag_ill true)).
  apply cut_admissible_ill_axfree ; [ intros a ; destruct a | ].
  apply neg_plus_propag; [ reflexivity | reflexivity | | ].
  + apply pntrans_to_trans in IHA1.
    cons2app in IHA1.
    assert (H1 := @ilmap_to_ineg _ ipfrag_ill (tl2ill (ptrans A1))).
    apply (stronger_ipfrag _ (cutupd_ipfrag ipfrag_ill true) (cutupd_ipfrag_true _)) in H1.
    apply (stronger_ipfrag _ (cutupd_ipfrag ipfrag_ill true) (cutupd_ipfrag_true _)) in IHA1.
    refine (cut_ir _ _ _ _ _ _ H1 IHA1); reflexivity.
  + apply pntrans_to_trans in IHA2.
    cons2app in IHA2.
    assert (H2 := @ilmap_to_ineg _ ipfrag_ill (tl2ill (ptrans A2))).
    apply (stronger_ipfrag _ (cutupd_ipfrag ipfrag_ill true) (cutupd_ipfrag_true _)) in H2.
    apply (stronger_ipfrag _ (cutupd_ipfrag ipfrag_ill true) (cutupd_ipfrag_true _)) in IHA2.
    refine (cut_ir _ _ _ _ _ _ H2 IHA2); reflexivity.
- rewrite <- (app_nil_l _).
  apply plus_ilr ; list_simpl.
  + apply plus_irr1; assumption.
  + apply plus_irr2; assumption.
- apply negR_irr.
  cons2app.
  apply neg_ilr.
  change (ioc (negR N (trans N A)) :: nil)
    with (map ioc (negR N (trans N A) :: nil)).
  apply oc_irr.
  rewrite <- (app_nil_l _).
  apply de_ilr.
  apply neg_irr.
  eapply ex_ir ; [ | apply Permutation_Type_swap ].
  apply negR_ilr; [ reflexivity | | assumption ].
  apply ax_ir.
- apply pntrans_to_trans in IHA.
  change (ioc (ineg (tl2ill (ptrans A))) :: nil)
    with (map ioc (ineg (tl2ill (ptrans A)) :: nil)).
  apply oc_irr.
  rewrite <- (app_nil_l _).
  apply de_ilr, negR_irr; assumption.
Qed.

Definition tpfrag_tl := @mk_tpfrag tatom false NoTAxioms true.
(*                                 atoms cut   axioms            perm  *)
Definition tl_ll := tl tpfrag_tl.

Proposition ll_to_tl (l : list formula) : ll_ll l -> tl_ll (map ntrans l) None.
Proof.
intros pi.
apply (@ll_ll_to_ill_trans _ _ AtomIAtomTAtom_Atom2IAtom N) in pi.
assert (forall l1 l2, ill_ll (map (trans N) l1 ++ map tl2ill (map ntrans l2)) N
          -> ill_ll (map tl2ill (map ntrans (l1 ++ l2))) N)
 as IH.
{ clear; induction l1; intros l2 pi; [ assumption | ].
  list_simpl in pi.
  assert (Ha := ntrans_to_trans a).
  eapply ex_ir in pi ; [ | apply Permutation_Type_middle ].
  assert (projT1 (@ipgax preiatom ipfrag_ill) -> False) as Hgax by (intros x; destruct x).
  eapply (cut_ir_axfree Hgax _ _ _ _ _ Ha) in pi.
  list_simpl in pi.
  change (tl2ill (ntrans a) :: map tl2ill (map ntrans l2))
    with (map tl2ill (map ntrans (a :: l2))) in pi.
  apply IHl1 in pi.
  eapply ex_ir;
    [ eassumption | list_simpl; symmetry; apply Permutation_Type_middle ]. }
rewrite <- (app_nil_r _) in pi.
change nil with (map tl2ill (map ntrans nil)) in pi.
apply IH in pi.
list_simpl in pi.
apply cut_admissible_ill in pi; try now (intros a; destruct a).
eapply (stronger_tpfrag (cutrm_tpfrag tpfrag_tl)).
- repeat split.
  intros a; destruct a.
- eapply tlfrag2tl_cutfree; [ reflexivity | ].
  rewrite <- (@cutrm_t2ipfrag atom_inf).
  eapply stronger_ipfrag; [ | apply pi].
  repeat split.
  intros a ; destruct a.
Qed.

(* ** Proof of Focusing *)

Section Focusing.

Inductive otl : list tformula -> option tformula -> Type :=
| ax_otr : forall X, otl (tvar X :: nil) (Some (tvar X))
| ex_otr : forall l1 l2 A, otl l1 A -> Permutation_Type l1 l2 ->
                           otl l2 A
| one_otrr : otl nil (Some tone)
| one_otlr : forall l1 l2 A, otl (l1 ++ l2) A ->
                             otl (l1 ++ tone :: l2) A
| tens_otrr : forall A B l1 l2,
                    otl l1 (Some A) -> otl l2 (Some B) ->
                    otl (l1 ++ l2) (Some (ttens A B))
| tens_otlr : forall A B l1 l2 C,
                    otl (l1 ++ A :: B :: l2) C ->
                    otl (l1 ++ ttens A B :: l2) C
| neg_otrr : forall A l,
                    otl (A :: l) None ->
                    otl l (Some (tneg A))
| neg_otlr : forall A l, otl l (Some A) ->
                         otl (l ++ tneg A :: nil) None
| zero_otlr : forall l1 l2 C, otl (l1 ++ tzero :: l2) C
| plus_otrr1 : forall A B l, otl l (Some A) ->
                             otl l (Some (tplus A B))
| plus_otrr2 : forall A B l, otl l (Some A) ->
                             otl l (Some (tplus B A))
| plus_otlr : forall A B l1 l2 C,
                        otl (l1 ++ A :: l2) C ->
                        otl (l1 ++ B :: l2) C ->
                        otl (l1 ++ tplus A B :: l2) C
| oc_otrr : forall A l, otl (A :: map toc l) None ->
                        otl (map toc l) (Some (toc (tneg A)))
| de_otlr : forall A l, otl l (Some A) ->
                        otl (l ++ toc (tneg A) :: nil) None
| wk_otlr : forall A l1 l2 C,
                        otl (l1 ++ l2) C ->
                        otl (l1 ++ toc A :: l2) C
| co_otlr : forall A l1 l2 C,
                        otl (l1 ++ toc A :: toc A :: l2) C ->
                        otl (l1 ++ toc A :: l2) C.

Instance otl_perm Pi : Proper ((@Permutation_Type _) ==> arrow) (fun l => otl l Pi).
Proof. intros l1 l2 HP pi; eapply ex_otr; eassumption. Qed.

Lemma neg_rev_ot A l : otl l (Some (tneg A)) -> otl (A :: l) None.
Proof.
intros pi.
remember (Some (tneg A)) as Pi.
revert A HeqPi; induction pi; intros A' HeqPi;
  try (now (inversion HeqPi)); subst;
  try (now (rewrite app_comm_cons;
            constructor;
            rewrite <- app_comm_cons;
            apply IHpi)).
- eapply ex_otr.
  + apply IHpi; reflexivity.
  + apply Permutation_Type_cons; [ reflexivity | assumption ].
- inversion HeqPi; subst; assumption.
- rewrite app_comm_cons.
  apply plus_otlr; rewrite <- app_comm_cons.
  + apply IHpi1; reflexivity.
  + apply IHpi2; reflexivity.
Qed.

Lemma tsubform_toc_ntrans A B : tsubform (toc A) (ntrans B) -> { A' | A = tneg A' }.
Proof.
intros Hsub.
apply (@inl _ (tsubform (toc A) (ptrans B))) in Hsub.
revert Hsub; clear; induction B; intros [ Hsub | Hsub ];
  try (now (inversion Hsub; subst ; inversion H1));
  try (now (inversion Hsub; inversion X; subst;
              try (apply IHB1; right; assumption);
              try (apply IHB2; right; assumption)));
  try (now (inversion Hsub; inversion X; subst;
              try (apply IHB1; left; assumption);
              try (apply IHB2; left; assumption))).
- inversion Hsub; inversion X; subst.
  + eexists; reflexivity.
  + inversion X0; subst; apply IHB; left; assumption.
  + eexists; reflexivity.
  + inversion X0; subst; apply IHB; left; assumption.
- inversion Hsub; subst.
  + eexists; reflexivity.
  + inversion X; subst; apply IHB; left; assumption.
- inversion Hsub; subst.
  + eexists; reflexivity.
  + inversion X; subst; apply IHB; right; assumption.
- inversion Hsub; inversion X; subst.
  + eexists; reflexivity.
  + inversion X0; subst; apply IHB; right; assumption.
  + eexists; reflexivity.
  + inversion X0; subst; apply IHB; right; assumption.
Qed.

(* ** From [tl] to [otl] *)

Ltac Forall_inf_cbn_hyp :=
  repeat (
    match goal with
    | H:Forall_inf _ (_ ++ _) |- _ => let H1 := fresh H in assert (H1 := Forall_inf_app_l _ _ H);
                                      let H2 := fresh H in assert (H2 := Forall_inf_app_r _ _ H);
                                      clear H
    | H:Forall_inf _ (_ :: _) |- _ => inversion H ; clear H
    end).
Ltac Forall_inf_solve_rec :=
  match goal with
  | |- Forall_inf _ (_ ++ _) => apply Forall_inf_app ; Forall_inf_solve_rec
  | |- Forall_inf _ (_ :: _) => constructor ; [ assumption | Forall_inf_solve_rec ]
  | |- Forall_inf _ nil => constructor
  | _ => try assumption
  end.
Ltac Forall_inf_solve := Forall_inf_cbn_hyp; cbn; Forall_inf_solve_rec.

Lemma tl_to_otl_neg l C : tl_ll l C ->
  Forall_inf (fun F => { x & tsubform F (ntrans x) }) l ->
  (forall D, C = Some D -> { x & tsubform D (ntrans x) } ) ->
  forall l1 l2, Permutation_Type l (l1 ++ map tneg l2) ->
  otl (l1 ++ map toc (map tneg l2)) C.
Proof.
intros pi%(@cut_admissible_tl_axfree atom_inf _ _ AtomIAtomTAtom_TAtom); [ | intros [] ].
induction pi; intros HF HC l1' l2' HP.
- apply Permutation_Type_length_1_inv in HP.
  destruct l1'; inversion HP.
  + destruct l2'; inversion H0.
  + apply app_eq_nil in H1.
    destruct H1; subst.
    destruct l2'; inversion H1.
    apply ax_otr.
- cbn in p.
  apply IHpi; [ | assumption | ].
  + symmetry in p.
    eapply Permutation_Type_Forall_inf; eassumption.
  + etransitivity; eassumption.
- apply (Permutation_Type_map toc) in p.
  apply IHpi; [ | assumption | ].
  + eapply Permutation_Type_Forall_inf; [ | eassumption ].
    apply Permutation_Type_app_head, Permutation_Type_app_tail; symmetry; assumption.
  + etransitivity; [ | eassumption ].
    apply Permutation_Type_app_head, Permutation_Type_app_tail; assumption.
- apply Permutation_Type_nil in HP.
  apply app_eq_nil in HP.
  destruct HP ; subst.
  destruct l2'; inversion H0.
  apply one_otrr.
- assert (HP' := HP).
  apply Permutation_Type_elt_map_inv in HP'; [ | intros b Hf ; inversion Hf ].
  destruct HP' as [(l1'' & l2'') ->].
  list_simpl; constructor.
  rewrite app_assoc.
  apply IHpi; [ Forall_inf_solve | assumption | ].
  list_simpl; list_simpl in HP.
  apply Permutation_Type_app_inv in HP; assumption.
- apply Permutation_Type_app_app_inv in HP.
  destruct HP as [[[[l3' l3''] l4'] l4''] [[HP1 HP2] [HP3 HP4]]].
  symmetry in HP4; apply Permutation_Type_map_inv in HP4 as [l3''' Heq HP4].
  symmetry in Heq; decomp_map_inf Heq; subst.
  apply ex_otr with ((l3' ++ map toc (map tneg l0)) ++ l3'' ++ map toc (map tneg l3)).
  + constructor.
    * apply IHpi1 in HP1; [ assumption | Forall_inf_solve | ].
      destruct (HC _ (eq_refl _)) as [D HD].
      intros D0 Heq0; inversion Heq0; subst.
      eexists.
      etransitivity; [ | apply HD].
      constructor; constructor.
    * apply IHpi2 in HP2; [ assumption | Forall_inf_solve | ].
      destruct (HC _ (eq_refl _)) as [D HD].
      intros D0 Heq0; inversion Heq0; subst.
      eexists.
      etransitivity; [ | apply HD].
      constructor; constructor.
  + assert (Permutation_Type (l1' ++ map toc (map tneg l2'))
                         ((l3' ++ l3'') ++ map toc (map tneg (l0 ++ l3)))) as HP'
      by (apply Permutation_Type_app, Permutation_Type_map, Permutation_Type_map; assumption).
    symmetry; etransitivity; [ apply HP' | ]; list_simpl.
    apply Permutation_Type_app_head; rewrite ? app_assoc;
      apply Permutation_Type_app_tail, Permutation_Type_app_comm.
- assert (HP' := HP).
  apply Permutation_Type_elt_map_inv in HP'; [ | intros b Hf; inversion Hf ].
  destruct HP' as [(l1'' & l2'') ->].
  list_simpl; constructor.
  rewrite 2 app_comm_cons, app_assoc.
  apply IHpi; [ | assumption | ].
  + Forall_inf_solve; Forall_inf_cbn_hyp; subst.
    destruct X as [S Hs].
    constructor.
    * exists S.
      etransitivity; [ | apply Hs].
      constructor; constructor.
    * constructor; [ | assumption ].
      exists S.
      etransitivity; [ | apply Hs].
      constructor; constructor.
  + list_simpl; list_simpl in HP.
    apply Permutation_Type_app_inv in HP.
    apply Permutation_Type_elt, Permutation_Type_elt; assumption.
- constructor.
  apply (@Permutation_Type_cons _ A _ (eq_refl _)) in HP.
  rewrite app_comm_cons in HP.
  apply IHpi in HP; [ assumption | | ].
  + constructor; [ | assumption ].
    destruct (HC _ (eq_refl _)) as [D HD].
    eexists.
    etransitivity; [ | apply HD ].
    constructor; constructor.
  + intros D HD; inversion HD.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_elt_inv in HP' as [(l' & l'') Heq].
  dichot_elt_app_inf_exec Heq; subst.
  + apply ex_otr with ((l' ++ l0 ++ map toc (map tneg l2')) ++ tneg A :: nil);
    [ | list_simpl; apply Permutation_Type_app_head; rewrite app_assoc; symmetry;
        apply Permutation_Type_cons_app; list_simpl; reflexivity ].
    constructor.
    rewrite app_assoc.
    apply IHpi; [ Forall_inf_solve | Forall_inf_solve | ].
    * intros D HD; inversion HD; subst.
      destruct X as [D' HD'].
      eexists.
      etransitivity; [ | apply HD'].
      constructor; constructor.
    * list_simpl; list_simpl in HP.
      apply Permutation_Type_app_inv in HP.
      list_simpl in HP; assumption.
  + symmetry in Heq1; decomp_map_inf Heq1; subst.
    inversion Heq1; subst.
    list_simpl.
    apply ex_otr with ((l1' ++ map toc (map tneg (l2 ++ l4))) ++ toc (tneg A) :: nil);
      [ | list_simpl;
          apply Permutation_Type_app_head, Permutation_Type_app_head, Permutation_Type_app_comm ].
    constructor.
    apply IHpi; [ Forall_inf_solve | Forall_inf_solve | ].
    * intros D HD; inversion HD; subst.
      destruct X as [D' HD'].
      eexists.
      etransitivity; [ | apply HD'].
      constructor; constructor.
    * list_simpl; list_simpl in HP.
      rewrite app_assoc in HP.
      apply Permutation_Type_app_inv in HP.
      list_simpl in HP; assumption.
- assert (HP' := HP).
  apply Permutation_Type_elt_map_inv in HP'; [ | intros b Hf ; inversion Hf ].
  destruct HP' as [(l1'' & l2'') ->].
  list_simpl; constructor.
- apply plus_otrr1.
  apply IHpi; [ Forall_inf_solve | | assumption ].
  destruct (HC _ (eq_refl _)) as [D HD].
  intros D0 Heq0; inversion Heq0; subst.
  eexists.
  etransitivity; [ | apply HD].
  constructor; constructor.
- apply plus_otrr2.
  apply IHpi; [ Forall_inf_solve | | assumption ].
  destruct (HC _ (eq_refl _)) as [D HD].
  intros D0 Heq0; inversion Heq0; subst.
  eexists.
  etransitivity; [ | apply HD].
  constructor; constructor.
- assert (HP' := HP).
  apply Permutation_Type_elt_map_inv in HP'; [ | intros b Hf ; inversion Hf ].
  destruct HP' as [(l1'' & l2'') ->].
  list_simpl.
  constructor; rewrite app_comm_cons, app_assoc.
  + apply IHpi1; [ Forall_inf_solve | Forall_inf_solve | ].
    * constructor; [ | assumption ].
      destruct X as [D' HD'].
      eexists.
      etransitivity; [ | apply HD'].
      constructor; constructor.
    * list_simpl; list_simpl in HP.
      apply Permutation_Type_app_inv in HP.
      apply Permutation_Type_elt; assumption.
  + apply IHpi2; [ Forall_inf_solve | Forall_inf_solve | ].
    * constructor; [ | assumption ].
      destruct X as [D' HD'].
      eexists.
      etransitivity; [ | apply HD'].
      constructor; constructor.
    * list_simpl; list_simpl in HP.
      apply Permutation_Type_app_inv in HP.
      apply Permutation_Type_elt; assumption.
- symmetry in HP.
  apply Permutation_Type_map_inv in HP as [l3 Heq HP].
  symmetry in Heq; decomp_map_inf Heq; subst.
  assert (l2' = nil) as -> by (destruct l2'; [ reflexivity | destruct l2; inversion Heq2 ]).
  list_simpl.
  destruct (HC (toc A) (eq_refl _)) as [A' HC'].
  destruct (tsubform_toc_ntrans _ HC') as [A'' ->].
  apply oc_otrr.
  destruct l2; inversion Heq2.
  replace (map toc l1) with (map toc l1 ++ map toc (map tneg nil)) by (list_simpl; reflexivity).
  apply neg_rev_ot.
  apply IHpi; [ Forall_inf_solve | | ].
  + destruct (HC _ (eq_refl _)) as [D HD].
    intros D0 Heq0; inversion Heq0; subst.
    eexists.
    etransitivity; [ | apply HD].
    constructor; constructor.
  + list_simpl in HP; list_simpl.
    apply Permutation_Type_map; assumption.
- Forall_inf_cbn_hyp; subst.
  destruct X as [At HAt].
  destruct (tsubform_toc_ntrans _ HAt) as [B ->].
  assert (HP' := HP).
  apply Permutation_Type_elt_map_inv in HP'; [ | intros b Hf ; inversion Hf ].
  destruct HP' as [(l1'' & l2'') ->].
  list_simpl.
  apply ex_otr with ((l1'' ++ l2'') ++ map toc (map tneg (B :: l2')));
    [ | list_simpl; apply Permutation_Type_app_head; symmetry; apply Permutation_Type_middle ].
  apply IHpi; [ Forall_inf_solve | Forall_inf_solve | ].
  + constructor; [ | assumption ].
    eexists.
    etransitivity; [ | apply HAt ].
    constructor; constructor.
  + list_simpl in HP.
    apply Permutation_Type_app_inv in HP.
    apply Permutation_Type_elt; list_simpl; assumption.
- assert (HP' := HP).
  apply Permutation_Type_elt_map_inv in HP'; [ | intros b Hf ; inversion Hf ].
  destruct HP' as [(l1'' & l2'') ->].
  list_simpl; constructor.
  rewrite app_assoc.
  apply IHpi; [ Forall_inf_solve | assumption | ].
  list_simpl; list_simpl in HP.
  apply Permutation_Type_app_inv in HP; assumption.
- assert { l3 & Permutation_Type l1' (toc A :: l3) } as [l3 HPw].
  { symmetry in HP; apply Permutation_Type_vs_elt_inv in HP.
    destruct HP as [[l1l l1r] Heq]; cbn in Heq.
    revert l1l Heq; clear ; induction l1'; intros l1l Heq.
    - exfalso.
      cbn in Heq; decomp_map Heq.
      inversion Heq3.
    - destruct l1l; inversion Heq; subst.
      + exists l1'; reflexivity.
      + apply IHl1' in H1 as [l3 H1].
        exists (t :: l3).
        apply (Permutation_Type_cons (eq_refl t)) in H1.
        etransitivity; [ eassumption | apply Permutation_Type_swap ]. }
  apply ex_otr with (l3 ++ toc A :: map toc (map tneg l2'));
    [ | symmetry; etransitivity; [ apply Permutation_Type_app_tail; eassumption
                                 | apply Permutation_Type_middle ] ].
  apply co_otlr.
  cons2app; rewrite 2 app_assoc.
  apply IHpi; [ Forall_inf_solve | assumption | ].
  list_simpl.
  apply Permutation_Type_elt.
  etransitivity; [ eassumption | ].
  etransitivity; [ apply Permutation_Type_app_tail; eassumption | apply Permutation_Type_middle ].
- inversion f.
- destruct a.
Qed.

Proposition tl_to_otl l : tl_ll (map ntrans l) None -> otl (map ntrans l) None.
Proof.
intros pi.
replace (map ntrans l) with (map ntrans l ++ map toc (map tneg nil))
  by (list_simpl; reflexivity).
eapply tl_to_otl_neg; [ eassumption | | | ].
+ clear; induction l; constructor; [ | assumption ].
  eexists; reflexivity.
+ intros D HD; inversion HD.
+ list_simpl; reflexivity.
Qed.

(* ** From [tl] to [llfoc] *)

Ltac splitIHpi H :=
  let HpiN := fresh "HpiN" in
  let HpiP := fresh "HpiP" in
  let HpiS := fresh "HpiS" in
  let HpiN' := fresh "HpiN" in
  let HpiP' := fresh "HpiP" in
  let HpiS' := fresh "HpiS" in
  try (destruct H as (HpiN & HpiP)) ;
  try (assert (HpiN' := HpiN (eq_refl _)) ; clear HpiN) ;
  try (assert (HpiP' := HpiP _ (eq_refl _)) ; clear HpiP).

Ltac polfoccont_cbn := unfold polfoc, polcont; cbn.

Theorem otl_to_llfoc l Pi : otl l Pi ->
  forall l0 : list formula, l = map ntrans l0 ->
    (Pi = None -> llfoc l0 None)
  * (forall D : formula, Pi = Some (ptrans D) -> llfoc (polcont l0 D) (polfoc D)).
Proof.
intros pi; induction pi; intros l0 Heq;
  (repeat split; [ intros HN; inversion HN
                  | intros D HD; inversion HD ]); subst; list_simpl.
- destruct l0; inversion Heq.
  destruct l0; inversion H2.
  destruct D; inversion H0.
  destruct f; inversion H1; subst.
  apply a2t_inj in H4; subst.
  polfoccont_cbn; apply (@ax_fr atom_inf).
- apply Permutation_Type_map_inv in p as [l' -> HP].
  assert (IHpi' := IHpi _ (eq_refl _)).
  splitIHpi IHpi'.
  eapply ex_fr; [ | symmetry ]; eassumption.
- apply Permutation_Type_map_inv in p as [l' -> HP].
  assert (IHpi' := IHpi _ (eq_refl _)).
  splitIHpi IHpi'.
  eapply ex_fr; [ eassumption | ].
  symmetry; polfoccont_cbn.
  destruct (polarity D); [ | apply Permutation_Type_cons; [ reflexivity | ] ]; assumption.
- destruct l0; inversion Heq.
  destruct D; inversion H0.
  constructor.
- symmetry in Heq; decomp_map_inf Heq.
  destruct x; inversion Heq3; subst.
  rewrite <- map_app in IHpi.
  assert (IHpi' := IHpi _ (eq_refl _)).
  splitIHpi IHpi'.
  eapply ex_fr; [ apply bot_fr; eassumption | apply Permutation_Type_middle ].
- symmetry in Heq; decomp_map_inf Heq.
  destruct x; inversion Heq3; subst.
  rewrite <- map_app in IHpi.
  assert (IHpi' := IHpi _ (eq_refl _)).
  splitIHpi IHpi'.
  eapply ex_fr ; [ apply bot_fr; eassumption | ].
  polfoccont_cbn; destruct (polarity D).
  + apply Permutation_Type_middle.
  + rewrite (app_comm_cons _ (bot :: l5)).
    apply Permutation_Type_cons_app, Permutation_Type_cons; reflexivity.
- destruct D; inversion HD.
  symmetry in Heq; decomp_map_inf Heq; subst.
  assert (IHpi1' := IHpi1 _ (eq_refl _)).
  assert (IHpi2' := IHpi2 _ (eq_refl _)).
  splitIHpi IHpi1'.
  splitIHpi IHpi2'.
  apply (@tens_fr atom_inf); assumption.
- symmetry in Heq; decomp_map_inf Heq; cbn in Heq3.
  destruct x; inversion Heq3; subst; cbn; cbn in IHpi.
  replace (map ntrans l3 ++ ntrans x2 :: ntrans x1 :: map ntrans l5)
     with (map ntrans (l3 ++ x2 :: x1 :: l5)) in IHpi
    by (list_simpl; reflexivity).
  assert (IHpi' := IHpi _ (eq_refl _)).
  splitIHpi IHpi'.
  eapply ex_fr; [ apply parr_fr | apply Permutation_Type_middle ].
  eapply ex_fr; [ eassumption | ].
  list_simpl; cons2app.
  rewrite ? app_assoc; apply Permutation_Type_app_tail.
  etransitivity; [ | apply Permutation_Type_app_comm ].
  list_simpl; apply Permutation_Type_app_head, Permutation_Type_swap.
- symmetry in Heq; decomp_map_inf Heq.
  destruct x; inversion Heq3; subst.
  replace (map ntrans l3 ++ ntrans x2 :: ntrans x1 :: map ntrans l5)
     with (map ntrans (l3 ++ x2 :: x1 :: l5)) in IHpi
    by (list_simpl; reflexivity).
  assert (IHpi' := IHpi _ (eq_refl _)).
  splitIHpi IHpi'.
  apply ex_fr with (@parr atom_inf x1 x2 :: @polcont atom_inf (l3 ++ l5) D).
  + apply parr_fr.
    eapply ex_fr; [ eassumption | ].
    assert (Permutation_Type (l3 ++ x2 :: x1 :: l5) (x1 :: x2 :: l3 ++ l5)) as HP.
    { list_simpl; cons2app.
      rewrite ? app_assoc; apply Permutation_Type_app_tail.
      etransitivity; [ | apply Permutation_Type_app_comm ].
      list_simpl; apply Permutation_Type_app_head, Permutation_Type_swap. }
    polfoccont_cbn; destruct (polarity D); [ assumption | ].
    cons2app; rewrite ? app_assoc.
    etransitivity; [ apply Permutation_Type_cons; [ reflexivity | ] | apply Permutation_Type_middle ].
    list_simpl; assumption.
  + apply (@Permutation_Type_middle_polcont atom_inf).
- polfoccont_cbn.
  destruct (polarity D) as [Hs | Ha].
  + exfalso; destruct D; inversion H0; inversion Hs.
  + apply IHpi; [ | reflexivity ].
    destruct D; inversion H0; reflexivity.
- symmetry in Heq; decomp_map_inf Heq; subst.
  destruct l4; inversion Heq4; subst.
  destruct (@polarity atom_inf x).
  + rewrite (proj2 (pntrans_neg x) s) in Heq3.
    inversion Heq3; subst.
    assert (IHpi' := IHpi _ (eq_refl _)).
    splitIHpi IHpi'.
    rewrite (polfocs s), (polconts _ s) in HpiP0.
    eapply ex_fr; [ apply (@foc_fr atom_inf); eassumption | ].
    apply Permutation_Type_cons_append.
  + exfalso.
    destruct x; inversion Heq3; inversion a.
- symmetry in Heq; decomp_map_inf Heq.
  destruct x; inversion Heq3; subst.
  eapply ex_fr; [ | apply Permutation_Type_middle ].
  cbn; apply (@top_gen_fr atom_inf); reflexivity.
- symmetry in Heq; decomp_map_inf Heq.
  destruct x; inversion Heq3; subst.
  polfoccont_cbn.
  destruct (polarity D) as [Hs | Ha].
  + eapply ex_fr; [ | apply Permutation_Type_middle ].
    apply (@top_gen_fr atom_inf); assumption.
  + rewrite app_comm_cons.
    eapply ex_fr; [ | apply Permutation_Type_middle ].
    apply (@top_gen_fr atom_inf); reflexivity.
- destruct D; inversion HD; subst.
  assert (IHpi' := IHpi _ (eq_refl _)).
  splitIHpi IHpi'.
  apply plus_fr1; assumption.
- destruct D; inversion HD; subst.
  assert (IHpi' := IHpi _ (eq_refl _)).
  splitIHpi IHpi'.
  apply plus_fr2; assumption.
- symmetry in Heq; decomp_map_inf Heq.
  destruct x; inversion Heq3; subst.
  replace (map ntrans l3 ++ ntrans x1 :: map ntrans l5)
     with (map ntrans (l3 ++ x1 :: l5)) in IHpi1
    by (list_simpl; reflexivity).
  replace (map ntrans l3 ++ ntrans x2 :: map ntrans l5)
     with (map ntrans (l3 ++ x2 :: l5)) in IHpi2
    by (list_simpl; reflexivity).
  assert (IHpi1' := IHpi1 _ (eq_refl _)).
  splitIHpi IHpi1'.
  assert (IHpi2' := IHpi2 _ (eq_refl _)).
  splitIHpi IHpi2'.
  eapply ex_fr; [ apply with_fr | apply Permutation_Type_middle ].
  + eapply ex_fr; [ apply HpiN0 | symmetry; apply Permutation_Type_middle ].
  + eapply ex_fr; [ apply HpiN1 | symmetry; apply Permutation_Type_middle ].
- symmetry in Heq; decomp_map_inf Heq.
  destruct x; inversion Heq3; subst.
  replace (map ntrans l3 ++ ntrans x1 :: map ntrans l5)
     with (map ntrans (l3 ++ x1 :: l5)) in IHpi1
    by (list_simpl; reflexivity).
  replace (map ntrans l3 ++ ntrans x2 :: map ntrans l5)
     with (map ntrans (l3 ++ x2 :: l5)) in IHpi2
    by (list_simpl; reflexivity).
  assert (IHpi1' := IHpi1 _ (eq_refl _)).
  splitIHpi IHpi1'.
  assert (IHpi2' := IHpi2 _ (eq_refl _)).
  splitIHpi IHpi2'.
  eapply ex_fr; [ apply with_fr | apply (@Permutation_Type_middle_polcont atom_inf) ].
  + eapply ex_fr; [ apply HpiP0 | ].
    polfoccont_cbn; destruct (polarity D).
    * symmetry; apply Permutation_Type_middle.
    * cons2app; apply Permutation_Type_cons_app.
      rewrite ? app_assoc; apply Permutation_Type_app_tail, Permutation_Type_app_comm.
  + eapply ex_fr; [ apply HpiP1 | ].
    polfoccont_cbn; destruct (polarity D).
    * symmetry; apply Permutation_Type_middle.
    * cons2app; apply Permutation_Type_cons_app.
      rewrite ? app_assoc; apply Permutation_Type_app_tail, Permutation_Type_app_comm.
- destruct D; inversion HD; subst.
  assert (ntrans D :: map toc l = map ntrans (D :: l0)) as Heq' by (rewrite Heq; reflexivity).
  assert (IHpi' := IHpi _ Heq').
  splitIHpi IHpi'.
  apply ntrans_map_toc_inv in Heq.
  destruct Heq as [lw -> ->].
  apply (@oc_fr atom_inf); assumption.
- symmetry in Heq; decomp_map_inf Heq.
  destruct x; inversion Heq3; subst.
  destruct l4; inversion Heq4.
  assert (IHpi' := IHpi _ (eq_refl _)).
  splitIHpi IHpi'.
  eapply ex_fr; [ apply (@de_fr atom_inf) | apply Permutation_Type_middle ].
  list_simpl; assumption.
- symmetry in Heq; decomp_map_inf Heq; subst.
  destruct x; inversion Heq3; subst.
  rewrite <- map_app in IHpi.
  assert (IHpi' := IHpi _ (eq_refl _)).
  splitIHpi IHpi'.
  eapply ex_fr; [ apply wk_fr; eassumption | apply Permutation_Type_middle ].
- symmetry in Heq; decomp_map_inf Heq; subst.
  destruct x; inversion Heq3; subst.
  rewrite <- map_app in IHpi.
  assert (IHpi' := IHpi _ (eq_refl _)).
  splitIHpi IHpi'.
  eapply ex_fr; [ apply wk_fr; eassumption | apply (@Permutation_Type_middle_polcont atom_inf) ].
- symmetry in Heq; decomp_map_inf Heq; subst.
  symmetry in Heq3; rewrite Heq3 in IHpi.
  replace (map ntrans l3 ++ ntrans x :: ntrans x :: map ntrans l5)
     with (map ntrans (l3 ++ x :: x :: l5)) in IHpi
    by (list_simpl; reflexivity).
  assert (IHpi' := IHpi _ (eq_refl _)).
  splitIHpi IHpi'.
  destruct x; inversion Heq3; subst.
  eapply ex_fr; [ apply co_fr | apply Permutation_Type_middle ].
  eapply ex_fr; [ apply HpiN0 | ].
  cons2app; rewrite ? app_assoc; apply Permutation_Type_app_tail.
  list_simpl; etransitivity; [ apply Permutation_Type_app_comm | reflexivity ].
- symmetry in Heq; decomp_map_inf Heq; subst.
  symmetry in Heq3; rewrite Heq3 in IHpi.
  replace (map ntrans l3 ++ ntrans x :: ntrans x :: map ntrans l5)
     with (map ntrans (l3 ++ x :: x :: l5)) in IHpi
    by (list_simpl; reflexivity).
  assert (IHpi' := IHpi _ (eq_refl _)).
  splitIHpi IHpi'.
  destruct x; inversion Heq3; subst.
  eapply ex_fr; [ apply co_fr | apply (@Permutation_Type_middle_polcont atom_inf) ].
  eapply ex_fr; [ apply HpiP0 | ].
  assert (Permutation_Type (l3 ++ wn x :: wn x :: l5) (wn x :: wn x :: l3 ++ l5)) as HP.
  { cons2app; rewrite ? app_assoc; apply Permutation_Type_app_tail.
    list_simpl; etransitivity; [ apply Permutation_Type_app_comm | reflexivity ]. }
  polfoccont_cbn; destruct (polarity D); [ assumption | ].
  cons2app; rewrite ? app_assoc; apply Permutation_Type_cons_app; list_simpl; assumption.
Qed.

Theorem tl_to_llfoc (l : list formula) : tl_ll (map ntrans l) None -> llfoc l None.
Proof.
intros pi%tl_to_otl.
eapply otl_to_llfoc in pi; [ | reflexivity ].
apply pi; reflexivity.
Qed.

End Focusing.


Theorem weak_focusing l : ll_ll l -> @llfoc atom_inf l None.
Proof. intros pi; apply tl_to_llfoc, ll_to_tl; assumption. Qed.

Theorem focusing l : ll_ll l -> @llFoc atom_inf l None.
Proof.
intros pi%weak_focusing.
refine (fst (fst (llfoc_to_llFoc pi _)) eq_refl).
unfold lt; reflexivity.
Qed.

End Atoms.
