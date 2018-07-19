(* nn_foc file for yalla library *)


(** * Focusing by Polarized Translation *)

Require Import CMorphisms.

Require Import Injective.
Require Import List_more.
Require Import List_Type_more.
Require Import Permutation_Type_more.
Require Import Permutation_Type_solve.
Require Import genperm_Type.

Require Import basic_tactics.
Require Import ll_fragments.
Require Import ill_prop.
Require Import llfoc.
Require Import tl.
Require Import nn_prop.


(** ** Polarized Translation *)

Definition a2t := yalla_ax.a2t.
Definition a2t_inj := yalla_ax.a2t_inj.
Definition a2i_a2i := yalla_ax.a2i_a2i.

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

Lemma pntrans_neg : forall A,
   (aformula A -> ptrans A = tneg (ntrans A))
/\ (sformula A -> ntrans A = tneg (ptrans A)).
Proof.
induction A ;
  (split ; intros Hpol ; inversion Hpol) ;
  reflexivity.
Qed.

Lemma pntrans_dual : forall A,
  ptrans (dual A) = ntrans A /\ ntrans (dual A) = ptrans A.
Proof.
induction A ; simpl ;
  try (destruct IHA as [IHAl IHAr]) ;
  try (destruct IHA1 as [IHA1l IHA1r]) ;
  try (destruct IHA2 as [IHA2l IHA2r]) ;
  try rewrite IHAl ;
  try rewrite IHAr ;
  try rewrite IHA1l ;
  try rewrite IHA1r ;
  try rewrite IHA2l ;
  try rewrite IHA2r ;
  split ; reflexivity.
Qed.

Lemma ntrans_map_toc : forall l,
  map ntrans (map wn l) = map toc (map tneg (map ptrans l)).
Proof with try reflexivity.
induction l...
simpl ; rewrite IHl...
Qed.

Lemma ntrans_map_toc_inv : forall l1 l2,
  map toc l1 = map ntrans l2 ->
    { l2' | l2 = map wn l2' & l1 = map tneg (map ptrans l2') }.
Proof with try assumption ; try reflexivity.
induction l1 ; intros l2 Heq ;
  destruct l2 ; inversion Heq...
- exists nil ; split...
- apply IHl1 in H1.
  destruct f ; inversion H0.
  destruct H1 as [l2' Heq1 H1] ; subst.
  exists (f :: l2') ; split...
Qed.

Lemma pntrans_to_trans : forall A,
  ill_ll (tl2ill (ntrans A) :: nil) (trans N A) ->
  ill_ll (negR N (trans N A) :: tl2ill (tneg (ptrans A)) :: nil) N.
Proof with myeeasy.
intros A pi.
destruct (polarity A).
- apply negR_ilr...
  + apply ax_ir.
  + rewrite <- (proj2 (pntrans_neg _))...
- rewrite (proj1 (pntrans_neg _))...
  cons2app.
  apply neg_ilr...
  apply neg_irr.
  eapply ex_ir ; [ | apply Permutation_Type_swap ].
  apply negR_ilr...
  apply ax_ir.
Qed.

Lemma ntrans_to_trans : forall A,
  ill_ll (tl2ill (ntrans A) :: nil) (trans N A).
Proof with myeeasy.
induction A ; simpl.
- apply negR_irr.
  cons2app.
  apply neg_ilr...
  rewrite a2i_a2i.
  apply ax_ir.
- rewrite a2i_a2i.
  apply ax_ir.
- apply negR_irr.
  cons2app.
  apply neg_ilr...
  rewrite <- (app_nil_l _).
  apply one_ilr.
  apply one_irr.
- rewrite <- (app_nil_l _).
  apply one_ilr.
  apply one_irr.
- apply pntrans_to_trans in IHA1.
  apply pntrans_to_trans in IHA2.
  assert (H1 := @ilmap_to_ineg ipfrag_ill (tl2ill (ptrans A1))).
  cons2app in IHA1.
  eapply (cut_ir_nzeropos_axfree_by_ll _ i2ac_inj _ _ _ _ _ _ _ H1) in IHA1...
  assert (H2 := @ilmap_to_ineg ipfrag_ill (tl2ill (ptrans A2))).
  cons2app in IHA2.
  eapply (cut_ir_nzeropos_axfree_by_ll _ i2ac_inj _ _ _ _ _ _ _ H2) in IHA2...
  eapply (neg_tens_propag _ _ _ _ _ _ _ IHA1) in IHA2.
  assert (H' := @ineg_to_ilmap ipfrag_ill
             (itens (tl2ill (ptrans A1)) (tl2ill (ptrans A2)))).
  cons2app in IHA2.
  eapply (cut_ir_nzeropos_axfree_by_ll _ i2ac_inj _ _ _ _ _ _ _ H') in IHA2...
  apply negR_irr...
- rewrite <- (app_nil_l _).
  apply tens_ilr.
  list_simpl.
  cons2app.
  apply tens_irr...
- apply negR_irr.
  rewrite <- (app_nil_l _).
  apply zero_ilr.
- rewrite <- (app_nil_l _).
  apply zero_ilr.
- apply pntrans_to_trans in IHA1.
  apply pntrans_to_trans in IHA2.
  assert (H1 := @ilmap_to_ineg ipfrag_ill (tl2ill (ptrans A1))).
  cons2app in IHA1.
  eapply (cut_ir_nzeropos_axfree_by_ll _ i2ac_inj _ _ _ _ _ _ _ H1) in IHA1...
  assert (H2 := @ilmap_to_ineg ipfrag_ill (tl2ill (ptrans A2))).
  cons2app in IHA2.
  eapply (cut_ir_nzeropos_axfree_by_ll _ i2ac_inj _ _ _ _ _ _ _ H2) in IHA2...
  eapply (neg_plus_propag _ _ _ _ _ _ _ IHA1) in IHA2.
  assert (H' := @ineg_to_ilmap ipfrag_ill
                  (iplus (tl2ill (ptrans A1)) (tl2ill (ptrans A2)))).
  cons2app in IHA2.
  eapply (cut_ir_nzeropos_axfree_by_ll _ i2ac_inj _ _ _ _ _ _ _ H') in IHA2...
  apply negR_irr...
- rewrite <- (app_nil_l _).
  apply plus_ilr ; list_simpl.
  + apply plus_irr1...
  + apply plus_irr2...
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
  apply negR_ilr...
  apply ax_ir.
- apply pntrans_to_trans in IHA.
  change (ioc (ineg (tl2ill (ptrans A))) :: nil)
    with (map ioc (ineg (tl2ill (ptrans A)) :: nil)).
  apply oc_irr.
  rewrite <- (app_nil_l _).
  apply de_ilr.
  apply negR_irr...
Unshelve.
all : try reflexivity.
all : try now (intros a ; destruct a).
all : constructor ; [ constructor | ]...
all : list_simpl.
all : constructor ; constructor ; try constructor.
all : try (apply trans_nz).
all : try (now (intros HN ; inversion HN)).
all : try (now constructor).
all : try (apply tl2ill_nz).
all : constructor ; apply tl2ill_nz.
Qed.

Definition tpfrag_tl := mk_tpfrag true NoTAxioms true.
(*                                cut  axioms            perm  *)
Definition tl_ll := tl tpfrag_tl.

Proposition ll_to_tl : forall l, ll_ll l -> tl_ll (map ntrans l) None.
Proof with myeeasy.
intros l pi.
apply (ll_ll_to_ill_trans N) in pi.
assert (forall l1 l2, ill_ll (map (trans N) l1 ++ map tl2ill (map ntrans l2)) N
          -> ill_ll (map tl2ill (map ntrans (l1 ++ l2))) N)
 as IH.
{ clear ; induction l1 ; intros l2 pi...
  list_simpl in pi.
    assert (Ha := ntrans_to_trans a).
    eapply ex_ir in pi ; [ | apply Permutation_Type_middle ].
    eapply (cut_ir_nzeropos_axfree_by_ll _ i2ac_inj _ _ _ _ _ _ _ Ha) in pi...
    list_simpl in pi.
    change (tl2ill (ntrans a) :: map tl2ill (map ntrans l2))
      with (map tl2ill (map ntrans (a :: l2))) in pi.
    apply IHl1 in pi.
    eapply ex_ir...
    PEperm_Type_solve.
  Unshelve.
  + clear ; intros a ; destruct a.
  + simpl.
    constructor.
    * constructor.
    * apply Forall_Type_app.
      -- clear ; induction l1 ; constructor...
         apply trans_nz.
         ++ intros Hz ; inversion Hz.
         ++ constructor.
      -- change (tl2ill (ntrans a) :: map tl2ill (map ntrans l2))
           with (map tl2ill (map ntrans (a :: l2))).
         remember (a :: l2) as l.
         clear ; induction l ; constructor...
         apply tl2ill_nz. }
rewrite <- (app_nil_r _) in pi.
change nil with (map tl2ill (map ntrans nil)) in pi.
apply IH in pi.
list_simpl in pi.
apply (cut_admissible_ill_nzeropos_axfree_by_ll _ i2ac_inj) in pi.
- eapply (stronger_tpfrag (cutrm_tpfrag tpfrag_tl)).
  + nsplit 3...
    intros a ; destruct a.
  + eapply tlfrag2tl_cutfree...
    rewrite <- cutrm_t2ipfrag.
    eapply stronger_ipfrag ; [ | apply pi].
    nsplit 3...
    intros a ; destruct a.
- intros a ; destruct a.
- constructor ; [ constructor | ]...
  clear ; induction l ; constructor...
  apply tl2ill_nz.
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
| co_otlr : forall A lw l1 l2 C,
                        otl (l1 ++ toc A :: map toc lw
                                ++ toc A :: l2) C ->
                        otl (l1 ++ map toc lw ++ toc A :: l2) C.

Instance otl_perm {Pi} : Proper ((@Permutation_Type _) ==> Basics.arrow) (fun l => otl l Pi).
Proof.
intros l1 l2 HP pi.
eapply ex_otr ; eassumption.
Qed.

Lemma neg_rev_ot : forall A l, otl l (Some (tneg A)) ->
  otl (A :: l) None.
Proof with myeeasy.
intros A l pi.
remember (Some (tneg A)) as Pi.
revert A HeqPi ; induction pi ; intros A' HeqPi ;
  try (now (inversion HeqPi)) ; subst ;
  try (now (rewrite app_comm_cons ;
            constructor ;
            rewrite <- app_comm_cons ;
            apply IHpi ; myeasy)).
- eapply ex_otr.
  + apply IHpi...
  + perm_Type_solve.
- inversion HeqPi ; subst...
- rewrite app_comm_cons.
  apply plus_otlr.
  + rewrite <- app_comm_cons.
    apply IHpi1...
  + rewrite <- app_comm_cons.
    apply IHpi2...
Qed.

Lemma tsubform_toc_ntrans : forall A B, tsubform (toc A) (ntrans B) ->
  { A' | A = tneg A' }.
Proof with myeasy.
intros A B Hsub.
apply (@inl _ (tsubform (toc A) (ptrans B))) in Hsub.
revert Hsub ; clear ; induction B ; intros [ Hsub | Hsub ] ;
  try (now (inversion Hsub ; subst ; inversion H1)) ;
  try (now (inversion Hsub ; inversion H1 ; subst ;
              try (apply IHB1 ; right ; assumption) ;
              try (apply IHB2 ; right ; assumption))) ;
  try (now (inversion Hsub ; inversion H1 ; subst ;
              try (apply IHB1 ; left ; assumption) ;
              try (apply IHB2 ; left ; assumption))).
- inversion Hsub ; inversion H1 ; subst.
  + eexists...
  + inversion H4 ; subst ; apply IHB ; left...
  + eexists...
  + inversion H4 ; subst ; apply IHB ; left...
- inversion Hsub ; subst.
  + eexists...
  + inversion H1 ; subst ; apply IHB ; left...
- inversion Hsub ; subst.
  + eexists...
  + inversion H1 ; subst ; apply IHB ; right...
- inversion Hsub ; inversion H1 ; subst.
  + eexists...
  + inversion H4 ; subst ; apply IHB ; right...
  + eexists...
  + inversion H4 ; subst ; apply IHB ; right...
Qed.

(* ** From [tl] to [otl] *)

Ltac Forall_Type_simpl_hyp :=
  repeat (
    match goal with
    | H:Forall_Type _ (_ ++ _) |- _ => apply Forall_Type_app_inv in H ; destruct H
    | H:Forall_Type _ (_ :: _) |- _ => inversion H ; clear H
    end).
Ltac Forall_Type_solve_rec :=
  match goal with
  | |- Forall_Type _ (_ ++ _) => apply Forall_Type_app ; Forall_Type_solve_rec
  | |- Forall_Type _ (_ :: _) => constructor ; [ assumption | Forall_Type_solve_rec ]
  | |- Forall_Type _ nil => constructor
  | _ => try assumption
  end.
Ltac Forall_Type_solve :=
  Forall_Type_simpl_hyp ; simpl ; Forall_Type_solve_rec.

Lemma tl_to_otl_neg : forall l C,
  tl_ll l C ->
  Forall_Type (fun F => { x & tsubform F (ntrans x) }) l ->
  (forall D, C = Some D -> { x & tsubform D (ntrans x) } ) ->
  forall l1 l2, Permutation_Type l (l1 ++ map tneg l2) ->
  otl (l1 ++ map toc (map tneg l2)) C.
Proof with (try Forall_Type_solve) ; myeeasy.
intros l C pi.
apply cut_admissible_tl_axfree in pi...
induction pi ; intros HF HC l1' l2' HP.
- apply Permutation_Type_length_1_inv in HP.
  destruct l1' ; inversion HP.
  + destruct l2' ; inversion H0.
  + apply app_eq_nil in H1.
    destruct H1 ; subst.
    destruct l2' ; inversion H1.
    apply ax_otr.
- simpl in p.
  apply IHpi...
  + symmetry in p.
    eapply Permutation_Type_Forall_Type...
  + etransitivity...
- apply Permutation_Type_nil in HP.
  apply app_eq_nil in HP.
  destruct HP ; subst.
  destruct l2' ; inversion H0.
  apply one_otrr.
- assert (HP' := HP).
  apply Permutation_Type_elt_map_inv in HP' ; [ | intros b Hf ; inversion Hf ].
  destruct HP' as [(l1'' & l2'') Heq] ; subst.
  list_simpl.
  constructor.
  rewrite app_assoc.
  apply IHpi...
  list_simpl.
  list_simpl in HP.
  apply Permutation_Type_app_inv in HP...
- apply Permutation_Type_app_app_inv in HP.
  destruct HP as [[[l3' l3''] [l4' l4'']] [[HP1 HP2] [HP3 HP4]]] ;
    simpl in HP1 ; simpl in HP2 ; simpl in HP3 ; simpl in HP4.
  symmetry in HP4.
  apply Permutation_Type_map_inv in HP4.
  destruct HP4 as [l3''' Heq HP4].
  decomp_map_Type Heq ; subst ; simpl in HP4.
  apply (ex_otr ((l3' ++ map toc (map tneg l0))
                 ++ l3'' ++ map toc (map tneg l3))).
  + constructor.
    * apply IHpi1 in HP1...
      destruct (HC _ (eq_refl _)) as [D HD].
      intros D0 Heq0.
      inversion Heq0 ; subst.
      eexists.
      etransitivity ; [ | apply HD].
      constructor ; constructor...
    * apply IHpi2 in HP2...
      destruct (HC _ (eq_refl _)) as [D HD].
      intros D0 Heq0.
      inversion Heq0 ; subst.
      eexists.
      etransitivity ; [ | apply HD].
      constructor ; constructor...
  + assert (Permutation_Type (l1' ++ map toc (map tneg l2'))
                         ((l3' ++ l3'') ++ map toc (map tneg (l0 ++ l3))))
    as HP'.
    { apply Permutation_Type_app...
      apply Permutation_Type_map.
      apply Permutation_Type_map.
      perm_Type_solve. }
    perm_Type_solve.
- assert (HP' := HP).
  apply Permutation_Type_elt_map_inv in HP' ; [ | intros b Hf ; inversion Hf ].
  destruct HP' as [(l1'' & l2'') Heq] ; subst.
  list_simpl.
  constructor.
  rewrite 2 app_comm_cons.
  rewrite app_assoc.
  apply IHpi...
  + Forall_Type_simpl_hyp ; subst.
    destruct H1 as [S Hs].
    constructor.
    * exists S.
      etransitivity ; [ | apply Hs].
      constructor ; constructor.
    * constructor...
      exists S.
      etransitivity ; [ | apply Hs].
      constructor ; constructor.
  + list_simpl.
    list_simpl in HP.
    apply Permutation_Type_app_inv in HP.
    apply Permutation_Type_elt.
    apply Permutation_Type_elt...
- constructor.
  apply (@Permutation_Type_cons _ A _ (eq_refl _)) in HP.
  rewrite app_comm_cons in HP.
  apply IHpi in HP...
  + constructor...
    destruct (HC _ (eq_refl _)) as [D HD].
    eexists.
    etransitivity ; [ | apply HD ].
    constructor ; constructor...
  + intros D HD.
    inversion HD.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_elt_inv in HP'.
  destruct HP' as [(l' & l'') Heq] ; simpl in Heq.
  dichot_Type_elt_app_exec Heq ; subst.
  + eapply (ex_otr ((l' ++ l0 ++ map toc (map tneg l2')) ++ tneg A :: nil)) ;
      [ | perm_Type_solve ].
    constructor.
    rewrite app_assoc.
    apply IHpi...
    * intros D HD.
      inversion HD ; subst.
      destruct H1 as [D' HD'].
      eexists.
      etransitivity ; [ | apply HD'].
      constructor ; constructor...
    * list_simpl.
      list_simpl in HP.
      apply Permutation_Type_app_inv in HP.
      list_simpl in HP...
  + decomp_map_Type Heq1 ; subst.
    inversion Heq1 ; subst.
    list_simpl.
    eapply (ex_otr ((l1' ++ map toc (map tneg (l2 ++ l4))) ++ toc (tneg x) :: nil)) ;
      [ | perm_Type_solve ].
    constructor.
    apply IHpi...
    * intros D HD.
      inversion HD ; subst.
      destruct H1 as [D' HD'].
      eexists.
      etransitivity ; [ | apply HD'].
      constructor ; constructor...
    * list_simpl.
      list_simpl in HP.
      rewrite app_assoc in HP.
      apply Permutation_Type_app_inv in HP.
      list_simpl in HP...
- assert (HP' := HP).
  apply Permutation_Type_elt_map_inv in HP' ; [ | intros b Hf ; inversion Hf ].
  destruct HP' as [(l1'' & l2'') Heq] ; subst.
  list_simpl.
  constructor.
- constructor.
  apply IHpi...
  destruct (HC _ (eq_refl _)) as [D HD].
  intros D0 Heq0.
  inversion Heq0 ; subst.
  eexists.
  etransitivity ; [ | apply HD].
  constructor ; constructor...
- apply plus_otrr2.
  apply IHpi...
  destruct (HC _ (eq_refl _)) as [D HD].
  intros D0 Heq0.
  inversion Heq0 ; subst.
  eexists.
  etransitivity ; [ | apply HD].
  constructor ; constructor...
- assert (HP' := HP).
  apply Permutation_Type_elt_map_inv in HP' ; [ | intros b Hf ; inversion Hf ].
  destruct HP' as [(l1'' & l2'') Heq] ; subst.
  list_simpl.
  constructor ; rewrite app_comm_cons ; rewrite app_assoc.
  + apply IHpi1...
    * constructor...
      destruct H1 as [D' HD'].
      eexists.
      etransitivity ; [ | apply HD'].
      constructor ; constructor...
    * list_simpl.
      list_simpl in HP.
      apply Permutation_Type_app_inv in HP.
      apply Permutation_Type_elt...
  + apply IHpi2...
    * constructor...
      destruct H1 as [D' HD'].
      eexists.
      etransitivity ; [ | apply HD'].
      constructor ; constructor...
    * list_simpl.
      list_simpl in HP.
      apply Permutation_Type_app_inv in HP.
      apply Permutation_Type_elt...
- symmetry in HP.
  apply Permutation_Type_map_inv in HP.
  destruct HP as [l3 Heq HP].
  decomp_map_Type Heq.
  assert (l2' = nil).
  { destruct l2'...
    destruct l2 ; inversion Heq2. }
  subst.
  list_simpl.
  destruct (HC (toc A) (eq_refl _)) as [A' HC'].
  destruct (tsubform_toc_ntrans _ _ HC') as [A'' HC''] ; subst.
  apply oc_otrr.
  destruct l2 ; inversion Heq2.
  replace (map toc l1) with (map toc l1 ++ map toc (map tneg nil))
    by (list_simpl ; myeasy).
  apply neg_rev_ot.
  apply IHpi...
  + destruct (HC _ (eq_refl _)) as [D HD].
    intros D0 Heq0.
    inversion Heq0 ; subst.
    eexists.
    etransitivity ; [ | apply HD].
    constructor ; constructor...
  + list_simpl in HP ; list_simpl.
    apply Permutation_Type_map...
- Forall_Type_simpl_hyp ; subst.
  destruct H1 as [At HAt].
  destruct (tsubform_toc_ntrans _ _ HAt) as [B HeqB] ; subst.
  assert (HP' := HP).
  apply Permutation_Type_elt_map_inv in HP' ; [ | intros b Hf ; inversion Hf ].
  destruct HP' as [(l1'' & l2'') Heq] ; subst.
  list_simpl.
  apply (ex_otr ((l1'' ++ l2'') ++ map toc (map tneg (B :: l2')))) ;
    [ | perm_Type_solve].
  apply IHpi...
  + constructor...
    eexists...
    etransitivity ; [ | apply HAt ].
    constructor ; constructor...
  + list_simpl in HP.
    apply Permutation_Type_app_inv in HP.
    apply Permutation_Type_elt.
    list_simpl...
- assert (HP' := HP).
  apply Permutation_Type_elt_map_inv in HP' ; [ | intros b Hf ; inversion Hf ].
  destruct HP' as [(l1'' & l2'') Heq] ; subst.
  list_simpl.
  constructor.
  rewrite app_assoc.
  apply IHpi...
  list_simpl.
  list_simpl in HP.
  apply Permutation_Type_app_inv in HP...
- assert { l3 & Permutation_Type l1' (l3 ++ toc A :: map toc lw) }
    as [l3 HPw].
  { assert (Permutation_Type (l1 ++ map toc (A :: lw) ++ l2) (l1' ++ map tneg l2'))
      as HP'.
    { etransitivity ; [ | apply HP ].
      apply Permutation_Type_app_head.
      list_simpl.
      apply Permutation_Type_middle. }
    change (toc A :: map toc lw) with (map toc (A :: lw)).
    remember (A :: lw) as lt.
    clear - HP'.
    revert l1 l2 l1' l2' HP' ; induction lt ; intros l1 l2 l1' l2' HP.
    + exists l1' ; list_simpl ; reflexivity.
    + list_simpl in HP.
      assert (HP' := HP).
      apply Permutation_Type_elt_map_inv in HP' ; [ | intros b Hf ; inversion Hf ].
      destruct HP' as [(l1'' & l2'') Heq] ; subst.
      list_simpl in HP.
      apply Permutation_Type_app_inv in HP.
      rewrite (app_assoc l1'' l2'') in HP.
      apply IHlt in HP.
      destruct HP as [l3 HP].
      eexists ; apply Permutation_Type_elt... }
  apply (ex_otr (l3 ++ map toc lw ++ toc A :: map toc (map tneg l2'))) ;
    [ | perm_Type_solve ].
  constructor.
  rewrite <- (app_nil_l (map toc (map _ _))).
  rewrite ? app_comm_cons.
  rewrite ? app_assoc.
  apply IHpi...
  list_simpl.
  rewrite (app_comm_cons (map toc lw) (toc A :: map tneg l2')).
  rewrite app_assoc.
  apply Permutation_Type_elt.
  list_simpl.
  etransitivity ; [ apply HP | ].
  rewrite app_comm_cons.
  rewrite app_assoc.
  apply Permutation_Type_app_tail...
- inversion f.
- destruct a.
- intros HFalse.
  destruct HFalse.
Qed.

Proposition tl_to_otl : forall l,
  tl_ll (map ntrans l) None -> otl (map ntrans l) None.
Proof with try eassumption.
intros l pi.
replace (map ntrans l) with (map ntrans l ++ map toc (map tneg nil))
  by (list_simpl ; reflexivity).
eapply tl_to_otl_neg...
+ clear ; induction l ; constructor...
  eexists ; reflexivity.
+ intros D HD.
  inversion HD.
+ list_simpl ; reflexivity.
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

Ltac polfoccont_simpl := unfold polfoc ; unfold polcont ; simpl.

Theorem otl_to_llfoc : forall l Pi, otl l Pi ->
  forall l0, l = map ntrans l0 ->
    (Pi = None -> llfoc l0 None)
  * (forall D, Pi = Some (ptrans D) -> llfoc (polcont l0 D) (polfoc D)).
Proof with (try perm_Type_solve) ; myeeasy.
intros l Pi pi.
induction pi ;
  intros l0 Heq ;
  (nsplit 2 ; [ intros HN ; inversion HN
              | intros D HD ; inversion HD ]) ;
  subst ; list_simpl.
- destruct l0 ; inversion Heq.
  destruct l0 ; inversion H2.
  destruct D ; inversion H0.
  destruct f ; inversion H1 ; subst.
  apply a2t_inj in H4 ; subst.
  polfoccont_simpl ; apply ax_fr.
- apply Permutation_Type_map_inv in p.
  destruct p as [l' Heq HP] ; subst.
  assert (IHpi' := IHpi _ (eq_refl _)).
  splitIHpi IHpi'.
  eapply ex_fr.
  + eassumption.
  + symmetry...
- apply Permutation_Type_map_inv in p.
  destruct p as [l' Heq HP] ; subst.
  assert (IHpi' := IHpi _ (eq_refl _)).
  splitIHpi IHpi'.
  eapply ex_fr.
  + eassumption.
  + polfoccont_simpl ; destruct (polarity D)...
- destruct l0 ; inversion Heq.
  destruct D ; inversion H0.
  constructor.
- decomp_map_Type Heq.
  destruct x ; inversion Heq3 ; subst.
  rewrite <- map_app in IHpi.
  assert (IHpi' := IHpi _ (eq_refl _)).
  splitIHpi IHpi'.
  eapply ex_fr ; [ apply bot_fr | ].
  + eassumption.
  + idtac...
- decomp_map_Type Heq.
  destruct x ; inversion Heq3 ; subst.
  rewrite <- map_app in IHpi.
  assert (IHpi' := IHpi _ (eq_refl _)).
  splitIHpi IHpi'.
  eapply ex_fr ; [ apply bot_fr | ].
  + eassumption.
  + polfoccont_simpl ; destruct (polarity D)...
- destruct D ; inversion HD.
  decomp_map_Type Heq ; subst.
  assert (IHpi1' := IHpi1 _ (eq_refl _)).
  assert (IHpi2' := IHpi2 _ (eq_refl _)).
  splitIHpi IHpi1'.
  splitIHpi IHpi2'.
  apply tens_fr...
- decomp_map_Type Heq ; simpl in Heq3.
  destruct x ; inversion Heq3 ; subst ; simpl ; simpl in IHpi.
  replace (map ntrans l3 ++ ntrans x2 :: ntrans x1 :: map ntrans l5)
     with (map ntrans (l3 ++ x2 :: x1 :: l5)) in IHpi
    by (list_simpl ; reflexivity).
  assert (IHpi' := IHpi _ (eq_refl _)).
  splitIHpi IHpi'.
  eapply ex_fr ; [ apply parr_fr | apply Permutation_Type_middle ].
  eapply ex_fr.
  + eassumption.
  + idtac...
- decomp_map_Type Heq.
  destruct x ; inversion Heq3 ; subst ; simpl ; simpl in IHpi.
  replace (map ntrans l3 ++ ntrans x2 :: ntrans x1 :: map ntrans l5)
     with (map ntrans (l3 ++ x2 :: x1 :: l5)) in IHpi
    by (list_simpl ; reflexivity).
  assert (IHpi' := IHpi _ (eq_refl _)).
  splitIHpi IHpi'.
  eapply ex_fr ; [ apply parr_fr | apply Permutation_Type_middle_polcont ].
  eapply ex_fr.
  + eassumption.
  + polfoccont_simpl ; destruct (polarity D)...
- polfoccont_simpl.
  destruct (polarity D) as [Hs | Ha].
  + exfalso ; destruct D ; inversion H0 ; inversion Hs.
  + apply IHpi...
    destruct D ; inversion H0...
- decomp_map_Type Heq ; subst.
  destruct l4 ; inversion Heq4 ; subst ; simpl in Heq3.
  destruct (polarity x).
  + rewrite (proj2 (pntrans_neg x) s) in Heq3.
    inversion Heq3 ; subst.
    assert (IHpi' := IHpi _ (eq_refl _)).
    splitIHpi IHpi'...
    rewrite (polfocs _ s) in HpiP0.
    rewrite (polconts _ _ s) in HpiP0.
    eapply ex_fr ; [ apply foc_fr | ].
    * eassumption.
    * idtac...
  + exfalso.
    destruct x ; inversion Heq3 ; inversion a.
- decomp_map_Type Heq.
  destruct x ; inversion Heq3 ; subst.
  eapply ex_fr ; [ | apply Permutation_Type_middle ].
  simpl ; apply top_gen_fr...
- decomp_map_Type Heq.
  destruct x ; inversion Heq3 ; subst.
  polfoccont_simpl.
  destruct (polarity D) as [Hs | Ha].
  + eapply ex_fr ; [ | apply Permutation_Type_middle ].
    apply top_gen_fr...
  + rewrite app_comm_cons.
    eapply ex_fr ; [ | apply Permutation_Type_middle ].
    apply top_gen_fr...
- destruct D ; inversion HD ; subst.
  assert (IHpi' := IHpi _ (eq_refl _)).
  splitIHpi IHpi'.
  apply plus_fr1...
- destruct D ; inversion HD ; subst.
  assert (IHpi' := IHpi _ (eq_refl _)).
  splitIHpi IHpi'.
  apply plus_fr2...
- decomp_map_Type Heq.
  destruct x ; inversion Heq3 ; subst ; simpl in IHpi1 ; simpl in IHpi2.
  replace (map ntrans l3 ++ ntrans x1 :: map ntrans l5)
     with (map ntrans (l3 ++ x1 :: l5)) in IHpi1
    by (list_simpl ; reflexivity).
  replace (map ntrans l3 ++ ntrans x2 :: map ntrans l5)
     with (map ntrans (l3 ++ x2 :: l5)) in IHpi2
    by (list_simpl ; reflexivity).
  assert (IHpi1' := IHpi1 _ (eq_refl _)).
  splitIHpi IHpi1'.
  assert (IHpi2' := IHpi2 _ (eq_refl _)).
  splitIHpi IHpi2'.
  eapply ex_fr ; [ apply with_fr | apply Permutation_Type_middle ].
  + eapply ex_fr ; [ apply HpiN0 | ]...
  + eapply ex_fr ; [ apply HpiN1 | ]...
- decomp_map_Type Heq.
  destruct x ; inversion Heq3 ; subst ; simpl in IHpi1 ; simpl in IHpi2.
  replace (map ntrans l3 ++ ntrans x1 :: map ntrans l5)
     with (map ntrans (l3 ++ x1 :: l5)) in IHpi1
    by (list_simpl ; reflexivity).
  replace (map ntrans l3 ++ ntrans x2 :: map ntrans l5)
     with (map ntrans (l3 ++ x2 :: l5)) in IHpi2
    by (list_simpl ; reflexivity).
  assert (IHpi1' := IHpi1 _ (eq_refl _)).
  splitIHpi IHpi1'.
  assert (IHpi2' := IHpi2 _ (eq_refl _)).
  splitIHpi IHpi2'.
  eapply ex_fr ; [ apply with_fr | apply Permutation_Type_middle_polcont ].
  + eapply ex_fr ; [ apply HpiP0 | ].
    polfoccont_simpl ; destruct (polarity D)...
  + eapply ex_fr ; [ apply HpiP1 | ].
    polfoccont_simpl ; destruct (polarity D)...
- destruct D ; inversion HD ; subst.
  assert (ntrans D :: map toc l = map ntrans (D :: l0)) as Heq'
    by (rewrite Heq ; myeasy).
  assert (IHpi' := IHpi _ Heq').
  splitIHpi IHpi'.
  apply ntrans_map_toc_inv in Heq.
  destruct Heq as [lw Heq HP] ; subst.
  apply oc_fr...
- decomp_map_Type Heq.
  destruct x ; inversion Heq3 ; subst.
  destruct l4 ; inversion Heq4.
  assert (IHpi' := IHpi _ (eq_refl _)).
  splitIHpi IHpi'.
  eapply ex_fr ; [ apply de_fr | apply Permutation_Type_middle ].
  list_simpl...
- decomp_map_Type Heq ; subst.
  destruct x ; inversion Heq3 ; subst.
  rewrite <- map_app in IHpi.
  assert (IHpi' := IHpi _ (eq_refl _)).
  splitIHpi IHpi'.
  eapply ex_fr ; [ apply wk_fr | ].
  * eassumption.
  * idtac...
- decomp_map_Type Heq ; subst.
  destruct x ; inversion Heq3 ; subst.
  rewrite <- map_app in IHpi.
  assert (IHpi' := IHpi _ (eq_refl _)).
  splitIHpi IHpi'.
  eapply ex_fr ; [ apply wk_fr | apply Permutation_Type_middle_polcont ]...
- decomp_map_Type Heq ; subst ; simpl in IHpi ; simpl in Heq2 ; simpl in Heq3.
  rewrite Heq2 in IHpi.
  rewrite Heq3 in IHpi.
  replace (map ntrans l3 ++ ntrans x :: map ntrans l5 ++ ntrans x :: map ntrans l7)
     with (map ntrans (l3 ++ x :: l5 ++ x :: l7)) in IHpi
    by (list_simpl ; reflexivity).
  assert (IHpi' := IHpi _ (eq_refl _)).
  splitIHpi IHpi'.
  destruct x ; inversion Heq2 ; subst.
  rewrite app_assoc.
  eapply ex_fr ; [ apply co_fr | apply Permutation_Type_middle ].
  eapply ex_fr.
  * eassumption.
  * idtac...
- decomp_map_Type Heq ; subst ; simpl in IHpi ; simpl in Heq2 ; simpl in Heq3.
  rewrite Heq2 in IHpi.
  rewrite Heq3 in IHpi.
  replace (map ntrans l3 ++ ntrans x :: map ntrans l5 ++ ntrans x :: map ntrans l7)
     with (map ntrans (l3 ++ x :: l5 ++ x :: l7)) in IHpi
    by (list_simpl ; reflexivity).
  assert (IHpi' := IHpi _ (eq_refl _)).
  splitIHpi IHpi'.
  destruct x ; inversion Heq2 ; subst.
  rewrite app_assoc.
  eapply ex_fr ; [ apply co_fr | apply Permutation_Type_middle_polcont ].
  eapply ex_fr.
  * eassumption.
  * polfoccont_simpl ; destruct (polarity D)...
Qed.

Theorem tl_to_llfoc : forall l, tl_ll (map ntrans l) None -> llfoc l None.
Proof with myeasy.
intros l pi.
apply tl_to_otl in pi...
eapply otl_to_llfoc in pi...
apply pi...
Qed.

End Focusing.


Theorem weak_focusing : forall l, ll_ll l -> llfoc l None.
Proof.
intros l pi.
apply tl_to_llfoc.
apply ll_to_tl.
assumption.
Qed.

Theorem focusing : forall l, ll_ll l -> llFoc l None.
Proof.
intros l pi.
apply weak_focusing in pi.
eapply (fst (fst (llfoc_to_llFoc (S (fpsize pi)) _ _ pi _))).
reflexivity.
Unshelve. unfold lt ; reflexivity.
Qed.


