(* tl example file for yalla library *)
(* v 1.1   Olivier Laurent *)


(** * Example of a concrete use of the yalla library: tensor logic *)

Require Import RelationClasses.
Require Import Arith.
Require Import Omega.
Require Import Morphisms.

Require Import Injective.
Require Import Bool_more.
Require Import List_more.
Require Import genperm.


(** ** 0. load the [ill] library *)

Require Import ill.

(** ** 1. define formulas *)

Definition TAtom := yalla_ax.TAtom.

(** Tensor formulas *)
Inductive tformula : Set :=
| tvar : TAtom -> tformula
| tone : tformula
| ttens : tformula -> tformula -> tformula
| tneg : tformula -> tformula
| tzero : tformula
| tplus : tformula -> tformula -> tformula
| toc : tformula -> tformula.

Inductive tsubform : tformula -> tformula -> Prop :=
| tsub_id : forall A, tsubform A A
| tsub_tens_l : forall A B C, tsubform A B -> tsubform A (ttens B C)
| tsub_tens_r : forall A B C, tsubform A B -> tsubform A (ttens C B)
| tsub_neg_l  : forall A B, tsubform A B -> tsubform A (tneg B)
| tsub_neg_r  : forall A B, tsubform A B -> tsubform A (tneg B)
| tsub_plus_l : forall A B C, tsubform A B -> tsubform A (tplus B C)
| tsub_plus_r : forall A B C, tsubform A B -> tsubform A (tplus C B)
| tsub_oc : forall A B, tsubform A B -> tsubform A (toc B).

Lemma tsub_trans : forall A B C, tsubform A B -> tsubform B C -> tsubform A C.
Proof with try assumption.
intros A B C Hl Hr ; revert A Hl ; induction Hr ; intros A' Hl ;
  try (constructor ; apply IHHr)...
Qed.

Instance tsub_po : PreOrder tsubform.
Proof.
split.
- intros l.
  apply tsub_id.
- intros l1 l2 l3.
  apply tsub_trans.
Qed.

(** ** 2. define embedding into [iformula] *)

Definition i2ac := yalla_ax.i2ac.
Definition i2ac_inj := yalla_ax.i2ac_inj.
Definition t2i := yalla_ax.t2i.
Definition t2i_inj := yalla_ax.t2i_inj.
Definition notatN := yalla_ax.notatN.
Definition iateq := yalla_ax.iateq.
Definition iateq_eq := yalla_ax.iateq_eq.

Fixpoint tl2ill P :=
match P with
| tvar x => ivar (t2i x)
| tone => ione
| ttens A B => itens (tl2ill A) (tl2ill B)
| tneg A => ineg (tl2ill A)
| tzero => izero
| tplus A B => iplus (tl2ill A) (tl2ill B)
| toc A => ioc (tl2ill A)
end.

Lemma tl2ill_inj : injective tl2ill.
Proof with try reflexivity.
intros A.
induction A ; intros B Heq ;
  destruct B ; inversion Heq ;
  try apply IHA in H0 ;
  try apply IHA1 in H0 ;
  try apply IHA2 in H1 ; subst...
Qed.

Lemma tl2ill_nz : forall A, nonzerospos (tl2ill A).
Proof.
induction A ; simpl ; constructor ; try assumption.
Qed.

Lemma tl2ill_map_ioc : forall l,
  map tl2ill (map toc l) = map ioc (map tl2ill l).
Proof with try reflexivity.
induction l...
simpl ; rewrite IHl...
Qed.

Lemma tl2ill_map_ioc_inv : forall l1 l2,
  map ioc l1 = map tl2ill l2 ->
    exists l2', l2 = map toc l2' /\ l1 = map tl2ill l2'.
Proof with try assumption ; try reflexivity.
induction l1 ; intros l2 Heq ;
  destruct l2 ; inversion Heq...
- exists nil ; split...
- apply IHl1 in H1.
  destruct t ; inversion H0.
  destruct H1 as (l2' & Heq1 & H1) ; subst.
  exists (t :: l2') ; split...
Qed.


(** ** 3. define proofs *)

Record tpfrag := mk_tpfrag {
  tpcut : bool ;
  tpgax : list tformula -> option tformula -> Prop ;
  tpperm : bool }.

Definition le_tpfrag P Q :=
     Bool.leb (tpcut P) (tpcut Q)
  /\ (forall f a, tpgax P f a -> tpgax Q f a)
  /\ Bool.leb (tpperm P) (tpperm Q).

Lemma le_tpfrag_trans : forall P Q R,
  le_tpfrag P Q -> le_tpfrag Q R -> le_tpfrag P R.
Proof.
intros P Q R H1 H2.
destruct H1 as (Hc1 & Ha1 & Hp1).
destruct H2 as (Hc2 & Ha2 & Hp2).
split ; [ | split ] ; try (eapply leb_trans ; eassumption).
intros f a Hax.
apply Ha2.
apply Ha1.
assumption.
Qed.

Definition cutupd_tpfrag P b := mk_tpfrag b (tpgax P) (tpperm P).

Definition axupd_tpfrag P G := mk_tpfrag (tpcut P) G (tpperm P).

Definition cutrm_tpfrag P := cutupd_tpfrag P false.

Inductive tl P : list tformula -> option tformula -> Prop :=
| ax_tr : forall X, tl P (tvar X :: nil) (Some (tvar X))
| ex_tr : forall l1 l2 A, tl P l1 A -> PEperm (tpperm P) l1 l2 ->
                          tl P l2 A
| one_trr : tl P nil (Some tone)
| one_tlr : forall l1 l2 A, tl P (l1 ++ l2) A ->
                            tl P (l1 ++ tone :: l2) A
| tens_trr : forall A B l1 l2,
                    tl P l1 (Some A) -> tl P l2 (Some B) ->
                    tl P (l1 ++ l2) (Some (ttens A B))
| tens_tlr : forall A B l1 l2 C,
                    tl P (l1 ++ A :: B :: l2) C ->
                    tl P (l1 ++ ttens A B :: l2) C
| neg_trr : forall A l,
                    tl P (A :: l) None ->
                    tl P l (Some (tneg A))
| neg_tlr : forall A l, tl P l (Some A) ->
                        tl P (l ++ tneg A :: nil) None
| zero_tlr : forall l1 l2 C, tl P (l1 ++ tzero :: l2) C
| plus_trr1 : forall A B l, tl P l (Some A) ->
                            tl P l (Some (tplus A B))
| plus_trr2 : forall A B l, tl P l (Some A) ->
                            tl P l (Some (tplus B A))
| plus_tlr : forall A B l1 l2 C,
                        tl P (l1 ++ A :: l2) C ->
                        tl P (l1 ++ B :: l2) C ->
                        tl P (l1 ++ tplus A B :: l2) C
| oc_trr : forall A l, tl P (map toc l) (Some A) ->
                       tl P (map toc l) (Some (toc A))
| de_tlr : forall A l1 l2 C,
                        tl P (l1 ++ A :: l2) C ->
                        tl P (l1 ++ toc A :: l2) C
| wk_tlr : forall A l1 l2 C,
                        tl P (l1 ++ l2) C ->
                        tl P (l1 ++ toc A :: l2) C
| co_tlr : forall A lw l1 l2 C,
                        tl P (l1 ++ toc A :: map toc lw
                                  ++ toc A :: l2) C ->
                        tl P (l1 ++ map toc lw ++ toc A :: l2) C
| cut_tr {f : tpcut P = true} : forall A l0 l1 l2 C,
                               tl P l0 (Some A) -> tl P (l1 ++ A :: l2) C ->
                               tl P (l1 ++ l0 ++ l2) C
| gax_tr : forall l A, tpgax P l A -> tl P l A. 

Instance tl_perm {P} {Pi} :
  Proper ((PEperm (tpperm P)) ==> Basics.impl) (fun l => tl P l Pi).
Proof.
intros l1 l2 HP pi.
eapply ex_tr ; eassumption.
Qed.

Lemma stronger_tpfrag P Q : le_tpfrag P Q -> forall l A, tl P l A -> tl Q l A.
Proof with try reflexivity ; try eassumption.
intros Hle l A H.
induction H ; try (constructor ; try assumption ; fail).
- apply (ex_tr _ l1)...
  destruct Hle as (_ & _ & Hp).
  hyps_PEperm_unfold ; unfold PEperm.
  destruct (tpperm P) ; destruct (tpperm Q) ;
    simpl in Hp ; try inversion Hp ; subst...
- destruct Hle as [Hcut _].
  rewrite f in Hcut.
  eapply (@cut_tr _ Hcut)...
- apply gax_tr.
  apply Hle...
Qed.

Instance Permutation_tl P Pi :
  Proper ((PEperm (tpperm P)) ==> Basics.impl) (fun l => tl P l Pi).
Proof.
intros l1 l2 HP pi.
eapply ex_tr ; eassumption.
Qed.


(** ** 4. characterize corresponding [ill] fragment *)

(*
Definition tl_fragment A := A = N \/ exists B, A = tl2ill B.

Lemma tl_is_fragment : ifragment tl_fragment.
Proof.
intros A HfA B Hsf.
induction Hsf ;
  try (apply IHHsf ;
       destruct HfA as [HfA | [F HfA]] ; (try destruct F) ; 
       inversion HfA ;
       right ; eexists ; reflexivity).
- assumption.
- apply IHHsf ;
    destruct HfA as [HfA | [F HfA]] ; (try destruct F) ; 
    inversion HfA ;
    left ; eexists ; reflexivity.
- left ; reflexivity.
Qed.
*)

Definition t2ipfrag P := {|
  ipcut := tpcut P ;
  ipgax := fun l C => 
              (exists l0 C0, l = map tl2ill l0 /\ C = tl2ill C0 
                        /\ tpgax P l0 (Some C0))
           \/ (exists l0, l = map tl2ill l0 /\ C = N /\ tpgax P l0 None) ;
  ipperm := tpperm P |}.

Lemma cutrm_t2ipfrag : forall P,
  cutrm_ipfrag (t2ipfrag P) = t2ipfrag (cutrm_tpfrag P).
Proof.
reflexivity.
Qed.


(** ** 5. prove equivalence of proof predicates *)

Lemma tl2tlfrag {P} : forall l C, tl P l C ->
   (forall D, C = Some D -> exists s, ill (t2ipfrag P) (map tl2ill l) (tl2ill D) s)
/\ (C = None -> exists s, ill (t2ipfrag P) (map tl2ill l) N s).
Proof with try eassumption ; try reflexivity.
intros l C pi.
induction pi ;
  (split ; [ intros D HeqC | intros HeqC ; (try (now inversion HeqC)) ]) ;
  try destruct IHpi as [piS piE] ;
  try destruct IHpi1 as [piS1 piE1] ;
  try destruct IHpi2 as [piS2 piE2] ;
  try rewrite ? map_app in piS ;
  try rewrite ? map_app in piE ;
  try rewrite ? map_app in piS1 ;
  try rewrite ? map_app in piE1 ;
  try rewrite ? map_app in piS2 ;
  try rewrite ? map_app in piE2 ;
  list_simpl.
- destruct D ; inversion HeqC ; subst.
  eexists.
  apply ax_ir.
- destruct (piS _ HeqC) as [s0 pi0].
  eexists.
  eapply ex_ir... 
  apply PEperm_map...
- destruct (piE HeqC) as [s0 pi0].
  eexists.
  eapply ex_ir... 
  apply PEperm_map...
- destruct D ; inversion HeqC ; subst.
  eexists.
  apply one_irr.
- destruct (piS _ HeqC) as [s0 pi0].
  eexists.
  apply one_ilr...
- destruct (piE HeqC) as [s0 pi0].
  eexists.
  apply one_ilr...
- destruct (piS1 _ (eq_refl _)) as [s1 pi1'].
  destruct (piS2 _ (eq_refl _)) as [s2 pi2'].
  destruct D ; inversion HeqC ; subst.
  eexists.
  eapply ex_ir.
  + apply (tens_irr _ _ _ _ _ _ _ pi1' pi2').
  + simpl ; PEperm_solve.
- destruct (piS _ HeqC) as [s0 pi0].
  eexists.
  apply tens_ilr...
- destruct (piE HeqC) as [s0 pi0].
  eexists.
  apply tens_ilr...
- destruct D ; inversion HeqC ; subst.
  destruct (piE (eq_refl _)) as [s0 pi0].
  eexists.
  apply neg_irr...
- inversion HeqC.
- destruct (piS _ (eq_refl _ )) as [s0 pi0].
  eexists.
  eapply ex_ir.
  + eapply neg_ilr.
    apply pi0.
  + simpl ; PEperm_solve.
- eexists.
  apply zero_ilr.
- eexists.
  apply zero_ilr.
- destruct (piS _ (eq_refl _)) as [s0 pi0].
  destruct D ; inversion HeqC ; subst.
  eexists.
  apply plus_irr1...
- destruct (piS _ (eq_refl _)) as [s0 pi0].
  destruct D ; inversion HeqC ; subst.
  eexists.
  apply plus_irr2...
- destruct (piS1 _ HeqC) as [s1 pi1'].
  destruct (piS2 _ HeqC) as [s2 pi2'].
  eexists.
  apply plus_ilr...
- destruct (piE1 HeqC) as [s1 pi1'].
  destruct (piE2 HeqC) as [s2 pi2'].
  eexists.
  apply plus_ilr...
- destruct (piS _ (eq_refl _)) as [s0 pi0].
  destruct D ; inversion HeqC ; subst.
  eexists.
  rewrite tl2ill_map_ioc ; simpl.
  apply oc_irr.
  rewrite <- tl2ill_map_ioc...
- destruct (piS _ HeqC) as [s0 pi0].
  eexists.
  apply de_ilr...
- destruct (piE HeqC) as [s0 pi0].
  eexists.
  apply de_ilr...
- destruct (piS _ HeqC) as [s0 pi0].
  eexists.
  apply wk_ilr...
- destruct (piE HeqC) as [s0 pi0].
  eexists.
  apply wk_ilr...
- destruct (piS _ HeqC) as [s0 pi0].
  eexists.
  list_simpl in pi0.
  rewrite tl2ill_map_ioc.
  simpl ; apply co_ilr.
  rewrite <- tl2ill_map_ioc...
- destruct (piE HeqC) as [s0 pi0].
  eexists.
  list_simpl in pi0.
  rewrite tl2ill_map_ioc.
  simpl ; apply co_ilr.
  rewrite <- tl2ill_map_ioc...
- destruct (piS1 _ (eq_refl _ )) as [s1 pi1'].
  destruct (piS2 _ HeqC) as [s2 pi2'].
  eexists.
  eapply ex_ir.
  + eapply (cut_ir _ _ _ _ _ _ _ _ pi1' pi2').
  + simpl ; PEperm_solve.
- destruct (piS1 _ (eq_refl _ )) as [s1 pi1'].
  destruct (piE2 HeqC) as [s2 pi2'].
  eexists.
  eapply ex_ir.
  + eapply (cut_ir _ _ _ _ _ _ _ _ pi1' pi2').
  + simpl ; PEperm_solve.
- subst.
  eexists.
  apply gax_ir.
  left.
  eexists ; eexists ; split ; [ | split ]...
- subst.
  eexists.
  apply gax_ir.
  right.
  eexists ; split ; [ | split ]...
Unshelve. all : simpl...
Qed.

Lemma tlfrag2tl_0 {P} : tpcut P = false -> forall l A s,
  ill (t2ipfrag P) l A s ->
      (forall l0 A0, l = map tl2ill l0 -> A = tl2ill A0 -> tl P l0 (Some A0))
  /\  (forall l0, l = map tl2ill l0 -> A = N -> tl P l0 None).
Proof with try reflexivity ; try eassumption ; try omega.
intros Hcut.
intros l A s pi.
induction pi ;
  (split ; [ intros l'' A'' Heql HeqA | intros l'' Heql HeqN ]) ; subst ; 
  try (now (destruct A'' ; inversion HeqA)) ;
  try (now (decomp_map Heql ; destruct x ; inversion Heql3)) ;
  try (now inversion HeqN).
- destruct l'' ; inversion Heql ;
    destruct l'' ; inversion Heql.
  destruct A'' ; inversion HeqA ;
    destruct t ; inversion H0 ; subst.
  apply t2i_inj in H4 ; subst.
  apply ax_tr.
- exfalso.
  rewrite HeqN in Heql.
  destruct l'' ; inversion Heql.
  destruct t ; inversion H0.
- apply PEperm_map_inv in H.
  destruct H as (l0 & Heq & HP) ; subst.
  eapply ex_tr.
  + apply IHpi...
  + rewrite HP...
- apply PEperm_map_inv in H.
  destruct H as (l0 & Heq & HP) ; subst.
  symmetry in HP.
  eapply ex_tr.
  + apply IHpi...
  + rewrite HP...
- destruct l'' ; inversion Heql.
  destruct A'' ; inversion HeqA ; subst.
  apply one_trr.
- decomp_map Heql ; subst.
  destruct x ; inversion Heql3 ; subst.
  apply one_tlr.
  apply IHpi...
  list_simpl...
- decomp_map Heql ; subst.
  destruct x ; inversion Heql3 ; subst.
  apply one_tlr.
  apply IHpi...
  list_simpl...
- decomp_map Heql ; destruct A'' ; inversion HeqA ; subst.
  apply tens_trr.
  + apply IHpi1...
  + apply IHpi2...
- decomp_map Heql ; subst.
  destruct x ; inversion Heql3 ; subst.
  apply tens_tlr.
  apply IHpi...
  list_simpl...
- decomp_map Heql ; subst.
  destruct x ; inversion Heql3 ; subst.
  apply tens_tlr.
  apply IHpi...
  list_simpl...
- destruct A'' ; inversion HeqA ; subst.
  apply neg_trr.
  apply IHpi...
- decomp_map Heql ; subst.
  destruct x ; inversion Heql3 ; subst.
  destruct l3 ; inversion Heql4.
  apply neg_tlr.
  apply IHpi...
- decomp_map Heql ; subst.
  destruct x ; inversion Heql3 ; subst.
  apply zero_tlr.
- decomp_map Heql ; subst.
  destruct x ; inversion Heql3 ; subst.
  apply zero_tlr.
- destruct A'' ; inversion HeqA ; subst.
  apply plus_trr1.
  apply IHpi...
- destruct A'' ; inversion HeqA ; subst.
  apply plus_trr2.
  apply IHpi...
- decomp_map Heql ; subst.
  destruct x ; inversion Heql3 ; subst.
  apply plus_tlr.
  + apply IHpi1...
    list_simpl...
  + apply IHpi2...
    list_simpl...
- decomp_map Heql ; subst.
  destruct x ; inversion Heql3 ; subst.
  apply plus_tlr.
  + apply IHpi1...
    list_simpl...
  + apply IHpi2...
    list_simpl...
- apply tl2ill_map_ioc_inv in Heql.
  destruct Heql as (l0' & Heq & Heq') ; subst.
  destruct A'' ; inversion HeqA ; subst.
  apply oc_trr.
  apply IHpi...
  rewrite tl2ill_map_ioc...
- decomp_map Heql ; subst.
  destruct x ; inversion Heql3 ; subst.
  apply de_tlr.
  apply IHpi...
  list_simpl...
- decomp_map Heql ; subst.
  destruct x ; inversion Heql3 ; subst.
  apply de_tlr.
  apply IHpi...
  list_simpl...
- decomp_map Heql ; subst.
  destruct x ; inversion Heql3 ; subst.
  apply wk_tlr.
  apply IHpi...
  list_simpl...
- decomp_map Heql ; subst.
  destruct x ; inversion Heql3 ; subst.
  apply wk_tlr.
  apply IHpi...
  list_simpl...
- decomp_map Heql ; subst.
  apply tl2ill_map_ioc_inv in Heql3.
  destruct Heql3 as (l0' & Heq & Heq') ; subst.
  destruct x ; inversion Heql2 ; subst.
  apply co_tlr.
  apply IHpi...
  rewrite <- tl2ill_map_ioc.
  list_simpl...
- decomp_map Heql ; subst.
  apply tl2ill_map_ioc_inv in Heql3.
  destruct Heql3 as (l0' & Heq & Heq') ; subst.
  destruct x ; inversion Heql2 ; subst.
  apply co_tlr.
  apply IHpi...
  rewrite <- tl2ill_map_ioc.
  list_simpl...
- inversion f.
  rewrite H0 in Hcut ; inversion Hcut.
- inversion f.
  rewrite H0 in Hcut ; inversion Hcut.
- destruct H as [ (l & C & Heq1 & Heq2 & Hax) | (l & Heq1 & Heq2 & Hax) ].
  + apply tl2ill_inj in Heq2.
    apply map_inj in Heq1 ; [ | apply tl2ill_inj ] ; subst.
    apply gax_tr...
  + exfalso.
    destruct A'' ; inversion Heq2.
- destruct H as [ (l & C & Heq1 & Heq2 & Hax) | (l & Heq1 & Heq2 & Hax) ].
  + exfalso.
    destruct C ; inversion Heq2.
  + apply map_inj in Heq1 ; [ | apply tl2ill_inj ] ; subst.
    apply gax_tr...
Qed.

Lemma tlfrag2tl_cutfree {P} : tpcut P = false -> forall l s,
   (forall A, ill (t2ipfrag P) (map tl2ill l) (tl2ill A) s -> tl P l (Some A))
/\ (ill (t2ipfrag P) (map tl2ill l) N s -> tl P l None).
Proof with try reflexivity ; try assumption.
intros l s ; split ; [ intros A | ] ; intros pi ; eapply tlfrag2tl_0 in pi...
all : apply pi...
Qed.

Lemma tlfrag2tl_axfree {P} : (forall l C, ~ tpgax P l C) -> forall l s,
   (forall A, ill (t2ipfrag P) (map tl2ill l) (tl2ill A) s -> tl P l (Some A))
/\ (ill (t2ipfrag P) (map tl2ill l) N s -> tl P l None).
Proof with try reflexivity ; try assumption.
intros Hgax.
intros l s ; split ; [ intros A | ] ; intros pi.
- apply (cut_admissible_ill_nzeropos_axfree_by_ll _ i2ac_inj) in pi...
  + clear s ; destruct pi as [s pi].
    rewrite cutrm_t2ipfrag in pi.
    apply tlfrag2tl_cutfree in pi...
    apply (stronger_tpfrag (cutrm_tpfrag P))...
    split ; [ | split ]...
    intros f a Hax...
  + intros l' C' Hax.
    destruct Hax as [(l'' & C'' & Hl & HC & Hax) | (l'' & Hl & HC & Hax)] ;
      apply Hgax in Hax...
  + replace (tl2ill A :: map tl2ill l)
      with (map tl2ill (A :: l)) by (list_simpl ; reflexivity).
    apply Forall_forall.
    intros x Hin.
    apply in_map_iff in Hin.
    destruct Hin as (x0 & Heq & _) ; subst.
    apply tl2ill_nz.
- apply (cut_admissible_ill_nzeropos_axfree_by_ll _ i2ac_inj) in pi...
  + clear s ; destruct pi as [s pi].
    rewrite cutrm_t2ipfrag in pi.
    apply tlfrag2tl_cutfree in pi...
    apply (stronger_tpfrag (cutrm_tpfrag P))...
    split ; [ | split ]...
    intros f a Hax...
  + intros l' C' Hax.
    destruct Hax as [(l'' & C'' & Hl & HC & Hax) | (l'' & Hl & HC & Hax)] ;
      apply Hgax in Hax...
  + constructor ; [ constructor | ]...
    apply Forall_forall.
    intros x Hin.
    apply in_map_iff in Hin.
    destruct Hin as (x0 & Heq & _) ; subst.
    apply tl2ill_nz.
Qed.


(** ** 6. import properties *)

(** *** axiom expansion *)

Lemma ax_gen_r {P} : forall A, tl P (A :: nil) (Some A).
Proof.
intro A.
destruct (@ax_exp_ill (t2ipfrag (cutrm_tpfrag P)) (tl2ill A))
  as [s Hax].
apply (stronger_tpfrag (cutrm_tpfrag P)).
- split ; [ | split ] ; simpl ; try reflexivity.
  intros f a Has ; assumption.
- eapply tlfrag2tl_cutfree ; try reflexivity.
  eassumption.
Qed.

(** *** cut elimination *)

Lemma cut_tl_r_axfree {P} : (forall l C, ~ tpgax P l C) -> forall A l0 l1 l2 C,
  tl P l0 (Some A) -> tl P (l1 ++ A :: l2) C -> tl P (l1 ++ l0 ++ l2) C.
Proof with try reflexivity ; try eassumption.
intros Hgax.
intros A l0 l1 l2 C pi1 pi2.
destruct (tl2tlfrag _ _ pi1) as [pi1' _] ; simpl in pi1'.
destruct (pi1' _ (eq_refl _)) as [s1 pi1''].
destruct (tl2tlfrag _ _ pi2) as [pi2' pi2''].
case_eq (tpcut P) ; intros Hcut.
- eapply cut_tr...
- case_eq C.
  + intros D HeqD.
    destruct (pi2' _ HeqD) as [s pi].
    list_simpl in pi.
    eapply (cut_ir_nzeropos_axfree_by_ll _ i2ac_inj _ _ _ (map tl2ill l1)
                                                 (map tl2ill l2) _ _ _ _ pi1'')
      in pi...
    clear s ; destruct pi as [s pi].
    rewrite <- ? map_app in pi.
    apply tlfrag2tl_cutfree in pi...
  + intros HeqD.
    destruct (pi2'' HeqD) as [s pi].
    list_simpl in pi.
    eapply (cut_ir_nzeropos_axfree_by_ll _ i2ac_inj _ _ _ (map tl2ill l1)
                                                 (map tl2ill l2) _ _ _ _ pi1'')
      in pi...
    clear s ; destruct pi as [s pi].
    rewrite <- ? map_app in pi.
    apply tlfrag2tl_cutfree in pi...
Unshelve.
* intros l C0 Hax ; inversion Hax.
  -- destruct H as (l' & C' & Hl & HC & H).
     apply Hgax in H...
  -- destruct H as (l' & Hl & HC & H).
     apply Hgax in H...
* replace (tl2ill D :: map tl2ill l1 ++ map tl2ill l0 ++ map tl2ill l2)
     with (map tl2ill (D :: l1 ++ l0 ++ l2)) by (list_simpl ; reflexivity).
  apply Forall_forall.
  intros x Hin.
  apply in_map_iff in Hin.
  destruct Hin as (x0 & Heq & _) ; subst.
  apply tl2ill_nz.
* intros l C0 Hax ; inversion Hax.
  -- destruct H as (l' & C' & Hl & HC & H).
     apply Hgax in H...
  -- destruct H as (l' & Hl & HC & H).
     apply Hgax in H...
* constructor ; [ constructor | ].
  replace (map tl2ill l1 ++ map tl2ill l0 ++ map tl2ill l2)
     with (map tl2ill (l1 ++ l0 ++ l2)) by (list_simpl ; reflexivity).
  apply Forall_forall.
  intros x Hin.
  apply in_map_iff in Hin.
  destruct Hin as (x0 & Heq & _) ; subst.
  apply tl2ill_nz.
Qed.

Lemma cut_admissible_tl_axfree {P} : (forall l C, ~ tpgax P l C) ->
  forall l Pi, tl P l Pi -> tl (cutrm_tpfrag P) l Pi.
Proof with try reflexivity ; try eassumption.
intros Hgax.
intros l Pi pi.
induction pi ;
  try (constructor ; eassumption ; fail) ;
  try (destruct IHpi as [s' IHpi] ; constructor ; eassumption ; fail) ;
  try (destruct IHpi1 as [s'1 IHpi1] ;
       destruct IHpi2 as [s'2 IHpi2] ; constructor ; eassumption ; fail).
- apply (ex_tr _ l1)...
- eapply cut_tl_r_axfree...
Qed.

(** *** conservativity with respect to [ll] *)

Require Import ll.

(*
Theorem ll_is_tl_cutfree {P} : tpcut P = false -> forall l,
  (forall A, tl P l (Some A)
         <-> exists s,
             ll (i2pfrag i2ac (t2ipfrag P)) (ill2ll i2ac (tl2ill A) ::
                          rev (map dual (map (ill2ll i2ac) (map tl2ill l)))) s)
/\          (tl P l None
         <-> exists s,
             ll (i2pfrag i2ac (t2ipfrag P)) (ill2ll i2ac N ::
                          rev (map dual (map (ill2ll i2ac) (map tl2ill l)))) s).
Proof with try eassumption.
intros Hcut.
split ; split ; intros pi ; try destruct pi as [s pi].
- apply tl2tlfrag in pi.
  destruct (proj1 pi _ (eq_refl _)) as [s pi'].
  eapply ill_to_ll...
- eapply (ll_to_ill_cutfree _ i2ac_inj _ _ (ill2ll i2ac (tl2ill A)
            :: rev (map dual (map (ill2ll i2ac) (map tl2ill l))))) in pi ;
    [ | | reflexivity ]...
  + clear s ; destruct pi as [s pi].
    apply tlfrag2tl_cutfree in pi...
  + change (tl2ill A :: map tl2ill l) with (map tl2ill (A :: l)).
    apply Forall_forall.
    intros x Hin.
    apply in_map_iff in Hin.
    destruct Hin as (s0 & Heq & Hin) ; subst.
    apply tl2ill_nz.
- apply tl2tlfrag in pi.
  destruct (proj2 pi (eq_refl _)) as [s pi'].
  eapply ill_to_ll...
- eapply (ll_to_ill_cutfree _ i2ac_inj _ _ (ill2ll i2ac N
            :: rev (map dual (map (ill2ll i2ac) (map tl2ill l))))) in pi ;
    [ | | reflexivity ]...
  + clear s ; destruct pi as [s pi].
    apply tlfrag2tl_cutfree in pi...
  + constructor ; [ constructor | ].
    apply Forall_forall.
    intros x Hin.
    apply in_map_iff in Hin.
    destruct Hin as (s0 & Heq & Hin) ; subst.
    apply tl2ill_nz.
Unshelve.
* simpl...
* apply t2ipfrag_easyipgax.
* simpl...
* apply t2ipfrag_easyipgax.
Qed.
*)

Theorem ll_is_tl_axfree {P} : (forall l C, ~ tpgax P l C) -> forall l,
  (forall A, tl P l (Some A)
         <-> exists s,
             ll (i2pfrag i2ac (t2ipfrag P)) (ill2ll i2ac (tl2ill A) ::
                          rev (map dual (map (ill2ll i2ac) (map tl2ill l)))) s)
/\          (tl P l None
         <-> exists s,
             ll (i2pfrag i2ac (t2ipfrag P)) (ill2ll i2ac N ::
                          rev (map dual (map (ill2ll i2ac) (map tl2ill l)))) s).
Proof with try eassumption.
intros Hgax.
split ; split ; intros pi ; try destruct pi as [s pi].
- apply tl2tlfrag in pi.
  destruct (proj1 pi _ (eq_refl _)) as [s pi'].
  eapply ill_to_ll...
- eapply (ll_to_ill_nzeropos_axfree _ i2ac_inj _ (ill2ll i2ac (tl2ill A)
            :: rev (map dual (map (ill2ll i2ac) (map tl2ill l))))) in pi ;
    [ | | reflexivity ]...
  + clear s ; destruct pi as [s pi].
    apply tlfrag2tl_axfree in pi...
  + change (tl2ill A :: map tl2ill l) with (map tl2ill (A :: l)).
    apply Forall_forall.
    intros x Hin.
    apply in_map_iff in Hin.
    destruct Hin as (s0 & Heq & Hin) ; subst.
    apply tl2ill_nz.
- apply tl2tlfrag in pi.
  destruct (proj2 pi (eq_refl _)) as [s pi'].
  eapply ill_to_ll...
- eapply (ll_to_ill_nzeropos_axfree _ i2ac_inj _ (ill2ll i2ac N
            :: rev (map dual (map (ill2ll i2ac) (map tl2ill l))))) in pi ;
    [ | | reflexivity ]...
  + clear s ; destruct pi as [s pi].
    apply tlfrag2tl_axfree in pi...
  + constructor ; [ constructor | ].
    apply Forall_forall.
    intros x Hin.
    apply in_map_iff in Hin.
    destruct Hin as (s0 & Heq & Hin) ; subst.
    apply tl2ill_nz.
Unshelve.
* intros l0 C0 Hax ; inversion Hax.
  -- destruct H as (l' & C' & Hl & HC & H).
     apply Hgax in H...
  -- destruct H as (l' & Hl & HC & H).
     apply Hgax in H...
* intros l0 C0 Hax ; inversion Hax.
  -- destruct H as (l' & C' & Hl & HC & H).
     apply Hgax in H...
  -- destruct H as (l' & Hl & HC & H).
     apply Hgax in H...
Qed.

