(* tl example file for yalla library *)

(* TODO clean file: using cut admissibility of [ill] *)


(** * Example of a concrete use of the yalla library: tensor logic *)

Require Import CRelationClasses.
Require Import Arith.
Require Import Omega.
Require Import CMorphisms.

Require Import Injective.
Require Import Bool_more.
Require Import List_more.
Require Import List_Type_more.
Require Import Permutation_Type_more.
Require Import genperm_Type.


(** ** 0. load the [ill] library *)

Require Import ill_vs_ll.

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

Inductive tatomic : tformula -> Prop :=
| tatomic_var : forall x, tatomic (tvar x).

Inductive tsubform : tformula -> tformula -> Type :=
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
Definition atN_or_t2i := yalla_ax.atN_or_t2i.
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

Lemma N_not_tl2ill : forall A, N = tl2ill A -> False.
Proof.
intros A Heq ; destruct A ; inversion Heq.
Qed.

Lemma tl2ill_inj : injective tl2ill.
Proof with try reflexivity.
intros A.
induction A ; intros B Heq ;
  destruct B ; inversion Heq ;
  try apply IHA in H0 ;
  try apply IHA1 in H0 ;
  try apply IHA2 in H1 ; subst...
intuition.
Qed.

Lemma tl2ll_inj : injective (fun x => ill2ll i2ac (tl2ill x)).
Proof with try reflexivity.
intros A.
induction A ; intros B Heq ; destruct B ;
 try (inversion Heq ;
      try apply IHA in H0 ;
      try apply IHA1 in H0 ;
      try apply IHA2 in H1 ; subst ; reflexivity ; fail).
- simpl in Heq.
  f_equal.
  apply t2i_inj.
  apply i2ac_inj.
  unfold t2i in Heq ; unfold i2ac in Heq.
  remember (yalla_ax.i2ac (yalla_ax.t2i t)) as t1.
  remember (yalla_ax.i2ac (yalla_ax.t2i t0)) as t2.
  inversion Heq...
- inversion Heq.
  apply formulas.dual_inj in H0.
  apply IHA in H0 ; subst...
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
    { l2' | l2 = map toc l2' & l1 = map tl2ill l2' }.
Proof with try assumption ; try reflexivity.
induction l1 ; intros l2 Heq ;
  destruct l2 ; inversion Heq...
- exists nil ; split...
- apply IHl1 in H1.
  destruct t ; inversion H0.
  destruct H1 as [l2' Heq1 H1] ; subst.
  exists (t :: l2') ; split...
Qed.


(** ** 3. define proofs *)

Definition NoTAxioms := (existT (fun x => x -> list tformula * option tformula) _ Empty_fun).

Record tpfrag := mk_tpfrag {
  tpcut : bool ;
  tpgax : { tptypgax : Type & tptypgax -> list tformula * option tformula } ; (* Many thanks to Damien Pous! *)
  tpperm : bool }.

Definition le_tpfrag P Q :=
  prod 
     (Bool.leb (tpcut P) (tpcut Q))
  (prod
     (forall a, { b | projT2 (tpgax P) a = projT2 (tpgax Q) b })
     (Bool.leb (tpperm P) (tpperm Q))).

Lemma le_tpfrag_trans : forall P Q R,
  le_tpfrag P Q -> le_tpfrag Q R -> le_tpfrag P R.
Proof.
intros P Q R H1 H2.
destruct H1 as (Hc1 & Ha1 & Hp1).
destruct H2 as (Hc2 & Ha2 & Hp2).
split ; [ | split ] ; try (eapply leb_trans ; eassumption).
intros a.
destruct (Ha1 a) as [b Heq].
destruct (Ha2 b) as [c Heq2].
exists c ; etransitivity ; eassumption.
Qed.

Definition cutupd_tpfrag P b := mk_tpfrag b (tpgax P) (tpperm P).

Definition axupd_tpfrag P G := mk_tpfrag (tpcut P) G (tpperm P).

Definition cutrm_tpfrag P := cutupd_tpfrag P false.

Inductive tl P : list tformula -> option tformula -> Type :=
| ax_tr : forall X, tl P (tvar X :: nil) (Some (tvar X))
| ex_tr : forall l1 l2 A, tl P l1 A -> PEperm_Type (tpperm P) l1 l2 ->
                          tl P l2 A
| ex_oc_tr : forall l1 lw lw' l2 A, tl P (l1 ++ map toc lw ++ l2) A ->
               Permutation_Type lw lw' -> tl P (l1 ++ map toc lw' ++ l2) A
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
| co_tlr : forall A l1 l2 C,
              tl P (l1 ++ toc A :: toc A :: l2) C -> tl P (l1 ++ toc A :: l2) C
| cut_tr {f : tpcut P = true} : forall A l0 l1 l2 C,
                               tl P l0 (Some A) -> tl P (l1 ++ A :: l2) C ->
                               tl P (l1 ++ l0 ++ l2) C
| gax_tr : forall a,
           tl P (fst (projT2 (tpgax P) a)) (snd (projT2 (tpgax P) a)).

Instance tl_perm {P} {Pi} :
  Proper ((PEperm_Type (tpperm P)) ==> Basics.arrow) (fun l => tl P l Pi).
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
  hyps_PEperm_Type_unfold ; unfold PEperm_Type.
  destruct (tpperm P) ; destruct (tpperm Q) ;
    simpl in Hp ; try inversion Hp ; subst...
- eapply ex_oc_tr ; [ apply IHtl | ]...
- destruct Hle as [Hcut _].
  rewrite f in Hcut.
  eapply (@cut_tr _ Hcut)...
- destruct Hle as (_ & Hgax & _).
  destruct (Hgax a) as [b Heq].
  rewrite Heq.
  apply gax_tr.
Qed.


(** ** 4. characterize corresponding [ill] fragment *)

(*
Lemma tl2ill_dec : forall A,
   {B | A = tl2ill B} + (A = N)
 + ((forall B, A = tl2ill B -> False) * (A = N -> False)).
Proof with try reflexivity.
induction A ;
  (try now (right ; intros B Heq ; destruct B ; inversion Heq))
 ;
  try (destruct IHA1 as [[[B1 Heq1] | Hr1] | [Hr1 HN1]] ;
  destruct IHA2 as [[[B2 Heq2] | Hr2] | [Hr2 HN2]] ; subst ;
  (try now (right ; split ;
     [ intros B Heq ; destruct B ; inversion Heq ; subst ;
       eapply Hr1 ; reflexivity
     | intros Heq ; inversion Heq])) ;
  (try now (right ; split ;
     [ intros B Heq ; destruct B ; inversion Heq ; subst ;
       eapply Hr2 ; reflexivity
     | intros Heq ; inversion Heq])) ;
  (try now (right ; split ;
     [ intros B Heq ; destruct B ; inversion Heq ; subst ;
       eapply N_not_tl2ill ; assumption
     | intros Heq ; inversion Heq])) ;
  (try now (right ; split ; [ intros B Heq ; destruct B | intros Heq ] ;
     inversion Heq ; eapply N_not_tl2ill ; eassumption))).
- destruct (atN_or_t2i i) as [HatN | [ j Heq ]].
  + left ; right ; subst...
  + subst ; left ; left ; exists (tvar j)...
- left ; left ; exists tone...
- left ; left ; exists (ttens B1 B2)...
- destruct IHA as [[[B Heq] | Hr] | [Hr HN]] ; subst.
  + left ; left ; exists (tneg B)...
  + right ; split ; [ intros B Heq ; destruct B | intros Heq ] ; inversion Heq.
    eapply N_not_tl2ill ; eassumption.
  + right ; split ; [ intros B Heq ; destruct B | intros Heq ] ; inversion Heq ; subst.
    eapply Hr ; reflexivity.
- right ; split ; [ intros B Heq ; destruct B | intros Heq ] ; inversion Heq.
- left ; left ; exists tzero...
- left ; left ; exists (tplus B1 B2)...
- destruct IHA as [[[B Heq] | Hr] | [Hr HN]] ; subst.
  + left ; left ; exists (toc B)...
  + right ; split ; [ intros B Heq ; destruct B | intros Heq ] ; inversion Heq.
    eapply N_not_tl2ill ; eassumption.
  + right ; split ; [ intros B Heq ; destruct B | intros Heq ] ; inversion Heq ; subst.
    eapply Hr ; reflexivity.
Qed.

Definition tl_fragment A :=
match (tl2ill_dec A) with
| inl _ => true
| inr _ => false
end.

Lemma tl_is_fragment : ifragment tl_fragment.
Proof with try reflexivity.
intros A HfA B Hsf.

induction Hsf ; unfold tl_fragment in HfA.
- assumption.
- destruct (tl2ill_dec (itens B C)) ; try now inversion HfA.
  destruct s as [[B' Heq] | Heq] ; try now inversion Heq.
  destruct B' ; inversion Heq ; subst.
  apply IHHsf.
  unfold tl_fragment ; destruct (tl2ill_dec (tl2ill B'1))...
  exfalso ; eapply (fst p)...
- destruct (tl2ill_dec (itens C B)) ; try now inversion HfA.
  destruct s as [[B' Heq] | Heq] ; try now inversion Heq.
  destruct B' ; inversion Heq ; subst.
  apply IHHsf.
  unfold tl_fragment ; destruct (tl2ill_dec (tl2ill B'2))...
  exfalso ; eapply (fst p)...
- destruct (tl2ill_dec (ilpam B C)) ; try now inversion HfA.
  destruct s as [[B' Heq] | Heq] ; try destruct B' ; inversion Heq.
- destruct (tl2ill_dec (ilpam C B)) ; try now inversion HfA.
  destruct s as [[B' Heq] | Heq] ; try destruct B' ; inversion Heq.
- destruct (tl2ill_dec (ilmap B C)) ; try now inversion HfA.
  destruct s as [[B' Heq] | Heq] ; try destruct B' ; inversion Heq.
- destruct (tl2ill_dec (ilmap C B)) ; try now inversion HfA.
  destruct s as [[B' Heq] | Heq] ; try destruct B' ; inversion Heq.
- destruct (tl2ill_dec (ineg B)) ; try now inversion HfA.
  destruct s as [[B' Heq] | Heq] ; try now inversion Heq.
  destruct B' ; inversion Heq ; subst.
  apply IHHsf.
  unfold tl_fragment ; destruct (tl2ill_dec (tl2ill B'))...
  exfalso ; eapply (fst p)...
- unfold tl_fragment ; destruct (tl2ill_dec N)...
  exfalso ; apply (snd p)...
- destruct (tl2ill_dec (iplus B C)) ; try now inversion HfA.
  destruct s as [[B' Heq] | Heq] ; try now inversion Heq.
  destruct B' ; inversion Heq ; subst.
  apply IHHsf.
  unfold tl_fragment ; destruct (tl2ill_dec (tl2ill B'1))...
  exfalso ; eapply (fst p)...
- destruct (tl2ill_dec (iplus C B)) ; try now inversion HfA.
  destruct s as [[B' Heq] | Heq] ; try now inversion Heq.
  destruct B' ; inversion Heq ; subst.
  apply IHHsf.
  unfold tl_fragment ; destruct (tl2ill_dec (tl2ill B'2))...
  exfalso ; eapply (fst p)...
- destruct (tl2ill_dec (iwith B C)) ; try now inversion HfA.
  destruct s as [[B' Heq] | Heq] ; try destruct B' ; inversion Heq.
- destruct (tl2ill_dec (iwith C B)) ; try now inversion HfA.
  destruct s as [[B' Heq] | Heq] ; try destruct B' ; inversion Heq.
- destruct (tl2ill_dec (ioc B)) ; try now inversion HfA.
  destruct s as [[B' Heq] | Heq] ; try now inversion Heq.
  destruct B' ; inversion Heq ; subst.
  apply IHHsf.
  unfold tl_fragment ; destruct (tl2ill_dec (tl2ill B'))...
  exfalso ; eapply (fst p)...
Qed.
*)

Definition t2ipfrag P := {|
  ipcut := tpcut P ;
  ipgax := existT (fun x => x -> list iformula * iformula) (projT1 (tpgax P))
             (fun a => (map tl2ill (fst (projT2 (tpgax P) a)),
                        match snd (projT2 (tpgax P) a) with
                        | Some C => tl2ill C
                        | None   => N
                        end)) ;
  ipperm := tpperm P |}.

Lemma cutrm_t2ipfrag : forall P,
  cutrm_ipfrag (t2ipfrag P) = t2ipfrag (cutrm_tpfrag P).
Proof.
reflexivity.
Qed.


(** ** 5. prove equivalence of proof predicates *)

Lemma tl2tlfrag {P} : forall l C, tl P l C ->
   (forall D, C = Some D -> ill (t2ipfrag P) (map tl2ill l) (tl2ill D))
 * (C = None -> ill (t2ipfrag P) (map tl2ill l) N).
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
  list_simpl ;
  (try now (constructor ; intuition)) ;
  try now (destruct D ; inversion HeqC ; subst ; constructor ; intuition).
- eapply ex_ir.
  + apply (piS _ HeqC).
  + apply PEperm_Type_map...
- eapply ex_ir.
  + apply (piE HeqC).
  + apply PEperm_Type_map...
- rewrite tl2ill_map_ioc.
  apply (Permutation_Type_map tl2ill) in p.
  eapply ex_oc_ir...
  rewrite <- tl2ill_map_ioc.
  eapply piS...
- rewrite tl2ill_map_ioc.
  apply (Permutation_Type_map tl2ill) in p.
  eapply ex_oc_ir...
  rewrite <- tl2ill_map_ioc.
  eapply piE...
- destruct D ; inversion HeqC ; subst.
  rewrite tl2ill_map_ioc ; simpl.
  apply oc_irr.
  rewrite <- tl2ill_map_ioc ; intuition.
- eapply ex_ir...
  eapply (cut_ir _ _ _ _ _ _ (piS1 _ eq_refl) (piS2 _ HeqC))...
- eapply ex_ir...
  eapply (cut_ir _ _ _ _ _ _ (piS1 _ eq_refl) (piE2 HeqC))...
- assert (pi := gax_ir (t2ipfrag P) a).
  simpl in pi.
  rewrite HeqC in pi...
- assert (pi := gax_ir (t2ipfrag P) a).
  simpl in pi.
  rewrite HeqC in pi...
Unshelve. all : simpl...
Qed.

Lemma tlfrag2tl_0 {P} : tpcut P = false -> forall l A,
  ill (t2ipfrag P) l A ->
      (forall l0 A0, l = map tl2ill l0 -> A = tl2ill A0 -> tl P l0 (Some A0))
    * (forall l0, l = map tl2ill l0 -> A = N -> tl P l0 None).
Proof with try reflexivity ; try eassumption ; try omega.
intros Hcut.
intros l A pi.
induction pi ;
  (split ; [ intros l'' A'' Heql HeqA | intros l'' Heql HeqN ]) ; subst ; 
  try (now (destruct A'' ; inversion HeqA)) ;
  try (now (decomp_map_Type Heql ; destruct x ; inversion Heql3)) ;
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
- apply PEperm_Type_map_inv in p.
  destruct p as [l0 Heq HP] ; subst.
  eapply ex_tr.
  + apply IHpi...
  + symmetry...
- apply PEperm_Type_map_inv in p.
  destruct p as [l0 Heq HP] ; subst.
  symmetry in HP.
  eapply ex_tr ; [ apply IHpi | ]...
- decomp_map_Type Heql ; subst.
  simpl in Heql3 ; apply tl2ill_map_ioc_inv in Heql3 ; destruct Heql3 as [l ? ?] ; subst.
  apply Permutation_Type_map_inv in p ; destruct p as [l' ? HP] ; subst.
  symmetry in HP.
  eapply ex_oc_tr ; [ | eassumption ].
  apply IHpi...
  rewrite <- tl2ill_map_ioc ; rewrite <- ? map_app...
- decomp_map_Type Heql ; subst.
  simpl in Heql3 ; apply tl2ill_map_ioc_inv in Heql3 ; destruct Heql3 as [l ? ?] ; subst.
  apply Permutation_Type_map_inv in p ; destruct p as [l' ? HP] ; subst.
  symmetry in HP.
  eapply ex_oc_tr ; [ | eassumption ].
  apply IHpi...
  rewrite <- tl2ill_map_ioc ; rewrite <- ? map_app...
- destruct l'' ; inversion Heql.
  destruct A'' ; inversion HeqA ; subst.
  apply one_trr.
- decomp_map_Type Heql ; subst.
  destruct x ; inversion Heql3 ; subst.
  apply one_tlr.
  apply IHpi...
  list_simpl...
- decomp_map_Type Heql ; subst.
  destruct x ; inversion Heql3 ; subst.
  apply one_tlr.
  apply IHpi...
  list_simpl...
- decomp_map_Type Heql ; destruct A'' ; inversion HeqA ; subst.
  apply tens_trr.
  + apply IHpi1...
  + apply IHpi2...
- decomp_map_Type Heql ; subst.
  destruct x ; inversion Heql3 ; subst.
  apply tens_tlr.
  apply IHpi...
  list_simpl...
- decomp_map_Type Heql ; subst.
  destruct x ; inversion Heql3 ; subst.
  apply tens_tlr.
  apply IHpi...
  list_simpl...
- destruct A'' ; inversion HeqA ; subst.
  apply neg_trr.
  apply IHpi...
- decomp_map_Type Heql ; subst.
  destruct x ; inversion Heql3 ; subst.
  destruct l3 ; inversion Heql4.
  apply neg_tlr.
  apply IHpi...
- decomp_map_Type Heql ; subst.
  destruct x ; inversion Heql3 ; subst.
  apply zero_tlr.
- decomp_map_Type Heql ; subst.
  destruct x ; inversion Heql3 ; subst.
  apply zero_tlr.
- destruct A'' ; inversion HeqA ; subst.
  apply plus_trr1.
  apply IHpi...
- destruct A'' ; inversion HeqA ; subst.
  apply plus_trr2.
  apply IHpi...
- decomp_map_Type Heql ; subst.
  destruct x ; inversion Heql3 ; subst.
  apply plus_tlr.
  + apply IHpi1...
    list_simpl...
  + apply IHpi2...
    list_simpl...
- decomp_map_Type Heql ; subst.
  destruct x ; inversion Heql3 ; subst.
  apply plus_tlr.
  + apply IHpi1...
    list_simpl...
  + apply IHpi2...
    list_simpl...
- apply tl2ill_map_ioc_inv in Heql.
  destruct Heql as [l0' Heq Heq'] ; subst.
  destruct A'' ; inversion HeqA ; subst.
  apply oc_trr.
  apply IHpi...
  rewrite tl2ill_map_ioc...
- decomp_map_Type Heql ; subst.
  destruct x ; inversion Heql3 ; subst.
  apply de_tlr.
  apply IHpi...
  list_simpl...
- decomp_map_Type Heql ; subst.
  destruct x ; inversion Heql3 ; subst.
  apply de_tlr.
  apply IHpi...
  list_simpl...
- decomp_map_Type Heql ; subst.
  destruct x ; inversion Heql3 ; subst.
  apply wk_tlr.
  apply IHpi...
  list_simpl...
- decomp_map_Type Heql ; subst.
  destruct x ; inversion Heql3 ; subst.
  apply wk_tlr.
  apply IHpi...
  list_simpl...
- decomp_map_Type Heql ; subst.
  destruct x ; inversion Heql3 ; subst.
  apply co_tlr.
  apply IHpi...
  list_simpl...
- decomp_map_Type Heql ; subst.
  destruct x ; inversion Heql3 ; subst.
  apply co_tlr.
  apply IHpi...
  list_simpl...
- inversion f.
  rewrite H0 in Hcut ; inversion Hcut.
- inversion f.
  rewrite H0 in Hcut ; inversion Hcut.
- simpl in Heql ; simpl in HeqA.
  case_eq (snd (projT2 (tpgax P) a)).
  + intros A Heq.
    rewrite_all Heq.
    apply tl2ill_inj in HeqA ; subst.
    rewrite <- Heq.
    apply map_inj in Heql ; [ | apply tl2ill_inj ] ; subst.
    apply gax_tr.
  + intros Heq ; exfalso.
    rewrite_all Heq.
    destruct A'' ; inversion HeqA.
- simpl in Heql ; simpl in HeqN.
  case_eq (snd (projT2 (tpgax P) a)).
  + intros A Heq ; exfalso.
    rewrite_all Heq.
    destruct A ; inversion HeqN.
  + intros Heq.
    rewrite_all Heq.
    rewrite <- Heq.
    apply map_inj in Heql ; [ | apply tl2ill_inj ] ; subst.
    apply gax_tr.
Qed.

Lemma tlfrag2tl_cutfree {P} : tpcut P = false -> forall l,
   (forall A, ill (t2ipfrag P) (map tl2ill l) (tl2ill A) -> tl P l (Some A))
 * (ill (t2ipfrag P) (map tl2ill l) N -> tl P l None).
Proof with try reflexivity ; try assumption.
intros l ; split ; [ intros A | ] ; intros pi ; eapply tlfrag2tl_0 in pi...
all : apply pi...
Qed.

Lemma tlfrag2tl_axfree {P} : (projT1 (tpgax P) -> False) -> forall l,
   (forall A, ill (t2ipfrag P) (map tl2ill l) (tl2ill A) -> tl P l (Some A))
 * (ill (t2ipfrag P) (map tl2ill l) N -> tl P l None).
Proof with try reflexivity ; try assumption.
intros Hgax.
intros l ; split ; [ intros A | ] ; intros pi.
- apply cut_admissible_ill in pi ; (try (now (intros a ; exfalso ; apply (Hgax a)))).
  rewrite cutrm_t2ipfrag in pi.
  apply tlfrag2tl_cutfree in pi...
  apply (stronger_tpfrag (cutrm_tpfrag P))...
  split ; [ | split ] ; intuition...
- apply cut_admissible_ill in pi ; (try (now (intros a ; exfalso ; apply (Hgax a)))).
  rewrite cutrm_t2ipfrag in pi.
  apply tlfrag2tl_cutfree in pi...
  apply (stronger_tpfrag (cutrm_tpfrag P))...
  split ; [ | split ] ; intuition...
Qed.


(** ** 6. import properties *)

(** *** axiom expansion *)

Lemma ax_gen_r {P} : forall A, tl P (A :: nil) (Some A).
Proof.
intro A.
apply (stronger_tpfrag (cutrm_tpfrag P)).
- split ; [ | split ] ; simpl ; try reflexivity.
  intros a ; exists a ; reflexivity.
- eapply tlfrag2tl_cutfree ; try reflexivity.
  apply ax_exp_ill.
Qed.

(** *** cut admissibility *)

Lemma cut_tl_r_axfree {P} : (projT1 (tpgax P) -> False) -> forall A l0 l1 l2 C,
  tl P l0 (Some A) -> tl P (l1 ++ A :: l2) C -> tl P (l1 ++ l0 ++ l2) C.
Proof with try reflexivity ; try eassumption.
intros Hgax.
intros A l0 l1 l2 C pi1 pi2.
destruct (tl2tlfrag _ _ pi1) as [pi1' _] ; simpl in pi1'.
assert (pi1'' := pi1' _ eq_refl).
destruct (tl2tlfrag _ _ pi2) as [pi2' pi2''].
case_eq (tpcut P) ; intros Hcut.
- eapply cut_tr...
- case_eq C.
  + intros D HeqD.
    apply tlfrag2tl_cutfree...
    assert (pi := pi2' _ HeqD).
    list_simpl in pi.
    list_simpl ; eapply cut_ir_axfree...
  + intros HeqD.
    apply tlfrag2tl_cutfree...
    assert (pi := pi2'' HeqD).
    list_simpl in pi ; rewrite <- ? map_app in pi.
    list_simpl ; eapply cut_ir_axfree...
Qed.

Lemma cut_admissible_tl_axfree {P} : (projT1 (tpgax P) -> False) ->
  forall l Pi, tl P l Pi -> tl (cutrm_tpfrag P) l Pi.
Proof with try reflexivity ; try eassumption.
intros Hgax.
intros l Pi pi.
induction pi ; try now econstructor.
- apply (ex_tr _ l1)...
- eapply ex_oc_tr ; [ apply IHpi | ]...
- eapply cut_tl_r_axfree...
Qed.

(** *** conservativity with respect to [ll] *)

Require Import ll_def.

Definition easytpgax P := forall a,
  (forall D, ill2ll i2ac (snd (projT2 (ipgax (t2ipfrag P)) a)) = dual (ill2ll i2ac D) -> False)
* (forall A C, snd (projT2 (tpgax P) a) = Some A -> ill2ll i2ac C = ill2ll i2ac (tl2ill A) -> C = tl2ill A)
* (forall A C, In_Type A (fst (projT2 (tpgax P) a)) -> ill2ll i2ac C = ill2ll i2ac (tl2ill A) -> C = tl2ill A).

Lemma tatomic_easytpgax {P} :
  (forall a, prod (option_prop tatomic (snd (projT2 (tpgax P) a)))
                  (Forall_Type tatomic (fst (projT2 (tpgax P) a)))) -> easytpgax P.
Proof.
intros Hgax a ; split ; [ split | ].
- destruct (Hgax a) as [Hat _].
  simpl ; intros D Heq.
  destruct (snd (projT2 (tpgax P) a)).
  + destruct t ; inversion Hat ; subst.
    destruct D ; inversion Heq.
  + destruct D ; inversion Heq.
- destruct (Hgax a) as [Hat _].
  simpl ; intros A C Heq1 Heq2.
  destruct (snd (projT2 (tpgax P) a)) ; inversion Heq1 ; subst.
  destruct A ; inversion Hat ; subst.
  destruct C ; inversion Heq2.
  apply i2ac_inj in H0 ; subst ; reflexivity.
- destruct (Hgax a) as [_ Hat].
  simpl ; intros A C Hin Heq.
  eapply Forall_Type_forall in Hat ; try eassumption.
  destruct A ; inversion Hat ; subst.
  destruct C ; inversion Heq.
  apply i2ac_inj in H0 ; subst ; reflexivity.
Qed.

Lemma easytpgax_easyipgax {P} : easytpgax P -> easyipgax_nzeropos yalla_ax.i2ac (t2ipfrag P).
Proof with try eassumption ; try reflexivity.
intros Hgax.
split ; [ split | ] ; simpl.
- intros D Heq ; exfalso.
  case_eq (snd (projT2 (tpgax P) a)) ; [intros t Heqa | intros Heqa] ; rewrite Heqa in Heq ; simpl in Heq.
  + assert (Hgaxa := fst (fst (Hgax a)) D).
    apply Hgaxa ; simpl.
    unfold i2ac ; rewrite <- Heq.
    rewrite Heqa...
  + destruct D ; inversion Heq.
- intros l C HP.
  assert (prod (sum (snd (projT2 (tpgax P) a) = None /\ C = N)
                    { C' | snd (projT2 (tpgax P) a) = Some C' /\ C = tl2ill C' })
               (PEperm_Type (tpperm P) (map tl2ill (fst (projT2 (tpgax P) a))) l))
    as [[[HeqNone HeqN] | [C' [Heq1 Heqé]]] HPE] ; subst.
  { apply PCperm_Type_vs_cons_inv in HP.
    destruct HP as [[l1 l2] Heq HP] ; simpl in Heq ; simpl in HP.
    destruct l1 ; inversion Heq ; subst.
    - split ; [ clear - Hgax H0 | clear - Hgax HP ].
      + assert (Hgaxa := snd (fst (Hgax a))).
        destruct (snd (projT2 (tpgax P) a)).
        * specialize Hgaxa with t C.
          right ; exists t ; split...
          apply Hgaxa...
          symmetry...
        * left.
          destruct C ; inversion H0 ; split...
          apply i2ac_inj in H1 ; subst...
      + rewrite app_nil_r in HP.
        apply PEperm_Type_rev in HP ; rewrite 2 rev_involutive in HP.
        apply PEperm_Type_map_inv_inj in HP ; [ | apply formulas.dual_inj ].
        remember (fst (projT2 (tpgax P) a)) as l0.
        assert (forall x, In_Type x l0 -> In_Type x (fst (projT2 (tpgax P) a))) as Hin
          by (intros x H ; rewrite <- Heql0 ; assumption).
        destruct (tpperm P) ; simpl in HP ; simpl.
        * clear Heql0 ; revert l0 Hin HP ; induction l ; intros l0 Hin Heq ; simpl in Heq.
          -- apply Permutation_Type_nil in Heq.
             destruct l0 ; inversion Heq...
          -- assert (HP := Heq).
             symmetry in Heq ; apply Permutation_Type_vs_cons_inv in Heq.
             destruct Heq as [[l1 l2] Heq] ; simpl in Heq.
             rewrite map_map in Heq ; symmetry in Heq ; decomp_map_Type Heq ; subst ;
               simpl in Hin ; simpl in Heq3 ; list_simpl.
             assert (a0 = tl2ill x) ; subst.
             { apply (snd (Hgax a))...
               apply Hin ; apply in_Type_elt. }
             symmetry ; apply Permutation_Type_cons_app.
             symmetry ; rewrite <- map_app ; apply IHl.
             ++ intros x0 Hin' ; apply Hin.
                apply in_Type_app_or in Hin' ; destruct Hin' as [Hin' | Hin'] ; apply in_Type_or_app.
                ** left...
                ** right ; apply in_Type_cons...
             ++ list_simpl in HP ; list_simpl.
                eapply Permutation_Type_cons_app_inv...
        * clear Heql0 ; revert l0 Hin HP ; induction l ; intros l0 Hin Heq ; simpl in Heq.
          -- symmetry in Heq ; apply map_eq_nil in Heq...
          -- destruct l0 ; inversion Heq.
             assert (forall x, In_Type x l0 -> In_Type x (fst (projT2 (tpgax P) a))) as Hin'
               by (intros x H ; apply Hin ; apply in_Type_cons ; assumption).
             simpl ; rewrite (IHl _ Hin' H1) ; f_equal.
             symmetry ; eapply (snd (Hgax _))...
             apply Hin ; constructor...
    - exfalso.
      apply PEperm_Type_vs_elt_inv in HP ; destruct HP as [[l1' l2'] Heq' HP] ;
        clear - Hgax Heq' ; simpl in Heq'.
      apply (f_equal (@rev _)) in Heq'.
      rewrite rev_involutive in Heq' ; list_simpl in Heq'.
      rewrite map_map in Heq'.
      symmetry in Heq' ; decomp_map Heq' ; subst.
      assert (Hgaxa := fst (fst (Hgax a)) x).
      apply Hgaxa ; simpl.
      unfold i2ac ; rewrite <- Heq'3... }
  + eapply ex_ir ; simpl...
    refine (snd (tl2tlfrag _ _ _) _)...
    apply gax_tr.
  + eapply ex_ir ; simpl...
    refine (fst (tl2tlfrag _ _ _) _ _)...
    apply gax_tr.
- intros Hin.
  apply in_Type_split in Hin ; destruct Hin as [(l1,l2) Heq].
  symmetry in Heq ; decomp_map Heq.
  eapply N_not_tl2ill...
Qed.

Theorem ll_is_tl_cutfree {P} : tpcut P = false -> easytpgax P -> forall l,
  (forall A, tl P l (Some A)
         -> ll (i2pfrag i2ac (t2ipfrag P)) (ill2ll i2ac (tl2ill A) ::
                          rev (map dual (map (ill2ll i2ac) (map tl2ill l)))))
* (forall A, 
        ll (i2pfrag i2ac (t2ipfrag P)) (ill2ll i2ac (tl2ill A) ::
                          rev (map dual (map (ill2ll i2ac) (map tl2ill l))))
        -> tl P l (Some A))
* (tl P l None
        -> ll (i2pfrag i2ac (t2ipfrag P)) (ill2ll i2ac N ::
                 rev (map dual (map (ill2ll i2ac) (map tl2ill l)))))
* (ll (i2pfrag i2ac (t2ipfrag P)) (ill2ll i2ac N ::
                 rev (map dual (map (ill2ll i2ac) (map tl2ill l)))) 
        -> tl P l None).
Proof with try eassumption.
intros Hcut Hgax l.
split ; [ split ; [ split | ] | ] ; (try intros A pi) ; try intros pi.
- apply tl2tlfrag in pi.
  assert (pi' := fst pi _ (eq_refl _)).
  eapply ill_to_ll...
- eapply (ll_to_ill_nzeropos_cutfree _ i2ac_inj _ _ (ill2ll i2ac (tl2ill A)
            :: rev (map dual (map (ill2ll i2ac) (map tl2ill l))))) in pi ;
    [ | | reflexivity ]...
  + apply tlfrag2tl_cutfree in pi...
  + change (tl2ill A :: map tl2ill l) with (map tl2ill (A :: l)).
    apply forall_Forall_Type.
    intros x Hin.
    apply in_Type_map_inv in Hin.
    destruct Hin as (s0 & Heq & Hin) ; subst.
    apply tl2ill_nz.
- apply tl2tlfrag in pi.
  assert (pi' := snd pi (eq_refl _)).
  eapply ill_to_ll...
- eapply (ll_to_ill_nzeropos_cutfree _ i2ac_inj _ _ (ill2ll i2ac N
            :: rev (map dual (map (ill2ll i2ac) (map tl2ill l))))) in pi ;
    [ | | reflexivity ]...
  + apply tlfrag2tl_cutfree in pi...
  + constructor ; [ constructor | ].
    apply forall_Forall_Type.
    intros x Hin.
    apply in_Type_map_inv in Hin.
    destruct Hin as (s0 & Heq & Hin) ; subst.
    apply tl2ill_nz.
Unshelve.
* simpl...
* apply easytpgax_easyipgax...
* simpl...
* apply easytpgax_easyipgax...
Qed.

Theorem ll_is_tl_axfree {P} : (projT1 (tpgax P) -> False) -> forall l,
   (forall A, tl P l (Some A)
           -> ll (i2pfrag i2ac (t2ipfrag P)) (ill2ll i2ac (tl2ill A) ::
                           rev (map dual (map (ill2ll i2ac) (map tl2ill l)))))
 * (forall A, ll (i2pfrag i2ac (t2ipfrag P)) (ill2ll i2ac (tl2ill A) ::
                           rev (map dual (map (ill2ll i2ac) (map tl2ill l))))
           -> tl P l (Some A))
 *           (tl P l None
           -> ll (i2pfrag i2ac (t2ipfrag P)) (ill2ll i2ac N ::
                           rev (map dual (map (ill2ll i2ac) (map tl2ill l)))))
 *           (ll (i2pfrag i2ac (t2ipfrag P)) (ill2ll i2ac N ::
                          rev (map dual (map (ill2ll i2ac) (map tl2ill l))))
           -> tl P l None).
Proof with try eassumption.
intros Hgax l.
split ; [ split ; [ split | ] | ] ; (try intros A pi) ; try intros pi.
- apply tl2tlfrag in pi.
  eapply ill_to_ll ; intuition.
- eapply (ll_to_ill_nzeropos_axfree _ i2ac_inj _ (ill2ll i2ac (tl2ill A)
            :: rev (map dual (map (ill2ll i2ac) (map tl2ill l))))) in pi ;
    [ | | reflexivity ]...
  + apply tlfrag2tl_axfree...
  + change (tl2ill A :: map tl2ill l) with (map tl2ill (A :: l)).
    remember (A :: l) as l0 ; clear.
    induction l0 ; simpl ; constructor ; intuition.
    apply tl2ill_nz.
- apply tl2tlfrag in pi.
  eapply ill_to_ll ; intuition.
- eapply (ll_to_ill_nzeropos_axfree _ i2ac_inj _ (ill2ll i2ac N
            :: rev (map dual (map (ill2ll i2ac) (map tl2ill l))))) in pi ;
    [ | | reflexivity ]...
  + apply tlfrag2tl_axfree...
  + constructor ; [ constructor | ].
    clear ; induction l ; simpl ; constructor ; intuition.
    apply tl2ill_nz.
Unshelve. all : intuition.
Qed.

