(* tl example file for yalla library *)

(** * Example of a concrete use of the yalla library: tensor logic *)

From Coq Require Import CMorphisms BoolOrder.
From OLlibs Require Import funtheory infinite List_more Permutation_Type_more GPermutation_Type.


(** ** 0. load the [ill] library *)

From Yalla Require Import ll_def ill_vs_ll.

Set Implicit Arguments.


Section Atoms.

Context { atom : InfDecType }.
Context { preiatom tatom : DecType }.
Context { Atoms : TLAtomType atom preiatom tatom }.


(** ** 1. define formulas *)

(** Tensor formulas *)
Inductive tformula :=
| tvar : tatom -> tformula
| tone : tformula
| ttens : tformula -> tformula -> tformula
| tneg : tformula -> tformula
| tzero : tformula
| tplus : tformula -> tformula -> tformula
| toc : tformula -> tformula.

Inductive tatomic : tformula -> Type :=
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

Lemma tsub_trans A B C : tsubform A B -> tsubform B C -> tsubform A C.
Proof.
intros Hl Hr; revert A Hl; induction Hr; intros A' Hl;
  try (constructor; apply IHHr); assumption.
Qed.

#[export] Instance tsub_po : PreOrder tsubform | 50.
Proof. split; [ intros l; apply tsub_id | intros l1 l2 l3; apply tsub_trans ]. Qed.

(** ** 2. define embedding into [iformula] *)

Lemma TAtom2PreIAtom_inj : injective TAtom2PreIAtom.
Proof. apply bijective_injective, TAtom2PreIAtom_bij. Qed.
Definition i2ac := IAtom2Atom.
Notation ill2ll := (@ill2ll _ _ IAtom2Atom_inj_base).
Notation i2pfrag := (@i2pfrag _ _ IAtom2Atom_inj_base).
Definition i2ac_inj : injective i2ac := IAtom2Atom_inj.
Definition t2i := fun x => Some (TAtom2PreIAtom x).
Lemma t2i_inj : injective t2i.
Proof.
unfold t2i; intros x y Heq; apply TAtom2PreIAtom_inj.
now injection Heq.
Qed.
Lemma atN_or_t2i x : (atN = x) + { y | x = t2i y }.
Proof.
destruct x as [c|]; [ right | left; reflexivity ].
unfold t2i.
destruct (bijective_surjective TAtom2PreIAtom_bij c) as [y ->].
now exists y.
Qed.
Lemma notatN x : ~ atN = t2i x.
Proof. unfold t2i; intros Heq; inversion Heq. Qed.
Definition iateq := @eqb (option_dectype preiatom).
Definition iateq_eq := @eqb_eq (option_dectype preiatom).

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
Proof.
intros A.
induction A; intros B Heq; destruct B; inversion Heq;
  try apply IHA in H0;
  try apply IHA1 in H0; try apply IHA2 in H1; subst; try reflexivity.
now apply TAtom2PreIAtom_inj in H0; subst.
Qed.

Lemma tl2ll_inj : injective (fun x => ill2ll (tl2ill x)).
Proof.
intros A.
induction A; intros B Heq; destruct B;
 try (now inversion Heq;
      try apply IHA in H0;
      try apply IHA1 in H0; try apply IHA2 in H1; subst).
- cbn in Heq.
  f_equal.
  apply t2i_inj, i2ac_inj.
  unfold t2i, i2ac in Heq.
  inversion Heq.
  now apply i2ac_inj, t2i_inj in H0; subst.
- inversion Heq.
  apply formulas.dual_inj in H0.
  apply IHA in H0 ; subst; reflexivity.
Qed.

Lemma N_not_tl2ill A : ~ N = tl2ill A.
Proof. intros Heq; destruct A; inversion Heq. Qed.

Lemma tl2ill_nz A : nonzerospos (tl2ill A).
Proof. induction A; cbn; constructor; assumption. Qed.

Lemma tl2ill_map_ioc l : map tl2ill (map toc l) = map ioc (map tl2ill l).
Proof. induction l; [ | cbn; rewrite IHl ]; reflexivity. Qed.

Lemma tl2ill_map_ioc_inv l1 l2 : map ioc l1 = map tl2ill l2 ->
  { l2' | l2 = map toc l2' & l1 = map tl2ill l2' }.
Proof.
induction l1 in l2 |- *; intros Heq; destruct l2; inversion Heq.
- exists nil; reflexivity.
- apply IHl1 in H1 as [l2' -> ->].
  destruct t; inversion H0.
  exists (t :: l2'); reflexivity.
Qed.


(** ** 3. define proofs *)

Definition NoTAxioms := (existT (fun x => x -> list tformula * option tformula) _ Empty_fun).

Record tpfrag := mk_tpfrag {
  tpcut : bool;
  tpgax : { tptypgax : Type & tptypgax -> list tformula * option tformula };
  tpperm : bool }.

Definition le_tpfrag P Q :=
  ((Bool.le (tpcut P) (tpcut Q))
 * (forall a, { b | projT2 (tpgax P) a = projT2 (tpgax Q) b })
 * (Bool.le (tpperm P) (tpperm Q)))%type.

Lemma le_tpfrag_trans P Q R : le_tpfrag P Q -> le_tpfrag Q R -> le_tpfrag P R.
Proof.
intros [[Hc1 Ha1] Hp1] [[Hc2 Ha2] Hp2].
repeat split; try (eapply BoolOrder.le_trans; eassumption).
intros a.
destruct (Ha1 a) as [b Heq], (Ha2 b) as [c Heq2].
exists c; etransitivity; eassumption.
Qed.

Definition cutupd_tpfrag P b := mk_tpfrag b (tpgax P) (tpperm P).

Definition axupd_tpfrag P G := mk_tpfrag (tpcut P) G (tpperm P).

Definition cutrm_tpfrag P := cutupd_tpfrag P false.

Inductive tl P : list tformula -> option tformula -> Type :=
| ax_tr : forall X, tl P (tvar X :: nil) (Some (tvar X))
| ex_tr : forall l1 l2 A, tl P l1 A -> PEPermutation_Type (tpperm P) l1 l2 ->
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

#[export] Instance tl_perm P Pi :
  Proper ((PEPermutation_Type (tpperm P)) ==> arrow) (fun l => tl P l Pi) | 100.
Proof. intros l1 l2 HP pi; apply ex_tr with l1; assumption. Qed.

Lemma stronger_tpfrag P Q : le_tpfrag P Q -> forall l A, tl P l A -> tl Q l A.
Proof.
intros [[Hcut Hgax] Hp] l A H.
induction H; (try now constructor).
- apply ex_tr with l1; [ assumption | ].
  hyps_GPermutation_Type_unfold; unfold PEPermutation_Type.
  destruct (tpperm P), (tpperm Q); cbn in Hp; try inversion Hp; subst;
    [ assumption | | ]; reflexivity.
- eapply ex_oc_tr; [ apply IHtl | assumption ].
- rewrite f in Hcut.
  apply (@cut_tr _ Hcut A); assumption.
- destruct (Hgax a) as [b ->].
  apply gax_tr.
Qed.


(** ** 4. characterize corresponding [ill] fragment *)

(*
Lemma tl2ill_dec A :
   {B | A = tl2ill B} + (A = N)
 + ((forall B, A = tl2ill B -> False) * (A = N -> False)).
Proof.
induction A;
  (try now (right; intros B Heq; destruct B; inversion Heq));
  try (destruct IHA1 as [[[B1 Heq1] | Hr1] | [Hr1 HN1]];
  destruct IHA2 as [[[B2 Heq2] | Hr2] | [Hr2 HN2]]; subst;
  (try now (right; split;
     [ intros B Heq; destruct B ; inversion Heq; subst;
       eapply Hr1; reflexivity
     | intros Heq; inversion Heq])) ;
  (try now (right; split;
     [ intros B Heq ; destruct B ; inversion Heq; subst;
       eapply Hr2; reflexivity
     | intros Heq; inversion Heq])) ;
  (try now (right; split;
     [ intros B Heq; destruct B ; inversion Heq; subst;
       eapply N_not_tl2ill ; assumption
     | intros Heq; inversion Heq])) ;
  (try now (right; split; [ intros B Heq; destruct B | intros Heq ];
     inversion Heq; eapply N_not_tl2ill; eassumption))).
- destruct (atN_or_t2i i) as [HatN | [ j Heq ]].
  + left; right; subst; reflexivity.
  + subst; left; left; exists (tvar j); reflexivity.
- left; left; exists tone; reflexivity.
- left; left; exists (ttens B1 B2); reflexivity.
- right; split; [ intros B Heq; destruct B | intros Heq ]; inversion Heq.
- destruct IHA as [[[B Heq] | Hr] | [Hr HN]]; subst.
  + left; left; exists (tneg B); reflexivity.
  + right; split; [ intros B Heq; destruct B | intros Heq ]; inversion Heq.
    apply N_not_tl2ill with B; assumption.
  + right; split ; [ intros B Heq; destruct B | intros Heq ]; inversion Heq; subst.
    apply Hr with B; reflexivity.
- right; split; [ intros B Heq; destruct B | intros Heq ]; inversion Heq.
- left; left; exists tzero; reflexivity.
- left; left; exists (tplus B1 B2); reflexivity.
- destruct IHA as [[[B Heq] | Hr] | [Hr HN]]; subst.
  + left; left; exists (toc B); reflexivity.
  + right; split; [ intros B Heq ; destruct B | intros Heq ]; inversion Heq.
    apply N_not_tl2ill with B; assumption.
  + right; split; [ intros B Heq; destruct B | intros Heq ]; inversion Heq; subst.
    apply Hr with B; reflexivity.
Qed.

Definition tl_fragment A :=
match (tl2ill_dec A) with
| inl _ => true
| inr _ => false
end.

Lemma tl_is_fragment : ifragment tl_fragment.
Proof.
intros A HfA B Hsf.
induction Hsf; unfold tl_fragment in HfA.
- assumption.
- destruct (tl2ill_dec (itens B C)); try now inversion HfA.
  destruct s as [[B' Heq] | Heq]; try now inversion Heq.
  destruct B'; inversion Heq; subst.
  apply IHHsf.
  unfold tl_fragment; destruct (tl2ill_dec (tl2ill B'1)); [ reflexivity | ].
  exfalso; apply (fst p) with B'1; reflexivity.
- destruct (tl2ill_dec (itens C B)); try now inversion HfA.
  destruct s as [[B' Heq] | Heq]; try now inversion Heq.
  destruct B'; inversion Heq; subst.
  apply IHHsf.
  unfold tl_fragment; destruct (tl2ill_dec (tl2ill B'2)); [ reflexivity | ].
  exfalso; apply (fst p) with B'2; reflexivity.
- destruct (tl2ill_dec (ilpam B C)); try now inversion HfA.
  destruct s as [[B' Heq] | Heq]; try destruct B'; inversion Heq.
- destruct (tl2ill_dec (ilpam C B)); try now inversion HfA.
  destruct s as [[B' Heq] | Heq]; try destruct B'; inversion Heq.
- destruct (tl2ill_dec (igen B)); try now inversion HfA.
  destruct s as [[B' Heq] | Heq]; try now inversion Heq.
  destruct B'; inversion Heq.
- unfold tl_fragment; destruct (tl2ill_dec N); [ reflexivity | ].
  exfalso; apply (snd p); reflexivity.
- destruct (tl2ill_dec (ilmap B C)) ; try now inversion HfA.
  destruct s as [[B' Heq] | Heq]; try destruct B'; inversion Heq.
- destruct (tl2ill_dec (ilmap C B)); try now inversion HfA.
  destruct s as [[B' Heq] | Heq]; try destruct B'; inversion Heq.
- destruct (tl2ill_dec (ineg B)); try now inversion HfA.
  destruct s as [[B' Heq] | Heq]; try now inversion Heq.
  destruct B'; inversion Heq; subst.
  apply IHHsf.
  unfold tl_fragment; destruct (tl2ill_dec (tl2ill B')); [ reflexivity | ].
  exfalso; apply (fst p) with B'; reflexivity.
- unfold tl_fragment; destruct (tl2ill_dec N); [ reflexivity | ].
  exfalso; apply (snd p); reflexivity.
- destruct (tl2ill_dec (iplus B C)); try now inversion HfA.
  destruct s as [[B' Heq] | Heq]; try now inversion Heq.
  destruct B'; inversion Heq; subst.
  apply IHHsf.
  unfold tl_fragment; destruct (tl2ill_dec (tl2ill B'1)); [ reflexivity | ].
  exfalso; apply (fst p) with B'1; reflexivity.
- destruct (tl2ill_dec (iplus C B)); try now inversion HfA.
  destruct s as [[B' Heq] | Heq]; try now inversion Heq.
  destruct B'; inversion Heq; subst.
  apply IHHsf.
  unfold tl_fragment; destruct (tl2ill_dec (tl2ill B'2)); [ reflexivity | ].
  exfalso; apply (fst p) with B'2; reflexivity.
- destruct (tl2ill_dec (iwith B C)); try now inversion HfA.
  destruct s as [[B' Heq] | Heq]; try destruct B'; inversion Heq.
- destruct (tl2ill_dec (iwith C B)); try now inversion HfA.
  destruct s as [[B' Heq] | Heq]; try destruct B'; inversion Heq.
- destruct (tl2ill_dec (ioc B)); try now inversion HfA.
  destruct s as [[B' Heq] | Heq]; try now inversion Heq.
  destruct B'; inversion Heq; subst.
  apply IHHsf.
  unfold tl_fragment; destruct (tl2ill_dec (tl2ill B')); [ reflexivity | ].
  exfalso; eapply (fst p) with B'; reflexivity.
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

Lemma cutrm_t2ipfrag P : cutrm_ipfrag (t2ipfrag P) = t2ipfrag (cutrm_tpfrag P).
Proof. reflexivity. Qed.


(** ** 5. prove equivalence of proof predicates *)

Lemma tl2tlfrag P l C : tl P l C ->
   (forall D, C = Some D -> ill (t2ipfrag P) (map tl2ill l) (tl2ill D))
 * (C = None -> ill (t2ipfrag P) (map tl2ill l) N).
Proof.
intros pi; induction pi;
  (split; [ intros D HeqC | intros HeqC; (try now inversion HeqC) ]);
  try destruct IHpi as [piS piE];
  try destruct IHpi1 as [piS1 piE1];
  try destruct IHpi2 as [piS2 piE2];
  try rewrite ? map_app in piS;
  try rewrite ? map_app in piE;
  try rewrite ? map_app in piS1;
  try rewrite ? map_app in piE1;
  try rewrite ? map_app in piS2;
  try rewrite ? map_app in piE2;
  list_simpl;
  (try now (constructor; intuition));
  try now (destruct D; inversion HeqC; subst; constructor; intuition).
- eapply ex_ir.
  + apply (piS _ HeqC).
  + apply PEPermutation_Type_map; assumption.
- eapply ex_ir.
  + apply (piE HeqC).
  + apply PEPermutation_Type_map; assumption.
- rewrite tl2ill_map_ioc.
  apply (Permutation_Type_map tl2ill) in p.
  eapply ex_oc_ir; [ | eassumption ].
  rewrite <- tl2ill_map_ioc; apply piS; assumption.
- rewrite tl2ill_map_ioc.
  apply (Permutation_Type_map tl2ill) in p.
  eapply ex_oc_ir; [ | eassumption ].
  rewrite <- tl2ill_map_ioc; apply piE; assumption.
- destruct D; inversion HeqC; subst.
  rewrite tl2ill_map_ioc; cbn; apply oc_irr.
  rewrite <- tl2ill_map_ioc; auto.
- assert (ipcut (t2ipfrag P) = true) as f' by assumption.
  apply (@cut_ir _ _ f' (tl2ill A) _ _ _ _ (piS1 _ eq_refl) (piS2 _ HeqC)).
- assert (ipcut (t2ipfrag P) = true) as f' by assumption.
  apply (@cut_ir _ _ f' (tl2ill A) _ _ _ _ (piS1 _ eq_refl) (piE2 HeqC)).
- assert (pi := @gax_ir _ (t2ipfrag P) a).
  cbn in pi.
  rewrite HeqC in pi; assumption.
- assert (pi := @gax_ir _ (t2ipfrag P) a).
  cbn in pi.
  rewrite HeqC in pi; assumption.
Qed.

Lemma tlfrag2tl_cutfree P : tpcut P = false -> forall l,
   (forall A, ill (t2ipfrag P) (map tl2ill l) (tl2ill A) -> tl P l (Some A))
 * (ill (t2ipfrag P) (map tl2ill l) N -> tl P l None).
Proof.
intros Hcut.
enough (forall l A, ill (t2ipfrag P) l A ->
      (forall l0 A0, l = map tl2ill l0 -> A = tl2ill A0 -> tl P l0 (Some A0))
    * (forall l0, l = map tl2ill l0 -> A = N -> tl P l0 None)) as HI
  by (intros l; split; [ intros A | ]; intros pi; apply (HI _ _ pi); reflexivity).
intros l A pi.
induction pi;
  (split; [ intros l'' A'' Heql HeqA | intros l'' Heql HeqN ]); subst;
  try (now (destruct A''; inversion HeqA));
  try (now (symmetry in Heql; decomp_map_inf Heql; destruct x; inversion Heql3));
  try (now inversion HeqN);
  try (symmetry in Heql; decomp_map_inf Heql; subst;
       destruct x; inversion Heql3; subst;
       constructor; apply IHpi; list_simpl; reflexivity);
  try (destruct A''; inversion HeqA; subst; constructor; apply IHpi; reflexivity).
- destruct l''; inversion Heql; destruct l''; inversion Heql.
  destruct A''; inversion HeqA; destruct t; inversion H0; subst.
  apply t2i_inj in H4; subst.
  apply ax_tr.
- exfalso.
  rewrite HeqN in Heql.
  destruct l''; inversion Heql.
  destruct t; inversion H0.
- apply PEPermutation_Type_map_inv in p.
  destruct p as [l0 Heq HP]; subst.
  eapply ex_tr.
  + apply IHpi; reflexivity.
  + symmetry; assumption.
- apply PEPermutation_Type_map_inv in p.
  destruct p as [l0 Heq HP] ; subst.
  symmetry in HP.
  eapply ex_tr ; [ apply IHpi; reflexivity | assumption ].
- symmetry in Heql; decomp_map_inf Heql; subst; symmetry in Heql3.
  cbn in Heql3; apply tl2ill_map_ioc_inv in Heql3; destruct Heql3 as [l ? ?]; subst.
  apply Permutation_Type_map_inv in p ; destruct p as [l' ? HP]; subst.
  symmetry in HP.
  eapply ex_oc_tr; [ | eassumption ].
  apply IHpi; [ rewrite <- tl2ill_map_ioc, <- ? map_app | ]; reflexivity.
- symmetry in Heql; decomp_map_inf Heql; subst; symmetry in Heql3.
  cbn in Heql3; apply tl2ill_map_ioc_inv in Heql3; destruct Heql3 as [l ? ?]; subst.
  apply Permutation_Type_map_inv in p; destruct p as [l' ? HP]; subst.
  symmetry in HP.
  eapply ex_oc_tr; [ | eassumption ].
  apply IHpi; [ rewrite <- tl2ill_map_ioc, <- ? map_app | ]; reflexivity.
- destruct l''; inversion Heql.
  destruct A''; inversion HeqA; subst.
  apply one_trr.
- symmetry in Heql; decomp_map_inf Heql; destruct A''; inversion HeqA; subst.
  apply tens_trr; [ apply IHpi1 | apply IHpi2 ]; reflexivity.
- symmetry in Heql; decomp_map_inf Heql; subst.
  destruct x; inversion Heql1; subst.
- symmetry in Heql; decomp_map_inf Heql; subst.
  destruct x; inversion Heql3; subst.
  destruct l3; inversion Heql4.
  apply neg_tlr, IHpi; reflexivity.
- symmetry in Heql; decomp_map_inf Heql; subst.
  destruct x; inversion Heql3; subst.
  apply plus_tlr; [ apply IHpi1 | apply IHpi2 ]; list_simpl; reflexivity.
- symmetry in Heql; decomp_map_inf Heql; subst.
  destruct x; inversion Heql3; subst.
  apply plus_tlr; [ apply IHpi1 | apply IHpi2 ]; list_simpl; reflexivity.
- apply tl2ill_map_ioc_inv in Heql.
  destruct Heql as [l0' Heq Heq']; subst.
  destruct A'' ; inversion HeqA; subst.
  apply oc_trr, IHpi; [ rewrite tl2ill_map_ioc | ]; reflexivity.
- inversion f.
  rewrite H0 in Hcut; inversion Hcut.
- inversion f.
  rewrite H0 in Hcut; inversion Hcut.
- cbn in Heql; cbn in HeqA.
  case_eq (snd (projT2 (tpgax P) a)).
  + intros A Heq.
    rewrite_all Heq.
    apply tl2ill_inj in HeqA; subst.
    rewrite <- Heq.
    apply map_injective in Heql; [ | apply tl2ill_inj ]; subst.
    apply gax_tr.
  + intros Heq; exfalso.
    rewrite_all Heq.
    destruct A''; inversion HeqA.
- cbn in Heql; cbn in HeqN.
  case_eq (snd (projT2 (tpgax P) a)).
  + intros A Heq; exfalso.
    rewrite_all Heq.
    destruct A; inversion HeqN.
  + intros Heq.
    rewrite_all Heq.
    rewrite <- Heq.
    apply map_injective in Heql; [ | apply tl2ill_inj ]; subst.
    apply gax_tr.
Qed.

Lemma tlfrag2tl_axfree P : (projT1 (tpgax P) -> False) -> forall l,
   (forall A, ill (t2ipfrag P) (map tl2ill l) (tl2ill A) -> tl P l (Some A))
 * (ill (t2ipfrag P) (map tl2ill l) N -> tl P l None).
Proof.
intros Hgax.
intros l; split; [ intros A | ]; intros pi.
- apply cut_admissible_ill in pi; (try now (intros a; exfalso; apply (Hgax a))).
  rewrite cutrm_t2ipfrag in pi.
  apply tlfrag2tl_cutfree in pi; [ | reflexivity ].
  apply (@stronger_tpfrag (cutrm_tpfrag P)); [ | assumption ].
  repeat split; try reflexivity; intuition.
- apply cut_admissible_ill in pi; (try now (intros a; exfalso; apply (Hgax a))).
  rewrite cutrm_t2ipfrag in pi.
  apply tlfrag2tl_cutfree in pi; [ | reflexivity ].
  apply (@stronger_tpfrag (cutrm_tpfrag P)); [ | assumption ].
  repeat split; try reflexivity.
  intros a; exists a; reflexivity.
Qed.


(** ** 6. import properties *)

(** *** axiom expansion *)

Lemma ax_gen_r P A : tl P (A :: nil) (Some A).
Proof.
apply (@stronger_tpfrag (cutrm_tpfrag P)).
- repeat split; try reflexivity.
  intros a; exists a; reflexivity.
- eapply tlfrag2tl_cutfree; try reflexivity.
  apply ax_exp_ill.
Qed.

(** *** cut admissibility *)

Lemma cut_tl_r_axfree P : (projT1 (tpgax P) -> False) -> forall A l0 l1 l2 C,
  tl P l0 (Some A) -> tl P (l1 ++ A :: l2) C -> tl P (l1 ++ l0 ++ l2) C.
Proof.
intros Hgax.
intros A l0 l1 l2 C pi1 pi2.
destruct (tl2tlfrag pi1) as [pi1' _]; cbn in pi1'.
assert (pi1'' := pi1' _ eq_refl).
destruct (tl2tlfrag pi2) as [pi2' pi2''].
case_eq (tpcut P); intros Hcut.
- eapply cut_tr; eassumption.
- case_eq C.
  + intros D HeqD.
    apply tlfrag2tl_cutfree; [ assumption | ].
    assert (pi := pi2' _ HeqD).
    list_simpl in pi.
    list_simpl; eapply cut_ir_axfree; eassumption.
  + intros HeqD.
    apply tlfrag2tl_cutfree; [ assumption | ].
    assert (pi := pi2'' HeqD).
    list_simpl in pi; rewrite <- ? map_app in pi.
    list_simpl; eapply cut_ir_axfree; eassumption.
Qed.

Lemma cut_admissible_tl_axfree P : notT (projT1 (tpgax P)) ->
  forall l Pi, tl P l Pi -> tl (cutrm_tpfrag P) l Pi.
Proof.
intros Hgax l Pi pi.
induction pi; try now econstructor.
- apply ex_tr with l1; assumption.
- eapply ex_oc_tr; [ apply IHpi | assumption ].
- eapply cut_tl_r_axfree; eassumption.
Qed.

(** *** conservativity with respect to [ll] *)

Definition easytpgax P := forall a,
  (forall D, ill2ll (snd (projT2 (ipgax (t2ipfrag P)) a)) = dual (ill2ll D) -> False)
* (forall A C, snd (projT2 (tpgax P) a) = Some A -> ill2ll C = ill2ll (tl2ill A) -> C = tl2ill A)
* (forall A C, In_inf A (fst (projT2 (tpgax P) a)) -> ill2ll C = ill2ll (tl2ill A) -> C = tl2ill A).

Lemma tatomic_easytpgax P :
  (forall a, prod (option_testT tatomic (snd (projT2 (tpgax P) a)))
                  (Forall_inf tatomic (fst (projT2 (tpgax P) a)))) -> easytpgax P.
Proof.
intros Hgax a; split; [ split | ].
- destruct (Hgax a) as [Hat _].
  cbn; intros D Heq.
  destruct (snd (projT2 (tpgax P) a)).
  + destruct t; inversion Hat; subst.
    destruct D; inversion Heq.
  + destruct D; inversion Heq.
- destruct (Hgax a) as [Hat _].
  cbn; intros A C Heq1 Heq2.
  destruct (snd (projT2 (tpgax P) a)); inversion Heq1; subst.
  destruct A; inversion Hat; subst.
  destruct C; inversion Heq2.
  apply i2ac_inj in H0; subst; reflexivity.
- destruct (Hgax a) as [_ Hat].
  cbn ; intros A C Hin Heq.
  eapply Forall_inf_forall in Hat; try eassumption.
  destruct A; inversion Hat; subst.
  destruct C; inversion Heq.
  apply i2ac_inj in H0; subst; reflexivity.
Qed.

Lemma easytpgax_easyipgax P : easytpgax P -> easyipgax_nzeropos (t2ipfrag P).
Proof.
intros Hgax.
split; [ split | ]; cbn.
- intros D Heq; exfalso.
  case_eq (snd (projT2 (tpgax P) a)); [intros t Heqa | intros Heqa]; rewrite Heqa in Heq; cbn in Heq.
  + assert (Hgaxa := fst (fst (Hgax a)) D).
    apply Hgaxa; cbn.
    rewrite <- Heq, Heqa; reflexivity.
  + destruct D; inversion Heq.
- intros l C HP.
  assert (prod (sum (snd (projT2 (tpgax P) a) = None /\ C = N)
                    { C' | snd (projT2 (tpgax P) a) = Some C' /\ C = tl2ill C' })
               (PEPermutation_Type (tpperm P) (map tl2ill (fst (projT2 (tpgax P) a))) l))
    as [[[HeqNone HeqN] | [C' [Heq1 Heqé]]] HPE]; subst.
  { apply PCPermutation_Type_vs_cons_inv in HP.
    destruct HP as [[l1 l2] HP Heq]; cbn in Heq, HP.
    destruct l1; inversion Heq; subst.
    - split; [ clear - Hgax H0 | clear - Hgax HP ].
      + assert (Hgaxa := snd (fst (Hgax a))).
        destruct (snd (projT2 (tpgax P) a)).
        * specialize Hgaxa with t C.
          right; exists t; split; [ reflexivity | ].
          apply Hgaxa; [ reflexivity | symmetry; assumption ].
        * left.
          destruct C; inversion H0; split; [ reflexivity | ].
          apply i2ac_inj in H1; subst; reflexivity.
      + rewrite app_nil_r in HP.
        apply PEPermutation_Type_rev in HP; rewrite 2 rev_involutive in HP.
        apply PEPermutation_Type_map_inv_inj in HP; [ | apply formulas.dual_inj ].
        remember (fst (projT2 (tpgax P) a)) as l0.
        assert (forall x, In_inf x l0 -> In_inf x (fst (projT2 (tpgax P) a))) as Hin
          by (intros x H; rewrite <- Heql0; assumption).
        destruct (tpperm P); cbn in HP; cbn.
        * clear Heql0; revert l0 Hin HP; induction l; intros l0 Hin Heq; cbn in Heq.
          -- apply Permutation_Type_nil in Heq.
             destruct l0; inversion Heq; reflexivity.
          -- assert (HP := Heq).
             symmetry in Heq; apply Permutation_Type_vs_cons_inv in Heq.
             destruct Heq as [[l1 l2] Heq]; cbn in Heq.
             rewrite map_map in Heq; decomp_map_inf Heq; subst;
               cbn in Hin, Heq3; symmetry in Heq3; list_simpl.
             assert (a0 = tl2ill x); subst.
             { apply (snd (Hgax a)); [ | assumption ].
               apply Hin; apply in_inf_elt. }
             symmetry; apply Permutation_Type_cons_app.
             symmetry; rewrite <- map_app; apply IHl.
             ++ intros x0 Hin'; apply Hin.
                apply in_inf_app_or in Hin'; destruct Hin' as [Hin' | Hin']; apply in_inf_or_app.
                ** left; assumption.
                ** right; apply in_inf_cons; assumption.
             ++ list_simpl in HP; list_simpl.
                eapply Permutation_Type_cons_app_inv; eassumption.
        * clear Heql0; revert l0 Hin HP; induction l; intros l0 Hin Heq; cbn in Heq.
          -- symmetry in Heq; apply map_eq_nil in Heq; assumption.
          -- destruct l0; inversion Heq.
             assert (forall x, In_inf x l0 -> In_inf x (fst (projT2 (tpgax P) a))) as Hin'
               by (intros x H; apply Hin, in_inf_cons; assumption).
             cbn; rewrite (IHl _ Hin' H1); f_equal.
             symmetry; eapply (snd (Hgax _)); [ | assumption ].
             apply Hin; constructor; reflexivity.
    - exfalso.
      apply PEPermutation_Type_vs_elt_inv in HP as [[l1' l2'] _ Heq'];
        clear - Hgax Heq'; cbn in Heq'.
      apply (f_equal (@rev _)) in Heq'; rewrite rev_involutive in Heq'; list_simpl in Heq'.
      rewrite map_map in Heq'; decomp_map Heq'; subst.
      symmetry in Heq'3.
      apply (fst (fst (Hgax a)) x Heq'3). }
  + eapply ex_ir; cbn; [ | eassumption ].
    refine (snd (tl2tlfrag _) _); [ apply gax_tr | assumption ].
  + eapply ex_ir; cbn; [ | eassumption ].
    refine (fst (tl2tlfrag _) _ _); [ apply gax_tr | assumption ].
- intros Hin.
  apply in_inf_split in Hin as [(l1,l2) Heq].
  decomp_map Heq; symmetry in Heq3.
  eapply N_not_tl2ill; eassumption.
Qed.

Theorem ll_is_tl_cutfree P : tpcut P = false -> easytpgax P -> forall l,
  (forall A, tl P l (Some A)
         -> ll (i2pfrag (t2ipfrag P)) (ill2ll (tl2ill A) ::
                          rev (map dual (map ill2ll (map tl2ill l)))))
* (forall A, 
        ll (i2pfrag (t2ipfrag P)) (ill2ll (tl2ill A) ::
                          rev (map dual (map ill2ll (map tl2ill l))))
        -> tl P l (Some A))
* (tl P l None
        -> ll (i2pfrag (t2ipfrag P)) (ill2ll N ::
                 rev (map dual (map ill2ll (map tl2ill l)))))
* (ll (i2pfrag (t2ipfrag P)) (ill2ll N ::
                 rev (map dual (map ill2ll (map tl2ill l)))) 
        -> tl P l None).
Proof.
intros Hcut Hgax l.
split; [ split; [ split | ] | ]; (try intros A pi); try intros pi.
- apply tl2tlfrag in pi.
  assert (pi' := fst pi _ (eq_refl _)).
  apply ill_to_ll; assumption.
- eapply (@ll_to_ill_nzeropos_cutfree _ _ _ (t2ipfrag P) Hcut
              (easytpgax_easyipgax Hgax)
            (ill2ll (tl2ill A)
              :: rev (map dual (map ill2ll (map tl2ill l))))) in pi ;
    [ | | reflexivity ].
  + apply tlfrag2tl_cutfree in pi; assumption.
  + change (tl2ill A :: map tl2ill l) with (map tl2ill (A :: l)).
    apply forall_Forall_inf.
    intros x Hin.
    apply in_inf_map_inv in Hin as [s0 Heq Hin]; subst.
    apply tl2ill_nz.
- apply tl2tlfrag in pi.
  assert (pi' := snd pi (eq_refl _)).
  apply ill_to_ll; assumption.
- eapply (@ll_to_ill_nzeropos_cutfree _ _ _ (t2ipfrag P) Hcut
           (easytpgax_easyipgax Hgax)
           (ill2ll N :: rev (map dual (map ill2ll (map tl2ill l))))) in pi ;
    [ | | reflexivity ].
  + apply tlfrag2tl_cutfree in pi; assumption.
  + constructor ; [ constructor | ].
    apply forall_Forall_inf.
    intros x Hin.
    apply in_inf_map_inv in Hin as [s0 Heq Hin]; subst.
    apply tl2ill_nz.
Qed.

Theorem ll_is_tl_axfree P : notT (projT1 (tpgax P)) -> forall l,
   (forall A, tl P l (Some A)
           -> ll (i2pfrag (t2ipfrag P)) (ill2ll (tl2ill A) ::
                           rev (map dual (map ill2ll (map tl2ill l)))))
 * (forall A, ll (i2pfrag (t2ipfrag P)) (ill2ll (tl2ill A) ::
                           rev (map dual (map ill2ll (map tl2ill l))))
           -> tl P l (Some A))
 *           (tl P l None
           -> ll (i2pfrag (t2ipfrag P)) (ill2ll N ::
                           rev (map dual (map ill2ll (map tl2ill l)))))
 *           (ll (i2pfrag (t2ipfrag P)) (ill2ll N ::
                          rev (map dual (map ill2ll (map tl2ill l))))
           -> tl P l None).
Proof.
intros Hgax l.
split; [ split; [ split | ] | ]; (try intros A pi); try intros pi.
- apply tl2tlfrag in pi.
  apply ill_to_ll; intuition.
- eapply (@ll_to_ill_nzeropos_axfree _ _ _ (t2ipfrag P) Hgax (ill2ll (tl2ill A)
            :: rev (map dual (map ill2ll (map tl2ill l))))) in pi ;
    [ | | reflexivity ].
  + apply tlfrag2tl_axfree; assumption.
  + change (tl2ill A :: map tl2ill l) with (map tl2ill (A :: l)).
    remember (A :: l) as l0 ; clear.
    induction l0; cbn; constructor; intuition.
    apply tl2ill_nz.
- apply tl2tlfrag in pi.
  apply ill_to_ll; intuition.
- eapply (@ll_to_ill_nzeropos_axfree _ _ _ (t2ipfrag P) Hgax (ill2ll N
            :: rev (map dual (map ill2ll (map tl2ill l))))) in pi ;
    [ | | reflexivity ].
  + apply tlfrag2tl_axfree; assumption.
  + constructor; [ constructor | ].
    clear; induction l; cbn; constructor; auto.
    apply tl2ill_nz.
Qed.

End Atoms.
