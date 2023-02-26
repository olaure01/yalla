(* tl example file for yalla library *)

(** * Example of a concrete use of the yalla library: tensor logic *)

From Coq Require Import CMorphisms.
From OLlibs Require Import funtheory infinite List_more Permutation_Type_more GPermutation_Type.


(** ** 0. load the [ill] library *)

From Yalla Require Import ll_def ill_vs_ll.

Set Implicit Arguments.


Section Atoms.

Context {atom : InfDecType} {preiatom tatom : DecType} {Atoms : TLAtomType atom preiatom tatom}.

(** ** 1. define formulas *)

(** Tensor formulas *)
Inductive tformula :=
| tvar (_ : tatom)
| tone | ttens (_ _ : tformula)
| tneg (_ : tformula)
| tzero | tplus (_ _ : tformula)
| toc (_ : tformula).

Variant tatomic : tformula -> Type :=
| tatomic_var x : tatomic (tvar x).

Inductive tsubform : tformula -> tformula -> Type :=
| tsub_id A : tsubform A A
| tsub_tens_l A B C : tsubform A B -> tsubform A (ttens B C)
| tsub_tens_r A B C : tsubform A B -> tsubform A (ttens C B)
| tsub_neg_l A B : tsubform A B -> tsubform A (tneg B)
| tsub_neg_r A B : tsubform A B -> tsubform A (tneg B)
| tsub_plus_l A B C : tsubform A B -> tsubform A (tplus B C)
| tsub_plus_r A B C : tsubform A B -> tsubform A (tplus C B)
| tsub_oc A B : tsubform A B -> tsubform A (toc B).

Lemma tsub_trans A B C : tsubform A B -> tsubform B C -> tsubform A C.
Proof. intros Hl Hr. induction Hr in A, Hl |- *; try (constructor; apply IHHr); assumption. Qed.

#[export] Instance tsub_po : PreOrder tsubform | 50.
Proof. split; [ intros l; apply tsub_id | intros l1 l2 l3; apply tsub_trans ]. Qed.

(** ** 2. define embedding into [iformula] *)

Lemma TAtom2PreIAtom_inj : injective TAtom2PreIAtom.
Proof. apply bijective_injective, TAtom2PreIAtom_bij. Qed.
Definition i2ac := IAtom2Atom.
Definition i2ac_inj : injective i2ac := section_injective IAtom2Atom_retract.
Definition t2i := fun x => Some (TAtom2PreIAtom x).
Lemma t2i_inj : injective t2i.
Proof. intros x y Heq. apply TAtom2PreIAtom_inj. injection Heq as [=]. assumption. Qed.
Lemma atN_or_t2i x : (atN = x) + { y | x = t2i y }.
Proof.
destruct x as [c|]; [ right | left; reflexivity ].
unfold t2i.
destruct (bijective_surjective TAtom2PreIAtom_bij c) as [y ->].
exists y. reflexivity.
Qed.
Lemma notatN x : atN <> t2i x.
Proof. unfold t2i. intros Heq. discriminate Heq. Qed.
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

Fixpoint tl2ill_inv (A : @iformula preiatom) :=
match A with
| ivar (Some x) => tvar (proj1_sig (sig_of_sig2 (bijective_inverse TAtom2PreIAtom_bij)) x)
| ione => tone
| itens A1 A2 => ttens (tl2ill_inv A1) (tl2ill_inv A2)
| ineg A1 => tneg (tl2ill_inv A1)
| izero => tzero
| iplus A1 A2 => tplus (tl2ill_inv A1) (tl2ill_inv A2)
| ioc A1 => toc (tl2ill_inv A1)
| _ => tone
end.

Lemma tl2ill_section A : tl2ill_inv (tl2ill A) = A.
Proof.
induction A; cbn; rewrite ? IHA, ? IHA1, ? IHA2; try reflexivity.
destruct (bijective_inverse TAtom2PreIAtom_bij) as [f _ ->]. reflexivity.
Qed.

Lemma tl2ill_dec A : {B | A = tl2ill B} + (A = N) + ((forall B, A <> tl2ill B) * (A <> N)).
Proof.
destruct (@eq_dt_dec iformulas_dectype A (tl2ill (tl2ill_inv A))) as [-> | Hneq];
  [ | destruct (@eq_dt_dec iformulas_dectype A N) as [-> | HneqN] ].
- left. left. exists (tl2ill_inv A). reflexivity.
- left. right. reflexivity.
- right. split; [ | assumption ].
  intros B ->.
  apply Hneq. rewrite tl2ill_section. reflexivity.
Qed.

Lemma tl2ill_inj : injective tl2ill.
Proof. exact (section_injective tl2ill_section). Qed.

Lemma tl2ll_inj : injective (fun x => ill2ll (tl2ill x)).
Proof.
intro A. induction A; intros [] Heq;
 try (now inversion Heq; try apply IHA in H0; try apply IHA1 in H0; try apply IHA2 in H1; subst).
- cbn in Heq.
  f_equal. apply t2i_inj, i2ac_inj.
  unfold t2i, i2ac in Heq. injection Heq as [=].
  apply i2ac_inj, t2i_inj in H as ->. reflexivity.
- inversion Heq.
  apply formulas.dual_inj in H0.
  apply IHA in H0 as ->. reflexivity.
Qed.

Lemma N_not_tl2ill A : N <> tl2ill A.
Proof. intros Heq. destruct A; discriminate Heq. Qed.

Lemma tl2ill_nz A : nonzerospos (tl2ill A).
Proof. induction A; cbn; constructor; assumption. Qed.

Lemma tl2ill_map_ioc l : map tl2ill (map toc l) = map ioc (map tl2ill l).
Proof. induction l as [ | ? l IHl]; [ | cbn; rewrite IHl ]; reflexivity. Qed.

Lemma tl2ill_map_ioc_inv l1 l2 : map ioc l1 = map tl2ill l2 ->
  { l2' | l2 = map toc l2' & l1 = map tl2ill l2' }.
Proof.
induction l1 in l2 |- *; intros Heq; destruct l2; inversion Heq.
- exists nil; reflexivity.
- apply IHl1 in H1 as [l2' -> ->].
  destruct t; inversion Heq.
  exists (t :: l2'); reflexivity.
Qed.


(** ** 3. define proofs *)

Definition NoTAxioms := (existT (fun x => x -> list tformula * option tformula) _ Empty_fun).

Record tpfrag := mk_tpfrag {
  tpcut : tformula -> bool;
  tpgax : { tptypgax : Type & tptypgax -> list tformula * option tformula };
  tpperm : bool }.

Definition tpcut_none (A : tformula) := false.

Definition no_tcut P := forall C, tpcut P C = false.

Definition no_tax P := notT (projT1 (tpgax P)).

Definition atomic_tax P := forall a,
 (option_testT tatomic (snd (projT2 (tpgax P) a))) * (Forall_inf tatomic (fst (projT2 (tpgax P) a))).

Definition le_tpfrag P Q :=
  ((forall A, Bool.le (tpcut P A) (tpcut Q A))
 * (forall a, { b | projT2 (tpgax P) a = projT2 (tpgax Q) b })
 * (Bool.le (tpperm P) (tpperm Q)))%type.

Lemma le_tpfrag_trans P Q R : le_tpfrag P Q -> le_tpfrag Q R -> le_tpfrag P R.
Proof.
intros [[Hc1 Ha1] Hp1] [[Hc2 Ha2] Hp2].
repeat split; try (eapply BoolOrder.le_trans; eassumption).
- intros A.
  apply BoolOrder.le_trans with (tpcut Q A); [ apply Hc1 | apply Hc2 ].
- intros a.
  destruct (Ha1 a) as [b ->], (Ha2 b) as [c ->].
  exists c. reflexivity.
Qed.

Definition cutupd_tpfrag P b := mk_tpfrag b (tpgax P) (tpperm P).

Definition axupd_tpfrag P G := mk_tpfrag (tpcut P) G (tpperm P).

Definition cutrm_tpfrag P := cutupd_tpfrag P tpcut_none.

Lemma notcut_cutrm P : no_tcut (cutrm_tpfrag P).
Proof. intro. reflexivity. Qed.

Lemma cutrm_tpfrag_le P : le_tpfrag (cutrm_tpfrag P) P.
Proof. repeat split; try reflexivity. intros a. exists a. reflexivity. Qed.

Inductive tl P : list tformula -> option tformula -> Type :=
| ax_tr X : tl P (tvar X :: nil) (Some (tvar X))
| ex_tr l1 l2 A : tl P l1 A -> PEPermutation_Type (tpperm P) l1 l2 -> tl P l2 A
| ex_oc_tr l1 lw lw' l2 A :
    tl P (l1 ++ map toc lw ++ l2) A -> Permutation_Type lw lw' -> tl P (l1 ++ map toc lw' ++ l2) A
| one_trr : tl P nil (Some tone)
| one_tlr l1 l2 A : tl P (l1 ++ l2) A -> tl P (l1 ++ tone :: l2) A
| tens_trr A B l1 l2 : tl P l1 (Some A) -> tl P l2 (Some B) -> tl P (l1 ++ l2) (Some (ttens A B))
| tens_tlr A B l1 l2 C : tl P (l1 ++ A :: B :: l2) C -> tl P (l1 ++ ttens A B :: l2) C
| neg_trr A l : tl P (A :: l) None -> tl P l (Some (tneg A))
| neg_tlr A l : tl P l (Some A) -> tl P (l ++ tneg A :: nil) None
| zero_tlr l1 l2 C : tl P (l1 ++ tzero :: l2) C
| plus_trr1 A B l : tl P l (Some A) -> tl P l (Some (tplus A B))
| plus_trr2 A B l : tl P l (Some A) -> tl P l (Some (tplus B A))
| plus_tlr A B l1 l2 C : tl P (l1 ++ A :: l2) C -> tl P (l1 ++ B :: l2) C -> tl P (l1 ++ tplus A B :: l2) C
| oc_trr A l : tl P (map toc l) (Some A) -> tl P (map toc l) (Some (toc A))
| de_tlr A l1 l2 C : tl P (l1 ++ A :: l2) C -> tl P (l1 ++ toc A :: l2) C
| wk_tlr A l1 l2 C : tl P (l1 ++ l2) C -> tl P (l1 ++ toc A :: l2) C
| co_tlr A l1 l2 C : tl P (l1 ++ toc A :: toc A :: l2) C -> tl P (l1 ++ toc A :: l2) C
| cut_tr A (f : tpcut P A = true) l0 l1 l2 C :
    tl P l0 (Some A) -> tl P (l1 ++ A :: l2) C -> tl P (l1 ++ l0 ++ l2) C
| gax_tr a : tl P (fst (projT2 (tpgax P) a)) (snd (projT2 (tpgax P) a)).

#[export] Instance tl_perm P Pi :
  Proper ((PEPermutation_Type (tpperm P)) ==> arrow) (fun l => tl P l Pi) | 100.
Proof. intros l1 l2 HP pi. apply ex_tr with l1; assumption. Qed.

Lemma stronger_tpfrag P Q (Hle : le_tpfrag P Q) l A : tl P l A -> tl Q l A.
Proof.
intros pi.
destruct Hle as [[Hcut Hgax] Hp].
induction pi; (try now constructor).
- apply ex_tr with l1; [ assumption | ].
  hyps_GPermutation_Type_unfold; unfold PEPermutation_Type.
  destruct (tpperm P), (tpperm Q); cbn in Hp; try inversion Hp; subst;
    [ assumption | | ]; reflexivity.
- eapply ex_oc_tr; [ apply IHpi | assumption ].
- specialize (Hcut A). rewrite f in Hcut. apply (cut_tr Hcut); assumption.
- destruct (Hgax a) as [b ->]. apply gax_tr.
Qed.


(** ** 4. characterize corresponding [ill] fragment *)

(*
Definition tl_fragment A :=
match (tl2ill_dec A) with
| inl _ => True
| inr _ => False
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
  ipcut := fun A => match tl2ill_dec A with
                    | inl (inl (exist _ B _)) => tpcut P B
                    | _ => false
                    end;
  ipgax := existT (fun x => x -> list iformula * iformula) (projT1 (tpgax P))
             (fun a => (map tl2ill (fst (projT2 (tpgax P) a)),
                        match snd (projT2 (tpgax P) a) with
                        | Some C => tl2ill C
                        | None   => N
                        end));
  ipperm := tpperm P |}.

Lemma ipcut_t2ipfrag P A : ipcut (t2ipfrag P) (tl2ill A) = tpcut P A.
Proof.
cbn. destruct (tl2ill_dec (tl2ill A)) as [[[B ->%tl2ill_inj]|Heq]|[Hneq _]].
- reflexivity.
- exfalso. symmetry in Heq. exact (N_not_tl2ill _ Heq).
- exfalso. apply (Hneq A). reflexivity.
Qed.

Lemma notcut_t2ipfrag P : no_tcut P -> no_icut (t2ipfrag P).
Proof.
intros Hcut A. cbn. destruct (tl2ill_dec A) as [[[B ->]|_]|_]; [ apply Hcut | reflexivity | reflexivity ].
Qed.

Lemma cutrm_t2ipfrag_le P : le_ipfrag (cutrm_ipfrag (t2ipfrag P)) (t2ipfrag (cutrm_tpfrag P)).
Proof. repeat split; [ intros a; exists a | ]; reflexivity. Qed.


(** ** 5. prove equivalence of proof predicates *)

Lemma tl2tlfrag P l C : tl P l C ->
   (forall D, C = Some D -> ill (t2ipfrag P) (map tl2ill l) (tl2ill D))
 * (C = None -> ill (t2ipfrag P) (map tl2ill l) N).
Proof.
intros pi. induction pi;
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
  (try now (constructor; auto));
  try now (destruct D; inversion HeqC; subst; constructor; auto).
- eapply ex_ir.
  + apply (piS _ HeqC).
  + apply PEPermutation_Type_map. assumption.
- eapply ex_ir.
  + apply (piE HeqC).
  + apply PEPermutation_Type_map. assumption.
- rewrite tl2ill_map_ioc.
  apply (Permutation_Type_map tl2ill) in p.
  eapply ex_oc_ir; [ | eassumption ].
  rewrite <- tl2ill_map_ioc; apply piS; assumption.
- rewrite tl2ill_map_ioc.
  apply (Permutation_Type_map tl2ill) in p.
  eapply ex_oc_ir; [ | eassumption ].
  rewrite <- tl2ill_map_ioc. apply piE, HeqC.
- destruct D; inversion HeqC. subst.
  rewrite tl2ill_map_ioc. cbn. apply oc_irr.
  rewrite <- tl2ill_map_ioc. apply piS. reflexivity.
- rewrite <- ipcut_t2ipfrag in f.
  apply (cut_ir (tl2ill A) f (piS1 _ eq_refl) (piS2 _ HeqC)).
- rewrite <- ipcut_t2ipfrag in f.
  apply (cut_ir (tl2ill A) f (piS1 _ eq_refl) (piE2 HeqC)).
- assert (pi := @gax_ir _ (t2ipfrag P) a).
  cbn in pi. rewrite HeqC in pi. assumption.
- assert (pi := @gax_ir _ (t2ipfrag P) a).
  cbn in pi. rewrite HeqC in pi. assumption.
Qed.

Lemma tlfrag2tl P l :
   (forall A, ill (t2ipfrag P) (map tl2ill l) (tl2ill A) -> tl P l (Some A))
 * (ill (t2ipfrag P) (map tl2ill l) N -> tl P l None).
Proof.
enough
   (forall l A, ill (t2ipfrag P) l A -> (forall l0 A0, l = map tl2ill l0 -> A = tl2ill A0 -> tl P l0 (Some A0))
 * (forall l0, l = map tl2ill l0 -> A = N -> tl P l0 None)) as HI
  by (split; [ intros A | ]; intros pi; apply (HI _ _ pi); reflexivity).
clear l. intros l A pi.
induction pi;
  (split; [ intros l'' A'' Heql HeqA | intros l'' Heql HeqN ]); subst;
  try (symmetry in Heql; decomp_map_inf Heql; destruct x; discriminate Heql3);
  try discriminate HeqN;
  try (symmetry in Heql; decomp_map_inf Heql; subst;
       destruct x; inversion Heql3; subst;
       constructor; apply IHpi; list_simpl; reflexivity);
  try (destruct A''; inversion HeqA; subst; constructor; apply IHpi; reflexivity).
- destruct l''; inversion Heql; destruct l''; inversion Heql.
  destruct A''; inversion HeqA; destruct t; inversion H0; subst.
  apply t2i_inj in H4 as ->. apply ax_tr.
- exfalso.
  rewrite HeqN in Heql.
  destruct l''; inversion Heql.
  destruct t; discriminate H0.
- apply PEPermutation_Type_map_inv in p.
  destruct p as [l0 Heq HP]; subst.
  eapply ex_tr.
  + apply IHpi; reflexivity.
  + symmetry. assumption.
- apply PEPermutation_Type_map_inv in p as [l0 -> HP]. symmetry in HP.
  eapply ex_tr; [ apply IHpi; reflexivity | assumption ].
- symmetry in Heql. decomp_map_inf Heql. subst. symmetry in Heql3.
  cbn in Heql3. apply tl2ill_map_ioc_inv in Heql3 as [l -> ->].
  apply Permutation_Type_map_inv in p as [l' -> HP]. symmetry in HP.
  eapply ex_oc_tr; [ | eassumption ].
  apply IHpi; [ rewrite <- tl2ill_map_ioc, <- ? map_app | ]; reflexivity.
- symmetry in Heql. decomp_map_inf Heql. subst. symmetry in Heql3.
  cbn in Heql3. apply tl2ill_map_ioc_inv in Heql3 as [l -> ->].
  apply Permutation_Type_map_inv in p as [l' -> HP].
  symmetry in HP.
  eapply ex_oc_tr; [ | eassumption ].
  apply IHpi; [ rewrite <- tl2ill_map_ioc, <- ? map_app | ]; reflexivity.
- destruct l''; inversion Heql.
  destruct A''; inversion HeqA; subst.
  apply one_trr.
- symmetry in Heql. decomp_map_inf Heql. destruct A''; inversion HeqA; subst.
  apply tens_trr; [ apply IHpi1 | apply IHpi2 ]; reflexivity.
- symmetry in Heql. decomp_map_inf Heql; subst.
  destruct x; discriminate Heql1.
- symmetry in Heql. decomp_map_inf Heql. destruct x; discriminate Heql2.
- symmetry in Heql. decomp_map_inf Heql. destruct x; discriminate Heql2.
- symmetry in Heql. decomp_map_inf Heql.
  destruct x; inversion Heql3; subst.
  destruct l3; inversion Heql4.
  apply neg_tlr, IHpi; reflexivity.
- symmetry in Heql. decomp_map_inf Heql.
  destruct x; inversion Heql3; subst.
  apply plus_tlr; [ apply IHpi1 | apply IHpi2 ]; list_simpl; reflexivity.
- symmetry in Heql. decomp_map_inf Heql.
  destruct x; inversion Heql3; subst.
  apply plus_tlr; [ apply IHpi1 | apply IHpi2 ]; list_simpl; reflexivity.
- apply tl2ill_map_ioc_inv in Heql.
  destruct Heql as [l0' Heq Heq']; subst.
  destruct A'' ; inversion HeqA; subst.
  apply oc_trr, IHpi; [ rewrite tl2ill_map_ioc | ]; reflexivity.
- cbn in f. destruct (tl2ill_dec A) as [[[B ->]|]|]; [ | discriminate f | discriminate f].
  symmetry in Heql. decomp_map_inf Heql. subst.
  eapply (cut_tr f).
  + apply IHpi1; reflexivity.
  + apply IHpi2; list_simpl; reflexivity.
- cbn in f. destruct (tl2ill_dec A) as [[[B ->]|]|]; [ | discriminate f | discriminate f].
  symmetry in Heql. decomp_map_inf Heql. subst.
  eapply (cut_tr f).
  + apply IHpi1; reflexivity.
  + apply IHpi2; list_simpl; reflexivity.
- cbn in Heql; cbn in HeqA.
  case_eq (snd (projT2 (tpgax P) a)).
  + intros A Heq. rewrite Heq in HeqA.
    apply tl2ill_inj in HeqA; subst.
    rewrite <- Heq.
    apply map_injective in Heql; [ | apply tl2ill_inj ]; subst.
    apply gax_tr.
  + intros Heq. exfalso. rewrite Heq in HeqA. destruct A''; inversion HeqA.
- cbn in Heql. cbn in HeqN.
  case_eq (snd (projT2 (tpgax P) a)).
  + intros A Heq. exfalso. rewrite Heq in HeqN. destruct A; discriminate HeqN.
  + intros Heq. rewrite Heq in HeqN. rewrite <- Heq.
    apply map_injective in Heql as <-; [ | apply tl2ill_inj ].
    apply gax_tr.
Qed.

Lemma tlfrag2tl_axfree P (Hgax : no_tax P) l :
   (forall A, ill (t2ipfrag P) (map tl2ill l) (tl2ill A) -> tl P l (Some A))
 * (ill (t2ipfrag P) (map tl2ill l) N -> tl P l None).
Proof.
split; [ intros A | ]; intros pi.
- apply cut_admissible_ill in pi; (try now (intros a; exfalso; apply (Hgax a))).
  apply (stronger_ipfrag (cutrm_t2ipfrag_le P)), tlfrag2tl in pi.
  apply (@stronger_tpfrag (cutrm_tpfrag P)); [ | assumption ].
  repeat split; [ | reflexivity ].
  intros a. destruct (Hgax a).
- apply cut_admissible_ill in pi; (try now (intros a; exfalso; apply (Hgax a))).
  apply (stronger_ipfrag (cutrm_t2ipfrag_le P)), tlfrag2tl in pi.
  apply (@stronger_tpfrag (cutrm_tpfrag P)); [ | assumption ].
  repeat split; try reflexivity.
  intros a. exists a. reflexivity.
Qed.


(** ** 6. import properties *)

(** *** axiom expansion *)

Lemma ax_gen_r P A : tl P (A :: nil) (Some A).
Proof. apply (stronger_tpfrag (cutrm_tpfrag_le P)), tlfrag2tl, ax_exp_ill. Qed.

(** *** cut admissibility *)

Lemma cut_tl_r_axfree P (Hgax : no_tax P) A l0 l1 l2 C :
  tl P l0 (Some A) -> tl P (l1 ++ A :: l2) C -> tl P (l1 ++ l0 ++ l2) C.
Proof.
intros pi1 pi2.
destruct (tl2tlfrag pi1) as [pi1' _].
assert (pi1'' := pi1' _ eq_refl).
destruct (tl2tlfrag pi2) as [pi2' pi2''].
destruct (tpcut P A) eqn:Hcut.
- eapply cut_tr; eassumption.
- case_eq C.
  + intros D HeqD.
    apply tlfrag2tl.
    assert (pi := pi2' _ HeqD).
    list_simpl in pi. list_simpl. eapply cut_ir_axfree; eassumption.
  + intros HeqD.
    apply tlfrag2tl.
    assert (pi := pi2'' HeqD).
    list_simpl in pi. rewrite <- ? map_app in pi. list_simpl. eapply cut_ir_axfree; eassumption.
Qed.

Lemma cut_admissible_tl_axfree P (Hgax : no_tax P) l Pi : tl P l Pi -> tl (cutrm_tpfrag P) l Pi.
Proof.
intros pi. induction pi; try (econstructor; eassumption).
- eapply cut_tl_r_axfree; eassumption.
- contradiction (Hgax a).
Qed.

(** *** conservativity with respect to [ll] *)

Definition easytpgax P := forall a,
  (forall D, notT (ill2ll (snd (projT2 (ipgax (t2ipfrag P)) a)) = dual (ill2ll D)))
* (forall A C, snd (projT2 (tpgax P) a) = Some A -> ill2ll C = ill2ll (tl2ill A) -> C = tl2ill A)
* (forall A C, In_inf A (fst (projT2 (tpgax P) a)) -> ill2ll C = ill2ll (tl2ill A) -> C = tl2ill A).

Lemma tatomic_easytpgax P : atomic_tax P -> easytpgax P.
Proof.
intros Hgax a. split; [ split | ].
- destruct (Hgax a) as [Hat _].
  cbn. intros D Heq.
  destruct (snd (projT2 (tpgax P) a)).
  + destruct t; inversion Hat; subst.
    destruct D; discriminate Heq.
  + destruct D; discriminate Heq.
- destruct (Hgax a) as [Hat _].
  intros A C Heq1 Heq2.
  destruct (snd (projT2 (tpgax P) a)); inversion Heq1; subst.
  destruct A; inversion Hat; subst.
  destruct C; inversion Heq2.
  apply i2ac_inj in H0 as ->. reflexivity.
- destruct (Hgax a) as [_ Hat].
  intros A C Hin Heq.
  eapply Forall_inf_forall in Hat; try eassumption.
  destruct A; inversion Hat; subst.
  destruct C; inversion Heq.
  apply i2ac_inj in H0 as ->. reflexivity.
Qed.

Lemma easytpgax_easyipgax P : easytpgax P -> easyipgax_nzeropos (t2ipfrag P).
Proof.
intros Hgax.
split; [ split | ]; cbn.
- intros D Heq. exfalso.
  remember (snd (projT2 (tpgax P) a)) as C eqn:HeqC; destruct C.
  + assert (Hgaxa := fst (fst (Hgax a)) D).
    apply Hgaxa. cbn.
    rewrite <- Heq, <- HeqC. reflexivity.
  + destruct D; inversion Heq.
- intros l C HP.
  assert (prod (sum (snd (projT2 (tpgax P) a) = None /\ C = N)
                    { C' | snd (projT2 (tpgax P) a) = Some C' & C = tl2ill C' })
               (PEPermutation_Type (tpperm P) (map tl2ill (fst (projT2 (tpgax P) a))) l))
    as [[[HeqNone HeqN] | [C' Heq1 Heqé]] HPE]; subst.
  { apply PCPermutation_Type_vs_cons_inv in HP.
    destruct HP as [[l1 l2] HP Heq]; cbn in Heq, HP.
    destruct l1; inversion Heq; subst.
    - split; [ clear - Hgax H0 | clear - Hgax HP ].
      + assert (Hgaxa := snd (fst (Hgax a))).
        destruct (snd (projT2 (tpgax P) a)).
        * specialize Hgaxa with t C.
          right; exists t; [ reflexivity | ].
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
  decomp_map Heq. symmetry in Heq3.
  eapply N_not_tl2ill. exact Heq3.
Qed.

Theorem ll_is_tl_cutfree P (Hcut : no_tcut P) (Hgax : easytpgax P) l :
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
split; [ split; [ split | ] | ]; (try intros A pi); try intros pi.
- apply tl2tlfrag in pi.
  assert (pi' := fst pi _ (eq_refl _)).
  apply ill_to_ll; assumption.
- eapply (@ll_to_ill_nzeropos_cutfree _ _ _ (t2ipfrag P) (notcut_t2ipfrag Hcut)
              (easytpgax_easyipgax Hgax)
            (ill2ll (tl2ill A)
              :: rev (map dual (map ill2ll (map tl2ill l))))) in pi ;
    [ | | reflexivity ].
  + exact (fst (tlfrag2tl _ _) _ pi).
  + change (tl2ill A :: map tl2ill l) with (map tl2ill (A :: l)).
    apply forall_Forall_inf.
    intros x Hin.
    apply in_inf_map_inv in Hin as [s0 <- Hin].
    apply tl2ill_nz.
- apply tl2tlfrag in pi.
  assert (pi' := snd pi (eq_refl _)).
  apply ill_to_ll; assumption.
- eapply (@ll_to_ill_nzeropos_cutfree _ _ _ (t2ipfrag P) (notcut_t2ipfrag Hcut)
           (easytpgax_easyipgax Hgax)
           (ill2ll N :: rev (map dual (map ill2ll (map tl2ill l))))) in pi ;
    [ | | reflexivity ].
  + exact (snd (tlfrag2tl _ _) pi).
  + constructor ; [ constructor | ].
    apply forall_Forall_inf.
    intros x [s0 <- _]%in_inf_map_inv.
    apply tl2ill_nz.
Qed.

Theorem ll_is_tl_axfree P (Hgax : no_tax P) l :
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
split; [ split; [ split | ] | ]; (try intros A pi); try intros pi.
- apply tl2tlfrag in pi.
  apply ill_to_ll, pi. reflexivity.
- apply ll_to_ill_nzeropos_axfree in pi.
  + apply tlfrag2tl_axfree; assumption.
  + intros a. destruct (Hgax a).
  + change (tl2ill A :: map tl2ill l) with (map tl2ill (A :: l)).
    remember (A :: l) as l0. clear.
    induction l0; cbn; constructor; [ apply tl2ill_nz | assumption ].
- apply tl2tlfrag in pi.
  apply ill_to_ll, pi. reflexivity.
- apply ll_to_ill_nzeropos_axfree in pi.
  + apply tlfrag2tl_axfree; assumption.
  + intros a. destruct (Hgax a).
  + constructor; [ constructor | clear ].
    induction l; cbn; constructor; [ apply tl2ill_nz | assumption ].
Qed.

End Atoms.
