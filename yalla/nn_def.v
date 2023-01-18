(* nn_def library for yalla *)

(** * Parametric negative translation from [ll] into [ill]. *)

From OLlibs Require Import funtheory infinite List_more Dependent_Forall_Type Permutation_Type GPermutation_Type.
From Yalla Require Import subs isubs.
From Yalla Require Export ill_vs_ll.

Set Implicit Arguments.


Section Atoms.

Context {atom : DecType} {preiatom : InfDecType} {Atoms : Atom2IAtomType_self atom preiatom}.

(** ** Basic ingredients for links with [ill] *)

Notation Na := (proj1_sig (projT3 Atom_self_inj)).
Notation atom2atom := (projT1 (sigT_of_sigT2 Atom_self_inj)).
Notation atom2atom_inj := (projT2 (sigT_of_sigT2 Atom_self_inj)).

Definition atom_inf := AtomType_self_InfDecType atom (@Atom2IAtom_Atom_self atom preiatom _).

Notation formula := (@formula atom_inf).
Notation iformula := (@iformula preiatom).

Lemma Atom2PreIAtom_inj : injective Atom2PreIAtom.
Proof. apply bijective_injective, Atom2PreIAtom_bij. Qed.
Notation p2a := (proj1_sig (sig_of_sig2 (bijective_inverse Atom2PreIAtom_bij))).
Definition i2a a :=
  match a with
  | None => Na
  | Some x => p2a x
  end.
Definition a2i := fun a => Some (Atom2PreIAtom a).
Lemma a2a_i : retract i2a a2i.
Proof. intros a. unfold i2a, a2i. apply (proj3_sig (bijective_inverse Atom2PreIAtom_bij)). Qed.
Lemma i2i_not_atN a : a <> atN -> a2i (i2a a) = a.
Proof.
intros Heq. unfold i2a, a2i.
destruct a; [ | contradiction Heq; reflexivity ].
f_equal. destruct (bijective_inverse Atom2PreIAtom_bij). trivial.
Qed.
Lemma i2a_inv_atN [i] : i2a i = i2a atN -> {i = atN} + {i = a2i (i2a atN)}.
Proof.
intros Heq. destruct i.
- right.
  enough (a2i (i2a (Some c)) = Some c) as Heqc by (rewrite <- Heqc; f_equal; assumption).
  apply i2i_not_atN. intros [=].
- left. reflexivity.
Qed.
Lemma ateq_a2i (a b : atom_inf) : ateq a b = true <-> iateq (a2i a) (a2i b) = true.
Proof.
unfold ateq, iateq. rewrite ? eqb_eq. split; intros Heq.
- subst. reflexivity.
- apply section_injective with (g := i2a) in Heq; [ assumption | ].
  exact a2a_i.
Qed.
Lemma i2a_fin a : { l & forall i, iffT (a = i2a i) (In_inf i l) }.
Proof.
destruct (eq_dt_dec a Na) as [ -> | Hneq ].
- exists (atN :: a2i (i2a atN) :: nil). intros i. split.
  + cbn. intros ->. destruct i.
    * right. left. rewrite i2i_not_atN; [ reflexivity | intros [=] ].
    * left. reflexivity.
  + intros [<- | [<- | []]]; rewrite ? a2a_i; reflexivity.
- exists (a2i a :: nil). intros i. split.
  + intros ->. destruct i.
    * left. rewrite i2i_not_atN; [ reflexivity | intros [=] ].
    * contradiction Hneq. reflexivity.
  + intros [<-|[]]. rewrite a2a_i. reflexivity.
Qed.

Definition i2ac a :=
  match a with
  | None => Na
  | Some x => atom2atom (p2a x)
  end.
Lemma i2ac_inj : injective i2ac.
Proof.
intros a b. destruct a, b; intros Heq; inversion Heq as [Heq']; subst.
- f_equal.
  apply atom2atom_inj in Heq'.
  apply (section_injective (proj2_sig (sig_of_sig2 ((bijective_inverse Atom2PreIAtom_bij))))).
  assumption.
- exfalso. symmetry in Heq'. apply (proj2_sig (projT3 Atom_self_inj)) in Heq' as [].
- exfalso. apply (proj2_sig (projT3 Atom_self_inj)) in Heq' as [].
- reflexivity.
Qed.

Definition iatom2atom : IAtom2AtomType atom_inf preiatom := i2a.
Definition iatom2atom_fin : IAtom2AtomType_fin atom_inf preiatom := {|
  IAtom2Atom_fin_base := iatom2atom;
  IAtom2Atom_fin := i2a_fin |}.
Definition unill := @ill2ll _ _ iatom2atom_fin.


(** ** The translation *)

Section RTranslation.

(** We fix the parameter [R] of the translation. *)

Variable R : iformula.
Definition negR A := ilmap A R.

Lemma negR_irr P A l : ill P (A :: l) R -> ill P l (negR A).
Proof. intros pi. apply lmap_irr. assumption. Qed.

Lemma negR_ilr P (Hperm : ipperm P = true) (HR : ill P (R :: nil) R) A l : ill P l A -> ill P (negR A :: l) R.
Proof.
intros pi.
rewrite <- (app_nil_r _), <- app_comm_cons.
eapply ex_ir; [ | symmetry; rewrite Hperm; apply Permutation_Type_middle ].
rewrite <- (app_nil_l _).
apply lmap_ilr; assumption.
Qed.

(** Definition of the translation of formulas *)
Fixpoint trans A :=
match A with
| var X     => negR (ivar (a2i X))
| covar X   => ivar (a2i X)
| one       => negR ione
| bot       => ione
| tens A B  => negR (itens (negR (trans A)) (negR (trans B)))
| parr A B  => itens (trans B) (trans A)
| zero      => negR izero
| top       => izero
| aplus A B => negR (iplus (negR (trans A)) (negR (trans B)))
| awith A B => iplus (trans A) (trans B)
| oc A      => negR (ioc (negR (trans A)))
| wn A      => ioc (negR (negR (trans A)))
end.

Lemma trans_inj : injective trans.
Proof.
intros a. induction a; intros b Heq; destruct b; inversion Heq;
  (try apply IHa in H0 as ->);
  (try apply IHa1 in H0 as ->);
  (try apply IHa2 in H1 as ->); try reflexivity.
- f_equal. apply Atom2PreIAtom_inj. assumption.
- f_equal. apply Atom2PreIAtom_inj. assumption.
- apply IHa1 in H1 as ->. apply IHa2 in H0 as ->. reflexivity.
Qed.

Lemma trans_wn l : map trans (map wn l) = map ioc (map (fun x => (negR (negR (trans x)))) l).
Proof. induction l as [ | a l IHl ]; [ | cbn; rewrite IHl ]; reflexivity. Qed.

Lemma neg_tens_propag P (Hperm : ipperm P = true) (Hcut : full_icut P) A1 A2 B1 B2 :
  ill P (A1 :: negR A2 :: nil) R -> ill P (B1 :: negR B2 :: nil) R ->
  ill P (itens A1 B1 :: negR (itens A2 B2) :: nil) R.
Proof.
intros pi1 pi2.
cons2app. rewrite <- (app_nil_l _).
apply (cut_ir (itens (negR (negR A2)) (negR (negR B2))) (Hcut _)).
- rewrite <- (app_nil_l _).
  apply tens_ilr.
  list_simpl. cons2app. apply tens_irr; apply lmap_irr.
  + eapply ex_ir; [ apply pi1 | rewrite Hperm; apply Permutation_Type_swap ].
  + eapply ex_ir; [ apply pi2 | rewrite Hperm; apply Permutation_Type_swap ].
- list_simpl. rewrite <- (app_nil_l _).
  apply tens_ilr.
  list_simpl.
  rewrite <- (app_nil_l (negR (itens _ _) :: _)), 2 app_comm_cons, <- (app_nil_l _).
  apply negR_ilr; [ assumption | | ].
  + apply ax_exp_ill.
  + apply negR_irr.
    eapply ex_ir; [ | rewrite Hperm; apply Permutation_Type_swap ].
    apply negR_ilr; [ assumption | | ].
    * apply ax_exp_ill.
    * apply negR_irr.
      cons2app. rewrite app_assoc.
      eapply ex_ir; [ | rewrite Hperm; apply Permutation_Type_middle ].
      list_simpl. apply negR_ilr; [ assumption | | ].
      -- apply ax_exp_ill.
      -- eapply ex_ir; [ | rewrite Hperm; apply Permutation_Type_swap ].
         cons2app. apply tens_irr; apply ax_exp_ill.
Qed.

Lemma neg_plus_propag P (Hperm : ipperm P = true) (Hcut : full_icut P) A1 A2 B1 B2 :
  ill P (A1 :: negR A2 :: nil) R -> ill P (B1 :: negR B2 :: nil) R ->
  ill P (iplus A1 B1 :: negR (iplus A2 B2) :: nil) R.
Proof.
intros pi1 pi2.
cons2app. rewrite <- (app_nil_l _).
apply (cut_ir (iplus (negR (negR A2)) (negR (negR B2))) (Hcut _)).
- rewrite <- (app_nil_l _). apply plus_ilr.
  + list_simpl. apply plus_irr1, negR_irr.
    eapply ex_ir; [ | rewrite Hperm; apply Permutation_Type_swap ]; assumption.
  + list_simpl. apply plus_irr2, negR_irr.
    eapply ex_ir; [ | rewrite Hperm; apply Permutation_Type_swap ]; assumption.
- list_simpl. rewrite <- (app_nil_l _).
  apply plus_ilr.
  + list_simpl. apply negR_ilr; [ assumption | | ].
    * apply ax_exp_ill.
    * apply negR_irr.
      eapply ex_ir; [ | rewrite Hperm; apply Permutation_Type_swap ].
      apply negR_ilr; [ assumption | | ].
      -- apply ax_exp_ill.
      -- apply plus_irr1, ax_exp_ill.
  + list_simpl. apply negR_ilr; [ assumption | | ].
    * apply ax_exp_ill.
    * apply negR_irr.
      eapply ex_ir; [ | rewrite Hperm; apply Permutation_Type_swap ].
      apply negR_ilr; [ assumption | | ].
      -- apply ax_exp_ill.
      -- apply plus_irr2, ax_exp_ill.
Qed.

Lemma trans_dual P (Hperm : ipperm P = true) (Hcut : full_icut P) A :
  ill P (negR (trans A) :: negR (trans (dual A)) :: nil) R.
Proof.
induction A; cbn.
- apply negR_ilr; [ assumption | | ]; apply ax_exp_ill.
- eapply ex_ir; [ | rewrite Hperm; apply Permutation_Type_swap ].
  apply negR_ilr; [ assumption | | ]; apply ax_exp_ill.
- apply negR_ilr; [ assumption | | ]; apply ax_exp_ill.
- eapply ex_ir; [ | rewrite Hperm; apply Permutation_Type_swap ].
  apply negR_ilr; [ assumption | | ]; apply ax_exp_ill.
- apply (neg_tens_propag Hperm Hcut IHA1) in IHA2.
  apply negR_ilr; [ assumption | apply ax_exp_ill | ].
  apply negR_irr.
  cons2app. rewrite <- (app_nil_l _).
  eapply cut_ir; [ exact (Hcut _) | | apply IHA2 ].
  apply ax_exp_ill.
- eapply ex_ir in IHA1; [ | rewrite Hperm; apply Permutation_Type_swap ].
  eapply ex_ir in IHA2; [ | rewrite Hperm; apply Permutation_Type_swap ].
  apply (neg_tens_propag Hperm Hcut IHA2) in IHA1.
  eapply ex_ir; [ | rewrite Hperm; apply Permutation_Type_swap ].
  apply negR_ilr; [ assumption | apply ax_exp_ill | ].
  apply negR_irr.
  cons2app. rewrite <- (app_nil_l _).
  eapply cut_ir; [ exact (Hcut _) | | apply IHA1 ].
  apply ax_exp_ill.
- apply negR_ilr; [ assumption | | ]; apply ax_exp_ill.
- eapply ex_ir; [ | rewrite Hperm; apply Permutation_Type_swap ].
  apply negR_ilr; [ assumption | | ]; apply ax_exp_ill.
- apply (neg_plus_propag Hperm Hcut IHA1) in IHA2.
  apply negR_ilr; [ assumption | apply ax_exp_ill | ].
  apply negR_irr.
  cons2app. rewrite <- (app_nil_l _).
  eapply cut_ir; [ exact (Hcut _) | | apply IHA2 ].
  apply ax_exp_ill.
- eapply ex_ir in IHA1; [ | rewrite Hperm; apply Permutation_Type_swap ].
  eapply ex_ir in IHA2; [ | rewrite Hperm; apply Permutation_Type_swap ].
  apply (neg_plus_propag Hperm Hcut IHA1) in IHA2.
  eapply ex_ir; [ | rewrite Hperm; apply Permutation_Type_swap ].
  apply negR_ilr; [ assumption | apply ax_exp_ill | ].
  apply negR_irr.
  cons2app. rewrite <- (app_nil_l _).
  eapply cut_ir; [ exact (Hcut _) | | apply IHA2 ].
  apply ax_exp_ill.
- apply negR_ilr; [ assumption | apply ax_exp_ill | ].
  apply negR_irr.
  eapply ex_ir; [ | rewrite Hperm; apply Permutation_Type_swap ].
  apply negR_ilr; [ assumption | apply ax_exp_ill | ].
  change (ioc (negR (trans A)) :: nil) with (map ioc (negR (trans A) :: nil)).
  apply oc_irr.
  rewrite <- (app_nil_l _).
  apply de_ilr, negR_irr.
  eapply ex_ir; [ eassumption | rewrite Hperm; apply Permutation_Type_swap ].
- eapply ex_ir; [ | rewrite Hperm; apply Permutation_Type_swap ].
  apply negR_ilr; [ assumption | apply ax_exp_ill | ].
  apply negR_irr.
  eapply ex_ir; [ | rewrite Hperm; apply Permutation_Type_swap ].
  apply negR_ilr; [ assumption | apply ax_exp_ill | ].
  change (ioc (negR (trans (dual A))) :: nil) with (map ioc (negR (trans (dual A)) :: nil)).
  apply oc_irr.
  rewrite <- (app_nil_l _).
  apply de_ilr, negR_irr; assumption.
Qed.

Lemma trans_subs P (Hperm : ipperm P = true) (Hcut : full_icut P) (A B : formula) x :
  (isubs (negR (trans B)) (a2i x) R = R) ->
  ill P (isubs (negR (trans B)) (a2i x) (trans A) :: negR (trans (subs B x A)):: nil) R.
Proof.
intros HR. induction A; cbn; rewrite ? HR.
- destruct (ateq c x) eqn:Hateq.
  + cbn in Hateq; unfold repl_at; rewrite Hateq; cbn.
    assert (iateq (a2i c) (a2i x) = true) as Hiateq
      by (rewrite <- ateq_a2i; assumption).
    unfold repl_iat. rewrite Hiateq.
    apply negR_ilr; [ assumption | | ]; apply ax_exp_ill.
  + destruct (iateq (a2i c) (a2i x)) eqn:Hiateq.
    * exfalso. rewrite <- ateq_a2i in Hiateq. rewrite Hiateq in Hateq. discriminate Hateq.
    * cbn in Hateq. unfold repl_at. rewrite Hateq. cbn. unfold repl_iat. rewrite Hiateq.
      eapply ex_ir; [ | rewrite Hperm; apply Permutation_Type_swap ].
      apply negR_ilr; [ assumption | | ]; apply ax_exp_ill.
- destruct (ateq c x) eqn:Hateq.
  + cbn in Hateq. unfold repl_at. rewrite Hateq. cbn.
    assert (iateq (a2i c) (a2i x) = true) as Hiateq
      by (rewrite <- ateq_a2i ; assumption).
    unfold repl_iat. rewrite Hiateq. cbn.
    apply trans_dual; assumption.
  + destruct (iateq (a2i c) (a2i x)) eqn:Hiateq.
    * exfalso. rewrite <- ateq_a2i in Hiateq. rewrite Hiateq in Hateq. discriminate Hateq.
    * cbn in Hateq. unfold repl_at. rewrite Hateq. cbn. unfold repl_iat. rewrite Hiateq. cbn.
      eapply ex_ir; [ | rewrite Hperm; apply Permutation_Type_swap ].
      apply negR_ilr; [ assumption | | ]; apply ax_exp_ill.
- eapply ex_ir; [ | rewrite Hperm; apply Permutation_Type_swap ].
  apply negR_ilr; [ assumption | | ]; apply ax_exp_ill.
- eapply ex_ir; [ | rewrite Hperm; apply Permutation_Type_swap ].
  apply negR_ilr; [ assumption | | ]; apply ax_exp_ill.
- eapply ex_ir; [ | rewrite Hperm; apply Permutation_Type_swap ].
  apply negR_ilr; [ assumption | apply ax_exp_ill | ].
  apply negR_irr.
  eapply ex_ir; [ | rewrite Hperm; apply Permutation_Type_swap ].
  apply negR_ilr; [ assumption | apply ax_exp_ill | ].
  rewrite <- (app_nil_l _).
  apply tens_ilr.
  list_simpl. cons2app.
  apply tens_irr; apply negR_irr; assumption.
- apply neg_tens_propag; assumption.
- eapply ex_ir; [ | rewrite Hperm; apply Permutation_Type_swap ].
  apply negR_ilr; [ assumption | | ]; apply ax_exp_ill.
- rewrite <- (app_nil_l _). apply zero_ilr.
- eapply ex_ir; [ | rewrite Hperm; apply Permutation_Type_swap ].
  apply negR_ilr; [ assumption | apply ax_exp_ill | ].
  apply negR_irr.
  eapply ex_ir; [ | rewrite Hperm; apply Permutation_Type_swap ].
  apply negR_ilr; [ assumption | apply ax_exp_ill | ].
  rewrite <- (app_nil_l _).
  apply plus_ilr; list_simpl.
  + apply plus_irr1, negR_irr. assumption.
  + apply plus_irr2, negR_irr. assumption.
- apply neg_plus_propag; assumption.
- eapply ex_ir; [ | rewrite Hperm; apply Permutation_Type_swap ].
  apply negR_ilr; [ assumption | apply ax_exp_ill | ].
  apply negR_irr.
  eapply ex_ir; [ | rewrite Hperm ; apply Permutation_Type_swap ].
  apply negR_ilr; [ assumption | apply ax_exp_ill | ].
  change (ioc (negR (trans (subs B x A))) :: nil)
    with (map ioc (negR (trans (subs B x A)) :: nil)).
  apply oc_irr.
  rewrite <- (app_nil_l _).
  apply de_ilr, negR_irr. assumption.
- eapply ex_ir; [ | rewrite Hperm; apply Permutation_Type_swap ].
  apply negR_ilr; [ assumption | apply ax_exp_ill | ].
  change (ioc (ilmap (ilmap (isubs (negR (trans B)) (a2i x) (trans A)) R) R) :: nil)
    with (map ioc (negR (negR (isubs (negR (trans B)) (a2i x) (trans A))) :: nil)).
  apply oc_irr.
  rewrite <- (app_nil_l _).
  apply de_ilr, negR_irr.
  list_simpl.
  eapply ex_ir; [ | rewrite Hperm; apply Permutation_Type_swap ].
  apply negR_ilr; [ assumption | apply ax_exp_ill | ].
  apply negR_irr. assumption.
Qed.


(** A provability statement [ll l] is translated as [ill (map trans l) R]. *)

Definition p2ipfrag P := {|
  ipcut := ipcut_all;
  ipgax := existT (fun x => x -> list iformula * iformula) (projT1 (pgax P))
                  (fun a => (map trans (projT2 (pgax P) a), R));
  ipperm := pperm P |}.

Context { P : @pfrag atom }.
Hypothesis P_perm : pperm P = true.


(** The translation maps [ll] proofs into [ill] proofs
(under some conditions for [mix0] and [mix2]). **)

Lemma ll_to_ill_trans_gen l l0 :
  (forall L, pmix P (length L) = true ->
             forall (FL : Forall_inf (ll P) L),
               Forall_Proofs (fun l pi => ill (p2ipfrag P) (map ioc l0 ++ map trans l) R) FL ->
               ill (p2ipfrag P) (map ioc l0 ++ map trans (concat L)) R) ->
  ll P l -> ill (p2ipfrag P) (map ioc l0 ++ map trans l) R.
Proof.
intros Hmix Hll.
assert (Hax := @ax_exp_ill _ (p2ipfrag P) R).
rewrite <- (app_nil_l (R :: _)) in Hax.
assert (ill (p2ipfrag P) (nil ++ map ioc l0 ++ R :: nil) R) as Hax'
  by apply wk_list_ilr, ax_exp_ill.
induction Hll using ll_nested_ind.
- cbn. cons2app. apply lmap_ilr; [ | apply Hax' ].
  apply (ax_ir (a2i X)).
- rewrite P_perm in p.
  eapply ex_ir; [ eassumption | ].
  apply PEPermutation_Type_app_head, PEPermutation_Type_map.
  cbn; rewrite P_perm; assumption.
- list_simpl in IHHll; rewrite map_map in IHHll; cbn in IHHll;
    rewrite <- (map_map _ _ lw) in IHHll.
  list_simpl; rewrite map_map; cbn; rewrite <- (map_map _ _ lw').
  rewrite app_assoc in IHHll; rewrite app_assoc.
  eapply Permutation_Type_map in p.
  eapply ex_oc_ir; eassumption.
- apply Hmix with PL; assumption.
- eapply ex_ir; [ | cbn; rewrite P_perm; apply Permutation_Type_middle ].
  rewrite <- 2 (app_nil_l _).
  apply lmap_ilr.
  + apply one_irr.
  + eapply ex_ir; [ eassumption
                  | cbn; rewrite P_perm; symmetry; apply Permutation_Type_middle ].
- apply one_ilr; assumption.
- apply (ex_ir _ (trans A :: map ioc l0 ++ map trans l1))
    in IHHll1; [ | cbn; rewrite P_perm; symmetry; apply Permutation_Type_middle ].
  apply negR_irr in IHHll1.
  apply (ex_ir _ (trans B :: map ioc l0 ++ map trans l2))
    in IHHll2; [ | cbn; rewrite P_perm; symmetry; apply Permutation_Type_middle ].
  apply negR_irr in IHHll2.
  apply (tens_irr _ _ _ _ IHHll1) in IHHll2.
  apply (lmap_ilr _ _ _ _ _ _ IHHll2) in Hax.
  rewrite <- (app_nil_l (map _ _ ++ _)).
  apply co_list_ilr.
  apply (ex_ir _ _ _ Hax).
  cbn; rewrite P_perm; list_simpl.
  apply Permutation_Type_app_head.
  etransitivity; [ apply Permutation_Type_app_comm | list_simpl; apply Permutation_Type_app_head ].
  etransitivity; [ apply Permutation_Type_app_comm | ].
  apply Permutation_Type_cons, Permutation_Type_app_comm; reflexivity.
- cbn; apply tens_ilr.
  eapply ex_ir; [ eassumption | ].
  cbn; rewrite P_perm; cbn.
  apply Permutation_Type_app_head, Permutation_Type_swap.
- apply zero_ilr.
- apply (ex_ir _ (trans A :: map ioc l0 ++ map trans l))
    in IHHll; [ | cbn; rewrite P_perm; symmetry; apply Permutation_Type_middle ].
  apply negR_irr in IHHll.
  apply (plus_irr1 _ (negR (trans B))) in IHHll.
  apply (lmap_ilr _ _ _ _ _ _ IHHll) in Hax.
  apply (ex_ir _ _ _ Hax).
  cbn; rewrite P_perm; list_simpl.
  apply Permutation_Type_app_head.
  etransitivity; [ apply Permutation_Type_app_comm | ].
  apply Permutation_Type_cons; reflexivity.
- apply (ex_ir _ (trans A :: map ioc l0 ++ map trans l))
    in IHHll; [ | cbn; rewrite P_perm; symmetry; apply Permutation_Type_middle ].
  apply negR_irr in IHHll.
  apply (plus_irr2 _ (negR (trans B))) in IHHll.
  apply (lmap_ilr _ _ _ _ _ _ IHHll) in Hax.
  apply (ex_ir _ _ _ Hax).
  cbn; rewrite P_perm; list_simpl.
  apply Permutation_Type_app_head.
  etransitivity; [ apply Permutation_Type_app_comm | ].
  apply Permutation_Type_cons; reflexivity.
- apply plus_ilr; assumption.
- cbn in IHHll; rewrite map_map in IHHll.
  cbn in IHHll; rewrite <- map_map in IHHll.
  apply (ex_ir _ (trans A :: map ioc (l0 ++ map (fun x => (negR (negR (trans x)))) l)))
    in IHHll; [ | cbn; rewrite P_perm; symmetry; apply Permutation_Type_cons_app;
                  list_simpl; rewrite map_id, map_map; reflexivity ].
  apply negR_irr, oc_irr in IHHll.
  eapply ex_ir; [ | cbn; rewrite P_perm; apply Permutation_Type_middle ].
    apply negR_ilr; [ assumption | apply ax_exp_ill | ].
    eapply ex_ir; [ eassumption | ].
    list_simpl; rewrite ? map_map; reflexivity.
- cbn; apply de_ilr.
  eapply ex_ir; [ | cbn; rewrite P_perm; apply Permutation_Type_middle ].
  apply negR_ilr; [ assumption | apply ax_exp_ill | ].
  apply negR_irr.
  eapply ex_ir; [ eassumption | cbn; rewrite P_perm; symmetry; apply Permutation_Type_middle ].
- apply wk_ilr; eassumption.
- rewrite <- (app_nil_l (map _ _ ++ _)).
  apply co_ilr; assumption.
- apply (ex_ir _ (trans (dual A) :: map ioc l0 ++ map trans l1)) in IHHll1;
    [ | cbn; rewrite P_perm; symmetry; apply Permutation_Type_middle ].
  apply negR_irr in IHHll1.
  apply (ex_ir _ (trans A :: map ioc l0 ++ map trans l2)) in IHHll2;
    [ | cbn; rewrite P_perm; symmetry; apply Permutation_Type_middle ].
  apply negR_irr in IHHll2.
  assert (ipperm (p2ipfrag P) = true) as Hperm by (cbn; assumption).
  assert (full_icut (p2ipfrag P)) as Hcut by (intro; reflexivity).
  assert (pi0 := trans_dual Hperm Hcut A).
  rewrite <- (app_nil_l _) in pi0.
  eapply (@cut_ir _ _ _ (Hcut _) _ _ _ _ IHHll2) in pi0.
  list_simpl in pi0 ; rewrite app_assoc in pi0.
  eapply (@cut_ir _ _ _ (Hcut _) _ _ _ _ IHHll1) in pi0.
  rewrite <- (app_nil_l (map ioc _ ++ _)).
  apply co_list_ilr.
  eapply ex_ir; [ eassumption | ].
  cbn; rewrite P_perm; list_simpl; apply Permutation_Type_app_head.
  rewrite ? app_assoc; apply Permutation_Type_app_tail, Permutation_Type_app_comm.
- rewrite <- (app_nil_l _).
  apply wk_list_ilr.
  change (projT1 (pgax P)) with (projT1 (ipgax (p2ipfrag P))) in a.
  apply (gax_ir a).
Qed.

Theorem ll_to_ill_trans l :
  (forall L : list (list formula),
     pmix P (length L) = true ->
     forall FL : Forall_inf (ll P) L,
       Forall_Proofs (fun l0 (_ : ll P l0) => ill (p2ipfrag P) (map ioc nil ++ map trans l0) R) FL ->
       ill (p2ipfrag P) (map ioc nil ++ map trans (concat L)) R) ->
  ll P l -> ill (p2ipfrag P) (map trans l) R.
Proof.
intros Hmix Hll.
rewrite <- (app_nil_l (map _ _)).
change nil with (map (@ioc preiatom) nil).
apply ll_to_ill_trans_gen; assumption.
Qed.

End RTranslation.

Lemma munit_trans A (x : atom_inf) : ~ In x (atom_list A) ->
  munit_smp (subs bot x (dual (unill (trans (ivar (a2i x)) A)))) A.
Proof.
induction A; simpl; intros Hnin; rewrite ? a2a_i; try apply munit_smp_id;
  destruct (bijective_inverse Atom2PreIAtom_bij) as [f Hr1 Hr2].
- rewrite repl_at_eq; [ | rewrite Hr2; reflexivity ].
  apply musmp_to.
  rewrite repl_at_neq; [ rewrite Hr2; apply munit_smp_id | ].
  intros Heq. apply Hnin. left. rewrite Hr2 in Heq. assumption.
- rewrite repl_at_neq, Hr2; [ apply munit_smp_id | ].
  intros Heq. apply Hnin. left. rewrite Hr2 in Heq. assumption.
- rewrite repl_at_eq; [ | rewrite Hr2; reflexivity ].
  apply musmp_to, munit_smp_id.
- rewrite repl_at_eq; [ | rewrite Hr2; reflexivity ].
  rewrite ? bidual.
  apply musmp_to.
  apply musmp_tens; apply musmp_pb; [ apply IHA1 | apply IHA2 ].
  + intros Hin. apply Hnin.
    apply in_or_app. left. assumption.
  + intros Hin. apply Hnin.
    apply in_or_app. right. assumption.
- apply musmp_parr; [ apply IHA1 | apply IHA2 ].
  + intros Hin. apply Hnin.
    apply in_or_app. left. assumption.
  + intros Hin. apply Hnin.
    apply in_or_app. right. assumption.
- rewrite repl_at_eq; [ | rewrite Hr2; reflexivity ].
  apply musmp_to, munit_smp_id.
- rewrite repl_at_eq; [ | rewrite Hr2; reflexivity ].
  rewrite ? bidual.
  apply musmp_to.
  apply musmp_plus; apply musmp_pb; [ apply IHA1 | apply IHA2 ].
  + intros Hin. apply Hnin.
    apply in_or_app. left. assumption.
  + intros Hin. apply Hnin.
    apply in_or_app. right. assumption.
- apply musmp_with; [ apply IHA1 | apply IHA2 ].
  + intros Hin. apply Hnin.
    apply in_or_app. left. assumption.
  + intros Hin. apply Hnin.
    apply in_or_app. right. assumption.
- rewrite repl_at_eq; [ | rewrite Hr2; reflexivity ].
  rewrite ? bidual.
  apply musmp_to.
  apply musmp_oc; apply musmp_pb; apply IHA; assumption.
- rewrite repl_at_eq; [ | rewrite Hr2; reflexivity ].
  rewrite ? bidual.
  apply musmp_wn, musmp_to, musmp_pb.
  apply IHA; assumption.
Qed.

End Atoms.
