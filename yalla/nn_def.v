(* nn_def library for yalla *)


(** * Parametric negative translation from [ll] into [ill]. *)

Require Import Injective.
Require Import List_more.
Require Import List_Type_more.
Require Import Permutation_Type.
Require Import genperm_Type.
Require Import Forall_Type_more2.
Require Import Dependent_Forall_Type.
Require Import concat_Type_more.

Require Import subs.
Require Import isubs.
Require Export ill_vs_ll.


(** ** Basic ingredients for links with [ill] *)

Definition i2a := yalla_ax.i2a.
Definition a2i := yalla_ax.a2i.
Definition a2a_i := yalla_ax.a2a_i.
Definition i2i_not_atN := yalla_ax.i2i_not_atN.
Definition i2ac := yalla_ax.i2ac.
Definition i2ac_inj := yalla_ax.i2ac_inj.
Definition ateq_a2i := yalla_ax.ateq_a2i.

Definition unill := ill2ll i2a.

(** ** The translation *)

Section RTranslation.

(** We fix the parameter [R] of the translation. *)

Variable R : iformula.
Definition negR A := ilmap A R.

Lemma negR_irr {P} : forall A l,
  ill P (A :: l) R -> ill P l (negR A).
Proof.
intros A l pi.
apply lmap_irr.
assumption.
Qed.

Lemma negR_ilr {P} : ipperm P = true -> ill P (R :: nil) R ->
  forall A l, ill P l A -> ill P (negR A :: l) R.
Proof.
intros Hperm HR A l pi.
rewrite <- (app_nil_r _).
rewrite <- app_comm_cons.
eapply ex_ir ; [ | symmetry ; rewrite Hperm ; apply Permutation_Type_middle ].
rewrite <- (app_nil_l _).
apply lmap_ilr ; assumption.
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
intros a.
induction a ; intros b Heq ; destruct b ; inversion Heq ;
  (try apply IHa in H0) ;
  (try apply IHa1 in H0) ;
  (try apply IHa2 in H1) ; subst ;
  intuition.
apply IHa1 in H1.
apply IHa2 in H0.
subst.
reflexivity.
Qed.

Lemma trans_wn : forall l,
  map trans (map wn l)
= map ioc (map (fun x => (negR (negR (trans x)))) l).
Proof with myeasy.
induction l...
simpl ; rewrite IHl...
Qed.

Lemma neg_tens_propag {P} : ipperm P = true -> ipcut P = true -> forall A1 A2 B1 B2,
  ill P (A1 :: negR A2 :: nil) R -> ill P (B1 :: negR B2 :: nil) R ->
    ill P (itens A1 B1 :: negR (itens A2 B2) :: nil) R.
Proof with myeeasy.
intros Hperm Hcut A1 A2 B1 B2 pi1 pi2.
cons2app.
rewrite <- (app_nil_l _).
eapply (@cut_ir _ Hcut (itens (negR (negR A2)) (negR (negR B2))))...
- rewrite <- (app_nil_l _).
  apply tens_ilr.
  list_simpl ; cons2app.
  apply tens_irr ; apply lmap_irr.
  + eapply ex_ir ; [ apply pi1 | rewrite Hperm ; apply Permutation_Type_swap ]...
  + eapply ex_ir ; [ apply pi2 | rewrite Hperm ; apply Permutation_Type_swap ]...
- list_simpl.
  rewrite <- (app_nil_l _).
  apply tens_ilr.
  list_simpl.
  rewrite <- (app_nil_l (negR (itens _ _) :: _)).
  rewrite 2 app_comm_cons.
  rewrite <- (app_nil_l _).
  apply negR_ilr...
  + apply ax_exp_ill.
  + apply negR_irr.
    eapply ex_ir ; [ | rewrite Hperm ; apply Permutation_Type_swap ].
    apply negR_ilr...
    * apply ax_exp_ill.
    * apply negR_irr.
      cons2app.
      rewrite app_assoc.
      eapply ex_ir ; [ | rewrite Hperm ; apply Permutation_Type_middle ].
      list_simpl.
      apply negR_ilr...
      -- apply ax_exp_ill.
      -- eapply ex_ir ; [ | rewrite Hperm ; apply Permutation_Type_swap ].
         cons2app.
         apply tens_irr ; apply ax_exp_ill.
Qed.

Lemma neg_plus_propag {P} : ipperm P = true -> ipcut P = true -> forall A1 A2 B1 B2,
  ill P (A1 :: negR A2 :: nil) R -> ill P (B1 :: negR B2 :: nil) R ->
    ill P (iplus A1 B1 :: negR (iplus A2 B2) :: nil) R.
Proof with myeeasy.
intros Hperm Hcut A1 A2 B1 B2 pi1 pi2.
cons2app.
rewrite <- (app_nil_l _).
eapply (@cut_ir _ Hcut (iplus (negR (negR A2)) (negR (negR B2))))...
- rewrite <- (app_nil_l _).
  apply plus_ilr.
  + list_simpl.
    apply plus_irr1.
    apply negR_irr.
    eapply ex_ir ; [ | rewrite Hperm ; apply Permutation_Type_swap ]...
  + list_simpl.
    apply plus_irr2.
    apply negR_irr.
    eapply ex_ir ; [ | rewrite Hperm ; apply Permutation_Type_swap ]...
- list_simpl.
  rewrite <- (app_nil_l _).
  apply plus_ilr.
  + list_simpl.
    apply negR_ilr...
    * apply ax_exp_ill.
    * apply negR_irr.
      eapply ex_ir ; [ | rewrite Hperm ; apply Permutation_Type_swap ].
      apply negR_ilr...
      -- apply ax_exp_ill.
      -- apply plus_irr1.
         apply ax_exp_ill.
  + list_simpl.
    apply negR_ilr...
    * apply ax_exp_ill.
    * apply negR_irr.
      eapply ex_ir ; [ | rewrite Hperm ; apply Permutation_Type_swap ].
      apply negR_ilr...
      -- apply ax_exp_ill.
      -- apply plus_irr2.
         apply ax_exp_ill.
Qed.

Lemma trans_dual {P} : ipperm P = true -> ipcut P = true -> forall A,
  ill P (negR (trans A) :: negR (trans (dual A)) :: nil) R.
Proof with myeeasy ; try now (apply ax_exp_ill).
intros Hperm Hcut.
induction A ; simpl.
- apply negR_ilr...
- eapply ex_ir ; [ | rewrite Hperm ; apply Permutation_Type_swap ].
  apply negR_ilr...
- apply negR_ilr...
- eapply ex_ir ; [ | rewrite Hperm ; apply Permutation_Type_swap ].
  apply negR_ilr...
- apply (neg_tens_propag Hperm Hcut _ _ _ _ IHA1) in IHA2.
  apply negR_ilr...
  apply negR_irr.
  cons2app.
  rewrite <- (app_nil_l _).
  eapply cut_ir ; [ | | apply IHA2 ]...
- eapply ex_ir in IHA1 ; [ | rewrite Hperm ; apply Permutation_Type_swap ].
  eapply ex_ir in IHA2 ; [ | rewrite Hperm ; apply Permutation_Type_swap ].
  apply (neg_tens_propag Hperm Hcut _ _ _ _ IHA2) in IHA1.
  eapply ex_ir ; [ | rewrite Hperm ; apply Permutation_Type_swap ].
  apply negR_ilr...
  apply negR_irr.
  cons2app.
  rewrite <- (app_nil_l _).
  eapply cut_ir ; [ | | apply IHA1 ]...
- apply negR_ilr...
- eapply ex_ir ; [ | rewrite Hperm ; apply Permutation_Type_swap ].
  apply negR_ilr...
- apply (neg_plus_propag Hperm Hcut _ _ _ _ IHA1) in IHA2.
  apply negR_ilr...
  apply negR_irr.
  cons2app.
  rewrite <- (app_nil_l _).
  eapply cut_ir ; [ | | apply IHA2 ]...
- eapply ex_ir in IHA1 ; [ | rewrite Hperm ; apply Permutation_Type_swap ].
  eapply ex_ir in IHA2 ; [ | rewrite Hperm ; apply Permutation_Type_swap ].
  apply (neg_plus_propag Hperm Hcut _ _ _ _ IHA1) in IHA2.
  eapply ex_ir ; [ | rewrite Hperm ; apply Permutation_Type_swap ].
  apply negR_ilr...
  apply negR_irr.
  cons2app.
  rewrite <- (app_nil_l _).
  eapply cut_ir ; [ | | apply IHA2 ]...
- apply negR_ilr...
  apply negR_irr.
  eapply ex_ir ; [ | rewrite Hperm ; apply Permutation_Type_swap ].
  apply negR_ilr...
  change (ioc (negR (trans A)) :: nil)
    with (map ioc (negR (trans A) :: nil)).
  apply oc_irr.
  rewrite <- (app_nil_l _).
  apply de_ilr.
  apply negR_irr.
  eapply ex_ir ; [ | rewrite Hperm ; apply Permutation_Type_swap ]...
- eapply ex_ir ; [ | rewrite Hperm ; apply Permutation_Type_swap ].
  apply negR_ilr...
  apply negR_irr.
  eapply ex_ir ; [ | rewrite Hperm ; apply Permutation_Type_swap ].
  apply negR_ilr...
  change (ioc (negR (trans (dual A))) :: nil)
    with (map ioc (negR (trans (dual A)) :: nil)).
  apply oc_irr.
  rewrite <- (app_nil_l _).
  apply de_ilr.
  apply negR_irr...
Qed.

Lemma trans_subs {P} : ipperm P = true -> ipcut P = true -> forall A B x,
  (isubs (negR (trans B)) (a2i x) R = R) ->
  ill P (isubs (negR (trans B)) (a2i x) (trans A)
             :: negR (trans (subs B x A)):: nil) R.
Proof with myeeasy ; try now (apply ax_exp_ill).
intros Hperm Hcut A B x HR.
induction A ; simpl ; try rewrite HR.
- case_eq (ateq a x) ; intros Hateq.
  + unfold repl_at ; rewrite Hateq ; simpl.
    assert (iateq (a2i a) (a2i x) = true) as Hiateq
      by (rewrite <- ateq_a2i ; assumption).
    unfold repl_iat ; rewrite Hiateq ; simpl.
    apply negR_ilr...
  + case_eq (iateq (a2i a) (a2i x)) ; intros Hiateq.
    * exfalso.
      rewrite <- ateq_a2i in Hiateq.
      unfold ateq in Hateq.
      rewrite Hiateq in Hateq.
      inversion Hateq.
    * unfold repl_at ; rewrite Hateq ; simpl.
      unfold repl_iat ; rewrite Hiateq ; simpl.
      eapply ex_ir ; [ | rewrite Hperm ; apply Permutation_Type_swap ].
      apply negR_ilr...
- case_eq (ateq a x) ; intros Hateq.
  + unfold repl_at ; rewrite Hateq ; simpl.
    assert (iateq (a2i a) (a2i x) = true) as Hiateq
      by (rewrite <- ateq_a2i ; assumption).
    unfold repl_iat ; rewrite Hiateq ; simpl.
    apply trans_dual...
  + case_eq (iateq (a2i a) (a2i x)) ; intros Hiateq.
    * exfalso.
      rewrite <- ateq_a2i in Hiateq.
      unfold ateq in Hateq.
      rewrite Hiateq in Hateq.
      inversion Hateq.
    * unfold repl_at ; rewrite Hateq ; simpl.
      unfold repl_iat ; rewrite Hiateq ; simpl.
      eapply ex_ir ; [ | rewrite Hperm ; apply Permutation_Type_swap ].
      apply negR_ilr...
- eapply ex_ir ; [ | rewrite Hperm ; apply Permutation_Type_swap ].
  apply negR_ilr...
- eapply ex_ir ; [ | rewrite Hperm ; apply Permutation_Type_swap ].
  apply negR_ilr...
- eapply ex_ir ; [ | rewrite Hperm ; apply Permutation_Type_swap ].
  apply negR_ilr...
  apply negR_irr.
  eapply ex_ir ; [ | rewrite Hperm ; apply Permutation_Type_swap ].
  apply negR_ilr...
  rewrite <- (app_nil_l _).
  apply tens_ilr.
  list_simpl ; cons2app.
  apply tens_irr ; apply negR_irr...
- eapply neg_tens_propag...
- eapply ex_ir ; [ | rewrite Hperm ; apply Permutation_Type_swap ].
  apply negR_ilr...
- rewrite <- (app_nil_l _).
  apply zero_ilr.
- eapply ex_ir ; [ | rewrite Hperm ; apply Permutation_Type_swap ].
  apply negR_ilr...
  apply negR_irr.
  eapply ex_ir ; [ | rewrite Hperm ; apply Permutation_Type_swap ].
  apply negR_ilr...
  rewrite <- (app_nil_l _).
  apply plus_ilr ; list_simpl.
  + apply plus_irr1.
    apply negR_irr...
  + apply plus_irr2.
    apply negR_irr...
- eapply neg_plus_propag...
- eapply ex_ir ; [ | rewrite Hperm ; apply Permutation_Type_swap ].
  apply negR_ilr...
  apply negR_irr.
  eapply ex_ir ; [ | rewrite Hperm ; apply Permutation_Type_swap ].
  apply negR_ilr...
  change (ioc (negR (trans (subs B x A))) :: nil)
    with (map ioc (negR (trans (subs B x A)) :: nil)).
  apply oc_irr.
  rewrite <- (app_nil_l _).
  apply de_ilr.
  apply negR_irr...
- eapply ex_ir ; [ | rewrite Hperm ; apply Permutation_Type_swap ].
  apply negR_ilr...
  change (ioc (ilmap (ilmap (isubs (negR (trans B)) (a2i x) (trans A)) R) R) :: nil)
    with (map ioc (negR (negR (isubs (negR (trans B)) (a2i x) (trans A))) :: nil)).
  apply oc_irr.
  rewrite <- (app_nil_l _).
  apply de_ilr.
  apply negR_irr.
  list_simpl.
  eapply ex_ir ; [ | rewrite Hperm ; apply Permutation_Type_swap ].
  apply negR_ilr...
  apply negR_irr...
Qed.


(** A provability statement [ll l] is translated as [ill (map trans l) R]. *)

Definition p2ipfrag P := {|
  ipcut := pcut P ;
  ipgax := existT (fun x => x -> list iformula * iformula) (projT1 (pgax P))
             (fun a => (map trans (projT2 (pgax P) a), R)) ;
  ipperm := pperm P |}.

Context {P : pfrag}.
(* Hypothesis P_axfree : projT1 (pgax P) -> False. *)
Hypothesis P_perm : pperm P = true.


(** The translation maps [ll] proofs into [ill] proofs
(under some conditions for [mix0] and [mix2]). **)

Lemma ll_to_ill_trans_gen : forall l l0,
  (forall L, pmix P (length L) = true ->
             forall (FL : Forall_Type (ll P) L),
               Forall_Proofs P (fun l pi => ill (p2ipfrag P) (map ioc l0 ++ map trans l) R) FL ->
               ill (p2ipfrag P) (map ioc l0 ++ map trans (concat L)) R) ->
  ll P l -> ill (p2ipfrag P) (map ioc l0 ++ map trans l) R.
Proof with myeeasy ; (try now (apply ax_exp_ill)) ;
                     try (simpl ; rewrite P_perm ; PEperm_Type_solve).
intros l l0 Hmix Hll.
assert (Hax := @ax_exp_ill (p2ipfrag P) R).
rewrite <- (app_nil_l (R :: _)) in Hax.
assert (ill (p2ipfrag P) (nil ++ map ioc l0 ++ R :: nil) R) as Hax'.
{ apply wk_list_ilr.
  apply ax_exp_ill. }
induction Hll using (ll_nested_ind _); 
  (try now (apply P_axfree in H ; inversion H)) ;
  (try now (inversion f)) ;
  simpl.
- eapply ex_ir.
  + eapply lmap_ilr ; [ | apply Hax' ].
    eapply (ax_ir _ (a2i X)).
  + PEperm_Type_solve.
- simpl in p.
  rewrite P_perm in p.
  eapply ex_ir...
  apply PEperm_Type_app_head...
  apply PEperm_Type_map.
  simpl ; rewrite P_perm...
- list_simpl in IHHll ; rewrite map_map in IHHll ; simpl in IHHll ;
    rewrite <- (map_map _ _ lw) in IHHll.
  list_simpl ; rewrite map_map ; simpl ; rewrite <- (map_map _ _ lw').
  rewrite app_assoc in IHHll ; rewrite app_assoc.
  eapply Permutation_Type_map in p.
  eapply ex_oc_ir...
- apply Hmix with PL...
- eapply ex_ir ; [ | simpl ; rewrite P_perm ; apply Permutation_Type_middle ].
  rewrite <- (app_nil_l _).
  rewrite <- (app_nil_l _).
  apply lmap_ilr...
  + apply one_irr.
  + eapply ex_ir...
- apply one_ilr...
- apply (ex_ir _ _ (trans A :: map ioc l0 ++ map trans l1))
    in IHHll1...
  apply negR_irr in IHHll1.
  apply (ex_ir _ _ (trans B :: map ioc l0 ++ map trans l2))
    in IHHll2...
  apply negR_irr in IHHll2.
  apply (tens_irr _ _ _ _ _ IHHll1) in IHHll2.
  apply (lmap_ilr _ _ _ _ _ _ _ IHHll2) in Hax.
  rewrite <- (app_nil_l (map _ _ ++ _)).
  eapply co_list_ilr.
  apply (ex_ir _ _ _ _ Hax)...
- apply tens_ilr.
  eapply ex_ir...
- apply zero_ilr.
- apply (ex_ir _ _ (trans A :: map ioc l0 ++ map trans l1))
    in IHHll...
  apply negR_irr in IHHll.
  apply (plus_irr1 _ _ (negR (trans B))) in IHHll.
  apply (lmap_ilr _ _ _ _ _ _ _ IHHll) in Hax.
  apply (ex_ir _ _ _ _ Hax)...
- apply (ex_ir _ _ (trans A :: map ioc l0 ++ map trans l1))
    in IHHll...
  apply negR_irr in IHHll.
  apply (plus_irr2 _ _ (negR (trans B))) in IHHll.
  apply (lmap_ilr _ _ _ _ _ _ _ IHHll) in Hax.
  apply (ex_ir _ _ _ _ Hax)...
- apply plus_ilr...
- simpl in IHHll ; rewrite map_map in IHHll.
  simpl in IHHll ; rewrite <- map_map in IHHll.
  apply (ex_ir _ _ (trans A :: map ioc (l0 ++ map (fun x => (negR (negR (trans x)))) l1)))
    in IHHll...
  + apply negR_irr in IHHll.
    apply oc_irr in IHHll.
    eapply ex_ir ; [ | simpl ; rewrite P_perm ; apply Permutation_Type_middle ].
    apply negR_ilr...
    eapply ex_ir...
    list_simpl...
    rewrite ? map_map...
  + list_simpl...
    rewrite ? map_map...
- apply de_ilr...
  eapply ex_ir ; [ | simpl ; rewrite P_perm ; apply Permutation_Type_middle ].
  apply negR_ilr...
  apply negR_irr.
  eapply ex_ir...
- apply wk_ilr...
- rewrite <- (app_nil_l (map _ _ ++ _)).
  apply co_ilr.
  eapply ex_ir...
- apply (ex_ir _ _ (trans (dual A) :: map ioc l0 ++ map trans l1)) in IHHll1...
  apply negR_irr in IHHll1.
  apply (ex_ir _ _ (trans A :: map ioc l0 ++ map trans l2)) in IHHll2...
  apply negR_irr in IHHll2.
  assert (ipperm (p2ipfrag P) = true) as Hperm by (simpl ; assumption).
  assert (ipcut (p2ipfrag P) = true) as Hcut by (simpl ; assumption).
  assert (pi0 := trans_dual Hperm f A).
  rewrite <- (app_nil_l _) in pi0.
  eapply (@cut_ir _ Hcut _ _ _ _ _ IHHll2) in pi0.
  list_simpl in pi0 ; rewrite app_assoc in pi0.
  eapply (@cut_ir _ Hcut _ _ _ _ _ IHHll1) in pi0.
  rewrite <- (app_nil_l (map ioc _ ++ _)).
  eapply co_list_ilr.
  eapply ex_ir...
- rewrite <- (app_nil_l _).
  apply wk_list_ilr.
  change (projT1 (pgax P)) with (projT1 (ipgax (p2ipfrag P))) in a.
  eapply (gax_ir _ a)...
Qed.

Theorem ll_to_ill_trans : forall l,
  (forall L : list (list formula),
      pmix P (length L) = true ->
      forall FL : Forall_Type (ll P) L,
        Forall_Proofs P (fun (l0 : list formula) (_ : ll P l0) => ill (p2ipfrag P) (map ioc nil ++ map trans l0) R) FL ->
        ill (p2ipfrag P) (map ioc nil ++ map trans (concat L)) R) ->
      ll P l -> ill (p2ipfrag P) (map trans l) R.
Proof with myeeasy.
intros l Hmix Hll.
rewrite <- (app_nil_l (map _ _)).
change nil with (map ioc nil).
eapply ll_to_ill_trans_gen...
Qed.

End RTranslation.

(** Ingredients for generating fresh variables *)
Definition a2n := yalla_ax.a2n.
Definition n2a := yalla_ax.n2a.
Definition n2n_a := yalla_ax.n2n_a.

Lemma munit_trans : forall A n, nat_fresh_of a2n A <= n ->
  munit_smp (subs bot (n2a n) (dual (unill (trans (ivar (a2i (n2a n))) A)))) A.
Proof with (try now (apply munit_smp_id)) ; myeasy.
induction A ; intros n Hf ; simpl...
- rewrite a2a_i.
  rewrite repl_at_eq ; try reflexivity.
  apply musmp_to.
  apply (subs_fresh_le _ n2a n2n_a bot) in Hf.
  simpl in Hf.
  rewrite a2a_i.
  rewrite Hf...
- apply (subs_fresh_le _ n2a n2n_a bot) in Hf.
  simpl in Hf.
  rewrite a2a_i.
  rewrite Hf...
- rewrite a2a_i.
  rewrite repl_at_eq ; try reflexivity.
  apply musmp_to...
- rewrite a2a_i.
  rewrite repl_at_eq ; try reflexivity.
  rewrite ? bidual.
  apply musmp_to.
  simpl in Hf.
  apply musmp_tens ; apply musmp_pb ; [ apply IHA1 | apply IHA2 ]...
- simpl in Hf.
  apply musmp_parr ; [ apply IHA1 | apply IHA2 ]...
- rewrite a2a_i.
  rewrite repl_at_eq ; try reflexivity.
  apply musmp_to...
- rewrite a2a_i.
  rewrite repl_at_eq ; try reflexivity.
  rewrite ? bidual.
  apply musmp_to.
  simpl in Hf.
  apply musmp_plus ; apply musmp_pb ; [ apply IHA1 | apply IHA2 ]...
- simpl in Hf.
  apply musmp_with ; [ apply IHA1 | apply IHA2 ]...
- rewrite a2a_i.
  rewrite repl_at_eq ; try reflexivity.
  rewrite ? bidual.
  apply musmp_to.
  simpl in Hf.
  apply musmp_oc ; apply musmp_pb ; apply IHA...
- rewrite a2a_i.
  rewrite repl_at_eq ; try reflexivity.
  rewrite ? bidual.
  apply musmp_wn.
  apply musmp_to.
  apply musmp_pb.
  apply IHA.
  simpl in Hf...
Qed.