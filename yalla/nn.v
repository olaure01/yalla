(* nn library for yalla *)
(* v 1.2   Olivier Laurent *)


(* TODO clean file *)


(** * Parametric negative translation from [ll] into [ill]. *)

Require Import Arith.
Require Import Omega.

Require Import Injective.
Require Import Bool_more.
Require Import List_more.
Require Import Permutation_more.
Require Import Permutation_solve.
Require Import genperm.

Require Import subs.
Require Import isubs.
Require Import ll_fragments.

Require Import bbb.

(** ** Basic ingredients for links with [ill] *)

Definition i2a := yalla_ax.i2a.
Definition a2i := yalla_ax.a2i.
Definition a2a_i := yalla_ax.a2a_i.
Definition i2i_not_atN := yalla_ax.i2i_not_atN.

Definition i2ac := yalla_ax.i2ac.
Definition i2ac_inj := yalla_ax.i2ac_inj.
Definition ateq_a2i := yalla_ax.ateq_a2i.

Definition ipfrag_ill := mk_ipfrag true (fun _ _ => False) true.
(*                                 cut   axioms            perm  *)
Definition ill_ll := ill ipfrag_ill.

Definition unill := ill2ll i2a.

(** ** The translation *)

Section RTranslation.

Context {P : pfrag}.
Hypothesis P_axfree : forall l, ~ pgax P l.
Hypothesis P_perm : pperm P = true.

(** We fix the parameter [R] of the translation. *)

Variable R : iformula.
Definition negR A := ilmap A R.

Lemma negR_irr : forall A l s,
  ill_ll (A :: l) R s -> ill_ll l (negR A) (S s).
Proof.
intros A l s pi.
apply lmap_irr.
assumption.
Qed.

Lemma negR_ilr : forall sR, ill_ll (R :: nil) R sR ->
  forall A l s, ill_ll l A s -> ill_ll (negR A :: l) R (S (S (s + sR))).
Proof.
intros sR HR A l s pi.
rewrite <- (app_nil_r _).
rewrite <- app_comm_cons.
eapply ex_ir ; [ | symmetry ; apply Permutation_middle ].
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
| parr A B  => itens (trans A) (trans B)
| zero      => negR izero
| top       => izero
| aplus A B => negR (iplus (negR (trans A)) (negR (trans B)))
| awith A B => iplus (trans A) (trans B)
| oc A      => negR (ioc (negR (trans A)))
| wn A      => ioc (negR (negR (trans A)))
end.

Lemma trans_wn : forall l,
  map trans (map wn l)
= map ioc (map (fun x => (negR (negR (trans x)))) l).
Proof with myeasy.
induction l...
simpl ; rewrite IHl...
Qed.

Lemma trans_nz : ~ zeropos R -> nonzerospos R ->
  forall A, nonzerospos (trans A).
Proof with myeasy.
intros Hnz Hnzsp.
induction A ; simpl ; try now constructor ;
  try (constructor ; try assumption ; now constructor).
Qed.

Lemma neg_tens_propag : forall A1 A2 B1 B2 s1 s2,
  ill_ll (A1 :: negR A2 :: nil) R s1 -> ill_ll (B1 :: negR B2 :: nil) R s2 -> 
    exists s, ill_ll (itens A1 B1 :: negR (itens A2 B2) :: nil) R s.
Proof with myeeasy.
intros A1 A2 B1 B2 s1 s2 pi1 pi2.
destruct (@ax_exp_ill ipfrag_ill R) as [sR axR].
destruct (@ax_exp_ill ipfrag_ill A2) as [sA2 axA2].
destruct (@ax_exp_ill ipfrag_ill B2) as [sB2 axB2].
eexists.
cons2app.
rewrite <- (app_nil_l _).
eapply (cut_ir _ (itens (negR (negR A2)) (negR (negR B2))))...
- rewrite <- (app_nil_l _).
  apply tens_ilr.
  list_simpl ; cons2app.
  apply tens_irr ; apply lmap_irr.
  + eapply ex_ir ; [ apply pi1 | apply perm_swap ]...
  + eapply ex_ir ; [ apply pi2 | apply perm_swap ]...
- list_simpl.
  rewrite <- (app_nil_l _).
  apply tens_ilr.
  list_simpl.
  rewrite <- (app_nil_l (negR (itens _ _) :: _)).
  rewrite 2 app_comm_cons.
  rewrite <- (app_nil_l _).
  apply negR_ilr...
  apply negR_irr.
  eapply ex_ir ; [ | apply perm_swap ].
  apply negR_ilr...
  apply negR_irr.
  cons2app.
  rewrite app_assoc.
  eapply ex_ir ; [ | apply Permutation_middle ].
  list_simpl.
  apply negR_ilr...
  eapply ex_ir ; [ | apply perm_swap ].
  cons2app.
  apply tens_irr...
Unshelve. reflexivity.
Qed.

Lemma neg_plus_propag : forall A1 A2 B1 B2 s1 s2,
  ill_ll (A1 :: negR A2 :: nil) R s1 -> ill_ll (B1 :: negR B2 :: nil) R s2 -> 
    exists s, ill_ll (iplus A1 B1 :: negR (iplus A2 B2) :: nil) R s.
Proof with myeeasy.
intros A1 A2 B1 B2 s1 s2 pi1 pi2.
destruct (@ax_exp_ill ipfrag_ill R) as [sR axR].
destruct (@ax_exp_ill ipfrag_ill A2) as [sA2 axA2].
destruct (@ax_exp_ill ipfrag_ill B2) as [sB2 axB2].
eexists.
cons2app.
rewrite <- (app_nil_l _).
eapply (cut_ir _ (iplus (negR (negR A2)) (negR (negR B2))))...
- rewrite <- (app_nil_l _).
  apply plus_ilr.
  + list_simpl.
    apply plus_irr1.
    apply negR_irr.
    eapply ex_ir ; [ | apply perm_swap ]...
  + list_simpl.
    apply plus_irr2.
    apply negR_irr.
    eapply ex_ir ; [ | apply perm_swap ]...
- list_simpl.
  rewrite <- (app_nil_l _).
  apply plus_ilr.
  + list_simpl.
    apply negR_ilr...
    apply negR_irr.
    eapply ex_ir ; [ | apply perm_swap ].
    apply negR_ilr...
    apply plus_irr1...
  + list_simpl.
    apply negR_ilr...
    apply negR_irr.
    eapply ex_ir ; [ | apply perm_swap ].
    apply negR_ilr...
    apply plus_irr2...
Unshelve. reflexivity.
Qed.

Lemma trans_dual : forall A, exists s,
  ill_ll (negR (trans A) :: negR (trans (dual A)) :: nil) R s.
Proof with myeeasy.
destruct (@ax_exp_ill ipfrag_ill R) as [sR axR].
induction A ;
  try destruct IHA as [s0 IHA] ;
  try destruct IHA1 as [s1 IHA1] ;
  try destruct IHA2 as [s2 IHA2] ;
  simpl.
- eexists.
  apply negR_ilr...
  apply negR_irr.
  eapply ex_ir ; [ | apply perm_swap ].
  apply negR_ilr...
  apply ax_ir.
- eexists.
  eapply ex_ir ; [ | apply perm_swap ].
  apply negR_ilr...
  apply negR_irr.
  eapply ex_ir ; [ | apply perm_swap ].
  apply negR_ilr...
  apply ax_ir.
- eexists.
  apply negR_ilr...
  apply negR_irr.
  eapply ex_ir ; [ | apply perm_swap ].
  apply negR_ilr...
  rewrite <- (app_nil_l _).
  apply one_ilr.
  apply one_irr.
- eexists.
  eapply ex_ir ; [ | apply perm_swap ].
  apply negR_ilr...
  apply negR_irr.
  eapply ex_ir ; [ | apply perm_swap ].
  apply negR_ilr...
  rewrite <- (app_nil_l _).
  apply one_ilr.
  apply one_irr.
- destruct (@ax_exp_ill ipfrag_ill (negR (trans A1))) as [sA1 axA1].
  destruct (@ax_exp_ill ipfrag_ill (negR (trans A2))) as [sA2 axA2].
  apply (neg_tens_propag _ _ _ _ _ _ IHA2) in IHA1.
  destruct IHA1 as [s IHA1].
  eexists.
  apply negR_ilr...
  apply negR_irr.
  cons2app.
  rewrite <- (app_nil_l _).
  eapply cut_ir ; [ | | apply IHA1 ]...
  rewrite <- (app_nil_l _).
  apply tens_ilr.
  list_simpl.
  eapply ex_ir ; [ | apply perm_swap ].
  cons2app.
  apply tens_irr...
- destruct (@ax_exp_ill ipfrag_ill (negR (trans (dual A1)))) as [sA1 axA1].
  destruct (@ax_exp_ill ipfrag_ill (negR (trans (dual A2)))) as [sA2 axA2].
  eapply ex_ir in IHA1 ; [ | apply perm_swap ].
  eapply ex_ir in IHA2 ; [ | apply perm_swap ].
  apply (neg_tens_propag _ _ _ _ _ _ IHA1) in IHA2.
  destruct IHA2 as [s IHA2].
  eexists.
  eapply ex_ir ; [ | apply perm_swap ].
  apply negR_ilr...
  apply negR_irr.
  cons2app.
  rewrite <- (app_nil_l _).
  eapply cut_ir ; [ | | apply IHA2 ]...
  rewrite <- (app_nil_l _).
  apply tens_ilr.
  list_simpl.
  eapply ex_ir ; [ | apply perm_swap ].
  cons2app.
  apply tens_irr...
- eexists.
  apply negR_ilr...
  apply negR_irr.
  rewrite <- (app_nil_l _).
  apply zero_ilr.
- eexists.
  eapply ex_ir ; [ | apply perm_swap ].
  apply negR_ilr...
  apply negR_irr.
  rewrite <- (app_nil_l _).
  apply zero_ilr.
- destruct (@ax_exp_ill ipfrag_ill (negR (trans A1))) as [sA1 axA1].
  destruct (@ax_exp_ill ipfrag_ill (negR (trans A2))) as [sA2 axA2].
  apply (neg_plus_propag _ _ _ _ _ _ IHA1) in IHA2.
  destruct IHA2 as [s IHA2].
  eexists.
  apply negR_ilr...
  apply negR_irr.
  cons2app.
  rewrite <- (app_nil_l _).
  eapply cut_ir ; [ | | apply IHA2 ]...
  rewrite <- (app_nil_l _).
  apply plus_ilr.
  + list_simpl.
    apply plus_irr1...
  + list_simpl.
    apply plus_irr2...
- destruct (@ax_exp_ill ipfrag_ill (negR (trans (dual A1)))) as [sA1 axA1].
  destruct (@ax_exp_ill ipfrag_ill (negR (trans (dual A2)))) as [sA2 axA2].
  eapply ex_ir in IHA1 ; [ | apply perm_swap ].
  eapply ex_ir in IHA2 ; [ | apply perm_swap ].
  apply (neg_plus_propag _ _ _ _ _ _ IHA1) in IHA2.
  destruct IHA2 as [s IHA2].
  eexists.
  eapply ex_ir ; [ | apply perm_swap ].
  apply negR_ilr...
  apply negR_irr.
  cons2app.
  rewrite <- (app_nil_l _).
  eapply cut_ir ; [ | | apply IHA2 ]...
  rewrite <- (app_nil_l _).
  apply plus_ilr.
  + list_simpl.
    apply plus_irr1...
  + list_simpl.
    apply plus_irr2...
- eexists.
  apply negR_ilr...
  apply negR_irr.
  eapply ex_ir ; [ | apply perm_swap ].
  apply negR_ilr...
  change (ioc (negR (trans A)) :: nil)
    with (map ioc (negR (trans A) :: nil)).
  apply oc_irr.
  rewrite <- (app_nil_l _).
  apply de_ilr.
  apply negR_irr.
  eapply ex_ir ; [ | apply perm_swap ]...
- eexists.
  eapply ex_ir ; [ | apply perm_swap ].
  apply negR_ilr...
  apply negR_irr.
  eapply ex_ir ; [ | apply perm_swap ].
  apply negR_ilr...
  change (ioc (negR (trans (dual A))) :: nil)
    with (map ioc (negR (trans (dual A)) :: nil)).
  apply oc_irr.
  rewrite <- (app_nil_l _).
  apply de_ilr.
  apply negR_irr...
Qed.

Lemma trans_subs : forall A B x,
  (isubs (negR (trans B)) (a2i x) R = R) -> exists s,
  ill_ll (isubs (negR (trans B)) (a2i x) (trans A)
              :: negR (trans (subs B x A)):: nil) R s.
Proof with myeeasy.
intros A B x HR.
induction A ;
  destruct (@ax_exp_ill ipfrag_ill R) as [sR axR] ;
  destruct (@ax_exp_ill ipfrag_ill (trans B)) as [sB axB] ;
  try destruct IHA as [s0 IHA] ;
  try destruct IHA1 as [s1 IHA1] ;
  try destruct IHA2 as [s2 IHA2] ;
  simpl ; try rewrite HR.
- case_eq (ateq a x) ; intros Hateq ; eexists.
  + unfold repl_at ; rewrite Hateq ; simpl.
    assert (iateq (a2i a) (a2i x) = true) as Hiateq
      by (rewrite <- ateq_a2i ; assumption).
    unfold repl_iat ; rewrite Hiateq ; simpl.
    apply negR_ilr...
    apply negR_irr.
    eapply ex_ir ; [ | apply perm_swap ].
    apply negR_ilr...
  + case_eq (iateq (a2i a) (a2i x)) ; intros Hiateq.
    * exfalso.
      rewrite <- ateq_a2i in Hiateq.
      unfold ateq in Hateq.
      rewrite Hiateq in Hateq.
      inversion Hateq.
    * unfold repl_at ; rewrite Hateq ; simpl.
      unfold repl_iat ; rewrite Hiateq ; simpl.
      eapply ex_ir ; [ | apply perm_swap ].
      apply negR_ilr...
      apply negR_irr.
      eapply ex_ir ; [ | apply perm_swap ].
      apply negR_ilr...
      apply ax_ir.
- case_eq (ateq a x) ; intros Hateq.
  + unfold repl_at ; rewrite Hateq ; simpl.
    assert (iateq (a2i a) (a2i x) = true) as Hiateq
      by (rewrite <- ateq_a2i ; assumption).
    unfold repl_iat ; rewrite Hiateq ; simpl.
    apply trans_dual.
  + case_eq (iateq (a2i a) (a2i x)) ; intros Hiateq.
    * exfalso.
      rewrite <- ateq_a2i in Hiateq.
      unfold ateq in Hateq.
      rewrite Hiateq in Hateq.
      inversion Hateq.
    * unfold repl_at ; rewrite Hateq ; simpl.
      unfold repl_iat ; rewrite Hiateq ; simpl.
      eexists.
      eapply ex_ir ; [ | apply perm_swap ].
      apply negR_ilr...
      apply ax_ir.
- eexists.
  eapply ex_ir ; [ | apply perm_swap ].
  apply negR_ilr...
  apply negR_irr.
  eapply ex_ir ; [ | apply perm_swap ].
  apply negR_ilr...
  rewrite <- (app_nil_l _).
  apply one_ilr.
  apply one_irr.
- eexists.
  eapply ex_ir ; [ | apply perm_swap ].
  apply negR_ilr...
  rewrite <- (app_nil_l _).
  apply one_ilr.
  apply one_irr.
- eexists.
  eapply ex_ir ; [ | apply perm_swap ].
  apply negR_ilr...
  apply negR_irr.
  eapply ex_ir ; [ | apply perm_swap ].
  apply negR_ilr...
  rewrite <- (app_nil_l _).
  apply tens_ilr.
  list_simpl ; cons2app.
  apply tens_irr ; apply negR_irr...
- eapply neg_tens_propag...
- eexists.
  eapply ex_ir ; [ | apply perm_swap ].
  apply negR_ilr...
  apply negR_irr.
  rewrite <- (app_nil_l _).
  apply zero_ilr...
- eexists.
  rewrite <- (app_nil_l _).
  apply zero_ilr.
- eexists.
  eapply ex_ir ; [ | apply perm_swap ].
  apply negR_ilr...
  apply negR_irr.
  eapply ex_ir ; [ | apply perm_swap ].
  apply negR_ilr...
  rewrite <- (app_nil_l _).
  apply plus_ilr ; list_simpl.
  + apply plus_irr1.
    apply negR_irr...
  + apply plus_irr2.
    apply negR_irr...
- eapply neg_plus_propag...
- eexists.
  eapply ex_ir ; [ | apply perm_swap ].
  apply negR_ilr...
  apply negR_irr.
  eapply ex_ir ; [ | apply perm_swap ].
  apply negR_ilr...
  change (ioc (negR (trans (subs B x A))) :: nil)
    with (map ioc (negR (trans (subs B x A)) :: nil)).
  apply oc_irr.
  rewrite <- (app_nil_l _).
  apply de_ilr.
  apply negR_irr...
- eexists.
  eapply ex_ir ; [ | apply perm_swap ].
  apply negR_ilr...
  change (ioc (ilmap (ilmap (isubs (negR (trans B)) (a2i x) (trans A)) R) R) :: nil)
    with (map ioc (negR (negR (isubs (negR (trans B)) (a2i x) (trans A))) :: nil)).
  apply oc_irr.
  rewrite <- (app_nil_l _).
  apply de_ilr.
  apply negR_irr.
  list_simpl.
  eapply ex_ir ; [ | apply perm_swap ].
  apply negR_ilr...
  apply negR_irr...
Qed.


(** A provability statement [ll l] is translated as [ill (map trans l) R]. *)

(** The translation maps [ll] proofs into [ill] proofs
(under some conditions for [mix0] and [mix2]). **)

Lemma ll_to_ill_trans_gen : forall l l0 s,
  (pmix0 P = true -> exists s0, ill_ll (map ioc l0) R s0) ->
  (pmix2 P = true -> forall l1 l2 s1 s2,
    ill_ll (map ioc l0 ++ map trans l1) R s1 ->
    ill_ll (map ioc l0 ++ map trans l2) R s2 ->
      exists s0, ill_ll (map ioc l0 ++ map trans l2 ++ map trans l1) R s0) ->
  ll P l s -> exists s', ill_ll (map ioc l0 ++ map trans l) R s'.
Proof with myeeasy ; try PEperm_solve.
intros l l0 s Hmix0 Hmix2 Hll.
destruct (@ax_exp_ill ipfrag_ill R) as [sax Hax].
rewrite <- (app_nil_l (R :: _)) in Hax.
assert (Hax' := wk_list_ilr l0 _ _ _ _ Hax).
destruct Hax' as [sax' Hax'].
rewrite <- (app_nil_r (map _ _)) in Hmix0.
induction Hll ; 
  try (destruct IHHll as [s' pi']) ;
  try (destruct IHHll1 as [s1' pi1']) ;
  try (destruct IHHll2 as [s2' pi2']) ;
  try (apply Hmix0 ; myeasy ; fail) ;
  try (rewrite map_app ; eapply Hmix2 ; myeeasy ; fail) ;
  try (apply P_axfree in H ; inversion H ; fail) ;
  try (inversion f ; fail) ;
  simpl.
- eexists.
  eapply ex_ir.
  + eapply lmap_ilr ; [ | apply Hax' ].
    eapply (ax_ir _ (a2i X)).
  + PEperm_solve.
- eexists.
  simpl in H.
  rewrite P_perm in H.
  eapply ex_ir...
  apply PEperm_app_head...
  apply Permutation_map...
- eexists.
  eapply ex_ir ; [ | apply Permutation_middle ].
  rewrite <- (app_nil_l _).
  rewrite <- (app_nil_l _).
  apply lmap_ilr...
  + apply one_irr.
  + eapply ex_ir...
- eexists.
  apply one_ilr...
- apply (ex_ir _ _ (trans A :: map ioc l0 ++ map trans l1))
    in pi1'...
  apply negR_irr in pi1'.
  apply (ex_ir _ _ (trans B :: map ioc l0 ++ map trans l2))
    in pi2'...
  apply negR_irr in pi2'.
  apply (tens_irr _ _ _ _ _ _ _ pi1') in pi2'.
  apply (lmap_ilr _ _ _ _ _ _ _ _ _ pi2') in Hax.
  rewrite <- (app_nil_l (map _ _ ++ _)).
  change nil with (map ioc nil).
  rewrite <- (app_nil_l (map _ _)).
  rewrite <- app_assoc.
  eapply co_list_ilr.
  apply (ex_ir _ _ _ _ _ Hax)...
- eexists.
  apply tens_ilr...
- eexists.
  apply zero_ilr.
- eexists.
  apply (ex_ir _ _ (trans A :: map ioc l0 ++ map trans l))
    in pi'...
  apply negR_irr in pi'.
  apply (plus_irr1 _ _ (negR (trans B))) in pi'.
  apply (lmap_ilr _ _ _ _ _ _ _ _ _ pi') in Hax.
  apply (ex_ir _ _ _ _ _ Hax)...
- eexists.
  apply (ex_ir _ _ (trans A :: map ioc l0 ++ map trans l))
    in pi'...
  apply negR_irr in pi'.
  apply (plus_irr2 _ _ (negR (trans B))) in pi'.
  apply (lmap_ilr _ _ _ _ _ _ _ _ _ pi') in Hax.
  apply (ex_ir _ _ _ _ _ Hax)...
- eexists.
  apply plus_ilr...
- eexists.
  simpl in pi' ; rewrite map_map in pi'.
  simpl in pi' ; rewrite <- map_map in pi'.
  apply (ex_ir _ _ (trans A :: map ioc (l0 ++ map (fun x => (negR (negR (trans x)))) l)))
    in pi'...
  + apply negR_irr in pi'.
    apply oc_irr in pi'.
    eapply ex_ir ; [ | apply Permutation_middle ].
    apply negR_ilr...
    eapply ex_ir...
    list_simpl...
    rewrite ? map_map...
  + list_simpl...
    rewrite ? map_map...
- eexists.
  apply de_ilr...
  eapply ex_ir ; [ | apply Permutation_middle ].
  apply negR_ilr...
  apply negR_irr.
  eapply ex_ir...
- eexists.
  apply wk_ilr...
- eexists.
  rewrite <- (app_nil_l (map _ _ ++ _)).
  apply co_ilr.
  eapply ex_ir...
- apply (ex_ir _ _ (trans (dual A) :: map ioc l0 ++ map trans l1)) in pi1'...
  apply negR_irr in pi1'.
  apply (ex_ir _ _ (trans A :: map ioc l0 ++ map trans l2)) in pi2'...
  apply negR_irr in pi2'.
  destruct (trans_dual A) as [s0 pi0].
  rewrite <- (app_nil_l _) in pi0.
  eapply (cut_ir _ _ _ _ _ _ _ _ pi2') in pi0.
  list_simpl in pi0 ; rewrite app_assoc in pi0.
  eapply (cut_ir _ _ _ _ _ _ _ _ pi1') in pi0.
  change (map ioc l0) with (map ioc nil ++ map ioc l0).
  rewrite <- (app_nil_l (map ioc nil)).
  rewrite <- ? app_assoc.
  eapply co_list_ilr.
  eapply ex_ir...
Unshelve. all : reflexivity.
Qed.

Theorem ll_to_ill_trans : forall l s,
  (pmix0 P = true -> exists s0, ill_ll nil R s0) ->
  (pmix2 P = true -> forall l1 l2 s1 s2,
    ill_ll (map trans l1) R s1 ->
    ill_ll (map trans l2) R s2 ->
    exists s0, ill_ll (map trans l2 ++ map trans l1) R s0) ->
      ll P l s -> exists s', ill_ll (map trans l) R s'.
Proof with myeeasy.
intros l s Hmix0 Hmix2 Hll.
rewrite <- (app_nil_l (map _ _)).
change nil with (map ioc nil).
eapply ll_to_ill_trans_gen...
Qed.


(** In [llR] (where [bot] is equivalent to [R]),
  [A] is implied by the dual of its translation. *)
Lemma back_to_llR : forall A, exists s,
  llR (unill R) (unill (trans A) :: A :: nil) s.
Proof with myeeasy ; try ((try rewrite a2a_i) ; PCperm_solve).
induction A ; simpl ; 
  try (destruct IHA as [s IHA]) ;
  try (destruct IHA1 as [s1 IHA1]) ;
  try (destruct IHA2 as [s2 IHA2]) ;
  rewrite ? bidual.
- eexists.
  apply parr_r.
  apply (ex_r _ ((covar a :: var a :: nil) ++ unill R :: nil))...
  eapply (@cut_r (pfrag_llR (unill R)) eq_refl (dual one)).
  + apply (ex_r _ (unill R :: one :: nil))...
    apply gax_r.
    right...
  + apply bot_r.
    apply ax_r.
- eexists.
  apply (ex_r _ (covar a :: var a :: nil))...
  apply ax_r...
- eexists.
  eapply parr_r.
  apply (bot_r (pfrag_llR (unill R))).
  apply gax_r.
  right...
- eexists.
  apply (ex_r _ (bot :: one :: nil))...
  apply bot_r.
  apply one_r.
- assert (Hax := @ax_exp (pfrag_llR (unill R)) (unill R)).
  destruct Hax as [sax Hax].
  eexists.
  apply parr_r.
  apply parr_r.
  change (tens (dual (unill R)) (unill (trans A2)) ::
  tens (dual (unill R)) (unill (trans A1)) :: unill R :: tens A1 A2 :: nil)
    with (tens (dual (unill R)) (unill (trans A2)) ::  
    (tens (dual (unill R)) (unill (trans A1)) :: unill R :: tens A1 A2 :: nil) ++ nil).
  apply tens_r.
  + apply gax_r.
    left...
  + apply (ex_r _ (tens (dual (unill R)) (unill (trans A1))
             :: (unill (trans A2) :: tens A1 A2 :: nil) ++ (unill R :: nil)))...
    apply tens_r.
    -- eapply ex_r ; [ | apply perm_swap ]...
    -- apply (ex_r _ (tens A1 A2 ::
             (unill (trans A2) :: nil) ++ unill (trans A1) :: nil))...
       apply tens_r.
       ++ eapply ex_r ; [ apply IHA1 | ]...
       ++ eapply ex_r ; [ apply IHA2 | ]...
- eexists.
  apply (ex_r _ (parr A1 A2 ::
                 tens (unill (trans A1)) (unill (trans A2)) :: nil))...
  apply parr_r.
  apply (ex_r _ (tens (unill (trans A1)) (unill (trans A2))
                  :: (A2 :: nil) ++ (A1 :: nil)))...
  apply tens_r...
- eexists.
  apply parr_r.
  apply top_r.
- eexists.
  eapply ex_r ; [ | apply perm_swap ].
  eapply top_r.
- assert (Hax := @ax_exp (pfrag_llR (unill R)) (unill R)).
  destruct Hax as [sax Hax].
  eexists.
  apply parr_r.
  apply with_r.
  + apply (ex_r _ (tens (dual (unill R)) (unill (trans A1)) ::
                    (aplus A1 A2 :: nil) ++ unill R :: nil))...
    apply tens_r.
    * eapply ex_r ; [ | apply perm_swap ]...
    * eapply ex_r ; [ | apply perm_swap ].
      apply plus_r1.
      eapply ex_r ; [ | apply perm_swap ]...
  + apply (ex_r _ (tens (dual (unill R)) (unill (trans A2)) ::
                    (aplus A1 A2 :: nil) ++ unill R :: nil))...
    apply tens_r...
    * eapply ex_r ; [ | apply perm_swap ]...
    * eapply ex_r ; [ | apply perm_swap ].
      apply plus_r2.
      eapply ex_r ; [ | apply perm_swap ]...
- assert (Hax := @ax_exp (pfrag_llR (unill R)) (unill R)).
  destruct Hax as [sax Hax].
  eexists.
  eapply ex_r ; [ | apply perm_swap ].
  apply with_r.
  + eapply ex_r ; [ | apply perm_swap ].
    apply plus_r1...
  + eapply ex_r ; [ | apply perm_swap ].
    apply plus_r2...
- eexists.
  apply parr_r.
  apply (ex_r _ ((oc A ::
                  map wn (tens (dual (unill R)) (unill (trans A)) :: nil))
                  ++ unill R :: nil)) ; [idtac | simpl]...
  apply (@cut_r (pfrag_llR (unill R)) eq_refl (dual one)).
  + apply (ex_r _ (unill R :: one :: nil))...
    apply gax_r.
    right...
  + apply bot_r.
    apply oc_r ; simpl.
    apply (ex_r _ ((wn (tens (dual (unill R)) (unill (trans A))) :: nil)
                     ++ (A :: nil) ++ nil))...
    apply de_r.
    apply tens_r...
    apply gax_r.
    left...
- assert (Hax := @ax_exp (pfrag_llR (unill R)) (unill R)).
  destruct Hax as [sax Hax].
  eexists.
  change (wn A :: nil) with (map wn (A :: nil)).
  apply oc_r ; simpl.
  apply parr_r.
  apply (ex_r _ (tens (dual (unill R)) (unill (trans A)) :: (wn A :: nil) ++ unill R :: nil))...
  apply tens_r.
  + eapply ex_r...
  + apply (ex_r _ (wn A :: unill (trans A) :: nil))...
    apply de_r...
    eapply ex_r ; [ | apply perm_swap ]...
Qed.

(** The previous lemma comes with the following result from the [ll_fragments] library:
<<
Lemma ll_to_llR : forall R l s, ll_ll l s -> exists s', llR R l s'.
>> to deduce: *)

(** A sequent whose translation is provable in [ill] was provable in [llR]. *)
Lemma ill_trans_to_llR : forall l s,
  ill_ll (map trans l) R s -> exists s', llR (unill R) l s'.
Proof with myeeasy ; try PCperm_solve.
intros l s Hill.
apply (ill_to_ll i2a) in Hill.
clear s ; destruct Hill as [s Hill].
apply (stronger_pfrag _ (mk_pfrag true (fun _ => False) false false true))
  in Hill.
- eapply cut_admissible_axfree in Hill.
  + clear s ; destruct Hill as [s Hill].
    apply (ll_to_llR (unill R)) in Hill.
    clear s ; destruct Hill as [s Hill].
    assert (forall l' s',
      llR (unill R) (l' ++ map dual (map unill (map trans (rev l)))) s'
        -> exists s'', llR (unill R) (l' ++ rev l) s'') as Hll.
    { clear.
      induction l using rev_ind ; intros...
      - eexists...
      - assert (Hb := back_to_llR x).
        destruct Hb as [sb Hb].
        rewrite rev_unit in H.
       apply (ex_r _ _ (dual (unill (trans x))
                 :: l' ++ map dual (map unill (map trans (rev l))))) in H...
        apply (@cut_r _ (eq_refl (pcut (pfrag_llR (unill R)))) _ _ _ _ _ H) in Hb.
        rewrite rev_unit.
        change (x :: rev l) with ((x :: nil) ++ rev l).
        rewrite app_assoc.
        eapply IHl.
        eapply ex_r... }
    assert (exists s, llR (unill R) (dual (unill R) :: nil) s) as [sR HR].
    { eexists.
      apply gax_r.
      left... }
    apply (@cut_r _ (eq_refl (pcut (pfrag_llR (unill R)))) _ _ _ _ _ HR) in Hill.
    rewrite app_nil_r in Hill.
    rewrite <- (app_nil_l (rev _)) in Hill.
    rewrite <- ? map_rev in Hill.
    apply Hll in Hill.
    destruct Hill as [s' Hill].
    eexists.
    eapply ex_r ; [ apply Hill | ].
    symmetry.
    apply Permutation_rev.
  + intros f Hax.
    apply Hax.
- nsplit 5 ; myeasy.
  intros f Hax.
  destruct Hax as (l0 & C & _ & Hax).
  inversion Hax.
Qed.


(* ** Sufficient condition on [R] for embedding [llR] into [ill_ll]
extension of [ll_to_ill_trans] *)

(** Elementary intuitionistic formulas *)
Inductive ielem : iformula -> Prop :=
| ie_ivar : forall X, X <> atN -> ielem (ivar X)
| ie_ione : ielem ione
| ie_itens : forall A B, ielem A -> ielem B -> ielem (itens A B)
| ie_izero : ielem izero
| ie_iplus : forall A B, ielem A -> ielem B -> ielem (iplus A B)
| ie_itop : ielem itop.

Lemma ie_ie : forall A, ielem A -> exists s,
  ill_ll (A :: nil) (negR (trans (unill A))) s.
Proof.
destruct (@ax_exp_ill ipfrag_ill R) as [sR HaxR].
induction A ; intros Hgfn ; inversion Hgfn ;
  simpl ; unfold trans.
- eexists.
  unfold a2i ; unfold i2a ; rewrite (i2i_not_atN _ H0).
  apply negR_irr.
  apply negR_ilr.
  + eassumption.
  + apply ax_ir.
- destruct (@ax_exp_ill ipfrag_ill ione) as [s1 Hax1].
  eexists.
  apply negR_irr.
  apply negR_ilr ; eassumption.
- apply IHA1 in H1.
  apply IHA2 in H2.
  destruct H1 as [s1 H1].
  destruct H2 as [s2 H2].
  eexists.
  apply negR_irr.
  apply negR_ilr.
  + eassumption.
  + rewrite <- (app_nil_l _).
    apply tens_ilr.
    list_simpl ; cons2app.
    apply tens_irr ; eassumption.
- destruct (@ax_exp_ill ipfrag_ill ione) as [s1 Hax1].
  eexists.
  apply negR_irr.
  rewrite <- (app_nil_l _).
  apply zero_ilr.
- destruct (@ax_exp_ill ipfrag_ill ione) as [s1 Hax1].
  eexists.
  rewrite <- (app_nil_l _).
  apply zero_ilr.
- apply IHA1 in H1.
  apply IHA2 in H2.
  destruct H1 as [s1 H1].
  destruct H2 as [s2 H2].
  eexists.
  apply negR_irr.
  apply negR_ilr.
  + eassumption.
  + rewrite <- (app_nil_l _).
    apply plus_ilr ; constructor ; eassumption.
Qed.

Lemma ie_dual : forall A, ielem A -> exists s,
  ill_ll (trans (dual (unill A)) :: nil) A s.
Proof.
destruct (@ax_exp_ill ipfrag_ill R) as [sR HaxR].
induction A ; intros Hgfn ; inversion Hgfn ;
  simpl ; unfold trans.
- eexists.
  unfold a2i ; unfold i2a ; rewrite (i2i_not_atN _ H0).
  apply ax_ir.
- apply ax_exp_ill.
- apply IHA1 in H1.
  apply IHA2 in H2.
  destruct H1 as [s1 H1].
  destruct H2 as [s2 H2].
  eexists.
  rewrite <- (app_nil_l _).
  apply tens_ilr.
  list_simpl.
  eapply ex_ir ; [ | apply perm_swap ].
  cons2app.
  apply tens_irr ; eassumption.
- eexists ; apply top_irr.
- eexists ; rewrite <- (app_nil_l _) ; apply zero_ilr.
- apply IHA1 in H1.
  apply IHA2 in H2.
  destruct H1 as [s1 H1].
  destruct H2 as [s2 H2].
  eexists.
  rewrite <- (app_nil_l _).
  apply plus_ilr ; constructor ; eassumption.
Qed.

End RTranslation.

Lemma ie_ie_diag : forall A, ielem A -> exists s,
  ill_ll (trans A (unill A) :: A :: nil) A s.
Proof.
intros A Hgfn.
destruct (ie_ie A _ Hgfn) as [s H].
destruct (@ax_exp_ill ipfrag_ill A) as [sA HaxA].
destruct (@ax_exp_ill ipfrag_ill (trans A (unill A))) as [sA' HaxA'].
eexists.
eapply ex_ir ; [ | apply perm_swap ].
cons2app.
rewrite <- (app_nil_l _).
eapply cut_ir.
- reflexivity.
- apply H.
- apply negR_ilr ; eassumption.
Qed.

Lemma ie_dual_diag : forall A, ielem A -> exists s,
  ill_ll (trans A (dual (unill A)) :: nil) A s.
Proof.
intros A.
apply ie_dual.
Qed.

Proposition llR_ie_to_ill_trans : forall R l s, ielem R ->
  llR (unill R) l s -> exists s', ill_ll (map (trans R) l) R s'.
Proof with myeeasy ; try PEperm_solve.
intros R l s Hie Hll.
destruct (@ax_exp_ill ipfrag_ill R) as [sax Hax].
rewrite <- (app_nil_l (R :: _)) in Hax.
induction Hll ; 
  try (destruct IHHll as [s' pi']) ;
  try (destruct IHHll1 as [s1' pi1']) ;
  try (destruct IHHll2 as [s2' pi2']) ;
  try (apply Hmix0 ; myeasy ; fail) ;
  try (rewrite map_app ; eapply Hmix2 ; myeeasy ; fail) ;
  try (apply P_axfree in H ; inversion H ; fail) ;
  try (inversion f ; fail) ;
  simpl.
- eexists.
  eapply ex_ir.
  + eapply lmap_ilr ; [ | apply Hax ].
    eapply (ax_ir _ (a2i X)).
  + PEperm_solve.
- eexists.
  eapply ex_ir...
  apply Permutation_map...
- eexists.
  rewrite <- (app_nil_l _).
  rewrite <- (app_nil_l _).
  apply lmap_ilr...
  apply one_irr.
- eexists.
  rewrite <- (app_nil_l (ione :: _)).
  apply one_ilr...
- apply negR_irr in pi1'.
  apply negR_irr in pi2'.
  apply (tens_irr _ _ _ _ _ _ _ pi1') in pi2'.
  apply (lmap_ilr _ _ _ _ _ _ _ _ _ pi2') in Hax.
  eexists.
  apply (ex_ir _ _ _ _ _ Hax)...
- eexists.
  rewrite <- (app_nil_l (itens _ _ :: _)).
  apply tens_ilr...
- eexists.
  rewrite <- (app_nil_l (izero :: _)).
  apply zero_ilr.
- eexists.
  apply negR_irr in pi'.
  apply (plus_irr1 _ _ (negR R (trans R B))) in pi'.
  apply (lmap_ilr _ _ _ _ _ _ _ _ _ pi') in Hax.
  apply (ex_ir _ _ _ _ _ Hax)...
- eexists.
  apply negR_irr in pi'.
  apply (plus_irr2 _ _ (negR R (trans R B))) in pi'.
  apply (lmap_ilr _ _ _ _ _ _ _ _ _ pi') in Hax.
  apply (ex_ir _ _ _ _ _ Hax)...
- eexists.
  rewrite <- (app_nil_l (iplus _ _ :: _)).
  apply plus_ilr...
- eexists.
  simpl in pi' ; rewrite map_map in pi'.
  simpl in pi' ; rewrite <- map_map in pi'.
  apply negR_irr in pi'.
  apply oc_irr in pi'.
  apply negR_ilr...
  eapply ex_ir...
  list_simpl...
  rewrite ? map_map...
- eexists.
  rewrite <- (app_nil_l (ioc _ :: _)).
  apply de_ilr...
  eapply ex_ir ; [ | apply Permutation_middle ].
  apply negR_ilr...
  apply negR_irr.
  eapply ex_ir...
- eexists.
  rewrite <- (app_nil_l (ioc _ :: _)).
  apply wk_ilr...
- eexists.
  rewrite <- (app_nil_l (ioc _ :: _)).
  change nil with (map ioc nil).
  rewrite <- (app_nil_l (map _ _ ++ _)).
  apply co_ilr.
  eapply ex_ir...
- apply negR_irr in pi1'.
  apply negR_irr in pi2'.
  destruct (trans_dual R A) as [s0 pi0].
  rewrite <- (app_nil_l _) in pi0.
  eapply (cut_ir _ _ _ _ _ _ _ _ pi2') in pi0.
  list_simpl in pi0.
  eapply (cut_ir _ _ _ _ _ _ _ _ pi1') in pi0.
  eexists.
  eapply ex_ir...
- destruct H ; subst.
  + apply ie_dual_diag...
  + simpl.
    destruct (ie_ie_diag R Hie) as [s HR].
    eexists.
    eapply ex_ir ; [ | apply perm_swap ].
    rewrite <- 2 (app_nil_l (negR _ _ :: _)).
    apply lmap_ilr...
    * apply one_irr.
    * eapply ex_ir...
Unshelve. all : reflexivity.
Qed.


(** Ingredients for generating fresh variables *)
Definition a2n := yalla_ax.a2n.
Definition n2a := yalla_ax.n2a.
Definition n2n_a := yalla_ax.n2n_a.


(** ** Study of the case [R = bot] *)

(** Given a sequent, the following 3 statements are equivalent:
 - the translation of the sequent is provable in [ill] for any [R];
 - the sequent is provable in [llR bot];
 - the sequent is provable in [ll].
*)

Theorem ill_trans_to_llR_bot : forall l s,
  (forall R, ill_ll (map (trans R) l) R s) -> exists s', llR bot l s'.
Proof with myeeasy ; try PCperm_solve.
intros l s Hill.
remember (fresh_of_list a2n n2a l) as z.
specialize Hill with (ivar (a2i z)).
apply ill_trans_to_llR in Hill...
destruct Hill as [s' Hill].
apply (subs_llR _ bot z) in Hill ; subst.
clear s' ; destruct Hill as [s' Hill].
eexists.
simpl in Hill.
rewrite repl_at_eq in Hill...
rewrite (subs_fresh_list _ _ n2n_a) in Hill...
Qed.

Theorem llR_bot_to_ll : forall l s, llR bot l s -> exists s', ll_ll l s'.
Proof with myeeasy.
intros l s HR.
induction HR ;
  try (inversion f ; fail) ;
  try (destruct IHHR as [s' IHHR]) ;
  try (destruct IHHR1 as [s1' IHHR1]) ;
  try (destruct IHHR2 as [s2' IHHR2]) ;
  try (eexists ; constructor ; myeeasy ; fail).
- eexists.
  eapply ex_r...
- eapply cut_ll_r...
- inversion H ; subst.
  + eexists.
    apply one_r.
  + eexists.
    apply bot_r.
    apply one_r.
Qed.

Theorem ll_ll_to_ill_trans : forall R l s,
  ll_ll l s -> exists s', ill_ll (map (trans R) l) R s'.
Proof.
intros R l s Hll.
eapply ll_to_ill_trans ; myeeasy.
- intros l' Hax ; inversion Hax.
- intros f ; inversion f.
- intros f ; inversion f.
Qed.


(** ** Study of the case [R = one] *)

(** Given a sequent, the following 3 statements are equivalent:
 - the translation of the sequent is provable in [ill] for parameter [ione];
 - the sequent is provable in [llR one];
 - the sequent is provable in [ll_mix02].
*)

Lemma ill_trans_to_llR_one : forall l s,
  ill_ll (map (trans ione) l) ione s -> exists s', llR one l s'.
Proof.
apply ill_trans_to_llR.
Qed.

Theorem llR_one_to_ll_mix02 : forall l s,
  llR one l s -> exists s', ll_mix02 l s'.
Proof with myeeasy.
intros l s pi.
induction pi ;
  try (destruct IHpi as [s' pi']) ;
  try (destruct IHpi1 as [s1' pi1']) ;
  try (destruct IHpi2 as [s2' pi2']) ;
  try (eexists ; constructor ; myeeasy ; fail).
- eexists.
  eapply ex_r...
- eapply cut_mix02_r...
- destruct H ; subst.
  + eexists.
    apply bot_r.
    apply (@mix0_r _ (eq_refl (pmix0 pfrag_mix02))).
  + eexists.
    change (one :: one :: nil) with ((one :: nil) ++ (one :: nil)).
    apply (@mix2_r _ (eq_refl (pmix2 pfrag_mix02))) ;
    apply one_r.
Qed.

Theorem ll_mix02_to_ill_trans : forall l s,
  ll_mix02 l s -> exists s', ill_ll (map (trans ione) l) ione s'.
Proof with myeeasy.
intros l s Hll.
eapply ll_to_ill_trans ; myeeasy ; myeeasy.
- intros l' Hax ; inversion Hax.
- intros f.
  eexists.
  apply one_irr.
- intros f l1 l2 s1 s2 pi1 pi2.
  rewrite <- (app_nil_l (map _ l2 ++ map _ l1)).
  rewrite <- (app_nil_r (map _ l2 ++ map _ l1)).
  assert (forall l C, ~ ipgax ipfrag_ill l C)
     as I_axfree by (intros ? ? Hgax ; inversion Hgax).
  eapply (@cut_ir_nzeropos_axfree_by_ll _ i2ac_inj _ I_axfree (itens ione ione)).
  + list_simpl ; constructor.
    * constructor.
    * apply Forall_app.
      -- apply Forall_forall.
         intros x Hin.
         apply in_map_iff in Hin.
         destruct Hin as (y & Heq & _) ; subst.
         apply trans_nz.
         ++ intros Hz.
            inversion Hz.
         ++ constructor.
      -- apply Forall_forall.
         intros x Hin.
         apply in_map_iff in Hin.
         destruct Hin as (y & Heq & _) ; subst.
         apply trans_nz.
         ++ intros Hz.
            inversion Hz.
         ++ constructor.
  + apply tens_irr...
  + apply tens_ilr.
    apply one_ilr.
    apply one_ilr.
    apply one_irr.
Qed.


(** ** Study of the case [R = wn one] *)

(** Given a sequent, the following 3 statements are equivalent:
 - the translation of the sequent is provable in [ill] for any parameter [R] such that [R] is provable in [ill];
 - the sequent is provable in [llR (wn one)];
 - the sequent is provable in [ll_mix0].
*)

Theorem ill_trans_to_llR_wn_one : forall l,
  (forall R s, ill_ll nil R s -> exists s', ill_ll (map (trans R) l) R s') ->
    exists s'', llR (wn one) l s''.
Proof with myeeasy ; try PCperm_solve.
intros l Hill.
remember (fresh_of_list a2n n2a l) as z.
assert (exists s, ill_ll nil (ilpam (ioc (ivar (a2i z))) (ivar (a2i z))) s)
  as [s Hz].
{ eexists.
  apply lpam_irr.
  apply de_ilr.
  apply ax_ir. }
specialize Hill with (ilpam (ioc (ivar (a2i z))) (ivar (a2i z))) s.
assert (Hz2 := Hz).
apply Hill in Hz2 ; clear Hill.
destruct Hz2 as [s' Hill].
apply ill_trans_to_llR in Hill...
clear s' ; destruct Hill as [s' Hill].
apply (subs_llR _ bot z) in Hill ; subst.
simpl in Hill.
rewrite repl_at_eq in Hill ; try rewrite a2a_i...
clear s' ; destruct Hill as [s' Hill].
assert (Hax := @ax_exp (pfrag_llR (wn one)) (wn one)).
destruct Hax as [sax Hax].
eapply (llR1_R2 _ (wn one)) in Hill.
- clear s' ; destruct Hill as [s' Hill].
  eexists.
  rewrite (subs_fresh_list _ _ n2n_a) in Hill...
- simpl.
  rewrite <- (app_nil_l (wn _ :: _)).
  apply tens_r.
  + change (wn one :: nil) with (map wn (one :: nil)).
    apply oc_r ; simpl.
    apply bot_r.
    apply de_r.
    apply one_r.
  + apply one_r.
- simpl.
  apply (ex_r _ (parr bot (wn one) :: oc bot :: nil))...
  apply parr_r.
  apply bot_r.
  change (wn one) with (dual (oc bot))...
Qed.

Theorem llR_wn_one_to_ll_mix0 : forall l s,
  llR (wn one) l s -> exists s', ll_mix0 l s'.
Proof with myeeasy.
intros l s pi.
induction pi ;
  try (destruct IHpi as [s' pi']) ;
  try (destruct IHpi1 as [s1' pi1']) ;
  try (destruct IHpi2 as [s2' pi2']) ;
  try (eexists ; constructor ; myeeasy ; fail).
- eexists.
  eapply ex_r...
- eapply cut_mix0_r...
- destruct H ; subst.
  + eexists.
    change nil with (map wn nil).
    apply oc_r.
    apply bot_r.
    apply (@mix0_r _ (eq_refl (pmix0 pfrag_mix0))).
  + eexists.
    apply wk_r.
    apply one_r.
Qed.

Theorem ll_mix0_to_ill_trans : forall R l s0 s,
  ill_ll nil R s0 -> ll_mix0 l s -> exists s', ill_ll (map (trans R) l) R s'.
Proof with myeeasy.
intros R l s0 s HR Hll.
eapply ll_to_ill_trans ; myeeasy ; myeeasy.
- intros l' Hax ; inversion Hax.
- intros f ; eexists...
- intros f ; inversion f.
Qed.


(** ** Study of the case [R = oc bot] *)

(** Given a sequent, the following 3 statements are equivalent:
 - the translation of the sequent is provable in [ill] for any parameter [ioc R];
 - the sequent is provable in [llR (oc bot)];
 - the sequent is provable in [ll_bbb].
*)

Theorem ill_trans_to_llR_oc_bot : forall l,
  (forall R, exists s, ill_ll (map (trans (ioc R)) l) (ioc R) s) ->
  exists s', llR (oc bot) l s'.
Proof with myeeasy ; try PCperm_solve.
intros l Hill.
remember (fresh_of_list a2n n2a l) as z.
specialize Hill with (ivar (a2i z)).
destruct Hill as [s Hill].
apply ill_trans_to_llR in Hill...
clear s ; destruct Hill as [s Hill].
apply (subs_llR _ bot z) in Hill ; subst.
clear s ; destruct Hill as [s Hill].
eexists.
simpl in Hill.
rewrite repl_at_eq in Hill...
rewrite (subs_fresh_list _ _ n2n_a) in Hill...
Qed.

Theorem llR_oc_bot_to_ll_bbb : forall l s,
  llR (oc bot) l s -> exists s', ll_bbb l s'.
Proof.
apply bb_to_bbb.
Qed.

Lemma ll_mix02_to_ill_trans_gen : forall R l s,
 ll_mix02 l s -> exists s',
   ill_ll (ioc R :: map (trans (ioc R)) l) (ioc R) s'.
Proof with myeeasy.
intros R l s Hll.
assert (Hax := @ax_exp_ill ipfrag_ill (ioc R)).
destruct Hax as [sax Hax].
change (ioc R :: map (trans _) l)
  with (map ioc (R :: nil) ++ map (trans (ioc R)) l).
eapply ll_to_ill_trans_gen ; intros ; simpl...
- intro Hgax ; inversion Hgax.
- eexists...
- rewrite <- (app_nil_l (ioc R :: _)).
  rewrite <- (app_nil_r (map _ l1)).
  rewrite app_comm_cons.
  rewrite (app_assoc _ (map _ l1)).
  assert (forall l C, ~ ipgax ipfrag_ill l C)
     as I_axfree by (intros ? ? Hgax ; inversion Hgax).
  eexists.
  assert (ipcut ipfrag_ill = true) as Hcut' by (simpl ; assumption).
  apply (@cut_ir _ Hcut' (itens (ioc R) (ioc R))).
  + rewrite <- 2 (app_nil_l (ioc R :: _)).
    rewrite <- ? app_assoc.
    change nil with (map ioc nil) at 2.
    apply co_ilr.
    eapply ex_ir.
    * apply tens_irr ; [ apply H0 | apply H1 ].
    * PEperm_solve.
  + apply tens_ilr.
    apply wk_ilr...
Qed.

Theorem ll_bbb_to_ill_trans : forall R l s,
  ll_bbb l s -> exists s', ill_ll (map (trans (ioc R)) l) (ioc R) s'.
Proof with myeeasy ; try PEperm_solve.
intros R l s Hll.
destruct (@ax_exp_ill ipfrag_ill (ioc R)) as [sax Hax].
rewrite <- (app_nil_l (ioc R :: _)) in Hax.
induction Hll ; 
  try (inversion f ; fail) ;
  try (inversion H ; fail) ;
  try (destruct IHHll as [s' pi']) ;
  try (destruct IHHll1 as [s1' pi1']) ;
  try (destruct IHHll2 as [s2' pi2']) ;
  simpl.
- eexists.
  eapply ex_ir.
  + eapply lmap_ilr ; [ | apply Hax ].
    eapply (ax_ir _ (a2i X)).
  + PEperm_solve.
- eexists.
  eapply ex_ir...
  apply Permutation_map...
- apply (ll_mix02_to_ill_trans_gen R) in H.
  destruct H as [s'' H].
  rewrite <- (app_nil_l (ioc _ :: _)) in H.
  rewrite map_app.
  eexists.
  assert (ipcut ipfrag_ill = true) as Hcut by reflexivity.
  rewrite <- (app_nil_r (map _ l1)).
  apply (@cut_ir _ Hcut (ioc R))...
  eapply ex_ir ; [ | apply Permutation_app_comm ]...
- eexists.
  apply negR_ilr...
  apply one_irr.
- eexists.
  rewrite <- (app_nil_l (ione :: _)).
  apply one_ilr...
- eexists.
  apply negR_ilr...
  list_simpl.
  eapply ex_ir ; [ | apply Permutation_app_comm ].
  apply tens_irr ; apply negR_irr ; eapply ex_ir.
  + apply pi1'.
  + PEperm_solve.
  + apply pi2'.
  + PEperm_solve.
- eexists.
  rewrite <- (app_nil_l (itens _ _ :: _)).
  apply tens_ilr...
- eexists.
  rewrite <- (app_nil_l (izero :: _)).
  apply zero_ilr.
- eexists.
  apply negR_ilr...
  apply plus_irr1 ; apply negR_irr ; eapply ex_ir...
- eexists.
  apply negR_ilr...
  apply plus_irr2 ; apply negR_irr ; eapply ex_ir...
- eexists.
  rewrite <- (app_nil_r (map _ _)).
  rewrite <- (app_nil_l (iplus _ _ :: _)).
  apply plus_ilr ; eapply ex_ir ; [ apply pi1' | | apply pi2' | ]...
- eexists.
  apply negR_ilr...
  rewrite map_map ; simpl.
  rewrite <- map_map.
  simpl in pi' ; rewrite map_map in pi'.
  simpl in pi' ; rewrite <- map_map in pi'.
  apply oc_irr.
  apply negR_irr.
  eapply ex_ir...
- eexists.
  rewrite <- (app_nil_l (ioc _ :: _)).
  apply de_ilr...
  list_simpl.
  apply negR_ilr...
  apply negR_irr...
- eexists.
  rewrite <- (app_nil_l (ioc _ :: _)).
  apply wk_ilr...
- eexists.
  rewrite <- 2 (app_nil_l (ioc _ :: _)).
  change nil with (map ioc nil).
  apply co_ilr.
  eapply ex_ir...
Qed.

(** The following result is the converse of [bb_to_bbb] proved in the [bbb] library *)

Theorem bbb_to_bb : forall l s, ll_bbb l s -> exists s', llR (oc bot) l s'.
Proof.
intros l s pi.
apply ill_trans_to_llR_oc_bot.
intros R.
eapply ll_bbb_to_ill_trans ; eassumption.
Qed.


