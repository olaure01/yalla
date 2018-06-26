(* nn library for yalla *)

(* output in Type *)


(* TODO clean file *)


(** * Parametric negative translation from [ll] into [ill]. *)

Require Import Arith.
Require Import Omega.

Require Import Injective.
Require Import Bool_more.
Require Import List_more.
Require Import List_Type.
Require Import List_Type_more.
Require Import Permutation_Type_more.
Require Import Permutation_Type_solve.
Require Import genperm_Type.

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

Definition ipfrag_ill := mk_ipfrag true NoIAxioms true.
(*                                 cut  axioms    perm  *)
Definition ill_ll := ill ipfrag_ill.

Definition unill := ill2ll i2a.

(** ** The translation *)

Section RTranslation.

Context {P : pfrag}.
Hypothesis P_axfree : forall a : projT1 (pgax P), False.
Hypothesis P_perm : pperm P = true.

(** We fix the parameter [R] of the translation. *)

Variable R : iformula.
Definition negR A := ilmap A R.

Lemma negR_irr : forall A l,
  ill_ll (A :: l) R -> ill_ll l (negR A).
Proof.
intros A l pi.
apply lmap_irr.
assumption.
Qed.

Lemma negR_ilr : ill_ll (R :: nil) R ->
  forall A l, ill_ll l A -> ill_ll (negR A :: l) R.
Proof.
intros HR A l pi.
rewrite <- (app_nil_r _).
rewrite <- app_comm_cons.
eapply ex_ir ; [ | symmetry ; apply Permutation_Type_middle ].
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

Lemma trans_wn : forall l,
  map trans (map wn l)
= map ioc (map (fun x => (negR (negR (trans x)))) l).
Proof with myeasy.
induction l...
simpl ; rewrite IHl...
Qed.

Lemma trans_nz : (zeropos R -> False) -> nonzerospos R ->
  forall A, nonzerospos (trans A).
Proof with myeasy.
intros Hnz Hnzsp.
induction A ; simpl ; try now constructor ;
  try (constructor ; try assumption ; now constructor).
Qed.

Lemma neg_tens_propag : forall A1 A2 B1 B2,
  ill_ll (A1 :: negR A2 :: nil) R -> ill_ll (B1 :: negR B2 :: nil) R ->
    ill_ll (itens A1 B1 :: negR (itens A2 B2) :: nil) R.
Proof with myeeasy.
intros A1 A2 B1 B2 pi1 pi2.
cons2app.
rewrite <- (app_nil_l _).
eapply (cut_ir _ (itens (negR (negR A2)) (negR (negR B2))))...
- rewrite <- (app_nil_l _).
  apply tens_ilr.
  list_simpl ; cons2app.
  apply tens_irr ; apply lmap_irr.
  + eapply ex_ir ; [ apply pi1 | apply Permutation_Type_swap ]...
  + eapply ex_ir ; [ apply pi2 | apply Permutation_Type_swap ]...
- list_simpl.
  rewrite <- (app_nil_l _).
  apply tens_ilr.
  list_simpl.
  rewrite <- (app_nil_l (negR (itens _ _) :: _)).
  rewrite 2 app_comm_cons.
  rewrite <- (app_nil_l _).
  apply negR_ilr.
  + apply ax_exp_ill.
  + apply negR_irr.
    eapply ex_ir ; [ | apply Permutation_Type_swap ].
    apply negR_ilr...
    * apply ax_exp_ill.
    * apply negR_irr.
      cons2app.
      rewrite app_assoc.
      eapply ex_ir ; [ | apply Permutation_Type_middle ].
      list_simpl.
      apply negR_ilr...
      -- apply ax_exp_ill.
      -- eapply ex_ir ; [ | apply Permutation_Type_swap ].
         cons2app.
         apply tens_irr ; apply ax_exp_ill.
Unshelve. reflexivity.
Qed.

Lemma neg_plus_propag : forall A1 A2 B1 B2,
  ill_ll (A1 :: negR A2 :: nil) R -> ill_ll (B1 :: negR B2 :: nil) R ->
    ill_ll (iplus A1 B1 :: negR (iplus A2 B2) :: nil) R.
Proof with myeeasy.
intros A1 A2 B1 B2 pi1 pi2.
cons2app.
rewrite <- (app_nil_l _).
eapply (cut_ir _ (iplus (negR (negR A2)) (negR (negR B2))))...
- rewrite <- (app_nil_l _).
  apply plus_ilr.
  + list_simpl.
    apply plus_irr1.
    apply negR_irr.
    eapply ex_ir ; [ | apply Permutation_Type_swap ]...
  + list_simpl.
    apply plus_irr2.
    apply negR_irr.
    eapply ex_ir ; [ | apply Permutation_Type_swap ]...
- list_simpl.
  rewrite <- (app_nil_l _).
  apply plus_ilr.
  + list_simpl.
    apply negR_ilr.
    * apply ax_exp_ill.
    * apply negR_irr.
      eapply ex_ir ; [ | apply Permutation_Type_swap ].
      apply negR_ilr.
      -- apply ax_exp_ill.
      -- apply plus_irr1.
         apply ax_exp_ill.
  + list_simpl.
    apply negR_ilr.
    * apply ax_exp_ill.
    * apply negR_irr.
      eapply ex_ir ; [ | apply Permutation_Type_swap ].
      apply negR_ilr.
      -- apply ax_exp_ill.
      -- apply plus_irr2.
         apply ax_exp_ill.
Unshelve. reflexivity.
Qed.

Lemma trans_dual : forall A,
  ill_ll (negR (trans A) :: negR (trans (dual A)) :: nil) R.
Proof with myeeasy ; try now (apply ax_exp_ill).
induction A ; simpl.
- apply negR_ilr...
- eapply ex_ir ; [ | apply Permutation_Type_swap ].
  apply negR_ilr...
- apply negR_ilr...
- eapply ex_ir ; [ | apply Permutation_Type_swap ].
  apply negR_ilr...
- apply (neg_tens_propag _ _ _ _ IHA1) in IHA2.
  apply negR_ilr...
  apply negR_irr.
  cons2app.
  rewrite <- (app_nil_l _).
  eapply cut_ir ; [ | | apply IHA2 ]...
- eapply ex_ir in IHA1 ; [ | apply Permutation_Type_swap ].
  eapply ex_ir in IHA2 ; [ | apply Permutation_Type_swap ].
  apply (neg_tens_propag _ _ _ _ IHA2) in IHA1.
  eapply ex_ir ; [ | apply Permutation_Type_swap ].
  apply negR_ilr...
  apply negR_irr.
  cons2app.
  rewrite <- (app_nil_l _).
  eapply cut_ir ; [ | | apply IHA1 ]...
- apply negR_ilr...
- eapply ex_ir ; [ | apply Permutation_Type_swap ].
  apply negR_ilr...
- apply (neg_plus_propag _ _ _ _ IHA1) in IHA2.
  apply negR_ilr...
  apply negR_irr.
  cons2app.
  rewrite <- (app_nil_l _).
  eapply cut_ir ; [ | | apply IHA2 ]...
- eapply ex_ir in IHA1 ; [ | apply Permutation_Type_swap ].
  eapply ex_ir in IHA2 ; [ | apply Permutation_Type_swap ].
  apply (neg_plus_propag _ _ _ _ IHA1) in IHA2.
  eapply ex_ir ; [ | apply Permutation_Type_swap ].
  apply negR_ilr...
  apply negR_irr.
  cons2app.
  rewrite <- (app_nil_l _).
  eapply cut_ir ; [ | | apply IHA2 ]...
- apply negR_ilr...
  apply negR_irr.
  eapply ex_ir ; [ | apply Permutation_Type_swap ].
  apply negR_ilr...
  change (ioc (negR (trans A)) :: nil)
    with (map ioc (negR (trans A) :: nil)).
  apply oc_irr.
  rewrite <- (app_nil_l _).
  apply de_ilr.
  apply negR_irr.
  eapply ex_ir ; [ | apply Permutation_Type_swap ]...
- eapply ex_ir ; [ | apply Permutation_Type_swap ].
  apply negR_ilr...
  apply negR_irr.
  eapply ex_ir ; [ | apply Permutation_Type_swap ].
  apply negR_ilr...
  change (ioc (negR (trans (dual A))) :: nil)
    with (map ioc (negR (trans (dual A)) :: nil)).
  apply oc_irr.
  rewrite <- (app_nil_l _).
  apply de_ilr.
  apply negR_irr...
Qed.

Lemma trans_subs : forall A B x,
  (isubs (negR (trans B)) (a2i x) R = R) ->
  ill_ll (isubs (negR (trans B)) (a2i x) (trans A)
              :: negR (trans (subs B x A)):: nil) R.
Proof with myeeasy ; try now (apply ax_exp_ill).
intros A B x HR.
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
      eapply ex_ir ; [ | apply Permutation_Type_swap ].
      apply negR_ilr...
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
      eapply ex_ir ; [ | apply Permutation_Type_swap ].
      apply negR_ilr...
- eapply ex_ir ; [ | apply Permutation_Type_swap ].
  apply negR_ilr...
- eapply ex_ir ; [ | apply Permutation_Type_swap ].
  apply negR_ilr...
- eapply ex_ir ; [ | apply Permutation_Type_swap ].
  apply negR_ilr...
  apply negR_irr.
  eapply ex_ir ; [ | apply Permutation_Type_swap ].
  apply negR_ilr...
  rewrite <- (app_nil_l _).
  apply tens_ilr.
  list_simpl ; cons2app.
  apply tens_irr ; apply negR_irr...
- eapply neg_tens_propag...
- eapply ex_ir ; [ | apply Permutation_Type_swap ].
  apply negR_ilr...
- rewrite <- (app_nil_l _).
  apply zero_ilr.
- eapply ex_ir ; [ | apply Permutation_Type_swap ].
  apply negR_ilr...
  apply negR_irr.
  eapply ex_ir ; [ | apply Permutation_Type_swap ].
  apply negR_ilr...
  rewrite <- (app_nil_l _).
  apply plus_ilr ; list_simpl.
  + apply plus_irr1.
    apply negR_irr...
  + apply plus_irr2.
    apply negR_irr...
- eapply neg_plus_propag...
- eapply ex_ir ; [ | apply Permutation_Type_swap ].
  apply negR_ilr...
  apply negR_irr.
  eapply ex_ir ; [ | apply Permutation_Type_swap ].
  apply negR_ilr...
  change (ioc (negR (trans (subs B x A))) :: nil)
    with (map ioc (negR (trans (subs B x A)) :: nil)).
  apply oc_irr.
  rewrite <- (app_nil_l _).
  apply de_ilr.
  apply negR_irr...
- eapply ex_ir ; [ | apply Permutation_Type_swap ].
  apply negR_ilr...
  change (ioc (ilmap (ilmap (isubs (negR (trans B)) (a2i x) (trans A)) R) R) :: nil)
    with (map ioc (negR (negR (isubs (negR (trans B)) (a2i x) (trans A))) :: nil)).
  apply oc_irr.
  rewrite <- (app_nil_l _).
  apply de_ilr.
  apply negR_irr.
  list_simpl.
  eapply ex_ir ; [ | apply Permutation_Type_swap ].
  apply negR_ilr...
  apply negR_irr...
Qed.


(** A provability statement [ll l] is translated as [ill (map trans l) R]. *)

(** The translation maps [ll] proofs into [ill] proofs
(under some conditions for [mix0] and [mix2]). **)

Lemma ll_to_ill_trans_gen : forall l l0,
  (pmix0 P = true -> ill_ll (map ioc l0) R) ->
  (pmix2 P = true -> forall l1 l2,
    ill_ll (map ioc l0 ++ map trans l1) R ->
    ill_ll (map ioc l0 ++ map trans l2) R ->
      ill_ll (map ioc l0 ++ map trans l2 ++ map trans l1) R) ->
  ll P l -> ill_ll (map ioc l0 ++ map trans l) R.
Proof with myeeasy ; (try now (apply ax_exp_ill)) ; try PEperm_Type_solve.
intros l l0 Hmix0 Hmix2 Hll.
assert (Hax := @ax_exp_ill ipfrag_ill R).
rewrite <- (app_nil_l (R :: _)) in Hax.
assert (ill ipfrag_ill (nil ++ map ioc l0 ++ R :: nil) R) as Hax'.
{ apply wk_list_ilr.
  apply ax_exp_ill. }
rewrite <- (app_nil_r (map _ _)) in Hmix0.
induction Hll ; 
  (try now (apply Hmix0)) ;
  (try now (rewrite map_app ; eapply Hmix2)) ;
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
  apply Permutation_Type_map...
- eapply ex_ir ; [ | apply Permutation_Type_middle ].
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
  change nil with (map ioc nil).
  rewrite <- (app_nil_l (map _ _)).
  rewrite <- app_assoc.
  eapply co_list_ilr.
  apply (ex_ir _ _ _ _ Hax)...
- apply tens_ilr.
  eapply ex_ir...
- apply zero_ilr.
- apply (ex_ir _ _ (trans A :: map ioc l0 ++ map trans l))
    in IHHll...
  apply negR_irr in IHHll.
  apply (plus_irr1 _ _ (negR (trans B))) in IHHll.
  apply (lmap_ilr _ _ _ _ _ _ _ IHHll) in Hax.
  apply (ex_ir _ _ _ _ Hax)...
- apply (ex_ir _ _ (trans A :: map ioc l0 ++ map trans l))
    in IHHll...
  apply negR_irr in IHHll.
  apply (plus_irr2 _ _ (negR (trans B))) in IHHll.
  apply (lmap_ilr _ _ _ _ _ _ _ IHHll) in Hax.
  apply (ex_ir _ _ _ _ Hax)...
- apply plus_ilr...
- simpl in IHHll ; rewrite map_map in IHHll.
  simpl in IHHll ; rewrite <- map_map in IHHll.
  apply (ex_ir _ _ (trans A :: map ioc (l0 ++ map (fun x => (negR (negR (trans x)))) l)))
    in IHHll...
  + apply negR_irr in IHHll.
    apply oc_irr in IHHll.
    eapply ex_ir ; [ | apply Permutation_Type_middle ].
    apply negR_ilr...
    eapply ex_ir...
    list_simpl...
    rewrite ? map_map...
  + list_simpl...
    rewrite ? map_map...
- apply de_ilr...
  eapply ex_ir ; [ | apply Permutation_Type_middle ].
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
  assert (pi0 := trans_dual A).
  rewrite <- (app_nil_l _) in pi0.
  eapply (cut_ir _ _ _ _ _ _ IHHll2) in pi0.
  list_simpl in pi0 ; rewrite app_assoc in pi0.
  eapply (cut_ir _ _ _ _ _ _ IHHll1) in pi0.
  change (map ioc l0) with (map ioc nil ++ map ioc l0).
  rewrite <- (app_nil_l (map ioc nil)).
  rewrite <- ? app_assoc.
  eapply co_list_ilr.
  eapply ex_ir...
- intuition.
Unshelve. all : reflexivity.
Qed.

Theorem ll_to_ill_trans : forall l,
  (pmix0 P = true -> ill_ll nil R) ->
  (pmix2 P = true -> forall l1 l2,
    ill_ll (map trans l1) R ->
    ill_ll (map trans l2) R ->
      ill_ll (map trans l2 ++ map trans l1) R) ->
      ll P l -> ill_ll (map trans l) R.
Proof with myeeasy.
intros l Hmix0 Hmix2 Hll.
rewrite <- (app_nil_l (map _ _)).
change nil with (map ioc nil).
eapply ll_to_ill_trans_gen...
Qed.


(** In [llR] (where [bot] is equivalent to [R]),
  [A] is implied by the dual of its translation. *)
Lemma back_to_llR : forall A,
  llR (unill R) (unill (trans A) :: A :: nil).
Proof with myeeasy ; try ((try rewrite a2a_i) ; PCperm_Type_solve).
induction A ; simpl ; rewrite ? bidual.
- apply parr_r.
  apply (ex_r _ ((covar a :: var a :: nil) ++ unill R :: nil))...
  eapply (@cut_r (pfrag_llR (unill R)) eq_refl (dual one)).
  + apply (ex_r _ (unill R :: one :: nil))...
    apply (gax_r (pfrag_llR (unill R)) false).
  + apply bot_r.
    apply ax_r.
- apply (ex_r _ (covar a :: var a :: nil))...
  apply ax_r...
- eapply parr_r.
  apply (bot_r (pfrag_llR (unill R))).
  apply (gax_r (pfrag_llR (unill R)) false).
- apply (ex_r _ (bot :: one :: nil))...
  apply bot_r.
  apply one_r.
- assert (Hax := @ax_exp (pfrag_llR (unill R)) (unill R)).
  apply parr_r.
  apply parr_r.
  change (tens (dual (unill R)) (unill (trans A2)) ::
  tens (dual (unill R)) (unill (trans A1)) :: unill R :: tens A1 A2 :: nil)
    with (tens (dual (unill R)) (unill (trans A2)) ::  
    (tens (dual (unill R)) (unill (trans A1)) :: unill R :: tens A1 A2 :: nil) ++ nil).
  apply tens_r.
  + apply (gax_r (pfrag_llR (unill R)) true).
  + apply (ex_r _ (tens (dual (unill R)) (unill (trans A1))
             :: (unill (trans A2) :: tens A1 A2 :: nil) ++ (unill R :: nil)))...
    apply tens_r.
    -- eapply ex_r ; [ | apply Permutation_Type_swap ]...
    -- apply (ex_r _ (tens A1 A2 ::
             (unill (trans A2) :: nil) ++ unill (trans A1) :: nil))...
       apply tens_r.
       ++ eapply ex_r ; [ apply IHA1 | ]...
       ++ eapply ex_r ; [ apply IHA2 | ]...
- apply (ex_r _ (parr A1 A2 ::
                 tens (unill (trans A2)) (unill (trans A1)) :: nil))...
  apply parr_r.
  apply (ex_r _ (tens (unill (trans A2)) (unill (trans A1))
                  :: (A1 :: nil) ++ (A2 :: nil)))...
  apply tens_r...
- apply parr_r.
  apply top_r.
- eapply ex_r ; [ | apply Permutation_Type_swap ].
  eapply top_r.
- assert (Hax := @ax_exp (pfrag_llR (unill R)) (unill R)).
  apply parr_r.
  apply with_r.
  + apply (ex_r _ (tens (dual (unill R)) (unill (trans A1)) ::
                    (aplus A1 A2 :: nil) ++ unill R :: nil))...
    apply tens_r.
    * eapply ex_r ; [ | apply Permutation_Type_swap ]...
    * eapply ex_r ; [ | apply Permutation_Type_swap ].
      apply plus_r1.
      eapply ex_r ; [ | apply Permutation_Type_swap ]...
  + apply (ex_r _ (tens (dual (unill R)) (unill (trans A2)) ::
                    (aplus A1 A2 :: nil) ++ unill R :: nil))...
    apply tens_r...
    * eapply ex_r ; [ | apply Permutation_Type_swap ]...
    * eapply ex_r ; [ | apply Permutation_Type_swap ].
      apply plus_r2.
      eapply ex_r ; [ | apply Permutation_Type_swap ]...
- assert (Hax := @ax_exp (pfrag_llR (unill R)) (unill R)).
  eapply ex_r ; [ | apply Permutation_Type_swap ].
  apply with_r.
  + eapply ex_r ; [ | apply Permutation_Type_swap ].
    apply plus_r1...
  + eapply ex_r ; [ | apply Permutation_Type_swap ].
    apply plus_r2...
- apply parr_r.
  apply (ex_r _ ((oc A ::
                  map wn (tens (dual (unill R)) (unill (trans A)) :: nil))
                  ++ unill R :: nil)) ; [idtac | simpl]...
  apply (@cut_r (pfrag_llR (unill R)) eq_refl (dual one)).
  + apply (ex_r _ (unill R :: one :: nil))...
    apply (gax_r (pfrag_llR (unill R)) false).
  + apply bot_r.
    apply oc_r ; simpl.
    apply (ex_r _ ((wn (tens (dual (unill R)) (unill (trans A))) :: nil)
                     ++ (A :: nil) ++ nil))...
    apply de_r.
    apply tens_r...
    apply (gax_r (pfrag_llR (unill R)) true).
- assert (Hax := @ax_exp (pfrag_llR (unill R)) (unill R)).
  change (wn A :: nil) with (map wn (A :: nil)).
  apply oc_r ; simpl.
  apply parr_r.
  apply (ex_r _ (tens (dual (unill R)) (unill (trans A)) :: (wn A :: nil) ++ unill R :: nil))...
  apply tens_r.
  + eapply ex_r...
  + apply (ex_r _ (wn A :: unill (trans A) :: nil))...
    apply de_r...
    eapply ex_r ; [ | apply Permutation_Type_swap ]...
Qed.

(** The previous lemma comes with the following result from the [ll_fragments] library:
<<
Lemma ll_to_llR : forall R l, ll_ll l -> llR R l.
>> to deduce: *)

(** A sequent whose translation is provable in [ill] was provable in [llR]. *)
Lemma ill_trans_to_llR : forall l,  ill_ll (map trans l) R -> llR (unill R) l.
Proof with myeeasy ; try PCperm_Type_solve.
intros l Hill.
apply (ill_to_ll i2a) in Hill.
apply (stronger_pfrag _ (mk_pfrag true NoAxioms false false true))
  in Hill.
- eapply cut_admissible_axfree in Hill.
  + apply (ll_to_llR (unill R)) in Hill.
    assert (forall l',
      llR (unill R) (l' ++ map dual (map unill (map trans (rev l))))
        -> llR (unill R) (l' ++ rev l)) as Hll.
    { clear.
      induction l using rev_ind_Type ; intros...
      assert (Hb := back_to_llR x).
      rewrite rev_unit in X.
      apply (ex_r _ _ (dual (unill (trans x))
               :: l' ++ map dual (map unill (map trans (rev l))))) in X...
      apply (@cut_r _ (eq_refl (pcut (pfrag_llR (unill R)))) _ _ _ X) in Hb.
      rewrite rev_unit.
      change (x :: rev l) with ((x :: nil) ++ rev l).
      rewrite app_assoc.
      eapply IHl.
      eapply ex_r... }
    assert (llR (unill R) (dual (unill R) :: nil)) as HR
      by (apply (gax_r (pfrag_llR (unill R)) true)).
    apply (@cut_r _ (eq_refl (pcut (pfrag_llR (unill R)))) _ _ _ HR) in Hill.
    rewrite app_nil_r in Hill.
    rewrite <- (app_nil_l (rev _)) in Hill.
    rewrite <- ? map_rev in Hill.
    apply Hll in Hill.
    eapply ex_r ; [ apply Hill | ].
    symmetry.
    apply Permutation_Type_rev.
  + intros Hax ; inversion Hax.
- nsplit 5 ; myeasy.
  intros Hax ; inversion Hax.
Qed.


(** *** Sufficient condition on [R] for embedding [llR] into [ill_ll]

extension of [ll_to_ill_trans] *)

(** Elementary intuitionistic formulas *)
Inductive ielem : iformula -> Type :=
| ie_ivar : forall X, X <> atN -> ielem (ivar X)
| ie_ione : ielem ione
| ie_itens : forall A B, ielem A -> ielem B -> ielem (itens A B)
| ie_izero : ielem izero
| ie_iplus : forall A B, ielem A -> ielem B -> ielem (iplus A B)
| ie_itop : ielem itop.

Lemma ie_ie : forall A, ielem A ->
  ill_ll (A :: nil) (negR (trans (unill A))).
Proof with try now (apply ax_exp_ill).
induction A ; intros Hgfn ; inversion Hgfn ;
  simpl ; unfold trans.
- unfold a2i ; unfold i2a ; rewrite (i2i_not_atN _ H0).
  apply negR_irr.
  apply negR_ilr...
- apply negR_irr.
  apply negR_ilr...
- apply IHA1 in H1.
  apply IHA2 in H2.
  apply negR_irr.
  apply negR_ilr...
  rewrite <- (app_nil_l _).
  apply tens_ilr.
  list_simpl ; cons2app.
  apply tens_irr ; eassumption.
- apply negR_irr.
  rewrite <- (app_nil_l _).
  apply zero_ilr.
- rewrite <- (app_nil_l _).
  apply zero_ilr.
- apply IHA1 in H1.
  apply IHA2 in H2.
  apply negR_irr.
  apply negR_ilr...
  rewrite <- (app_nil_l _).
  apply plus_ilr ; constructor ; eassumption.
Qed.

Lemma ie_dual : forall A, ielem A ->
  ill_ll (trans (dual (unill A)) :: nil) A.
Proof with try now (apply ax_exp_ill).
induction A ; intros Hgfn ; inversion Hgfn ;
  simpl ; unfold trans...
- unfold a2i ; unfold i2a ; rewrite (i2i_not_atN _ H0)...
- apply IHA1 in H1.
  apply IHA2 in H2.
  rewrite <- (app_nil_l _).
  apply tens_ilr.
  list_simpl.
  cons2app.
  apply tens_irr ; eassumption.
- apply top_irr.
- apply IHA1 in H1.
  apply IHA2 in H2.
  rewrite <- (app_nil_l _).
  apply plus_ilr ; constructor ; eassumption.
Qed.

End RTranslation.

Lemma ie_ie_diag : forall A, ielem A ->
  ill_ll (trans A (unill A) :: A :: nil) A.
Proof.
intros A Hgfn.
eapply ex_ir ; [ | apply Permutation_Type_swap ].
cons2app.
rewrite <- (app_nil_l _).
eapply cut_ir.
- reflexivity.
- apply ie_ie.
  assumption.
- apply negR_ilr ; apply ax_exp_ill.
Qed.

Lemma ie_dual_diag : forall A, ielem A ->
  ill_ll (trans A (dual (unill A)) :: nil) A.
Proof.
intros A.
apply ie_dual.
Qed.

Proposition llR_ie_to_ill_trans : forall R l, ielem R ->
  llR (unill R) l -> ill_ll (map (trans R) l) R.
Proof with myeeasy ; try PEperm_Type_solve.
intros R l Hie Hll.
assert (Hax := @ax_exp_ill ipfrag_ill R).
rewrite <- (app_nil_l (R :: _)) in Hax.
induction Hll ; 
  (try now (apply Hmix0)) ;
  (try now (rewrite map_app ; eapply Hmix2)) ;
  (try now (apply P_axfree in H ; inversion H)) ;
  (try now (inversion f)) ;
  simpl.
- eapply ex_ir.
  + eapply lmap_ilr ; [ | apply Hax ].
    eapply (ax_ir _ (a2i X)).
  + PEperm_Type_solve.
- eapply ex_ir...
  apply Permutation_Type_map...
- rewrite <- (app_nil_l _).
  rewrite <- (app_nil_l _).
  apply lmap_ilr...
  apply one_irr.
- rewrite <- (app_nil_l (ione :: _)).
  apply one_ilr...
- apply negR_irr in IHHll1.
  apply negR_irr in IHHll2.
  apply (tens_irr _ _ _ _ _ IHHll1) in IHHll2.
  apply (lmap_ilr _ _ _ _ _ _ _ IHHll2) in Hax.
  apply (ex_ir _ _ _ _ Hax)...
- rewrite <- (app_nil_l (itens _ _ :: _)).
  apply tens_ilr.
  eapply ex_ir...
- rewrite <- (app_nil_l (izero :: _)).
  apply zero_ilr.
- apply negR_irr in IHHll.
  apply (plus_irr1 _ _ (negR R (trans R B))) in IHHll.
  apply (lmap_ilr _ _ _ _ _ _ _ IHHll) in Hax.
  apply (ex_ir _ _ _ _ Hax)...
- apply negR_irr in IHHll.
  apply (plus_irr2 _ _ (negR R (trans R B))) in IHHll.
  apply (lmap_ilr _ _ _ _ _ _ _ IHHll) in Hax.
  apply (ex_ir _ _ _ _ Hax)...
- rewrite <- (app_nil_l (iplus _ _ :: _)).
  apply plus_ilr...
- simpl in IHHll ; rewrite map_map in IHHll.
  simpl in IHHll ; rewrite <- map_map in IHHll.
  apply negR_irr in IHHll.
  apply oc_irr in IHHll.
  apply negR_ilr...
  eapply ex_ir...
  list_simpl...
  rewrite ? map_map...
- rewrite <- (app_nil_l (ioc _ :: _)).
  apply de_ilr...
  eapply ex_ir ; [ | apply Permutation_Type_middle ].
  apply negR_ilr...
  apply negR_irr.
  eapply ex_ir...
- rewrite <- (app_nil_l (ioc _ :: _)).
  apply wk_ilr...
- rewrite <- (app_nil_l (ioc _ :: _)).
  change nil with (map ioc nil).
  rewrite <- (app_nil_l (map _ _ ++ _)).
  apply co_ilr.
  eapply ex_ir...
- apply negR_irr in IHHll1.
  apply negR_irr in IHHll2.
  assert (pi0 := trans_dual R A).
  rewrite <- (app_nil_l _) in pi0.
  eapply (cut_ir _ _ _ _ _ _ IHHll2) in pi0.
  list_simpl in pi0.
  eapply (cut_ir _ _ _ _ _ _ IHHll1) in pi0.
  eapply ex_ir...
- destruct a ; subst.
  + apply ie_dual_diag...
  + simpl.
    eapply ex_ir ; [ | apply Permutation_Type_swap ].
    rewrite <- 2 (app_nil_l (negR _ _ :: _)).
    apply lmap_ilr...
    * apply one_irr.
    * eapply ex_ir.
      -- apply ie_ie_diag...
      -- PEperm_Type_solve.
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

Theorem ill_trans_to_llR_bot : forall l,
  (forall R, ill_ll (map (trans R) l) R) -> llR bot l.
Proof with myeeasy ; try PCperm_Type_solve.
intros l Hill.
remember (fresh_of_list a2n n2a l) as z.
specialize Hill with (ivar (a2i z)).
apply ill_trans_to_llR in Hill...
apply (subs_llR _ bot z) in Hill ; subst.
simpl in Hill.
rewrite repl_at_eq in Hill...
rewrite (subs_fresh_list _ _ n2n_a) in Hill...
Qed.

Theorem llR_bot_to_ll : forall l, llR bot l -> ll_ll l.
Proof with myeeasy.
intros l HR.
induction HR ;
  (try now (inversion f)) ;
  try now constructor.
- eapply ex_r...
- eapply cut_ll_r...
- destruct a.
  + apply one_r.
  + apply bot_r.
    apply one_r.
Qed.

Theorem ll_ll_to_ill_trans : forall R l,
  ll_ll l -> ill_ll (map (trans R) l) R.
Proof.
intros R l Hll.
eapply ll_to_ill_trans ; myeeasy.
- intros a ; destruct a.
- intros f ; inversion f.
- intros f ; inversion f.
Qed.


(** ** Study of the case [R = one] *)

(** Given a sequent, the following 3 statements are equivalent:
 - the translation of the sequent is provable in [ill] for parameter [ione];
 - the sequent is provable in [llR one];
 - the sequent is provable in [ll_mix02].
*)

Lemma ill_trans_to_llR_one : forall l,
  ill_ll (map (trans ione) l) ione -> llR one l.
Proof.
apply ill_trans_to_llR.
Qed.

Theorem llR_one_to_ll_mix02 : forall l, llR one l -> ll_mix02 l.
Proof with myeeasy.
intros l pi.
induction pi ; try now constructor.
- eapply ex_r...
- eapply cut_mix02_r...
- destruct a ; simpl.
  + apply bot_r.
    apply mix0_r...
  + change (one :: one :: nil) with ((one :: nil) ++ (one :: nil)).
    apply mix2_r ; try apply one_r...
Qed.

Theorem ll_mix02_to_ill_trans : forall l,
  ll_mix02 l -> ill_ll (map (trans ione) l) ione.
Proof with myeeasy.
intros l Hll.
eapply ll_to_ill_trans ; myeeasy.
- intros a ; destruct a.
- intros f.
  apply one_irr.
- intros f l1 l2 pi1 pi2.
  rewrite <- (app_nil_l (map _ l2 ++ map _ l1)).
  rewrite <- (app_nil_r (map _ l2 ++ map _ l1)).
eapply cut_ir_nzeropos_axfree_by_ll.
  + apply i2ac_inj.
  + intros ; destruct a.
  + list_simpl ; constructor.
    * constructor.
    * apply Forall_Type_app.
      -- clear ; induction l2 ; constructor...
         apply trans_nz.
         ++ intros Hz.
            inversion Hz.
         ++ constructor.
      -- clear ; induction l1 ; constructor...
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


(** ** Study of the case [R = zero] *)

(** Given a sequent, the following 2 statements are equivalent:
 - the translation of the sequent is provable in [ill] for parameter [izero];
 - the sequent is provable in [llR zero].
*)

Lemma ill_trans_to_llR_zero : forall l,
  ill_ll (map (trans izero) l) izero -> llR zero l.
Proof.
apply ill_trans_to_llR.
Qed.

Lemma llR_zero_to_ill_trans : forall l,
  llR zero l -> ill_ll (map (trans izero) l) izero.
Proof with myeeasy.
intros l pi.
eapply llR_ie_to_ill_trans...
constructor.
Qed.

(** Moreover in these systems, the general weakening rule is admissible. *)
Lemma aff_to_ill_trans : forall l A,
  ill_ll (map (trans izero) l) izero -> ill_ll (map (trans izero) (A :: l)) izero.
Proof with myeeasy.
intros l A Hll.
simpl.
cons2app.
rewrite <- (app_nil_r (map _ _)).
eapply cut_ir...
apply zero_ilr.
Qed.


(** ** Study of the case [R = wn one] *)

(** Given a sequent, the following 3 statements are equivalent:
 - the translation of the sequent is provable in [ill] for any parameter [R] such that [R] is provable in [ill];
 - the sequent is provable in [llR (wn one)];
 - the sequent is provable in [ll_mix0].
*)

Theorem ill_trans_to_llR_wn_one : forall l,
  (forall R, ill_ll nil R -> ill_ll (map (trans R) l) R) -> llR (wn one) l.
Proof with myeeasy ; try PCperm_Type_solve.
intros l Hill.
remember (fresh_of_list a2n n2a l) as z.
assert (ill_ll nil (ilpam (ioc (ivar (a2i z))) (ivar (a2i z))))
  as Hz.
{ apply lpam_irr.
  apply de_ilr.
  apply ax_ir. }
specialize Hill with (ilpam (ioc (ivar (a2i z))) (ivar (a2i z))).
assert (Hz2 := Hz).
apply Hill in Hz2 ; clear Hill.
apply ill_trans_to_llR in Hz2...
apply (subs_llR _ bot z) in Hz2 ; subst.
simpl in Hz2.
rewrite repl_at_eq in Hz2 ; try rewrite a2a_i...
eapply (llR1_R2 _ (wn one)) in Hz2.
- rewrite (subs_fresh_list _ _ n2n_a) in Hz2...
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
  change (wn one) with (dual (oc bot)).
  apply ax_exp.
Qed.

Theorem llR_wn_one_to_ll_mix0 : forall l, llR (wn one) l -> ll_mix0 l.
Proof with myeeasy.
intros l pi.
induction pi ; try now constructor.
- eapply ex_r...
- eapply cut_mix0_r...
- destruct a ; simpl.
  + change nil with (map wn nil).
    apply oc_r.
    apply bot_r.
    apply mix0_r...
  + apply wk_r.
    apply one_r.
Qed.

Theorem ll_mix0_to_ill_trans : forall R l,
  ill_ll nil R -> ll_mix0 l -> ill_ll (map (trans R) l) R.
Proof with myeeasy.
intros R l HR Hll.
eapply ll_to_ill_trans ; myeeasy.
- intros a ; destruct a.
- intros f...
- intros f ; inversion f.
Qed.


(** ** Study of the case [R = oc bot] *)

(** Given a sequent, the following 3 statements are equivalent:
 - the translation of the sequent is provable in [ill] for any parameter [ioc R];
 - the sequent is provable in [llR (oc bot)];
 - the sequent is provable in [ll_bbb].
*)

Theorem ill_trans_to_llR_oc_bot : forall l,
  (forall R, ill_ll (map (trans (ioc R)) l) (ioc R)) ->
  llR (oc bot) l.
Proof with myeeasy ; try PCperm_Type_solve.
intros l Hill.
remember (fresh_of_list a2n n2a l) as z.
specialize Hill with (ivar (a2i z)).
apply ill_trans_to_llR in Hill...
apply (subs_llR _ bot z) in Hill ; subst.
simpl in Hill.
rewrite repl_at_eq in Hill...
rewrite (subs_fresh_list _ _ n2n_a) in Hill...
Qed.

Theorem llR_oc_bot_to_ll_bbb : forall l, llR (oc bot) l -> ll_bbb l.
Proof.
apply bb_to_bbb.
Qed.

Lemma ll_mix02_to_ill_trans_gen : forall R l,
 ll_mix02 l -> ill_ll (ioc R :: map (trans (ioc R)) l) (ioc R).
Proof with myeeasy.
intros R l Hll.
change (ioc R :: map (trans _) l)
  with (map ioc (R :: nil) ++ map (trans (ioc R)) l).
eapply ll_to_ill_trans_gen ; intros ; simpl...
- destruct a.
- apply ax_exp_ill.
- rewrite <- (app_nil_l (ioc R :: _)).
  rewrite <- (app_nil_r (map _ l1)).
  rewrite app_comm_cons.
  rewrite (app_assoc _ (map _ l1)).
eapply (cut_ir _ (itens (ioc R) (ioc R))).
  + rewrite <- 2 (app_nil_l (ioc R :: _)).
    rewrite <- ? app_assoc.
    change nil with (map ioc nil) at 2.
    apply co_ilr.
    eapply ex_ir.
    * apply tens_irr ; [ apply X | apply X0 ].
    * PEperm_Type_solve.
  + apply tens_ilr.
    apply wk_ilr.
    apply ax_exp_ill.
Unshelve. reflexivity.
Qed.

Theorem ll_bbb_to_ill_trans : forall R l,
  ll_bbb l -> ill_ll (map (trans (ioc R)) l) (ioc R).
Proof with myeeasy ; try PEperm_Type_solve ; try now (apply ax_exp_ill).
intros R l Hll.
(*
destruct (@ax_exp_ill ipfrag_ill (ioc R)) as [sax Hax].
rewrite <- (app_nil_l (ioc R :: _)) in Hax.
*)
induction Hll ; (try now (inversion f)) ; simpl.
- eapply ex_ir.
  + eapply lmap_ilr ; [ | ].
    * eapply (ax_ir _ (a2i X)).
    * rewrite app_nil_l...
  + PEperm_Type_solve.
- eapply ex_ir...
  apply Permutation_Type_map...
- apply (ll_mix02_to_ill_trans_gen R) in l.
  rewrite <- (app_nil_l (ioc _ :: _)) in l.
  rewrite map_app.
  assert (ipcut ipfrag_ill = true) as Hcut by reflexivity.
  rewrite <- (app_nil_r (map _ l1)).
  apply (@cut_ir _ Hcut (ioc R))...
  eapply ex_ir ; [ | apply Permutation_Type_app_comm ]...
- apply negR_ilr...
  apply one_irr.
- rewrite <- (app_nil_l (ione :: _)).
  apply one_ilr...
- apply negR_ilr...
  list_simpl.
  eapply ex_ir ; [ | apply Permutation_Type_app_comm ].
  apply tens_irr ; apply negR_irr ; eapply ex_ir.
  + apply IHHll1.
  + PEperm_Type_solve.
  + apply IHHll2.
  + PEperm_Type_solve.
- rewrite <- (app_nil_l (itens _ _ :: _)).
  apply tens_ilr.
  eapply ex_ir...
- rewrite <- (app_nil_l (izero :: _)).
  apply zero_ilr.
- apply negR_ilr...
  apply plus_irr1 ; apply negR_irr ; eapply ex_ir...
- apply negR_ilr...
  apply plus_irr2 ; apply negR_irr ; eapply ex_ir...
- rewrite <- (app_nil_r (map _ _)).
  rewrite <- (app_nil_l (iplus _ _ :: _)).
  apply plus_ilr ; eapply ex_ir ; [ apply IHHll1 | | apply IHHll2 | ]...
- apply negR_ilr...
  rewrite map_map ; simpl.
  rewrite <- map_map.
  simpl in IHHll ; rewrite map_map in IHHll.
  simpl in IHHll ; rewrite <- map_map in IHHll.
  apply oc_irr.
  apply negR_irr.
  eapply ex_ir...
- rewrite <- (app_nil_l (ioc _ :: _)).
  apply de_ilr...
  list_simpl.
  apply negR_ilr...
  apply negR_irr...
- rewrite <- (app_nil_l (ioc _ :: _)).
  apply wk_ilr...
- rewrite <- 2 (app_nil_l (ioc _ :: _)).
  change nil with (map ioc nil).
  apply co_ilr.
  eapply ex_ir...
Qed.

(** The following result is the converse of [bb_to_bbb] proved in the [bbb] library *)

Theorem bbb_to_bb : forall l, ll_bbb l -> llR (oc bot) l.
Proof.
intros l pi.
apply ill_trans_to_llR_oc_bot.
intros R.
apply ll_bbb_to_ill_trans ; eassumption.
Qed.


