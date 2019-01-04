(* ll_cut library for yalla *)

(** * Cut elimination for [ll] from cut elimination for [ill] *)


Require Import Arith.

Require Import List_more.
Require Import Permutation_Type_more.
Require Import Permutation_Type_solve.
Require Import genperm_Type.

Require Export ll_def.
Require Import ll_mix.
Require Import subs.
Require Import ill_cut.
Require Import nn_def.



(** Ingredients for generating fresh variables *)
Definition a2n := yalla_ax.a2n.
Definition n2a := yalla_ax.n2a.
Definition n2n_a := yalla_ax.n2n_a.


Section CutElimTransfer.

Variable P : pfrag.
Hypothesis Hnogax : projT1 (pgax P) -> False.
Hypothesis Hperm : pperm P = true.  (* TODO generalize to the cyclic case *)

Theorem cut_elim_no_mix : pmix0 P = false -> pmix2 P = false -> forall A l1 l2,
ll P (dual A :: l1) -> ll P (A :: l2) -> ll P (l2 ++ l1).
Proof with myeasy.
intros Hmix0 Hmix2.
intros A l1 l2 pi1 pi2.
apply (stronger_pfrag _ _ (cutupd_pfrag_true _)) in pi1.
apply (stronger_pfrag _ _ (cutupd_pfrag_true _)) in pi2.
pose (nat_fresh_of_list a2n ((rev l1 ++ rev l2))) as z.
apply (ll_to_ill_trans (ivar (a2i (n2a z)))) in pi1 ;
  [ | assumption | simpl ; intros f ; rewrite f in Hmix0 ; inversion Hmix0
                 | simpl ; intros f ; rewrite f in Hmix2 ; inversion Hmix2 ].
apply (ll_to_ill_trans (ivar (a2i (n2a z)))) in pi2 ;
  [ | assumption | simpl ; intros f ; rewrite f in Hmix0 ; inversion Hmix0
                 | simpl ; intros f ; rewrite f in Hmix2 ; inversion Hmix2 ].
simpl in pi1 ; simpl in pi2.
apply negR_irr in pi1.
apply negR_irr in pi2.
assert (ipperm (cutupd_ipfrag (p2ipfrag (ivar (a2i (n2a z))) P) true) = true) as Hperm'
  by (simpl ; rewrite Hperm ; reflexivity).
assert (pi0 := trans_dual (ivar (a2i (n2a z))) Hperm' eq_refl A).
rewrite <- (app_nil_l _) in pi0.
eapply (cut_ir _ _ _ _ _ _ pi2) in pi0.
list_simpl in pi0.
eapply (cut_ir _ _ _ _ _ _ pi1) in pi0.
apply cut_admissible_ill in pi0 ; try (intros a ; exfalso ; apply (Hnogax a)).
apply (ill_to_ll i2a) in pi0.
list_simpl in pi0.
apply (subs_ll bot (n2a z)) in pi0.
list_simpl in pi0.
rewrite repl_at_eq in pi0 ; [ | rewrite a2a_i ; reflexivity ].
apply (ax_gen _ P) in pi0...
- rewrite <- app_nil_l in pi0.
  eapply bot_rev_axat in pi0 ; [ | intros a ; exfalso ; apply (Hnogax a) | reflexivity ]...
  list_simpl in pi0.
  apply (ex_r _ (rev l1 ++ rev l2)) ;
    [ | rewrite Hperm ; 
        rewrite <- rev_app_distr ;
        symmetry ; apply Permutation_Type_rev ].
  eapply munit_elim ; [ intros a ; exfalso ; apply (Hnogax a) | exact pi0 | ]...
  rewrite <- ? map_app.
  remember (rev l1 ++ rev l2) as l ; clear.
  assert (HF : Forall (fun x : formula => nat_fresh_of a2n x <= z) l).
  { assert (Hle : nat_fresh_of_list a2n l <= z)
      by (unfold z ; unfold nat_fresh_of_list ; list_simpl ; myeasy).
    clearbody z ; revert Hle ; clear.
    unfold nat_fresh_of_list.
    revert z ; induction l ; intros z Hle ; constructor.
    - simpl in Hle...
    - apply IHl ; simpl in Hle... }
  clearbody z ; revert HF ; induction l ; intros HF ; constructor.
  + rewrite <- (yalla_ax.a2a_n z).
    apply munit_trans.
    rewrite yalla_ax.a2a_n.
    inversion HF ; simpl...
  + apply IHl.
    inversion HF ; subst ; assumption.
- intros a ; exfalso ; apply (Hnogax a).
Unshelve. all: reflexivity.
Qed.

Lemma cut_elim_with_wn : pmix0 P = false -> pmix2 P = false -> forall A l1 l2 l0,
  ll P (dual A :: l1 ++ map wn l0) -> ll P (A :: l2 ++ map wn l0) ->
  ll P (l2 ++ l1 ++ map wn l0).
Proof with myeeasy.
intros Hmix0 Hmix2.
intros A l1 l2 l0 pi1 pi2.
eapply ex_r ; [ | rewrite Hperm ; rewrite app_assoc ; apply Permutation_Type_app_swap ].
apply co_list_r.
eapply ex_r ; [ | rewrite Hperm ; apply Permutation_Type_app_swap ].
list_simpl ; rewrite app_assoc.
eapply cut_elim_no_mix...
eapply ex_r...
rewrite Hperm ; simpl ; perm_Type_solve.
Qed.

End CutElimTransfer.


Section CutElimTransfer2.

Variable P : pfrag.
Hypothesis Hnogax : projT1 (pgax P) -> False.
Hypothesis Hperm : pperm P = true.  (* TODO generalize to the cyclic case *)

Theorem cut_elim_mix0 : pmix0 P = true -> pmix2 P = false -> forall A l1 l2,
  ll P (dual A :: l1) -> ll P (A :: l2) -> ll P (l2 ++ l1).
Proof with myeeasy.
intros Hmix0 Hmix2.
intros A l1 l2 pi1 pi2.
pose (Q := mk_pfrag P.(pcut) P.(pgax) false P.(pmix2) true).
assert (P = mix0add_pfrag Q) as HP.
{ destruct P ; unfold mix0add_pfrag ; simpl.
  simpl in Hmix0 ; rewrite Hmix0.
  simpl in Hperm ; rewrite Hperm... }
rewrite HP in pi1.
apply mix0_to_ll in pi1...
rewrite HP in pi2.
apply mix0_to_ll in pi2...
eapply ex_r in pi1 ; [ | apply Permutation_Type_cons_append ].
rewrite <- app_comm_cons in pi1.
eapply ex_r in pi2 ; [ | apply Permutation_Type_cons_append ].
rewrite <- app_comm_cons in pi2.
rewrite HP.
apply ll_to_mix0...
- intros a ; exfalso ; apply (Hnogax a).
- apply (ex_r _ (l2 ++ l1 ++ map wn (one :: nil))) ; [ | simpl ; perm_Type_solve ].
  eapply cut_elim_with_wn...
Qed.

Theorem cut_elim_mix2 : pmix0 P = false -> pmix2 P = true -> forall A l1 l2,
  ll P (dual A :: l1) -> ll P (A :: l2) -> ll P (l2 ++ l1).
Proof with myeeasy.
intros Hmix0 Hmix2.
intros A l1 l2 pi1 pi2.
pose (Q := mk_pfrag P.(pcut) P.(pgax) P.(pmix0) false true).
assert (P = mix2add_pfrag Q) as HP.
{ destruct P ; unfold mix2add_pfrag ; simpl.
  simpl in Hmix2 ; rewrite Hmix2.
  simpl in Hperm ; rewrite Hperm... }
rewrite HP in pi1.
apply mix2_to_ll in pi1...
rewrite HP in pi2.
apply mix2_to_ll in pi2...
eapply ex_r in pi1 ; [ | apply Permutation_Type_cons_append ].
rewrite <- app_comm_cons in pi1.
eapply ex_r in pi2 ; [ | apply Permutation_Type_cons_append ].
rewrite <- app_comm_cons in pi2.
rewrite HP.
apply ll_to_mix2...
- intros a ; exfalso ; apply (Hnogax a).
- apply (ex_r _ (l2 ++ l1 ++ map wn (tens bot bot :: nil))) ; [ | simpl ; perm_Type_solve ].
  eapply cut_elim_with_wn...
Qed.

Theorem cut_elim_mix02 : pmix0 P = true -> pmix2 P = true -> forall A l1 l2,
  ll P (dual A :: l1) -> ll P (A :: l2) -> ll P (l2 ++ l1).
Proof with myeeasy.
intros Hmix0 Hmix2.
intros A l1 l2 pi1 pi2.
pose (Q := mk_pfrag P.(pcut) P.(pgax) false false true).
assert (P = mix2add_pfrag (mix0add_pfrag Q)) as HP.
{ destruct P ; unfold mix2add_pfrag ; simpl.
  simpl in Hmix0 ; rewrite Hmix0.
  simpl in Hmix2 ; rewrite Hmix2.
  simpl in Hperm ; rewrite Hperm... }
rewrite HP in pi1.
apply (@mix02_to_ll' Q) in pi1...
rewrite HP in pi2.
apply (@mix02_to_ll' Q) in pi2...
eapply ex_r in pi1 ; [ | apply Permutation_Type_cons_append ].
rewrite <- app_comm_cons in pi1.
eapply ex_r in pi1 ; [ | apply Permutation_Type_cons_append ].
list_simpl in pi1.
eapply ex_r in pi2 ; [ | apply Permutation_Type_cons_append ].
rewrite <- app_comm_cons in pi2.
eapply ex_r in pi2 ; [ | apply Permutation_Type_cons_append ].
list_simpl in pi2.
rewrite HP.
apply ll_to_mix02...
- intros a ; exfalso ; apply (Hnogax a).
- apply (ex_r _ (l2 ++ l1 ++ map wn (one :: tens bot bot :: nil))) ; [ | simpl ; perm_Type_solve ].
  eapply cut_elim_with_wn...
Qed.


Theorem cut_elim_perm : forall A l1 l2,
  ll P (dual A :: l1) -> ll P (A :: l2) -> ll P (l2 ++ l1).
Proof with myeasy.
case_eq (pcut P) ; intros Hcut.
- apply cut_r...
- case_eq (pmix0 P) ; case_eq (pmix2 P) ; intros Hmix2 Hmix0.
  + apply cut_elim_mix02...
  + apply cut_elim_mix0...
  + apply cut_elim_mix2...
  + apply cut_elim_no_mix...
Qed.

End CutElimTransfer2.

(*
Axiom cut_elim_cyclic :
  forall P, pperm P = false ->
  forall P_gax_atomic : forall a, Forall atomic (projT2 (pgax P) a),
  (forall a l, PCperm_Type (pperm P) (projT2 (pgax P) a) l -> exists b, l = projT2 (pgax P) b) ->
  (forall a b x l1 l2 l3, projT2 (pgax P) a = (dual x :: l1) -> projT2 (pgax P) b = (l2 ++ x :: l3) ->
     exists c, projT2 (pgax P) c = l2 ++ l1 ++ l3) ->
  forall A l1 l2 l3,
  ll P (dual A :: l1) -> ll P (l2 ++ A :: l3) -> ll P (l2 ++ l1 ++ l3).

Theorem cut_elim :
  forall P,
  forall P_gax_atomic : forall a, Forall atomic (projT2 (pgax P) a),
  (forall a l, PCperm_Type (pperm P) (projT2 (pgax P) a) l -> exists b, l = projT2 (pgax P) b) ->
  (forall a b x l1 l2 l3, projT2 (pgax P) a = (dual x :: l1) -> projT2 (pgax P) b = (l2 ++ x :: l3) ->
     exists c, projT2 (pgax P) c = l2 ++ l1 ++ l3) ->
  forall A l1 l2 l3,
  ll P (dual A :: l1) -> ll P (l2 ++ A :: l3) -> ll P (l2 ++ l1 ++ l3).
Proof.
intros P.
case_eq (pperm P).
- intros Hperm Hgax_at Hgax_ex Hgax_cut A l1 l2 l3 pi1 pi2.
  eapply ex_r in pi2 ; [ | rewrite Hperm ; apply Permutation_Type_app_swap ].
  rewrite <- app_comm_cons in pi2.
  eapply ex_r ; [ | rewrite Hperm ; apply Permutation_Type_app_rot ].
  rewrite app_assoc.
  refine (cut_elim_perm _ _ _ _ _ A _ _ _ _) ; try assumption.
  rewrite Hperm ; assumption.
- intros Hperm Hgax_at Hgax_ex Hgax_cut A l1 l2 l3 pi1 pi2.
  refine (cut_elim_cyclic _ _ _ _ _ A _ _ _ _ _) ; try assumption.
  rewrite Hperm ; assumption.
Qed.
*)

Axiom cut_elim :
  forall P,
  forall P_gax_atomic : forall a, Forall atomic (projT2 (pgax P) a),
  (forall a l, PCperm_Type (pperm P) (projT2 (pgax P) a) l -> exists b, l = projT2 (pgax P) b) ->
  (forall a b x l1 l2 l3, projT2 (pgax P) a = (dual x :: l1) -> projT2 (pgax P) b = (l2 ++ x :: l3) ->
     exists c, projT2 (pgax P) c = l2 ++ l1 ++ l3) ->
  forall A l1 l2 l3,
  ll P (dual A :: l1) -> ll P (l2 ++ A :: l3) -> ll P (l2 ++ l1 ++ l3).

