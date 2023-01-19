(* subs library for yalla *)


(** * Substitutions in Linear Logic formulas and proofs *)

From OLlibs Require Import infinite List_more Permutation_Type GPermutation_Type Dependent_Forall_Type.
From Yalla Require Export ll_def.

Set Implicit Arguments.


Section Atoms.

Context {atom : DecType}.
Notation formula := (@formula atom).

Definition ateq := @eqb atom.
Definition ateq_eq := @eqb_eq atom.

(** ** Substitutions *)

(** basic operation for substitution of atoms *)
Definition repl_at x y A := if ateq x y then A else var x.

Lemma repl_at_eq x y A : x = y -> repl_at x y A = A.
Proof. intros ->. unfold repl_at. rewrite (proj2 (ateq_eq _ _) (eq_refl _)). reflexivity. Qed.

Lemma repl_at_neq x y A : x <> y -> repl_at x y A = var x.
Proof.
intros Hneq. unfold repl_at.
destruct (ateq x y) eqn:Heqb; [ | reflexivity ].
exfalso. rewrite ateq_eq in Heqb. contradiction Heqb.
Qed.

(** Substitution in [formula]: substitutes [x] by [C] in [A] *)
Fixpoint subs C x A :=
match A with
| var y     => repl_at y x C
| covar y   => dual (repl_at y x C)
| one       => one
| bot       => bot
| tens A B  => tens (subs C x A) (subs C x B)
| parr A B  => parr (subs C x A) (subs C x B)
| zero      => zero
| top       => top
| aplus A B => aplus (subs C x A) (subs C x B)
| awith A B => awith (subs C x A) (subs C x B)
| oc A      => oc (subs C x A)
| wn A      => wn (subs C x A)
end.

Lemma subs_refl x A : subs (var x) x A = A.
Proof.
induction A as [ a | a | | | | | | | | | | ]; cbn; rewrite ?IHA, ?IHA1, ?IHA2; try reflexivity.
- destruct (eq_dt_dec a x) eqn:Heq.
  + rewrite repl_at_eq by assumption. subst. reflexivity.
  + rewrite repl_at_neq by assumption. reflexivity.
- destruct (eq_dt_dec a x) eqn:Heq.
  + rewrite repl_at_eq by assumption. subst. reflexivity.
  + rewrite repl_at_neq by assumption. reflexivity.
Qed.

Lemma subs_dual A C x : subs C x (dual A) = dual (subs C x A).
Proof. induction A; cbn; rewrite ? bidual, ? IHA, ? IHA1, ? IHA2; reflexivity. Qed.

(** Parallel substitution in [formula] with distinguished substitution for positive and negative atoms *)
Fixpoint psubs2 (sl sr : atom -> formula) (A : formula) :=
match A with
| var x     => sl x
| covar x   => dual (sr x)
| one       => one
| bot       => bot
| tens A B  => tens (psubs2 sl sr A) (psubs2 sl sr B)
| parr A B  => parr (psubs2 sl sr A) (psubs2 sl sr B)
| zero      => zero
| top       => top
| aplus A B => aplus (psubs2 sl sr A) (psubs2 sl sr B)
| awith A B => awith (psubs2 sl sr A) (psubs2 sl sr B)
| oc A      => oc (psubs2 sl sr A)
| wn A      => wn (psubs2 sl sr A)
end.

Lemma dual_psubs2 sl sr A : dual (psubs2 sl sr A) = psubs2 sr sl (dual A).
Proof. induction A; cbn; rewrite ? IHA, ? IHA1, ? IHA2, ?bidual; reflexivity. Qed.

Lemma psubs2_var A : psubs2 var var A = A.
Proof. induction A; cbn; rewrite ? IHA, ? IHA1, ? IHA2; reflexivity. Qed.

Lemma psubs2_comp rl rr sl sr A :
  psubs2 rl rr (psubs2 sl sr A) = psubs2 (fun x => psubs2 rl rr (sl x)) (fun x => psubs2 rr rl (sr x)) A.
Proof. induction A; cbn; rewrite ? IHA, ? IHA1, ? IHA2, ? dual_psubs2; reflexivity. Qed.

Lemma subs_psubs2 C x A : subs C x A = psubs2 (fun y => repl_at y x C) (fun y => repl_at y x C) A.
Proof. induction A; cbn; rewrite ? IHA, ? IHA1, ? IHA2; reflexivity. Qed.


(** Monotony of connectives *)

(* With restriction to occurring atoms *)
Lemma psubs2_monot_loc P A sl sr :
  Forall_inf (fun x => ll P (sl x :: dual (sr x) :: nil)) (atom_list A) ->
  ll P (psubs2 sl sr A :: psubs2 sl sr (dual A) :: nil).
Proof.
induction A; cbn; intros Hfv.
- inversion Hfv. assumption.
- ll_swap. inversion Hfv. assumption.
- ll_swap. apply bot_r, one_r.
- apply bot_r, one_r.
- ll_swap. apply parr_r.
  cons2app. eapply ex_r; [ | apply PCPermutation_Type_app_rot ].
  rewrite app_assoc. apply tens_r.
  + apply Forall_inf_app_l in Hfv.
    apply IHA1. assumption.
  + apply Forall_inf_app_r in Hfv.
    apply IHA2. assumption.
- apply parr_r.
  cons2app. eapply ex_r; [ | apply PCPermutation_Type_app_rot ].
  rewrite app_assoc. apply tens_r.
  + apply Forall_inf_app_r in Hfv.
    specialize (IHA2 Hfv). ll_swap in IHA2. assumption.
  + apply Forall_inf_app_l in Hfv.
    specialize (IHA1 Hfv). ll_swap in IHA1. assumption.
- ll_swap. apply top_r.
- apply top_r.
- eapply plus_r1 in IHA1; [ | eapply Forall_inf_app_l, Hfv ]. ll_swap in IHA1.
  eapply plus_r2 in IHA2; [ | eapply Forall_inf_app_r, Hfv ]. ll_swap in IHA2.
  ll_swap. apply with_r; eassumption.
- apply with_r; ll_swap; [ apply plus_r1 | apply plus_r2 ]; ll_swap.
  + eapply IHA1, Forall_inf_app_l, Hfv.
  + eapply IHA2, Forall_inf_app_r, Hfv.
- change (ll P (oc (psubs2 sl sr A) :: map wn (psubs2 sl sr (dual A) :: nil))).
  apply oc_r.
  specialize (IHA Hfv). ll_swap in IHA.
  cbn. ll_swap. apply de_r. assumption.
- apply de_r in IHA; [ | assumption ]. ll_swap in IHA.
  ll_swap.
  change (ll P (oc (psubs2 sl sr (dual A)) :: map wn (psubs2 sl sr A :: nil))).
  apply oc_r. assumption.
Qed.

Lemma psubs2_monot P sl sr (Hs : forall x, ll P (sl x :: dual (sr x) :: nil)) A :
  ll P (psubs2 sl sr A :: psubs2 sl sr (dual A) :: nil).
Proof. apply psubs2_monot_loc, forall_Forall_inf. intros ? _. apply Hs. Qed.

Lemma ax_exp_from_monot P (A : formula) : ll P (A :: dual A :: nil).
Proof. rewrite <- (psubs2_var A), dual_psubs2. apply psubs2_monot. intro. ll_swap. apply ax_r. Qed.


(** Substitution in proofs *)

Lemma subs_ll P A x l :
  (forall C, Bool.le (pcut P C) (pcut P (subs A x C))) ->
  ll P l ->
    ll (axupd_pfrag P (existT (fun x => x -> list formula) _
                            (fun a => map (subs A x) (projT2 (pgax P) a))))
       (map (subs A x) l).
Proof.
intros Hcut pi.
assert (forall l, map (subs A x) (map wn l) = map wn (map (subs A x) l)) as Hmapwn
  by (clear; induction l; [ | cbn; rewrite IHl ]; reflexivity).
induction pi using ll_nested_ind; list_simpl; try (constructor; assumption).
- eapply ex_r; [ apply ax_exp | apply PCPermutation_Type_swap ].
- eapply PCPermutation_Type_map in p.
  eapply ex_r; eassumption.
- rewrite ? map_app, Hmapwn in IHpi. rewrite Hmapwn.
  eapply Permutation_Type_map in p.
  eapply ex_wn_r; eassumption.
- rewrite concat_map. apply mix_r.
  + cbn. rewrite map_length. assumption.
  + apply forall_Forall_inf.
    intros l' Hin.
    destruct (in_inf_map_inv (map (subs A x)) L l' Hin) as [l0 <- Hin'].
    apply (In_Forall_inf_in _ PL) in Hin' as [pi' Hin'].
    refine (Dependent_Forall_inf_forall_formula _ _ X Hin').
- specialize Hmapwn with l.
  rewrite Hmapwn. apply oc_r. rewrite <- Hmapwn. assumption.
- refine (cut_r (subs A x A0) _ _ _); [ | rewrite <- subs_dual; assumption | assumption ].
  specialize (Hcut A0).
  eapply Bool.implb_true_iff, f. apply Bool.le_implb, Hcut.
- apply (@gax_r _ (axupd_pfrag P (existT (fun x => x -> _) _
                                         (fun a => map (subs A x) (projT2 (pgax P) a)))) a).
Qed.

Lemma subs_ll_axfree P (P_axfree : notT (projT1 (pgax P))) A x l : (forall C, Bool.le (pcut P C) (pcut P (subs A x C))) ->
  ll P l -> ll P (map (subs A x) l).
Proof.
intros Hcut pi.
apply (subs_ll A x) in pi; [ | assumption ].
eapply stronger_pfrag; [ | eassumption ].
repeat split; try reflexivity. intro. contradiction P_axfree.
Qed.

End Atoms.


(** ** Fresh atoms and associated properties *)

Section InfAtoms.

Context {atom : InfDecType}.
Notation formula := (@formula atom).

(** Provide an [Atom] which is fresh for [A] *)
Definition fresh_of (A : formula) := fresh (atom_list A).

Lemma subs_fresh_incl C lat (A : formula) :
  incl (atom_list A) lat -> subs C (fresh lat) A = A.
Proof.
induction A; cbn; intros Hincl;
  rewrite ? IHA, ? IHA1, ? IHA2;
  cbn; trivial;
  try now apply incl_app_inv in Hincl.
all: rewrite repl_at_neq; [ reflexivity | intros -> ].
all: apply (fresh_prop lat), (Hincl (fresh lat)).
all: left; reflexivity.
Qed.

Lemma subs_fresh C A : subs C (fresh_of A) A = A.
Proof. apply subs_fresh_incl. intro. exact id. Qed.

(** Provide an [Atom] which is fresh for all elements of [l] *)
Definition fresh_of_list (l : list formula) := fresh (flat_map atom_list l).

Lemma subs_fresh_list_incl C lat (l : list formula) : incl (flat_map atom_list l) lat -> map (subs C (fresh lat)) l = l.
Proof.
induction l as [|a l IHl]; cbn; intros Hincl; [ reflexivity | ].
apply incl_app_inv in Hincl.
now rewrite subs_fresh_incl; [ rewrite IHl | ].
Qed.

Lemma subs_fresh_list C l : map (subs C (fresh_of_list l)) l = l.
Proof. apply subs_fresh_list_incl. intro. exact id. Qed.

End InfAtoms.
