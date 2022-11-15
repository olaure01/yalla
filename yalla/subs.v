(* subs library for yalla *)


(** * Substitutions in Linear Logic formulas and proofs *)

From OLlibs Require Import infinite List_more Permutation_Type GPermutation_Type
                           Dependent_Forall_Type.
From Yalla Require Export ll_def.

Set Implicit Arguments.


Section Atoms.

Context {atom : DecType}.

Definition ateq := @eqb atom.
Definition ateq_eq := @eqb_eq atom.

(** ** Substitutions *)

(** basic operation for substitution of atoms *)
Definition repl_at x y A := if ateq x y then A else var x.

Lemma repl_at_eq x y A : x = y -> repl_at x y A = A.
Proof.
intros ->; unfold repl_at.
rewrite (proj2 (ateq_eq _ _) (eq_refl _)); reflexivity.
Qed.

Lemma repl_at_neq x y A : x <> y -> repl_at x y A = var x.
Proof.
intros Hneq; unfold repl_at.
case_eq (ateq x y); intros Heqb; [ | reflexivity ].
exfalso.
rewrite ateq_eq in Heqb.
contradiction Heqb.
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

Lemma subs_dual A C x : subs C x (dual A) = dual (subs C x A).
Proof.
induction A; cbn; rewrite ? bidual;
  try (now rewrite IHA); try (now rewrite IHA1, IHA2); reflexivity.
Qed.

(** Substitution in proofs *)

Lemma subs_ll P A x l :
  ll P l ->
    ll (axupd_pfrag P (existT (fun x => x -> list formula) _
                            (fun a => map (subs A x) (projT2 (pgax P) a))))
       (map (subs A x) l).
Proof.
intros pi.
assert (forall l, map (subs A x) (map wn l) = map wn (map (subs A x) l)) as Hmapwn
  by (clear; induction l; [ | cbn; rewrite IHl ]; reflexivity).
induction pi using ll_nested_ind; list_simpl; try (now constructor).
- eapply ex_r; [ apply ax_exp | apply PCPermutation_Type_swap ].
- eapply PCPermutation_Type_map in p.
  eapply ex_r; eassumption.
- rewrite ? map_app, Hmapwn in IHpi; rewrite Hmapwn.
  eapply Permutation_Type_map in p.
  eapply ex_wn_r; eassumption.
- rewrite concat_map.
  apply mix_r.
  + cbn; rewrite map_length; assumption.
  + apply forall_Forall_inf.
    intros l' Hin.
    destruct (in_inf_map_inv (map (subs A x)) L l' Hin) as [l0 <- Hin'].
    apply (In_Forall_inf_in _ PL) in Hin' as [pi' Hin'].
    refine (Dependent_Forall_inf_forall_formula _ _ X Hin').
- specialize Hmapwn with l.
  rewrite Hmapwn.
  apply oc_r.
  rewrite <- Hmapwn; assumption.
- refine (cut_r (subs A x A0) _ _); [ | rewrite <- subs_dual | ]; assumption.
- apply (@gax_r _ (axupd_pfrag P (existT (fun x => x -> list formula) _
                               (fun a => map (subs A x) (projT2 (pgax P) a)))) a).
Qed.

Lemma subs_ll_axfree P : (projT1 (pgax P) -> False) -> forall A x l,
  ll P l -> ll P (map (subs A x) l).
Proof.
intros P_axfree A x l pi.
apply (subs_ll A x) in pi.
eapply stronger_pfrag; [ | eassumption ].
repeat split; try reflexivity.
cbn; intros a.
contradiction P_axfree.
Qed.


(** ** Fresh atoms and associated properties *)

Fixpoint atom_list A : list atom :=
match A with
| var x     => x :: nil
| covar x   => x :: nil
| one       => nil
| bot       => nil
| tens B C  => atom_list B ++ atom_list C
| parr B C  => atom_list B ++ atom_list C
| zero      => nil
| top       => nil
| aplus B C => atom_list B ++ atom_list C
| awith B C => atom_list B ++ atom_list C
| oc B      => atom_list B
| wn B      => atom_list B
end.

End Atoms.


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
Proof. now intros; apply subs_fresh_incl. Qed.

(** Provide an [Atom] which is fresh for all elements of [l] *)
Definition fresh_of_list (l : list formula) := fresh (flat_map atom_list l).

Lemma subs_fresh_list_incl C lat (l : list formula) :
  incl (flat_map atom_list l) lat -> map (subs C (fresh lat)) l = l.
Proof.
induction l; cbn; intros Hincl; [ reflexivity | ].
apply incl_app_inv in Hincl.
rewrite subs_fresh_incl; [ rewrite IHl | ]; intuition.
Qed.

Lemma subs_fresh_list C l : map (subs C (fresh_of_list l)) l = l.
Proof. now intros; apply subs_fresh_list_incl. Qed.

End InfAtoms.
