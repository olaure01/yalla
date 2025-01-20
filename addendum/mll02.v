(** ¬ ∃ A, ⊢ A ∧ ⊢ Aᗮ   in unit-free MLL with mix0 and mix2 *)

(* This is very special property of this system
   due to the absence of any kind of weakening including the absence of [bot] *)

(* The standard approach for this kind of result is:
     * prove cut-admissibility;
     * deduce a proof of the empty sequent ⊢ from the proofs of ⊢ A and ⊢ Aᗮ;
     * conclude with a contradiction since ⊢ is not provable.
   However this is not possible here since ⊢ *is* provable thanks to the mix0 rule *)

(* The trick is instead to do this reasoning on unit-free MLL with mix2 only,
   and to prove that non-empty provability is the same in the two systems. *)


(** ** 0. load the [yalla] library *)

From Yalla Require Import List_more Permutation_Type ll_cut.
Import ListNotations.


(** ** 1. define formulas *)

(* We rely on formulas from formulas.v *)
Print formula.


(** ** 2. define embedding into [formulas.formula] *)
(* useless since we do not define a new formula set *)


(** ** 3. define proofs *)

(* unit-free multiplicative linear logic with mix0 and mix2 *)
Inductive mll02 : list formula -> Type :=
| ax A : mll02 [A; dual A]
| ex l1 l2 : mll02 l1 -> Permutation_Type l1 l2 -> mll02 l2
| mix0 : mll02 nil
| mix2 l1 l2 : mll02 l1 -> mll02 l2 -> mll02 (l1 ++ l2)
| ten A B l1 l2 : mll02 (A :: l1) -> mll02 (B :: l2) -> mll02 (tens A B :: l1 ++ l2)
| par A B l : mll02 (A :: B :: l) -> mll02 (parr A B :: l).


(** ** 4. characterize corresponding [ll] fragment *)
(* we do not need to import results on [mll02] but on the mix0-free fragment *)
(* we characterize unit-free multiplicative linear logic with mix2 as an [ll] fragment *)

(* commutative, no cut, no axiom, mix2 rule only *)
Definition ll2_frag := mk_pfrag false NoAxioms false true true.
(*                               cut   axioms   mix0  mix2 perm  *)
Definition ll2 := ll ll2_frag.


(** ** 5. prove relations between proof predicates *)

(* non-empty provability in [mll02] entails provability in [ll2] *)
Lemma mix02_to_mix2 l : mll02 l -> l <> [] -> ll2 l.
Proof.
intro pi. induction pi; intro Hl.
- (* ax *) apply ax_exp.
- (* ex *) eapply ex_r; [ apply IHpi | eassumption ].
  intros ->. apply Permutation_Type_nil in p. subst. apply Hl. reflexivity.
- (* mix0 *) contradiction Hl. reflexivity.
- (* mix2 *)
  destruct l1 as [ | A l1 ]; [ | destruct l2 as [ | B l2 ] ].
  + apply IHpi2. assumption.
  + list_simpl in *. apply IHpi1. assumption.
  + apply mix2_r; [ reflexivity | apply IHpi2 | apply IHpi1 ]; intros [=].
- (* ten *) eapply ex_r; [ apply (tens_r _ A B l1 l2) | rewrite Permutation_Type_app_comm; reflexivity ].
  + apply IHpi1. intros [=].
  + apply IHpi2. intros [=].
- (* par *) apply parr_r, IHpi. intros [=].
Qed.


(** ** 6. Prove properties thanks to Yalla results *)

Require Import consistency.

(* first we have cut admissibility in [ll2]
   second the empty sequent is not provable in [ll2] thanks to the absence of mix0 *)

Lemma mll02_weak_consistency : notT { A & mll02 [A] & mll02 [dual A] }.
Proof.
intros [A pi1%mix02_to_mix2 pi2%mix02_to_mix2]; [ | intros [=] .. ].
assert (ll2 []) as pi by (refine (cut_r_axfree _ _ _ _ pi2 pi1); intros []).
revert pi. now apply not_empty_provable.
Qed.
