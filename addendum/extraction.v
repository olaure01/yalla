From Stdlib Require Import List.
From Yalla Require Import Permutation_Type_more ll_fragments.
Import ListNotations.

Set Implicit Arguments.

Lemma boolean_extraction (pi : ll_ll [aplus one one]) : bool.
Proof.
remember ([aplus one one]) as l eqn:Heql.
induction pi in Heql |- *; try (discriminate Heql); subst.
- cbn in p. symmetry in p. apply Permutation_Type_length_1_inv in p as ->.
  apply IHpi. reflexivity.
- destruct l1, lw', l2; inversion Heql; (try (destruct l1; discriminate)); subst.
  + symmetry in p. apply Permutation_Type_nil in p as ->.
    apply IHpi. reflexivity.
  + destruct l1; [ | discriminate Heql ].
    symmetry in p. apply Permutation_Type_nil in p as ->.
    apply IHpi. reflexivity.
- discriminate f.
- exact true.
- exact false.
- discriminate f.
- destruct a.
Defined.

Example proof_of_true : ll_ll [aplus one one].
Proof. apply plus_r1, one_r. Defined.
(* Compute (boolean_extraction proof_of_true). *)

Example proof_of_true_extract : boolean_extraction proof_of_true = true.
Proof. reflexivity. Qed.

Example proof_of_false : ll_ll [aplus one one].
Proof. apply plus_r2, one_r. Defined.
(* Compute (boolean_extraction proof_of_false). *)

Example proof_of_false_extract : boolean_extraction proof_of_false = false.
Proof. reflexivity. Qed.
