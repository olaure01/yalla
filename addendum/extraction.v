From Stdlib Require Import List.
From Yalla Require Import Permutation_Type_more ll_fragments.
Import ListNotations.

Lemma boolean_extraction : ll_ll [aplus one one] -> bool.
Proof.
intro pi. remember [aplus one one] as l eqn:Heql.
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


(* counts the number of times the two occurrences of [covar 0] are commuted in the proof of [ll_ll l] *)
Lemma multiplicative_boolean_extraction_perm l :
  ll_ll l -> Permutation_Type l [tens (var 0) (var 0); covar 0; covar 0] -> bool.
Proof.
intro pi. induction pi; intro HP.
- exfalso.
  apply Permutation_Type_length in HP. cbn in HP. discriminate HP.
- clear pi.
  induction p in HP, IHpi |- *; subst.
  + apply Permutation_Type_nil_cons in HP as [].
  + assert (length l' = 2) as Hl'.
    { apply Permutation_Type_length in HP. cbn in HP. injection HP as [= ->]. reflexivity. }
    assert (length l = 2) as Hl.
    { apply Permutation_Type_length in p. rewrite p, Hl'. reflexivity. }
    rewrite <- p in HP. apply IHpi in HP.
    destruct l as [ | a [ | b [ | ] ] ]; try discriminate Hl.
    destruct l' as [ | a' [ | b' [ | ] ] ]; try discriminate Hl'.
    clear - HP p.
    remember [a; b] as l eqn:Hl. remember [a'; b'] as l' eqn:Hl'.
    induction p in a, b, a', b', Hl, Hl', HP |- *; subst.
    * discriminate.
    * exact HP.
    * apply negb, HP.
    * destruct l' as [ | c [ | d [ | ] ] ]; try (apply Permutation_Type_length in p2; discriminate p2).
      apply (IHp2 _ _ _ _ eq_refl eq_refl).
      apply (IHp1 _ _ _ _ eq_refl eq_refl).
      apply HP.
  + apply negb, IHpi.
    etransitivity; [ constructor | eassumption ].
  + apply IHp2; [ apply IHp1, IHpi | assumption ].
- apply IHpi.
  enough (lw' = []) as ->.
  { symmetry in p. apply Permutation_Type_nil in p. subst. assumption. }
  clear - HP. destruct lw' as [ | w l ]; [ reflexivity | exfalso ].
  eapply Permutation_Type_in in HP; [ | apply in_or_app; right; apply in_eq ].
  repeat destruct HP as [ | HP ]; try discriminate. destruct HP.
- apply Permutation_Type_nil in HP. discriminate.
- discriminate f.
- exfalso.
  apply Permutation_Type_length in HP. cbn in HP. discriminate HP.
- exfalso.
  eapply Permutation_Type_in in HP; [ | apply in_eq ].
  repeat destruct HP as [ | HP ]; try discriminate. destruct HP.
- exact true.
- exfalso.
  eapply Permutation_Type_in in HP; [ | apply in_eq ].
  repeat destruct HP as [ | HP ]; try discriminate. destruct HP.
- exfalso.
  eapply Permutation_Type_in in HP; [ | apply in_eq ].
  repeat destruct HP as [ | HP ]; try discriminate. destruct HP.
- exfalso.
  eapply Permutation_Type_in in HP; [ | apply in_eq ].
  repeat destruct HP as [ | HP ]; try discriminate. destruct HP.
- exfalso.
  eapply Permutation_Type_in in HP; [ | apply in_eq ].
  repeat destruct HP as [ | HP ]; try discriminate. destruct HP.
- exfalso.
  eapply Permutation_Type_in in HP; [ | apply in_eq ].
  repeat destruct HP as [ | HP ]; try discriminate. destruct HP.
- exfalso.
  eapply Permutation_Type_in in HP; [ | apply in_eq ].
  repeat destruct HP as [ | HP ]; try discriminate. destruct HP.
- exfalso.
  eapply Permutation_Type_in in HP; [ | apply in_eq ].
  repeat destruct HP as [ | HP ]; try discriminate. destruct HP.
- exfalso.
  eapply Permutation_Type_in in HP; [ | apply in_eq ].
  repeat destruct HP as [ | HP ]; try discriminate. destruct HP.
- exfalso.
  eapply Permutation_Type_in in HP; [ | apply in_eq ].
  repeat destruct HP as [ | HP ]; try discriminate. destruct HP.
- discriminate f.
- destruct a.
Defined.

Lemma multiplicative_boolean_extraction : ll_ll [tens (var 0) (var 0); covar 0; covar 0] -> bool.
Proof. intros pi%multiplicative_boolean_extraction_perm; [ assumption | reflexivity ]. Defined.

(* The proof of [true]: no transposition *)
Example multiplicative_proof_of_true : ll_ll [tens (var 0) (var 0); covar 0; covar 0].
Proof. apply (tens_r _ _ _ [covar 0] [covar 0]); ll_swap; apply ax_r. Defined.
(* Compute (multiplicative_boolean_extraction multiplicative_proof_of_true). *)

(* The proof of [false]: 1 transposition *)
Example multiplicative_proof_of_false : ll_ll [tens (var 0) (var 0); covar 0; covar 0].
Proof.
eapply ex_r; [ apply (tens_r _ (var 0) (var 0) [covar 0] [covar 0]); ll_swap; apply ax_r | ].
constructor. apply Permutation_Type_swap.
Defined.
(* Compute (multiplicative_boolean_extraction multiplicative_proof_of_false). *)

(* Another proof of [true]: twice the transposition *)
Example multiplicative_proof_of_true2 : ll_ll [tens (var 0) (var 0); covar 0; covar 0].
Proof.
eapply ex_r; [ apply (tens_r _ (var 0) (var 0) [covar 0] [covar 0]); ll_swap; apply ax_r | ].
constructor.
etransitivity; apply Permutation_Type_swap.
Defined.
(* Compute (multiplicative_boolean_extraction multiplicative_proof_of_true2). *)
