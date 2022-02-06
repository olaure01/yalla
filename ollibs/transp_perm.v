(** Transposition function on elements of a list *)

From Coq Require Import List Lia.
From Yalla.OLlibs Require Import funtheory Permutation_Type.

Set Implicit Arguments.


(** Transpose elements of index [n] and [n + 1] in [l] *)
Fixpoint transp A n (l : list A) :=
match n, l with
| 0, x :: y :: r => y :: x :: r
| S n, x :: r => x :: transp n r
| _, r => r
end.
Arguments transp {_} _ _.

Lemma transp_cons A n l (a : A) : transp (S n) (a :: l) = a :: transp n l.
Proof. reflexivity. Qed.

Lemma transp_nil A n : transp n (@nil A) = @nil A.
Proof. destruct n; reflexivity. Qed.

Lemma transp_app A n (l l0 : list A) :
  transp (length l0 + n) (l0 ++ l) = l0 ++ transp n l.
Proof.
revert n l; induction l0 as [|a l0 IHl0] using rev_ind; intros n l; auto.
rewrite <- ? app_assoc, <- app_comm_cons; simpl.
rewrite <- transp_cons, <- IHl0; f_equal.
rewrite last_length; simpl; lia.
Qed.

Lemma transp_transp A l1 l2 (a b : A) :
  transp (length l1) (l1 ++ a :: b :: l2) = l1 ++ b :: a :: l2.
Proof.
change (b :: a :: l2) with (transp 0 (a :: b :: l2)).
rewrite <- transp_app; f_equal; lia.
Qed.

Lemma transp_idem A n : retract (@transp A n) (@transp A n).
Proof.
induction n as [|n IHn]; intros l; (destruct l; [ | destruct l ]); auto.
- now simpl; f_equal; rewrite ? transp_nil.
- now simpl; f_equal; rewrite ? IHn.
Qed.

Lemma transp_inj A n : injective (@transp A n).
Proof. apply section_injective with (transp n); apply transp_idem. Qed.

Lemma transp_refl A n (l : list A) : length l < n + 2 -> transp n l = l.
Proof.
revert l; induction n as [|n IHn]; intros l Hlt.
- destruct l; [ | destruct l]; auto.
  exfalso; simpl in Hlt; lia.
- destruct l; auto.
  simpl in Hlt; simpl; f_equal.
  apply IHn; lia.
Qed.

Lemma transp_decomp A n (l : list A) : n + 1 < length l ->
  {'(l1, l2, a, b) & length l1 = n & prod (l = l1 ++ a :: b :: l2)
                                          (transp n l = l1 ++ b :: a :: l2) }.
Proof.
revert l; induction n as [|n IHn]; intros l Hlt; destruct l ; try (exfalso; inversion Hlt; fail).
- destruct l ; try (exfalso; simpl in Hlt ; lia; fail).
  exists (nil, l, a, a0); try split; try reflexivity.
- assert (n + 1 < length l) as Hlt2 by (simpl in Hlt; lia).
  destruct (IHn _ Hlt2) as [(((l1, l2), a'), b') Hl [Heq1 Heq2]]; subst.
  exists (a :: l1, l2, a', b'); try split; try reflexivity.
  simpl; f_equal; assumption.
Qed.

Lemma transp_map A B (f : A -> B) n l : transp n (map f l) = map f (transp n l).
Proof.
revert l; induction n as [|n IHn]; intros l; destruct l; auto.
- now destruct l; simpl.
- simpl; f_equal; apply IHn.
Qed.

Lemma transp_perm A n (l : list A) : Permutation_Type l (transp n l).
Proof.
revert l; induction n; intros l; simpl; destruct l; auto.
destruct l; auto.
apply Permutation_Type_swap.
Qed.

Lemma perm_transp A (l1 l2 : list A) :
  Permutation_Type l1 l2 -> { l & l2 = fold_right transp l1 l }.
Proof.
intros HP; induction HP as [ | a l1 l2 HP IHHP | | l1 l2 l3 HP1 IHHP1 HP2 IHHP2].
- now exists nil.
- destruct IHHP as [l0 Heq]; subst.
  exists (map S l0).
  clear HP; induction l0; auto.
  now simpl; rewrite <- IHl0.
- now exists (0 :: nil).
- destruct IHHP1 as [l1' ->]; destruct IHHP2 as [l2' ->].
  exists (l2' ++ l1').
  now rewrite fold_right_app.
Qed.
