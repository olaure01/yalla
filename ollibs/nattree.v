(** [nat]-labelled binary trees and embedding into [nat] *)

From Coq Require Import PeanoNat Lia.
From OLlibs Require Import funtheory.

Set Implicit Arguments.


(** * Coding of pairs of [nat] *)

(** Simple coding into [nat]\0 **)
Definition cpair n m := 2 ^ n * (2 * m + 1).

Lemma cpair_pos : forall n m, 0 < cpair n m.
Proof.
intros n m; unfold cpair.
enough (2 ^ n <> 0) by nia.
now apply Nat.pow_nonzero.
Qed.

Lemma cpair_inj : injective2 cpair.
Proof.
intros n; induction n; unfold cpair; simpl; intros m n' m' Hc.
- assert (0 = n') as <- by (destruct n'; simpl in Hc; lia).
  simpl in Hc; split; lia.
- destruct n'; simpl in Hc.
  + exfalso; lia.
  + assert (n = n' /\ m = m') as [-> ->] by (apply IHn; unfold cpair; lia); intuition.
Qed.

(* No easy non-deprecated way to do this found in Standard Library *)
Lemma even_odd_decomp k : { n | k = 2 * n } + { n | k = 2 * n + 1}.
Proof.
induction k.
- left; exists 0; reflexivity.
- destruct IHk as [ [ n -> ] | [ n -> ] ].
  + right; exists n; lia.
  + left; exists (S n); lia.
Qed.

Lemma cpair_surj : forall k, 0 < k -> {'(n, m) | k = cpair n m }.
Proof.
induction k using (well_founded_induction Wf_nat.lt_wf); intros Hpos.
destruct (even_odd_decomp k) as [ [k' ->] | [ k' -> ] ].
- assert (0 < k') as Hpos2 by lia.
  assert (k' < 2 * k') as Hdec by lia.
  destruct (H k' Hdec Hpos2) as [(n, m) ->].
  exists (S n, m).
  unfold cpair; simpl; lia.
- exists (0, k').
  unfold cpair; simpl; lia.
Qed.

Definition dpair1 k (Hpos : k > 0) := fst (proj1_sig (cpair_surj Hpos)).
Definition dpair2 k (Hpos : k > 0) := snd (proj1_sig (cpair_surj Hpos)).

Lemma cpair_dpair : forall k (Hpos : 0 < k),
  k = cpair (dpair1 Hpos) (dpair2 Hpos).
Proof.
intros k Hpos.
assert (Heq := proj2_sig (cpair_surj Hpos)).
now rewrite surjective_pairing in Heq.
Qed.


(** Refined surjective coding in [nat] **)
Definition pcpair n m := pred (cpair n m).

Lemma pcpair_inj : injective2 pcpair.
Proof.
intros n m n' m' Heq.
assert (Hpos := cpair_pos n m).
assert (Hpos' := cpair_pos n' m').
unfold pcpair in *; apply cpair_inj; lia.
Qed.

Lemma pcpair_surj : surjective2 pcpair.
Proof.
intros k.
destruct (cpair_surj (Nat.lt_0_succ k)) as [(n, m) Heq].
exists (n, m); unfold pcpair; lia.
Qed.

Definition pdpair1 k := dpair1 (Nat.lt_0_succ k).
Definition pdpair2 k := dpair2 (Nat.lt_0_succ k).

Lemma pcpair_pdpair : forall k, k = pcpair (pdpair1 k) (pdpair2 k).
Proof.
intros k.
unfold pcpair, pdpair1, pdpair2.
rewrite <- cpair_dpair; lia.
Qed.

Lemma pdpair1_pcpair : forall n m, pdpair1 (pcpair n m) = n.
Proof.
intros n m.
symmetry; apply (pcpair_inj _ _ _ _ (pcpair_pdpair (pcpair n m))).
Qed.

Lemma pdpair2_pcpair : forall n m, pdpair2 (pcpair n m) = m.
Proof.
intros n m.
symmetry; apply (pcpair_inj _ _ _ _ (pcpair_pdpair (pcpair n m))).
Qed.


(** ** Properties of coding functions *)

Lemma cpair_inc_l : forall n n' m, n < n' -> cpair n m < cpair n' m.
Proof.
intros n n' m Hlt; unfold cpair.
apply Nat.pow_lt_mono_r with (a:=2) in Hlt; simpl; nia.
Qed.

Lemma cpair_inc_r : forall n m m', m < m' -> cpair n m < cpair n m'.
Proof.
intros n m m' Hlt; unfold cpair.
enough (2 ^ n <> 0) by nia.
now apply Nat.pow_nonzero.
Qed.

Lemma cpair_lt_l : forall n m, n < cpair n m.
Proof. intros n m; unfold cpair; induction n; simpl; lia. Qed.

Lemma cpair_lt_r : forall n m, m < cpair n m.
Proof. intros n m; unfold cpair; induction n; simpl; lia. Qed.

Lemma pcpair_inc_l : forall n n' m, n < n' -> pcpair n m < pcpair n' m.
Proof.
intros n n' m Hlt.
assert (Hpos := cpair_pos n m).
assert (Hinc := cpair_inc_l m Hlt).
unfold pcpair; case_eq (cpair n m); intros; lia.
Qed.

Lemma pcpair_inc_r : forall n m m', m < m' -> pcpair n m < pcpair n m'.
Proof.
intros n m m' Hlt.
assert (Hpos := cpair_pos n m).
assert (Hinc := cpair_inc_r n Hlt).
unfold pcpair; case_eq (cpair n m); intros; lia.
Qed.

Lemma pcpair_le_l : forall n m, n <= pcpair n m.
Proof. intros n m; assert (Hlt := cpair_lt_l n m); unfold pcpair; lia. Qed.

Lemma pcpair_le_r : forall n m, m <= pcpair n m.
Proof. intros n m; assert (Hlt := cpair_lt_r n m); unfold pcpair; lia. Qed.


(** * Coding of [nat]-labelled binary trees *)

Inductive nattree : Set :=
| Lnt : nattree
| Bnt : nat -> nattree -> nattree -> nattree.

Fixpoint nattree2nat t :=
match t with
| Lnt => 0
| Bnt k t1 t2 => cpair k (pcpair (nattree2nat t1) (nattree2nat t2))
end.

Lemma nattree2nat_inj : injective nattree2nat.
Proof.
intros t1; induction t1; simpl; intros t2 Heq; destruct t2; intuition.
- exfalso.
  assert (Hpos := cpair_pos n (pcpair (nattree2nat t2_1) (nattree2nat t2_2))).
  simpl in Heq; lia.
- exfalso.
  assert (Hpos := cpair_pos n (pcpair (nattree2nat t1_1) (nattree2nat t1_2))).
  simpl in Heq; lia.
- simpl in Heq; apply cpair_inj in Heq.
  destruct Heq as [Heq1 Heq]; subst.
  apply pcpair_inj in Heq.
  destruct Heq as [Heq2 Heq3].
  apply IHt1_1 in Heq2.
  now apply IHt1_2 in Heq3; subst.
Qed.

Lemma nattree2nat_surj : surjective nattree2nat.
Proof.
intros y.
induction y using (well_founded_induction Wf_nat.lt_wf).
destruct y.
- exists Lnt; reflexivity.
- assert (0 < S y) as Hlt by lia.
  destruct (cpair_surj Hlt) as [(n, m) Heq].
  destruct (pcpair_surj m) as [(n', m') Heq'].
  assert (m < S y) as Hm by (rewrite Heq ; apply cpair_lt_r).
  assert (n' <= pcpair n' m') as Hl by apply pcpair_le_l.
  assert (n' < S y) as Hn' by lia.
  assert (m' <= pcpair n' m') as Hr by apply pcpair_le_r.
  assert (m' < S y) as Hm' by lia.
  apply H in Hn'.
  apply H in Hm'.
  destruct Hn' as [t1 ->].
  destruct Hm' as [t2 ->].
  now subst; exists (Bnt n t1 t2).
Qed.
