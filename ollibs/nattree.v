(** [nat]-labelled binary trees and embedding into [nat] *)

From Coq Require Import PeanoNat Lia.
From OLlibs Require Import funtheory.

Set Implicit Arguments.

(* TODO use Cantor pairing from stdlib ?*)


(** * Coding of pairs of [nat] *)

(** Simple coding into [nat]\{0} **)
Definition cpair n m := 2 ^ n * (2 * m + 1).

Lemma cpair_pos n m : 0 < cpair n m.
Proof.
unfold cpair.
enough (2 ^ n <> 0) by nia.
now apply Nat.pow_nonzero.
Qed.

Lemma cpair_inj : injective2 cpair.
Proof.
intros n; induction n as [|n IHn]; unfold cpair; cbn; intros m n' m' Hc.
- assert (0 = n') as <- by (destruct n'; cbn in Hc; lia).
  cbn in Hc; split; lia.
- destruct n'; cbn in Hc.
  + exfalso; lia.
  + assert (n = n' /\ m = m') as [-> ->] by (apply IHn; unfold cpair; lia); intuition.
Qed.

Lemma cpair_surj k : 0 < k -> {'(n, m) | k = cpair n m }.
Proof.
induction k as [k IH] using (well_founded_induction Wf_nat.lt_wf); intros Hpos.
rewrite (Nat.div2_odd k) in *; destruct (Nat.odd k); cbn in *.
- exists (0, Nat.div2 k); cbn; lia.
- destruct (IH (Nat.div2 k)) as [(n, m) ->]; [ lia | lia | ].
  exists (S n, m); unfold cpair; cbn; lia.
Qed.

Definition dpair1 k (Hpos : k > 0) := fst (proj1_sig (cpair_surj Hpos)).
Definition dpair2 k (Hpos : k > 0) := snd (proj1_sig (cpair_surj Hpos)).

Lemma cpair_dpair k (Hpos : 0 < k) : k = cpair (dpair1 Hpos) (dpair2 Hpos).
Proof.
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

Lemma pcpair_pdpair k : k = pcpair (pdpair1 k) (pdpair2 k).
Proof. unfold pcpair, pdpair1, pdpair2; rewrite <- cpair_dpair; lia. Qed.

Lemma pdpair1_pcpair n m : pdpair1 (pcpair n m) = n.
Proof. symmetry; apply (pcpair_inj _ _ _ _ (pcpair_pdpair (pcpair n m))). Qed.

Lemma pdpair2_pcpair n m : pdpair2 (pcpair n m) = m.
Proof. symmetry; apply (pcpair_inj _ _ _ _ (pcpair_pdpair (pcpair n m))). Qed.


(** ** Properties of coding functions *)

Lemma cpair_inc_l n n' m : n < n' -> cpair n m < cpair n' m.
Proof.
intros Hlt; unfold cpair.
apply (Nat.pow_lt_mono_r 2) in Hlt; nia.
Qed.

Lemma cpair_inc_r n m m' : m < m' -> cpair n m < cpair n m'.
Proof.
intros Hlt; unfold cpair.
enough (2 ^ n <> 0) by nia.
now apply Nat.pow_nonzero.
Qed.

Lemma cpair_lt_l n m : n < cpair n m.
Proof. unfold cpair; induction n; cbn; lia. Qed.

Lemma cpair_lt_r n m : m < cpair n m.
Proof. unfold cpair; induction n; cbn; lia. Qed.

Lemma pcpair_inc_l n n' m : n < n' -> pcpair n m < pcpair n' m.
Proof.
intros Hlt.
assert (Hpos := cpair_pos n m).
assert (Hinc := cpair_inc_l m Hlt).
unfold pcpair; case_eq (cpair n m); lia.
Qed.

Lemma pcpair_inc_r n m m' : m < m' -> pcpair n m < pcpair n m'.
Proof.
intros Hlt.
assert (Hpos := cpair_pos n m).
assert (Hinc := cpair_inc_r n Hlt).
unfold pcpair; case_eq (cpair n m); lia.
Qed.

Lemma pcpair_le_l n m : n <= pcpair n m.
Proof. assert (Hlt := cpair_lt_l n m); unfold pcpair; lia. Qed.

Lemma pcpair_le_r n m : m <= pcpair n m.
Proof. assert (Hlt := cpair_lt_r n m); unfold pcpair; lia. Qed.


(** * Coding of [nat]-labelled binary trees *)

(* possible future generalization
Inductive bintree A :=
| Lnode : bintree A
| Bnode : A -> bintree A -> bintree A -> bintree A.
*)

Inductive nattree :=
| Lnt : nattree
| Bnt : nat -> nattree -> nattree -> nattree.

Fixpoint nattree2nat t :=
match t with
| Lnt => 0
| Bnt k t1 t2 => cpair k (pcpair (nattree2nat t1) (nattree2nat t2))
end.

Lemma nattree2nat_inj : injective nattree2nat.
Proof.
intro t1; induction t1 as [|n t1' IH' t1'' IH'']; cbn;
  intros [|m t2' t2''] Heq; intuition.
- exfalso.
  assert (Hpos := cpair_pos m (pcpair (nattree2nat t2') (nattree2nat t2''))).
  cbn in Heq; lia.
- exfalso.
  assert (Hpos := cpair_pos n (pcpair (nattree2nat t1') (nattree2nat t1''))).
  cbn in Heq; lia.
- cbn in Heq; apply cpair_inj in Heq as [-> Heq].
  apply pcpair_inj in Heq as [Heq' Heq''].
  now apply IH' in Heq'; apply IH'' in Heq''; subst.
Qed.

Lemma nattree2nat_surj : surjective nattree2nat.
Proof.
intro y; induction y as [[|y] IH] using (well_founded_induction Wf_nat.lt_wf).
- exists Lnt; reflexivity.
- assert (0 < S y) as Hlt by lia.
  destruct (cpair_surj Hlt) as [(n, m) Heq].
  destruct (pcpair_surj m) as [(n', m') Heq'].
  assert (m < S y) as Hm by (rewrite Heq; apply cpair_lt_r).
  assert (n' <= pcpair n' m') as Hl by apply pcpair_le_l.
  assert (n' < S y) as Hn' by lia.
  assert (m' <= pcpair n' m') as Hr by apply pcpair_le_r.
  assert (m' < S y) as Hm' by lia.
  apply IH in Hn' as [t1 ->].
  apply IH in Hm' as [t2 ->].
  now subst; exists (Bnt n t1 t2).
Qed.
