(** [nat]-labelled binary trees and embedding into [nat] *)

From Coq Require Import PeanoNat Lia.
From OLlibs Require Import funtheory.

Set Implicit Arguments.

(* TODO use Cantor pairing from stdlib? *)


(** * Coding of pairs of [nat] *)

(** Simple coding into [nat]\{0} **)
Definition cpair n m := 2 ^ n * (2 * m + 1).

Lemma cpair_pos n m : 0 < cpair n m.
Proof. unfold cpair. enough (2 ^ n <> 0) by nia. apply Nat.pow_nonzero. intros [=]. Qed.

Lemma cpair_inj : injective2 cpair.
Proof.
intros n. induction n as [|n IHn]; unfold cpair; cbn; intros m n' m' Hc.
- assert (0 = n') as <- by (destruct n'; cbn in Hc; lia).
  cbn in Hc. split; lia.
- destruct n'; cbn in Hc.
  + exfalso. lia.
  + assert (n = n' /\ m = m') as [-> ->] by (apply IHn; unfold cpair; lia). repeat split.
Qed.

Lemma cpair_surj k : {'(n, m) | S k = cpair n m }.
Proof.
induction k as [k IH] using (well_founded_induction Wf_nat.lt_wf).
rewrite (Nat.div2_odd (S k)) in *. remember (Nat.odd (S k)) as b eqn:Hodd. destruct b; cbn in *.
- exists (0, Nat.div2 (S k)). cbn. lia.
- destruct k as [|k]; [inversion Hodd|].
  destruct (IH (Nat.div2 k)) as [(n, m) ->].
  + apply Nat.lt_succ_r, Nat.div2_decr. lia.
  + exists (S n, m). unfold cpair. cbn. lia.
Qed.

Definition dpair1 k := fst (proj1_sig (cpair_surj k)).
Definition dpair2 k := snd (proj1_sig (cpair_surj k)).

Lemma cpair_dpair k : S k = cpair (dpair1 k) (dpair2 k).
Proof. assert (Heq := proj2_sig (cpair_surj k)). rewrite surjective_pairing in Heq. assumption. Qed.


(** Refined surjective coding in [nat] **)
Definition pcpair n m := pred (cpair n m).

Lemma pcpair_cpair n m : S (pcpair n m) = cpair n m.
Proof. assert (Hp := cpair_pos n m). unfold pcpair. lia. Qed.

Lemma pcpair_inj : injective2 pcpair.
Proof. intros n m n' m' Heq. apply cpair_inj. rewrite <- ? pcpair_cpair, Heq. reflexivity. Qed.

Lemma pcpair_surj : surjective2 pcpair.
Proof. intros k. destruct (cpair_surj k) as [(n, m) Heq]. exists (n, m). unfold pcpair. lia. Qed.

Lemma pcpair_dpair k : k = pcpair (dpair1 k) (dpair2 k).
Proof. unfold pcpair. rewrite <- cpair_dpair. reflexivity. Qed.

Lemma dpair1_pcpair n m : dpair1 (pcpair n m) = n.
Proof. symmetry. apply (pcpair_inj _ _ _ _ (pcpair_dpair (pcpair n m))). Qed.

Lemma dpair2_pcpair n m : dpair2 (pcpair n m) = m.
Proof. symmetry. apply (pcpair_inj _ _ _ _ (pcpair_dpair (pcpair n m))). Qed.


(** ** Properties of coding functions *)

Lemma cpair_inc_l n n' m : n < n' -> cpair n m < cpair n' m.
Proof. intros Hlt%(Nat.pow_lt_mono_r 2); unfold cpair; nia. Qed.

Lemma cpair_inc_r n m m' : m < m' -> cpair n m < cpair n m'.
Proof. intros Hlt. unfold cpair. enough (2 ^ n <> 0) by nia. apply Nat.pow_nonzero. intros [=]. Qed.

Lemma cpair_lt_l n m : n < cpair n m.
Proof. unfold cpair. induction n; cbn; lia. Qed.

Lemma cpair_lt_r n m : m < cpair n m.
Proof. unfold cpair. induction n; cbn; lia. Qed.

Lemma pcpair_inc_l n n' m : n < n' -> pcpair n m < pcpair n' m.
Proof. intros Hinc%(cpair_inc_l m). rewrite <- ? pcpair_cpair in Hinc. lia. Qed.

Lemma pcpair_inc_r n m m' : m < m' -> pcpair n m < pcpair n m'.
Proof. intros Hinc%(cpair_inc_r n). rewrite <- ? pcpair_cpair in Hinc. lia. Qed.

Lemma pcpair_le_l n m : n <= pcpair n m.
Proof. assert (Hlt := cpair_lt_l n m). unfold pcpair. lia. Qed.

Lemma pcpair_le_r n m : m <= pcpair n m.
Proof. assert (Hlt := cpair_lt_r n m). unfold pcpair. lia. Qed.


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
intro t1. induction t1 as [|n t1' IH' t1'' IH'']; intros [|m t2' t2'']; cbn; intros Heq; [ reflexivity | | | ].
- exfalso. rewrite <- pcpair_cpair in Heq. discriminate Heq.
- exfalso. rewrite <- pcpair_cpair in Heq. discriminate Heq.
- apply cpair_inj in Heq as [-> [->%IH' ->%IH'']%pcpair_inj]. reflexivity.
Qed.

Lemma nattree2nat_surj : surjective nattree2nat.
Proof.
intro y. induction y as [[|y] IH] using (well_founded_induction Wf_nat.lt_wf).
- exists Lnt. reflexivity.
- destruct (cpair_surj y) as [(n, m) Heq].
  destruct (pcpair_surj m) as [(n', m') ->].
  assert (pcpair n' m' < S y) as Hm by (rewrite Heq; apply cpair_lt_r).
  assert (Hl := pcpair_le_l n' m').
  assert (Hr := pcpair_le_r n' m').
  assert (n' < S y) as [t1 ->]%IH by lia.
  assert (m' < S y) as [t2 ->]%IH by lia.
  exists (Bnt n t1 t2). assumption.
Qed.
