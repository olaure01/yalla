(* natree Library *)
(* Coq v8.6 *)
(* v0   Olivier Laurent *)


(** * [nat]-labelled binary trees and embedding into nat *)

Require Import Lt Plus Mult Even Div2 Wf_nat.
Require Import NPeano.
Require Import Psatz.

Require Import Injective.
Require Import Surjective.

(* begin hide *)
Lemma pow_inc : forall n m m', 1 < n -> m < m' -> pow n m < pow n m'.
Proof.
intros n m m' Hn Hlt.
induction Hlt.
- simpl.
  destruct n ; try (now inversion Hn).
  destruct n ; try (now inversion Hn).
  simpl.
  rewrite <- (plus_0_r (S (S n) ^ m)).
  rewrite <- plus_assoc.
  apply plus_lt_compat_l.
  simpl.
  induction m ; simpl ; lia.
- simpl.
  etransitivity ; [ apply IHHlt | ].
  clear - Hn.
  induction m0 ; simpl ; try lia.
  apply mult_lt_compat_l ; lia.
Qed.
(* end hide *)

(** * Coding of pairs of [nat] *)

(** Simple coding **)
Definition cpair n m := 2 ^ n * (2 * m + 1).

Lemma cpair_not_0 : forall n m, cpair n m <> 0.
Proof.
induction n ; unfold cpair ; simpl ; intros m H.
- destruct m ; inversion H.
- specialize IHn with m.
  unfold cpair in IHn.
  lia.
Qed.

Lemma cpair_inc_l : forall n n' m, n < n' -> cpair n m < cpair n' m.
Proof.
intros n n' m Hlt.
unfold cpair.
apply mult_lt_compat_r ; try lia.
apply (pow_inc 2) ; [ lia | assumption ].
Qed.

Lemma cpair_inc_r : forall n m m', m < m' -> cpair n m < cpair n m'.
Proof.
intros n m m' Hlt.
unfold cpair.
apply mult_lt_compat_l ; try lia.
clear ; induction n ; simpl ; lia.
Qed.

Lemma cpair_lt_l : forall n m, n < cpair n m.
Proof.
intros n m.
unfold cpair.
induction n ; simpl ; lia.
Qed.

Lemma cpair_lt_r : forall n m, m < cpair n m.
Proof.
intros n m.
unfold cpair.
induction n ; simpl ; lia.
Qed.

Lemma cpair_inj : injective2 cpair.
Proof.
intros n.
induction n ; intros m n' m' Hc ; unfold cpair in Hc ; simpl in Hc.
- assert (0 = n') by (destruct n' ; simpl in Hc ; lia) ; subst.
  simpl in Hc ; split ; lia.
- destruct n' ; simpl in Hc.
  + exfalso ; lia.
  + assert (n = n' /\ m = m') as [Hn Hm] by (apply IHn ; unfold cpair ; lia).
    split ; [ f_equal | ] ; assumption.
Qed.

Lemma cpair_surj : forall k , 0 < k -> exists n m, k = cpair n m.
Proof.
induction k using (well_founded_induction lt_wf).
intros Hpos.
destruct (even_or_odd k) as [ He | Ho ].
- assert (0 < div2 k) as Hpos2.
  {
    destruct k.
    - inversion Hpos.
    - apply even_div2 in He.
      rewrite He.
      apply lt_0_Sn.
  }
  destruct (H (div2 k) (lt_div2 _ Hpos) Hpos2) as (n & m & Heq).
  exists (S n) ; exists m.
  unfold cpair in Heq ; simpl.
  unfold cpair ; simpl.
  apply even_double in He.
  rewrite He ; unfold double.
  lia.
- apply odd_S2n in Ho.
  destruct Ho as [p Hp] ; subst.
  exists 0 ; exists p.
  unfold double ; unfold cpair ; simpl ; lia.
Qed.

(** Refined surjective coding **)
Definition pcpair n m := pred (cpair n m).

Lemma pcpair_inc_l : forall n n' m, n < n' -> pcpair n m < pcpair n' m.
Proof.
intros n n' m Hlt.
unfold pcpair.
case_eq (cpair n m).
- intros Heq.
  apply cpair_not_0 in Heq.
  inversion Heq.
- intros n0 Heq.
  simpl.
  case_eq (cpair n' m).
  + intros Heq'.
    apply cpair_not_0 in Heq'.
    inversion Heq'.
  + intros m0 Heq'.
    simpl.
    apply (cpair_inc_l _ _ m) in Hlt.
    rewrite Heq in Hlt.
    rewrite Heq' in Hlt.
    lia.
Qed.

Lemma pcpair_inc_r : forall n m m', m < m' -> pcpair n m < pcpair n m'.
Proof.
intros n m m' Hlt.
unfold pcpair.
case_eq (cpair n m).
- intros Heq.
  apply cpair_not_0 in Heq.
  inversion Heq.
- intros n0 Heq.
  simpl.
  case_eq (cpair n m').
  + intros Heq'.
    apply cpair_not_0 in Heq'.
    inversion Heq'.
  + intros m0 Heq'.
    simpl.
    apply (cpair_inc_r n) in Hlt.
    rewrite Heq in Hlt.
    rewrite Heq' in Hlt.
    lia.
Qed.

Lemma pcpair_le_l : forall n m, n <= pcpair n m.
Proof.
intros n m.
unfold pcpair ; unfold cpair.
assert (n <= pred (2 ^ n)) as Hp.
{
  induction n ; simpl.
  - reflexivity.
  - apply (plus_le_compat_l _ _ 1) in IHn.
    etransitivity ; [ apply IHn | ].
    assert (forall n, 0 < 2 ^ n) as Hpos
      by (clear ; intros n ; induction n ; simpl ; lia).
    specialize Hpos with n.
    lia.
}
etransitivity ; [ apply Hp | ].
clear Hp.
induction m ; simpl ; try lia.
Qed.

Lemma pcpair_le_r : forall n m, m <= pcpair n m.
Proof.
intros n m.
unfold pcpair ; unfold cpair.
induction n ; simpl ; try lia.
Qed.

Lemma pcpair_inj : injective2 pcpair.
Proof.
intros n m n' m' Heq.
apply cpair_inj.
unfold pcpair in Heq.
case_eq (cpair n m).
- intros Hc ; exfalso ; apply cpair_not_0 in Hc ; assumption.
- intros n0 Hc.
  case_eq (cpair n' m').
  + intros Hc' ; exfalso ; apply cpair_not_0 in Hc' ; assumption.
  + intros n1 Hc'.
    rewrite Hc in Heq.
    rewrite Hc' in Heq.
    rewrite <- 2 pred_Sn in Heq.
    subst ; reflexivity.
Qed.

Lemma pcpair_surj : surjective2 pcpair.
Proof.
intros k.
destruct (cpair_surj (S k) (lt_0_Sn _)) as (n & m & Heq).
exists n ; exists m ; unfold pcpair ; rewrite <- Heq.
apply pred_Sn.
Qed.


(** * Coding of [nat]-labelled binary trees *)

Inductive nattree : Set :=
| Lnt : nattree
| Bnt : nat -> nattree -> nattree -> nattree
.

Fixpoint nattree2nat t :=
match t with
| Lnt => 0
| Bnt k t1 t2 => cpair k (pcpair (nattree2nat t1) (nattree2nat t2))
end.

Lemma nattree2nat_inj : injective nattree2nat.
Proof.
intros t1.
induction t1 ; intros t2 Heq ; destruct t2 ; simpl in Heq.
- reflexivity.
- exfalso.
  symmetry in Heq.
  apply cpair_not_0 in Heq.
  assumption.
- exfalso.
  apply cpair_not_0 in Heq.
  assumption.
- apply cpair_inj in Heq.
  destruct Heq as [Heq1 Heq].
  apply pcpair_inj in Heq.
  destruct Heq as [Heq2 Heq3].
  apply IHt1_1 in Heq2.
  apply IHt1_2 in Heq3.
  f_equal ; assumption.
Qed.

Lemma nattree2nat_surj : surjective nattree2nat.
Proof.
intros y.
induction y using (well_founded_induction lt_wf).
destruct y.
- exists Lnt ; reflexivity.
- destruct (cpair_surj _ (lt_O_Sn y)) as (n & m & Heq).
  destruct (pcpair_surj m) as (n' & m' & Heq').
  assert (m < S y) as Hm by (rewrite Heq ; apply cpair_lt_r).
  assert (n' <= pcpair n' m') as Hl by apply pcpair_le_l.
  assert (n' < S y) as Hn' by lia.
  assert (m' <= pcpair n' m') as Hr by apply pcpair_le_r.
  assert (m' < S y) as Hm' by lia.
  apply H in Hn'.
  apply H in Hm'.
  destruct Hn' as [t1 H1].
  destruct Hm' as [t2 H2] ; subst.
  exists (Bnt n t1 t2).
  assumption.
Qed.


