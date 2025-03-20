(** Axiom(s) of Finite Choice *)

Set Mangle Names.
Set Mangle Names Light.
Set Implicit Arguments.

From Stdlib Require Import PeanoNat Lia List.

(** * Functional Axiom of Choice for finite functions *)
Lemma AFC A (a : A) k (R : nat -> A -> Prop):
  (forall x, x < k -> exists y, R x y) -> exists f, forall x, x < k -> R x (f x).
Proof.
induction k as [| k IHk]; intros He.
- exists (fun _ => a). intros x Hx. inversion Hx.
- destruct IHk as [g Hg].
  { intros x Hk. apply He. lia. }
  destruct (He _ (Nat.lt_succ_diag_r _)) as [y Hy].
  exists (fun x => if S x <=? k then g x else y).
  intros x Hl.
  destruct (S x <=? k) eqn:Heqb.
  + apply Nat.leb_le in Heqb. apply Hg. lia.
  + enough (x = k) as -> by assumption.
    case (Nat.compare_spec (S x) k); intros Ho; [ exfalso .. | lia ].
    * rewrite <- Ho, Nat.leb_refl in Heqb. discriminate Heqb.
    * eapply or_introl, Nat.le_lteq, Nat.leb_le in Ho.
      rewrite Ho in Heqb. discriminate Heqb.
Qed.

(** * Axiom of Finite Choices over lists *)
Lemma AFClist A (R : nat -> A -> Prop) l :
  (forall a i j, In a l -> R i a -> i < j -> R j a) ->
    (Forall (fun x => exists k, R k x) l) -> exists k, Forall (R k) l.
Proof.
induction l as [|b l IHl]; intros Hinc HF.
- exists 0. constructor.
- inversion_clear HF as [ | ? ? HF1 HF2 ].
  apply IHl in HF2 as [k2 Hk2].
  + destruct HF1 as [k1 Hk1].
    exists (S (max k1 k2)). apply Forall_cons.
    * now apply (Hinc _ k1); [ left | | lia ].
    * apply Forall_forall. intros x Hx.
      apply (Forall_forall _ _) with x in Hk2; [ | assumption ].
      apply Hinc with k2; [ right | | lia ]; assumption.
  + intros ? i. intros. apply Hinc with i; [ right | | ]; assumption.
Qed.

Lemma AFCinc (R : nat -> nat -> Prop) :
  (forall n i j, R i n -> i < j -> R j n) ->
    forall m, (forall n, n < m -> exists k, R k n) ->
    exists k, forall n, n < m -> R k n.
Proof.
intros Hinc m HF. induction m as [|m IHm].
- exists 0. intros n Hn. inversion Hn.
- assert (exists k, R k m) as [k' Hk'] by (apply HF; lia).
  assert (forall n, n < m -> exists k, R k n) as [k Hk]%IHm by (intros; apply HF; lia).
  exists (S (S (max k k'))).
  intros n Hlt. inversion_clear Hlt.
  + apply (Hinc _ k'); [ assumption | lia ].
  + apply (Hinc _ k); [ apply Hk | ]; lia.
Qed.

Lemma AFCincdep m (R : nat -> forall n, n < m -> Prop) :
  (forall i n H1 H2, R i n H1 -> R i n H2) ->
  (forall n H i j, R i n H -> i < j -> R j n H) ->
    (forall n H, exists k, R k n H) -> exists k, forall n H, R k n H.
Proof.
induction m as [|m IHm]; intros Hext Hinc HI.
- exists 0. intros n Hn. inversion Hn.
- assert (forall n H, exists k, R k n (Nat.lt_lt_succ_r _ _ H)) as [k Hk]%IHm by (intros; apply HI).
  + assert (exists k, R k m (Nat.lt_succ_diag_r _)) as [k' Hk'] by apply HI.
    exists (S (max k k')).
    intros n Hn. inversion Hn; subst.
    * apply (Hinc _ _ k'); [ | lia ].
      exact (Hext _ _ _ _ Hk').
    * apply (Hinc _ _ k); [ | lia ].
      refine (Hext _ _ _ _ (Hk _ _)). lia.
  + intros ? ? ? ? HR. exact (Hext _ _ _ _ HR).
  + intros ? ? i. exact (Hinc _ _ i).
Qed.
