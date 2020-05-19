(** Axiom(s) of Finite Choice *)

From Coq Require Import PeanoNat Lia List.

Set Implicit Arguments.

(** * Functional Axiom of Choice for finite functions *)
Lemma AFC A : forall (a : A) k (R : nat -> A -> Prop),
  (forall x, x < k -> exists y, R x y) ->
     exists f, forall x, x < k -> R x (f x).
Proof.
induction k; intros R He.
- exists (fun _ => a).
  intros x Hx; inversion Hx.
- destruct (IHk R) as [g Hg].
  + intros x Hk.
    apply He; lia.
  + destruct (He k (Lt.lt_n_Sn _)) as [y Hy].
    exists (fun x => if S x <=? k then g x else y).
    intros x Hl.
    case_eq (S x <=? k); intros Heqb.
    * apply Nat.leb_le in Heqb.
      now apply Hg; lia.
    * enough (x = k) by (subst; intuition).
      case (Nat.compare_spec (S x) k); intros Ho; try lia.
      -- exfalso.
         rewrite <- Ho, Nat.leb_refl in Heqb; inversion Heqb.
      -- eapply or_introl, Nat.le_lteq, Nat.leb_le in Ho.
         rewrite Ho in Heqb; inversion Heqb.
Qed.

(** * Axiom of Finite Choices over lists *)
Lemma AFClist : forall A (R : nat -> A -> Prop) l,
  (forall a i j, In a l -> R i a -> i < j -> R j a) ->
    (Forall (fun x => exists k, R k x) l) -> exists k, Forall (R k) l.
Proof.
induction l; intros Hinc HF.
- exists 0; constructor.
- inversion_clear HF as [ | ? ? HF1 HF2 ].
  apply IHl in HF2.
  + destruct HF1 as [k1 Hk1].
    destruct HF2 as [k2 Hk2].
    exists (S (max k1 k2)); constructor.
    * apply (Hinc _ k1); intuition.
    * apply Forall_forall; intros x Hx.
      apply (Forall_forall _) with (x0:=x) in Hk2; intuition.
      apply Hinc with k2; intuition.
  + intros ? i; intros; apply Hinc with i; intuition.
Qed.

Lemma AFCinc : forall R : nat -> nat -> Prop,
  (forall n i j, R i n -> i < j -> R j n) ->
    forall m, (forall n, n < m -> exists k, R k n) ->
    exists k, forall n, n < m -> R k n.
Proof.
intros R Hinc; induction m; intros HF.
- exists 0; intros n Hn; inversion Hn.
- assert (exists k, R k m) as HS by (apply HF; lia).
  assert (forall n, n < m -> exists k, R k n) as Hm
    by (intros; apply HF; lia).
  apply IHm in Hm.
  destruct Hm as [k Hk].
  destruct HS as [k' Hk'].
  exists (S (S (max k k'))).
  intros n Hlt.
  inversion_clear Hlt; intuition.
  + apply Hinc with k'; intuition.
  + apply Hinc with k; intuition.
Qed.


(** * Axioms of Finite Choices over vectors *)
Lemma AFCvec : forall A (R : nat -> A -> Prop) n (l : Vector.t _ n),
  (forall a i j, Vector.In a l -> R i a -> i < j -> R j a) ->
    (Vector.Forall (fun x => exists k, R k x) l) -> exists k, Vector.Forall (R k) l.
Proof.
induction l; intros Hinc HF.
- exists 0; constructor.
- inversion HF as [ | ? ? v HF1 HF2 Heq0 [Heq1 Heq] ]; subst.
  apply Eqdep_dec.inj_pair2_eq_dec in Heq; [ | exact Nat.eq_dec ]; subst.
  apply IHl in HF2.
  + destruct HF1 as [k1 Hk1].
    destruct HF2 as [k2 Hk2].
    exists (S (max k1 k2)); constructor.
    * apply (Hinc h k1); intuition; constructor.
    * revert Hk2; clear - Hinc; induction l; intros HF;
        inversion HF as [ | ? ? v HF1 HF2 Heq0 [Heq1 Heq] ]; 
        try (apply Eqdep_dec.inj_pair2_eq_dec in Heq; [ | exact Nat.eq_dec ]);
        subst; constructor.
      -- apply Hinc with k2; intuition; constructor; constructor.
      -- apply IHl; intuition.
         inversion H as [ ? v Heq0 [Heq1 Heq] | ? ? v Hin Heq0 [t Heq]]; subst;
           apply Eqdep_dec.inj_pair2_eq_dec in Heq; subst; try exact Nat.eq_dec;
           apply Hinc with i; intuition; constructor; constructor; assumption.
  + intros ? i; intros; apply Hinc with i; intuition; now constructor.
Qed.

Lemma AFCvec_incdep : forall m (R : nat -> forall n, n < m -> Prop),
  (forall i n H1 H2, R i n H1 -> R i n H2) ->
  (forall n H i j, R i n H -> i < j -> R j n H) ->
    (forall n H, exists k, R k n H) -> exists k, forall n H, R k n H.
Proof.
induction m; intros R Hext Hinc HI.
- exists 0; intros n Hn; inversion Hn.
- assert (forall n H, exists k, R k n (Lt.lt_S _ _ H)) as Hm
    by (intros; apply HI).
  apply IHm in Hm.
  + destruct Hm as [k Hk].
    assert (exists k, R k m (Lt.lt_n_Sn _)) as [k' Hk'] by (apply HI).
    exists (S (max k k')).
    intros n Hn; inversion Hn; subst.
    * apply (Hinc _ _ k'); [ | lia ].
      eapply Hext; apply Hk'.
    * apply (Hinc _ _ k); [ | lia ].
      eapply Hext; refine (Hk _ _); lia.
  + intros; eapply Hext; eassumption.
  + intros; now apply (Hinc _ _ i).
Qed.
