(** Add-ons for Vector library *)

Set Mangle Names.
Set Mangle Names Light.
Set Implicit Arguments.

#[local] Set Warnings "-stdlib-vector".
From Stdlib Require Import PeanoNat Lia Vector.

(** * Axioms of Finite Choices over vectors *)
Lemma AFCvec A (R : nat -> A -> Prop) n (l : Vector.t _ n) :
  (forall a i j, Vector.In a l -> R i a -> i < j -> R j a) ->
    (Vector.Forall (fun x => exists k, R k x) l) -> exists k, Vector.Forall (R k) l.
Proof.
induction l as [| b n l IHl]; intros Hinc HF.
- exists 0. constructor.
- inversion HF as [ | ? ? v HF1 HF2 Heq0 [Heq1 Heq] ]; subst.
  apply Eqdep_dec.inj_pair2_eq_dec in Heq as ->; [ | exact Nat.eq_dec ].
  apply IHl in HF2 as [k2 Hk2].
  + destruct HF1 as [k1 Hk1].
    exists (S (max k1 k2)). constructor.
    * apply (Hinc b k1); [ apply Vector.In_cons_hd | assumption | lia ].
    * revert Hk2. clear - Hinc.
      induction l as [|c m l IHl]; intros HF; inversion HF as [ | ? ? v HF1 HF2 Heq0 [Heq1 Heq] ]; constructor.
      -- apply Hinc with k2; [ apply Vector.In_cons_tl, Vector.In_cons_hd | assumption | lia ].
      -- apply Eqdep_dec.inj_pair2_eq_dec in Heq as ->; [ subst | exact Nat.eq_dec ].
         apply IHl; [ intros a i j H ? ? | assumption ].
         inversion H as [ ? v Heq0 [Heq1 Heq] | ? ? v Hin Heq0 [t Heq]]; subst;
           apply Eqdep_dec.inj_pair2_eq_dec in Heq as ->; try exact Nat.eq_dec;
           apply Hinc with i; [ | assumption | lia | | assumption | lia ].
         ++ apply Vector.In_cons_hd.
         ++ do 2 apply Vector.In_cons_tl. assumption.
  + intros ? i. intros. apply Hinc with i; [ apply Vector.In_cons_tl | | lia ]; assumption.
Qed.
