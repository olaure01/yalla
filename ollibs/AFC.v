(* AFC Library *)
(* v0   Olivier Laurent *)

(** * Axiom(s) of Finite Choice *)

Require Import Le Lt Max.
Require Import Compare_dec.
Require Import List.

Require Vector_more.

(** * Functional Axiom of Choice for finite functions *)
Lemma AFC : forall k (R : nat -> nat -> Prop),
  (forall x, x < k -> exists y, R x y) ->
     exists f, forall x,  x < k -> R x (f x).
Proof with try reflexivity ; try assumption.
induction k ; intros R He.
- exists (fun _ => 0).
  intros x Hx ; inversion Hx.
- destruct (IHk R) as [g Hg].
  + intros x Hk.
    apply He.
    transitivity k...
    apply lt_n_Sn.
  + destruct (He k (lt_n_Sn _)) as [y Hy].
    exists (fun x => if leb (S x) k then g x else y).
    intros x Hl.
    case_eq (leb (S x) k) ; intros Heqb.
    * apply leb_complete in Heqb.
      apply Hg.
      apply lt_S_n.
      apply le_lt_n_Sm...
    * apply leb_complete_conv in Heqb.
      replace x with k...
      inversion Hl...
      exfalso.
      apply lt_le_S in Heqb.
      apply (le_trans _ _ _ Heqb) in H0.
      apply lt_not_le in H0.
      apply H0...
Qed.

(** * Axiom of Finite Choices over lists *)
Lemma AFClist : forall {A} (P : nat -> A -> Prop) l,
  (forall a i j, In a l -> P i a -> i <= j -> P j a) ->
    (Forall (fun x => exists k, P k x) l) -> exists k, Forall (P k) l.
Proof with try eassumption ; try reflexivity.
induction l ; intros.
- exists 0 ; constructor.
- inversion H0 ; subst.
  apply IHl in H4.
  + destruct H3 as [k1 Hk1].
    destruct H4 as [k2 Hk2].
    exists (max k1 k2) ; constructor.
    * eapply H...
      -- left...
      -- apply le_max_l.
    * revert Hk2.
      clear - H.
      induction l ; intro Hl ; constructor ; inversion Hl ; subst.
      -- eapply H...
         ++ right ; left...
         ++ apply le_max_r.
      -- apply IHl...
         intros.
         eapply H...
         inversion H0 ; subst.
         ++ left...
         ++ right ; right...
  + intros.
    eapply H...
    right...
Qed.

Lemma AFCinc : forall P : nat -> nat -> Prop,
  (forall n i j, P i n -> i <= j -> P j n) ->
    forall m, (forall n, n < m -> exists k, P k n) ->
    exists k, forall n, n < m -> P k n.
Proof.
induction m ; intros.
- exists 0 ; intros n Hn.
  inversion Hn.
- assert (exists k, P k m) as HS by (apply H0 ; apply lt_n_Sn).
  assert (forall n, n < m -> exists k, P k n) as Hm
    by (intros ;
        apply H0 ;
        etransitivity ;
        [ apply H1 | apply lt_n_Sn ]).
  apply IHm in Hm.
  destruct Hm as [k Hk].
  destruct HS as [k' Hk'].
  exists (max (S k) (S k')).
  intros.
  inversion H1 ; subst ; eapply H.
  + apply Hk'.
  + etransitivity ; [ | apply le_max_r ].
    apply le_n_Sn.
  + apply Hk.
    apply lt_S_n.
    apply le_lt_n_Sm ; assumption.
  + etransitivity ; [ | apply le_max_l ].
    apply le_n_Sn.
Qed.


(** * Axioms of Finite Choices over vectors *)
Lemma AFCvec : forall {A} (P : nat -> A -> Prop) n (l : Vector.t _ n),
  (forall a i j, Vector.In a l -> P i a -> i <= j -> P j a) ->
    (Vector.Forall (fun x => exists k, P k x) l) -> exists k, Vector.Forall (P k) l.
Proof with try eassumption ; try reflexivity.
induction l ; intros.
- exists 0 ; constructor.
- inversion H0 ; subst.
  apply Vector_more.inj_pairT2_nat in H3 ; subst.
  apply IHl in H5.
  + destruct H4 as [k1 Hk1].
    destruct H5 as [k2 Hk2].
    exists (max k1 k2) ; constructor.
    * eapply H...
      -- left.
      -- apply le_max_l.
    * revert Hk2 ; clear - H.
      induction l ; intro Hl ; constructor ; inversion Hl ; subst.
      -- eapply H...
         ++ right ; left.
         ++ apply le_max_r.
      -- apply Vector_more.inj_pairT2_nat in H2 ; subst.
         apply IHl...
         intros.
         eapply H...
         inversion H0 ; subst.
         ++ left.
         ++ apply Vector_more.inj_pairT2_nat in H8 ; subst.
            right ; right...
  + intros.
    eapply H...
    right...
Qed.

Lemma AFCvec_incdep : forall m (P : nat -> forall n, n < m -> Prop),
  (forall i n H1 H2, P i n H1 -> P i n H2) ->
  (forall n H i j, P i n H -> i <= j -> P j n H) ->
    (forall n H, exists k, P k n H) -> exists k, forall n H, P k n H.
Proof with try eassumption.
induction m ; intros P Hext Hinc HI.
- exists 0 ; intros n Hn ; inversion Hn.
- assert (forall n H, exists k, P k n (lt_S _ _ H)) as Hm
    by (intros ; apply HI).
  apply IHm in Hm.
  + destruct Hm as [k Hk].
    assert (exists k, P k m (lt_n_Sn _)) as [k' Hk'] by (apply HI).
    exists (max (S k) (S k')).
    intros n Hn.
    inversion Hn ; subst.
    * apply (Hinc _ _ k').
      -- eapply Hext ; apply Hk'.
      -- etransitivity ; [ apply le_n_Sn | apply le_max_r ].
    * apply (Hinc _ _ k)...
      -- eapply Hext ; apply (Hk _ H0).
      -- etransitivity ; [ apply le_n_Sn | apply le_max_l ].
  + intros ; eapply Hext...
  + intros ; apply (Hinc _ _ i)...
Qed.






