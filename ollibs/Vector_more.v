(* Vector_more Library *)

(** * Add-ons for Vector library
Usefull properties apparently missing in the Vector library. *)


Require Import Peano_dec Lt.
Require Export Vector.


(* Decidability over nat for decomposing vectors with inj_pairT2 *)
Require Import Eqdep_dec.


Lemma inj_pairT2_nat : forall (P:nat -> Type) p x y,
  existT P p x = existT P p y -> x = y.
Proof.
apply inj_pair2_eq_dec.
apply eq_nat_dec.
Qed.

Lemma case0_nil {A} : forall (v : t A 0) P, P (nil A) -> P v.
Proof.
intros.
apply case0.
assumption.
Qed.

Lemma nth_order_ext {A n} : forall k (H1 H2 : k < n) (v : t A n),
  nth_order v H1 = nth_order v H2.
Proof.
intros.
unfold nth_order.
rewrite (Fin.of_nat_ext H1 H2).
reflexivity.
Qed.

Lemma hd_nth_order {A n} : forall (H : 0 < S n) (v : t A (S n)),
  hd v = nth_order v H.
Proof.
intros.
rewrite (eta v).
reflexivity.
Qed.

Lemma nth_order_tl {A n} : forall k (H : k < n) (HS : S k < S n)(v : t A (S n)),
  nth_order (tl v) H = nth_order v HS.
Proof.
induction n ; intros.
- inversion H.
- rewrite (eta v).
  unfold nth_order.
  simpl.
  rewrite (Fin.of_nat_ext H (Lt.lt_S_n _ _ HS)).
  reflexivity.
Qed.

Lemma nth_order_replace_eq {A n} : forall k (H1 : k < n) (H2 : k < n) (v : t A n) a,
  nth_order (replace v (Fin.of_nat_lt H2) a) H1 = a.
Proof.
intros k ; revert n ; induction k ; intros ; (destruct n ; [ inversion H1 | subst ]).
- rewrite <- hd_nth_order.
  rewrite (eta v) ; reflexivity.
- rewrite <- (nth_order_tl _ (lt_S_n _ _ H1)).
  rewrite (eta v).
  apply IHk.
Qed.

Lemma nth_order_replace_neq {A n} : forall k1 k2, k1 <> k2 ->
  forall (H1 : k1 < n) (H2 : k2 < n) (v : t A n) a,
  nth_order (replace v (Fin.of_nat_lt H2) a) H1 = nth_order v H1.
Proof.
intros k1 ; revert n ; induction k1 ; intros ; (destruct n ; [ inversion H1 | subst ]).
- rewrite <- 2 hd_nth_order.
  destruct k2.
  + exfalso ; apply H ; reflexivity.
  + rewrite 2 (eta v) ; reflexivity.
- rewrite <- 2 (nth_order_tl _ (lt_S_n _ _ H1)).
  rewrite 2 (eta v).
  destruct k2.
  + reflexivity.
  + apply IHk1.
    intros Hk ; apply H ; rewrite Hk ; reflexivity.
Qed.


Lemma replace_replace_eq {A n} : forall p (v : t A n) a b,
  replace (replace v p a) p b = replace v p b.
Proof.
intros.
induction p ; rewrite 2 (eta v) ; simpl.
- reflexivity.
- f_equal.
  apply IHp.
Qed.

Lemma replace_id {A n} : forall p (v : t A n),
  replace v p (nth v p) = v.
Proof.
induction p ; intros ; rewrite 2 (eta v) ; simpl ; try reflexivity.
f_equal.
apply IHp.
Qed.


Lemma Forall_impl {A} : forall (P Q : A -> Prop), (forall a, P a -> Q a) ->
  forall n (v : t A n), Forall P v -> Forall Q v.
Proof.
induction v ; intros HP ; constructor ;
  inversion HP ; apply inj_pairT2_nat in H2 ; subst ; intuition.
Qed.


Lemma Forall_In {A} : forall P n (v : t A n) a, Forall P v -> In a v -> P a.
Proof.
intros P n v a HP Hin.
revert HP ; induction Hin ; intros HP ; inversion HP ; subst.
- assumption.
- apply inj_pairT2_nat in H1 ; subst ; auto.
Qed.

Lemma inc_Forall {A n} : forall (P : nat -> A -> Prop) (v : t A n) i j,
  (forall i j a, P i a -> i <= j -> P j a) ->
    Forall (P i) v -> i <= j -> Forall (P j) v.
Proof with try eassumption.
intros P v i j Hinc.
induction v ; intros H Hv ; constructor ; inversion H.
- eapply Hinc...
- apply inj_pairT2_nat in H2 ; subst.
  apply IHv...
Qed.

Lemma Forall_nth_order {A} : forall P n (v : t A n),
  Forall P v -> forall i (Hi : i < n), P (nth_order v Hi).
Proof with try assumption.
induction n ; intros.
- inversion Hi.
- rewrite (eta v).
  rewrite (eta v) in H.
  inversion H ; subst.
  apply inj_pairT2_nat in H2 ; subst.
  destruct i.
  + rewrite <- hd_nth_order...
  + rewrite <- (nth_order_tl _ (lt_S_n _ _ Hi) Hi).
    apply IHn...
Qed.

Lemma nth_order_Forall {A} : forall (P : A -> Prop) n (v : t A n),
  (forall i (Hi : i < n), P (nth_order v Hi)) -> Forall P v.
Proof with try assumption.
induction n ; intros.
- apply case0.
  constructor.
- rewrite (eta v).
  rewrite (eta v) in H.
  constructor.
  + specialize H with 0 (lt_0_Sn n).
    rewrite <- hd_nth_order in H...
  + apply IHn ; intros.
    specialize H with (S i) (lt_n_S _ _ Hi).
    rewrite <- (nth_order_tl _ Hi) in H...
Qed.

Lemma Forall2_nth_order {A} : forall P n (v1 v2 : t A n),
  Forall2 P v1 v2 -> forall i (Hi : i < n), P (nth_order v1 Hi) (nth_order v2 Hi).
Proof with try assumption.
induction n ; intros.
- inversion Hi.
- rewrite (eta v1).
  rewrite (eta v1) in H.
  rewrite (eta v2).
  rewrite (eta v2) in H.
  inversion H ; subst.
  apply inj_pairT2_nat in H2 ; subst.
  apply inj_pairT2_nat in H5 ; subst.
  destruct i.
  + rewrite <- hd_nth_order...
  + rewrite <- 2 (nth_order_tl _ (lt_S_n _ _ Hi) Hi).
    apply IHn...
Qed.

Lemma nth_order_Forall2 {A} : forall (P : A -> A -> Prop) n (v1 v2 : t A n),
  (forall i (Hi : i < n), P (nth_order v1 Hi) (nth_order v2 Hi)) -> Forall2 P v1 v2.
Proof with try assumption.
induction n ; intros.
- apply case0.
  apply (case0_nil v1).
  constructor.
- rewrite (eta v1).
  rewrite (eta v1) in H.
  rewrite (eta v2).
  rewrite (eta v2) in H.
  constructor.
  + specialize H with 0 (lt_0_Sn _).
    rewrite <- hd_nth_order in H...
  + apply IHn ; intros.
    specialize H with (S i) (lt_n_S _ _ Hi).
    rewrite <- 2 (nth_order_tl _ Hi) in H...
Qed.


