(** Boolean-valued total orders as a [Class] *)

From Coq Require Import Bool PeanoNat Wf_nat Lia List Orders.
From Yalla.OLlibs Require Import funtheory.

Set Implicit Arguments.

(** * Class of Boolean-valued total orders *)

Definition brelation A := A -> A -> bool.

Class BOrder := {
  car : Type;
  leb : brelation car;
  total a b : leb a b = false -> leb b a = true;
  asym a b : leb a b = true -> leb b a = true -> a = b;
  trans a b c : leb a b = true -> leb b c = true -> leb a c = true }.
Coercion car : BOrder >-> Sortclass. (* TODO integrate as [car :> Type] when available for coercion *)

(** ** Equivalence with [UsualOrderedTypeFull] *)
Module Type ModBOrder.
  Parameter t : BOrder.
End ModBOrder.

Module ModBOrder_as_UsualOrderedTypeFull (B : ModBOrder) : UsualOrderedTypeFull.

  Definition t := @car B.t.
  Definition eq := @eq B.t.
  Definition eq_equiv : Equivalence eq := eq_equivalence.
  #[local] Coercion is_true : bool >-> Sortclass.
  Definition lt x y := @leb B.t x y /\ x <> y.

  Lemma lt_strorder : StrictOrder lt.
  Proof.
  split.
  - intros a [Hleq Hneq]. apply Hneq. reflexivity.
  - intros a b c [Hleq1 Hneq1] [Hleq2 Hneq2]. split.
    + eapply trans; eassumption.
    + intros ->.
      destruct (leb b c) eqn: Heqbb1; [ destruct (leb c b) eqn:Heqbb2 | ].
      * apply asym in Heqbb1 as ->; [ | assumption ].
        apply Hneq1. reflexivity.
      * discriminate Hleq1.
      * discriminate Hleq2.
  Qed.

  Lemma lt_compat : Proper (eq==>eq==>iff) lt.
  Proof. intros a b H1 c d H2. unfold eq in H1, H2. subst. reflexivity. Qed.

  Definition compare x y := if @leb B.t x y then (if leb y x then Eq else Lt) else Gt.

  Lemma compare_spec x y : CompSpec eq lt x y (compare x y).
  Proof.
  unfold compare.
  destruct (leb x y) eqn:Hlebx; [ destruct (leb y x) eqn:Hleby | ]; constructor.
  - apply asym; assumption.
  - split; [ assumption | ].
    intros ->.
    rewrite Hlebx in Hleby. discriminate Hleby.
  - assert (Ht := total _ _ Hlebx).
    split; [ assumption | ].
    intros ->.
    rewrite Ht in Hlebx. discriminate Hlebx.
  Qed.

  Lemma eq_dec x y : {eq x y} + {eq x y -> False}.
  Proof.
  destruct (leb x y) eqn:Heq1, (leb y x) eqn:Heq2.
  - destruct (asym _ _ Heq1 Heq2). left. reflexivity.
  - right. intros Heq. unfold eq in Heq. subst.
    rewrite Heq1 in Heq2. discriminate Heq2.
  - right. intros Heq. unfold eq in Heq. subst.
    rewrite Heq1 in Heq2. discriminate Heq2.
  - apply total in Heq1. rewrite Heq1 in Heq2. discriminate Heq2.
  Qed.

  Definition le x y := is_true (@leb B.t x y).

  Lemma le_lteq x y : le x y <-> lt x y \/ eq x y.
  Proof.
  split.
  - intro Hle.
    destruct (eq_dec x y).
    + right. assumption.
    + left. split; assumption.
  - intros [[Hle Heq] | ->]; [ assumption | ].
    destruct (leb y y) eqn:Heq2.
    + assumption.
    + exfalso.
      assert (Heq3 := total _ _ Heq2).
      rewrite Heq2 in Heq3. discriminate Heq3.
  Qed.

End ModBOrder_as_UsualOrderedTypeFull.

Module UsualOrderedTypeFull_as_BOrder (T : UsualOrderedTypeFull).

  Definition leb x y :=
  match T.compare x y with
  | Gt => false
  | _  => true
  end.

  Lemma leb_le x y : leb x y = true -> T.le x y.
  Proof.
  unfold leb. intro Hcmp.
  apply T.le_lteq.
  destruct (T.compare_spec x y) as [ Heq | Hlt | Hgt ].
  - right. assumption.
  - left. assumption.
  - discriminate Hcmp.
  Qed.

  Lemma le_leb x y : T.le x y -> leb x y = true.
  Proof.
  intro Hle. unfold leb.
  destruct (T.compare_spec x y) as [ Heq | Hlt | Hgt]; [ reflexivity | reflexivity | ].
  destruct (StrictOrder_Irreflexive x).
  apply T.le_lteq in Hle as [ Hlt | -> ].
  - transitivity y; assumption.
  - assumption.
  Qed.

  Lemma nleb_lt x y : leb x y = false -> T.lt y x.
  Proof.
  unfold leb. intro Hleb.
  destruct (T.compare_spec x y) as [ Heq | Hlt | Hgt]; [ discriminate Hleb | discriminate Hleb | assumption ].
  Qed.

  Lemma lt_nleb x y : T.lt y x -> leb x y = false.
  Proof.
  unfold leb. intro Hlty.
  destruct (T.compare_spec x y) as [ -> | Hlt | Hgt]; [ | | reflexivity ].
  - apply StrictOrder_Irreflexive in Hlty as [].
  - apply (StrictOrder_Transitive _ _ _ Hlty) in Hlt.
    apply StrictOrder_Irreflexive in Hlt as [].
  Qed.

  Lemma to_BOrder : BOrder.
  Proof.
  split with T.t leb.
  - intros a b Hf%nleb_lt. apply le_leb, T.le_lteq.
    left. assumption.
  - intros a b [H1|H1]%leb_le%T.le_lteq [H2|H2]%leb_le%T.le_lteq; auto.
    apply (StrictOrder_Transitive _ _ _ H2) in H1.
    apply StrictOrder_Irreflexive in H1 as [].
  - intros a b c [ H1 | -> ]%leb_le%T.le_lteq [ H2 | -> ]%leb_le%T.le_lteq; apply le_leb, T.le_lteq.
    + left. transitivity b; assumption.
    + left. assumption.
    + left. assumption.
    + right. reflexivity.
  Qed.

End UsualOrderedTypeFull_as_BOrder.

Module UsualOrderedTypeFull_as_ModBOrder (T : UsualOrderedTypeFull) : ModBOrder.
  Module TBOrder := UsualOrderedTypeFull_as_BOrder T.
  Definition t := TBOrder.to_BOrder.
End UsualOrderedTypeFull_as_ModBOrder.


(** * [BOrder] structure over [nat]. *)
#[export] Instance border_nat : BOrder.
Proof.
split with nat Nat.leb; intros a b.
- intros Hleb.
  case (Nat.compare_spec a b); intros Ho; apply Nat.leb_le; [ lia | | lia ].
  exfalso.
  eapply or_introl, Nat.le_lteq, Nat.leb_le in Ho.
  rewrite Ho in Hleb. discriminate Hleb.
- intros Hleb%Nat.leb_le Hleb2%Nat.leb_le. lia.
- intros c Hleb%Nat.leb_le Hleb2%Nat.leb_le. apply Nat.leb_le. lia.
Defined.

Lemma border_inj A B (f : A -> @car B) (Hi : injective f) : BOrder.
Proof.
split with A (fun x y => leb (f x) (f y)); intros.
- apply total. assumption.
- apply Hi, asym; assumption.
- apply trans with (f b); assumption.
Defined.


(** * Sorted lists over [BOrder] *)

(** ** Insertion sort *)

Fixpoint insert B (a : @car B) l :=
match l with
| nil => a :: nil
| b :: t => if (leb a b) then a :: b :: t
                         else b :: (insert B a t)
end.
Arguments insert {_} _ _.

Lemma insert_insert B : forall (x y : @car B) l,
  insert y (insert x l) = insert x (insert y l).
Proof.
induction l as [|a l IHl]; cbn.
- destruct (leb x y) eqn:Heqbb1, (leb y x) eqn:Heqbb2; try reflexivity.
  + apply (asym _ _ Heqbb1) in Heqbb2 as ->. reflexivity.
  + apply total in Heqbb1. rewrite Heqbb1 in Heqbb2. discriminate Heqbb2.
- destruct (leb x a) eqn:Heqbb1, (leb y a) eqn:Heqbb2; cbn.
  + destruct (leb x y) eqn:Heqbb, (leb y x) eqn:Heqbb'; rewrite ? Heqbb1, ? Heqbb2; try reflexivity.
    * apply (asym _ _ Heqbb') in Heqbb as ->. reflexivity.
    * apply total in Heqbb'. rewrite Heqbb' in Heqbb. discriminate Heqbb.
  + destruct (leb y x) eqn:Heqbb'; rewrite ? Heqbb1, ? Heqbb2; try reflexivity.
    apply (trans _ _ _ Heqbb') in Heqbb1. rewrite Heqbb1 in Heqbb2. discriminate Heqbb2.
  + destruct (leb x y) eqn:Heqbb; rewrite ? Heqbb1, ? Heqbb2; try reflexivity.
    apply (trans _ _ _ Heqbb) in Heqbb2. rewrite Heqbb1 in Heqbb2. discriminate Heqbb2.
  + rewrite Heqbb1, Heqbb2, IHl. reflexivity.
Qed.

(** ** Sorted lists *)

Fixpoint is_sorted B (l : list (@car B)) :=
match l with
| nil => true
| a :: nil => true
| a :: (b :: _) as r => leb a b && is_sorted B r
end.
Arguments is_sorted {_} _.

Lemma is_sorted_tail B a l : @is_sorted B (a :: l) = true -> is_sorted l = true.
Proof. intros Hs. destruct l as [|b l]; [ reflexivity | apply andb_true_iff in Hs; apply Hs ]. Qed.

Definition SortedList B := { m | @is_sorted B m = true }.

Lemma sortedlist_equality B (m1 m2 : SortedList B) : proj1_sig m1 = proj1_sig m2 -> m1 = m2.
Proof.
destruct m1 as [m1' B1], m2 as [m2' B2]. cbn. intros ->.
f_equal. apply (Eqdep_dec.UIP_dec bool_dec).
Qed.

Lemma insert_sorted B a (m : SortedList B) :
  let l := insert a (proj1_sig m) in
    is_sorted l = true /\ l <> nil
 /\ forall c, In c l -> In c (proj1_sig m) \/ c = a.
Proof.
enough (forall s a (m : SortedList B),
  length (proj1_sig m) = s ->
  let l := insert a (proj1_sig m) in
    is_sorted l = true /\ l <> nil
 /\ forall c, In c l -> In c (proj1_sig m) \/ c = a) as Hlen
  by now intros; apply Hlen with (length (proj1_sig m)).
induction s as [s IH] using (well_founded_induction lt_wf).
clear a m; intros a m Hlen l.
destruct m as [l0 Hsort].
destruct l0; repeat split; auto.
- intros [=].
- intros c Hc.
  inversion Hc as [ -> | [] ].
  right. reflexivity.
- unfold l. cbn.
  destruct (leb a c) eqn:Heqbb.
  + now apply andb_true_iff; split.
  + destruct s; inversion Hlen.
    destruct (IH s (le_n _) a (exist _ l0 (is_sorted_tail _ _ _ Hsort)) H0)
      as [Hsort' _].
    apply total in Heqbb.
    destruct l0 ; try (apply andb_true_iff ; split); auto.
    simpl; simpl in Hsort'.
    destruct (leb a c0); apply andb_true_iff; split; auto.
    clear Hlen l. simpl in Hsort.
    apply andb_true_iff in Hsort. apply Hsort.
- intro Heq. unfold l in Heq. cbn in Heq.
  destruct (leb a c); discriminate Heq.
- intros d Hd. unfold l in Hd. cbn in Hd.
  destruct (leb a c).
  + inversion Hd as [ -> | ]; [ right | left ]; trivial.
  + inversion Hd as [ -> | Hin ].
    * left. apply in_eq.
    * destruct s; inversion Hlen as [ Hlen' ].
      destruct (IH s (le_n _) a (exist _ l0 (is_sorted_tail _ _ _ Hsort)) Hlen') as [_ Hin'].
      apply Hin' in Hin.
      destruct Hin; [ left; apply in_cons | right ]; assumption.
Qed.
