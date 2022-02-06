(** Boolean-valued total orders as a [Class] *)

From Coq Require Import Bool PeanoNat Wf_nat Lia List Orders.
From Yalla.OLlibs Require Import funtheory.

Set Implicit Arguments.

(** * Class of Boolean-valued total orders *)

Definition brelation A := A -> A -> bool.

Class BOrder := {
  car : Type ;
  leb : brelation car ;
  total : forall a b, leb a b = false -> leb b a = true ;
  asym :  forall a b, leb a b = true -> leb b a = true -> a = b ;
  trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true
}.

(** ** Equivalence with [UsualOrderedTypeFull] *)
Module Type ModBOrder.
  Parameter t : BOrder.
End ModBOrder.

Module ModBOrder_as_UsualOrderedTypeFull (B : ModBOrder) : UsualOrderedTypeFull.

  Definition t := @car B.t.
  Definition eq := @eq (@car B.t).
  Definition eq_equiv : Equivalence eq := eq_equivalence.
  #[local] Coercion is_true : bool >-> Sortclass.
  Definition lt x y := @leb B.t x y /\ x <> y.

  Lemma lt_strorder : StrictOrder lt.
  Proof.
  split.
  - intros a.
    unfold complement.
    intros [Hleq Hneq].
    apply Hneq ; reflexivity.
  - intros a b c [Hleq1 Hneq1] [Hleq2 Hneq2] ; split.
    + eapply trans ; eassumption.
    + intros Heq ; subst.
      case_eq (leb b c); intros Heqbb ;
        [ case_eq (leb c b); intros Heqbb2 | ].
      * apply asym in Heqbb ; try assumption ; subst.
        apply Hneq1 ; reflexivity.
      * rewrite Heqbb2 in Hleq1; inversion Hleq1.
      * rewrite Heqbb in Hleq2; inversion Hleq2.
  Qed.

  Lemma lt_compat : Proper (eq==>eq==>iff) lt.
  Proof.
  intros a b H1 c d H2; unfold eq in H1, H2; subst; reflexivity.
  Qed.

  Definition compare x y :=
    if @leb B.t x y then (if leb y x then Eq else Lt) else Gt.

  Lemma compare_spec x y : CompSpec eq lt x y (compare x y).
  Proof.
  unfold compare.
  case_eq (leb x y).
  - case_eq (leb y x); intros Hleby Hlebx; constructor.
    + apply asym; assumption.
    + split; try assumption.
      intros Heq; subst.
      rewrite Hlebx in Hleby; inversion Hleby.
  - intros Hlebx; constructor.
    assert (Ht := total _ _ Hlebx).
    split; try assumption.
    intros Heq; subst.
    rewrite Ht in Hlebx; inversion Hlebx.
  Qed.

  Lemma eq_dec x y : {eq x y} + {eq x y -> False}.
  Proof.
  case_eq (leb x y); case_eq (leb y x); intros Heq1 Heq2.
  - apply asym in Heq1; subst; intuition.
  - right; intros Heq; unfold eq in Heq; subst.
    rewrite Heq1 in Heq2; inversion Heq2.
  - right; intros Heq; unfold eq in Heq; subst.
    rewrite Heq1 in Heq2; inversion Heq2.
  - apply total in Heq1.
    rewrite Heq1 in Heq2; inversion Heq2.
  Qed.

  Definition le x y := is_true (@leb B.t x y).

  Lemma le_lteq x y : le x y <-> lt x y \/ eq x y.
  Proof.
  split.
  - intros Hle.
    destruct (eq_dec x y).
    + right ; assumption.
    + left ; split ; assumption.
  - intros [[Hle Heq] | Heq]; auto.
    rewrite Heq.
    case_eq (leb y y); intros Heq2.
    + unfold le; rewrite Heq2; reflexivity.
    + exfalso.
      assert (Heq3 := total _ _ Heq2).
      rewrite Heq2 in Heq3; inversion Heq3.
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
  unfold leb; intros Hcmp.
  apply T.le_lteq.
  destruct (T.compare_spec x y) as [ Heq | Hlt | Hgt ] ;
    try reflexivity.
  - right; assumption.
  - left; assumption.
  - discriminate.
  Qed.

  Lemma le_leb x y : T.le x y -> leb x y = true.
  Proof.
  intros Hle.
  unfold leb.
  destruct (T.compare_spec x y) as [ Heq | Hlt | Hgt] ;
    intros ; try reflexivity.
  destruct (StrictOrder_Irreflexive x).
  apply T.le_lteq in Hle.
  destruct Hle as [ Hlt | Heq ].
  - transitivity y; assumption.
  - rewrite <- Heq in Hgt; assumption.
  Qed.

  Lemma nleb_lt x y : leb x y = false -> T.lt y x.
  Proof.
  unfold leb; intros Hleb.
  destruct (T.compare_spec x y) as [ Heq | Hlt | Hgt] ;
    try reflexivity ; try discriminate ; try assumption.
  Qed.

  Lemma lt_nleb x y : T.lt y x -> leb x y = false.
  Proof.
  intros Hlty.
  unfold leb.
  destruct (T.compare_spec x y) as [ Heq | Hlt | Hgt] ;
    intros ; try reflexivity ; subst.
  - apply StrictOrder_Irreflexive in Hlty.
    destruct Hlty.
  - apply (StrictOrder_Transitive _ _ _ Hlty) in Hlt.
    apply StrictOrder_Irreflexive in Hlt.
    destruct Hlt.
  Qed.

  Lemma to_BOrder : BOrder.
  Proof.
  split with T.t leb.
  - intros a b Hf.
    apply nleb_lt in Hf.
    apply le_leb.
    apply T.le_lteq.
    left ; assumption.
  - intros a b H1 H2.
    apply leb_le in H1.
    apply leb_le in H2.
    apply T.le_lteq in H1.
    apply T.le_lteq in H2.
    destruct H1 as [H1|H1], H2 as [H2|H2]; auto.
    apply (StrictOrder_Transitive _ _ _ H2) in H1.
    apply StrictOrder_Irreflexive in H1.
    destruct H1.
  - intros a b c H1 H2.
    apply le_leb ; apply T.le_lteq.
    apply leb_le in H1.
    apply leb_le in H2.
    apply T.le_lteq in H1.
    apply T.le_lteq in H2.
    destruct H1 ; destruct H2 ; subst.
    + left ; transitivity b ; assumption.
    + left ; assumption.
    + left ; assumption.
    + right ; reflexivity.
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
  case (Nat.compare_spec a b); intros Ho; apply Nat.leb_le; try lia.
  exfalso.
  eapply or_introl, Nat.le_lteq, Nat.leb_le in Ho.
  rewrite Ho in Hleb; inversion Hleb.
- intros Hleb Hleb2.
  apply Nat.leb_le in Hleb.
  apply Nat.leb_le in Hleb2; lia.
- intros c Hleb Hleb2.
  apply Nat.leb_le in Hleb.
  apply Nat.leb_le in Hleb2.
  apply Nat.leb_le; lia.
Defined.

Lemma border_inj A B (f : A -> @car B) (Hi : injective f) : BOrder.
Proof.
split with A (fun x y => leb (f x) (f y)) ; intros.
- now apply total.
- apply Hi.
  now apply asym.
- now apply trans with (f b).
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
induction l ; simpl.
- case_eq (leb x y); case_eq (leb y x); intros Heqbb1 Heqbb2; auto.
  + now apply (asym _ _ Heqbb1) in Heqbb2; subst.
  + apply total in Heqbb1.
    rewrite Heqbb1 in Heqbb2 ; now discriminate Heqbb2.
- case_eq (leb x a); case_eq (leb y a); intros Heqbb1 Heqbb2; simpl;
    try rewrite Heqbb1; try rewrite Heqbb2.
  + case_eq (leb x y); case_eq (leb y x); intros Heqbb Heqbb';
      try rewrite Heqbb1; try rewrite Heqbb2; auto.
    * now apply (asym _ _ Heqbb) in Heqbb'; subst.
    * apply total in Heqbb.
      rewrite Heqbb in Heqbb'; now discriminate Heqbb'.
  + case_eq (leb y x); intros Heqbb';
      try rewrite Heqbb1; try rewrite Heqbb2; auto.
    apply (trans _ _ _ Heqbb') in Heqbb2.
    rewrite Heqbb1 in Heqbb2 ; now discriminate Heqbb2.
  + case_eq (leb x y); intros Heqbb;
      try rewrite Heqbb1 ; try rewrite Heqbb2; auto.
    apply (trans _ _ _ Heqbb) in Heqbb1.
    rewrite Heqbb1 in Heqbb2 ; now discriminate Heqbb2.
  + now rewrite IHl.
Qed.

(** ** Sorted lists *)

Fixpoint is_sorted B (l : list (@car B)) :=
match l with
| nil => true
| a :: nil => true
| a :: (b :: _) as r => leb a b && is_sorted B r
end.
Arguments is_sorted {_} _.

Lemma is_sorted_tail B a l :
  @is_sorted B (a :: l) = true -> is_sorted l = true.
Proof.
intros Hs; destruct l.
- reflexivity.
- apply andb_true_iff in Hs.
  apply Hs.
Qed.

Definition SortedList B := { m | @is_sorted B m = true }.

Lemma sortedlist_equality B (m1 m2 : SortedList B) :
  proj1_sig m1 = proj1_sig m2 -> m1 = m2.
Proof.
intros Heq.
destruct m1 as [m1' B1].
destruct m2 as [m2' B2].
simpl in Heq; subst.
f_equal.
apply (Eqdep_dec.UIP_dec bool_dec).
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
- intro Heq; discriminate Heq.
- intros c Hc.
  inversion Hc as [ -> | Hin ].
  + now right.
  + inversion Hin.
- unfold l; simpl.
  case_eq (leb a c); intros Heqbb.
  + now apply andb_true_iff; split.
  + destruct s; inversion Hlen.
    destruct (IH s (le_n _) a (exist _ l0 (is_sorted_tail _ _ _ Hsort)) H0)
      as [Hsort' _].
    apply total in Heqbb.
    destruct l0 ; try (apply andb_true_iff ; split); auto.
    simpl; simpl in Hsort'.
    destruct (leb a c0); apply andb_true_iff; split; auto.
    clear Hlen l; simpl in Hsort.
    apply andb_true_iff in Hsort.
    apply Hsort.
- intro Heq; unfold l in Heq; simpl in Heq.
  destruct (leb a c); discriminate Heq.
- intros d Hd; unfold l in Hd; simpl in Hd.
  destruct (leb a c).
  + now inversion Hd as [ -> | ]; [ right | left ].
  + inversion Hd as [ -> | Hin ].
    * now left; left.
    * destruct s; inversion Hlen as [ Hlen' ].
      destruct (IH s (le_n _) a (exist _ l0 (is_sorted_tail _ _ _ Hsort)) Hlen')
        as [_ Hin'].
      apply Hin' in Hin.
      now destruct Hin; [ left; apply in_cons | right ].
Qed.
