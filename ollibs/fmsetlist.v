(* fmsetlist Library *)
(* v0   Olivier Laurent *)


(** * Finite Multiset over Lists
   We define an axiomatization of finite multisets through their relation with lists.
   Equality is required to be Coq equality.
   An implementation of the axioms is provided by sorted lists
   for every type equiped with a Boolean-valued total order relation *)

Require Import Le.
Require Import Compare_dec.
Require Import Wf_nat.
Require Import List.
Require Import Morphisms.
Require Import Orders.

Require Import Bool_more.
Require Import Injective.
Require Import Permutation_more.


(** * Axiomatization *)

(** A finite multiset with elements in [A] is a type [M]
    related with [list A] as follows: *)
Class FinMultiset M A := {
  empty : M;
  add : A -> M -> M;
  elts : M -> list A;
  elts_empty : elts empty = @nil A;
  elts_add : forall a m, Permutation (elts (add a m)) (a :: elts m);
  elts_retract : forall m, fold_right add empty (elts m) = m;
  perm_eq : forall l1 l2, Permutation l1 l2 ->
                  fold_right add empty l1 = fold_right add empty l2
}.

(** [Mst] and [Elt] define a finite multiset construction over a type [K]
    if for any [A] in [K], [Mst A] is a finite multiset with elements [Elt A]. *)
Definition FMConstructor K Mst Elt := forall A : K, FinMultiset (Mst A) (Elt A).


(** * Constructions and properties over finite multisets *)

Section FMSet2List.

Context {M A : Type}.
Context {fm : FinMultiset M A}.

Definition list2fm l := fold_right add empty l.

Global Instance list2fm_perm : Proper (@Permutation A ==> eq) list2fm
  := perm_eq.

Lemma list2fm_retract : forall m, list2fm (elts m) = m.
Proof. apply elts_retract. Qed.

Lemma list2fm_nil : list2fm nil = empty.
Proof. reflexivity. Qed.

Lemma list2fm_elt : forall l1 l2 a,
  list2fm (l1 ++ a :: l2) = add a (list2fm (l1 ++ l2)).
Proof.
intros l1 l2 a.
change (add a (list2fm (l1 ++ l2)))
  with (list2fm (a :: l1 ++ l2)).
apply perm_eq.
symmetry.
apply Permutation_middle.
Qed.

Lemma list2fm_cons : forall l a, list2fm (a :: l) = add a (list2fm l).
Proof.
intros l a.
rewrite <- (app_nil_l (a :: l)).
rewrite list2fm_elt.
reflexivity.
Qed.

Lemma elts_perm : forall l, Permutation (elts (list2fm l)) l.
Proof.
induction l ; simpl.
- rewrite elts_empty.
  reflexivity.
- rewrite elts_add.
  rewrite IHl.
  reflexivity.
Qed.

Global Instance elts_perm' : Proper (eq ==> @Permutation A) elts.
Proof.
intros m1 m2 Heq ; subst.
reflexivity.
Qed.

Lemma elts_eq_nil : forall m, elts m = nil -> m = empty.
Proof.
intros m Heq.
assert (Hr := elts_retract m) ; rewrite Heq in Hr ; simpl in Hr.
subst ; reflexivity.
Qed.

Lemma add_swap : forall m a b, add a (add b m) = add b (add a m).
Proof.
intros m a b.
rewrite <- list2fm_retract.
rewrite <- list2fm_retract at 1.
rewrite 4 elts_add.
rewrite perm_swap.
reflexivity.
Qed.

Definition sum m1 m2 := list2fm (elts m1 ++ elts m2).

Lemma elts_sum : forall m1 m2,
  Permutation (elts (sum m1 m2)) (elts m1 ++ elts m2).
Proof.
intros.
apply elts_perm.
Qed.

Lemma sum_empty_left : forall m, sum empty m = m.
Proof.
intros m.
unfold sum.
rewrite elts_empty.
apply elts_retract.
Qed.

Lemma sum_empty_right : forall m, sum m empty = m.
Proof.
intros m.
unfold sum.
rewrite elts_empty.
rewrite app_nil_r.
apply elts_retract.
Qed.

Lemma sum_comm : forall m1 m2, sum m1 m2 = sum m2 m1.
Proof.
intros m1 m2.
unfold sum.
rewrite Permutation_app_comm.
reflexivity.
Qed.

Lemma sum_ass : forall m1 m2 m3, sum (sum m1 m2) m3 = sum m1 (sum m2 m3).
Proof.
intros m1 m2 m3.
unfold sum.
apply perm_eq.
etransitivity.
- apply Permutation_app_tail.
  apply elts_perm.
- rewrite <- app_assoc.
  apply Permutation_app_head.
  symmetry.
  apply elts_perm.
Qed.

Lemma list2fm_app : forall l1 l2,
  list2fm (l1 ++ l2) = sum (list2fm l1) (list2fm l2).
Proof.
intros l1 l2.
unfold sum.
apply perm_eq.
etransitivity.
- apply Permutation_app_tail.
  symmetry.
  apply elts_perm.
- apply Permutation_app_head.
  symmetry.
  apply elts_perm.
Qed.

End FMSet2List.


Section Fmmap.

Context {M A N B : Type}.
Context {fm : FinMultiset M A}.
Context {fm' : FinMultiset N B}.
Variable f : A -> B.

Definition fmmap (m : M) := list2fm (map f (elts m)).

Lemma list2fm_map : forall l, list2fm (map f l) = fmmap (list2fm l).
Proof.
intros l.
apply perm_eq.
apply Permutation_map.
symmetry.
apply elts_perm.
Qed.

Lemma elts_fmmap : forall m, Permutation (elts (fmmap m)) (map f (elts m)).
Proof.
intros m.
rewrite <- (elts_retract m).
remember (elts m) as l.
clear m Heql.
induction l.
- simpl.
  unfold fmmap.
  rewrite elts_empty.
  simpl.
  rewrite elts_empty.
  reflexivity.
- apply elts_perm.
Qed.

End Fmmap.


Section Induction.

Context {M A : Type}.
Context {fm : FinMultiset M A}.

Lemma fm_rect : forall (P : M -> Type),
  P empty -> (forall a m, P m -> P (add a m)) -> forall m, P m.
Proof.
intros P He Ha m.
remember (elts m) as l.
assert (HP := Permutation_refl l).
rewrite Heql in HP at 2 ; clear Heql.
revert m HP ; induction l ; intros m Heql.
- apply Permutation_nil in Heql.
  apply elts_eq_nil in Heql ; subst ; assumption.
- assert (Hr := elts_retract m).
  symmetry in Heql ; rewrite (perm_eq _ _ Heql) in Hr ; simpl in Hr ; subst.
  apply Ha.
  apply IHl.
  symmetry.
  change (fold_right add empty l) with (list2fm l).
  apply elts_perm.
Defined.

Lemma fm_ind : forall (P : M -> Prop),
  P empty -> (forall a m, P m -> P (add a m)) -> forall m, P m.
Proof.
intros ; apply fm_rect ; assumption.
Defined.

Lemma fm_rec : forall (P : M -> Set),
  P empty -> (forall a m, P m -> P (add a m)) -> forall m, P m.
Proof.
intros ; apply fm_rect ; assumption.
Defined.

End Induction.


(** * Notations *)

Module FMSetNotations.
Infix ":::" := add (at level 60, right associativity).
Infix "+++" := sum (right associativity, at level 60).
Notation " [[ ]] " := empty.
Notation " [[ x ]] " := (add x empty).
Notation " [[ x ; .. ; y ]] " := (add x .. (add y empty) ..).
End FMSetNotations.


(** * Class of Boolean-valued total orders *)

Definition BRelation A := A -> A -> bool.

Class BOrder := {
  carrier : Type ;
  leqb : BRelation carrier ;
  total : forall a b, leqb a b = false -> leqb b a = true ;
  asym :  forall a b, leqb a b = true -> leqb b a = true -> a = b ;
  trans : forall a b c, leqb a b = true -> leqb b c = true -> leqb a c = true
}.

(** Equivalence with UsualOrderedTypeFull. *)
Module BOrder_to_UsualOrderedTypeFull : UsualOrderedTypeFull.

  Parameter B : BOrder.

  Definition t := @carrier B.
  Definition eq := @eq (@carrier B).
  Definition eq_equiv : Equivalence eq := eq_equivalence.
  Local Coercion is_true : bool >-> Sortclass.
  Definition lt x y := @leqb B x y /\ x <> y.

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
      case_eq (leqb b c) ; intros Heqbb ;
        [ case_eq (leqb c b) ; intros Heqbb2 | ].
      * apply asym in Heqbb ; try assumption ; subst.
        apply Hneq1 ; reflexivity.
      * rewrite Heqbb2 in Hleq1 ; inversion Hleq1.
      * rewrite Heqbb in Hleq2 ; inversion Hleq2.
  Qed.

  Lemma lt_compat : Proper (eq==>eq==>iff) lt.
  Proof.
  intros a b H1 c d H2 ; unfold eq in H1 ; unfold eq in H2 ;
    subst ; reflexivity.
  Qed.

  Definition compare x y :=
    if @leqb B x y then (if leqb y x then Eq else Lt) else Gt.

  Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
  Proof.
  intros.
  unfold compare.
  case_eq (leqb x y).
  - case_eq (leqb y x) ; constructor.
    + apply asym ; assumption.
    + split ; try assumption.
      intros Heq ; subst.
      rewrite H0 in H ; inversion H.
  - constructor.
    assert (Ht := total _ _ H).
    split ; try assumption.
    intros Heq ; subst.
    rewrite Ht in H ; inversion H.
  Qed.

  Lemma eq_dec : forall x y, { eq x y } + { ~ eq x y }.
  Proof.
  intros.
  case_eq (leqb x y) ; case_eq (leqb y x) ; intros Heq1 Heq2.
  - apply asym in Heq1 ; try assumption ; subst.
    left ; reflexivity.
  - right ; intros Heq ; unfold eq in Heq ; subst.
    rewrite Heq1 in Heq2 ; inversion Heq2.
  - right ; intros Heq ; unfold eq in Heq ; subst.
    rewrite Heq1 in Heq2 ; inversion Heq2.
  - apply total in Heq1.
    rewrite Heq1 in Heq2 ; inversion Heq2.
  Qed.

  Definition le x y := is_true (@leqb B x y).

  Lemma le_lteq : forall x y, le x y <-> lt x y \/ eq x y.
  Proof.
  intros ; split.
  - intros Hle.
    destruct (eq_dec x y).
    + right ; assumption.
    + left ; split ; assumption.
  - intros [[Hle Heq] | Heq] ; try assumption.
    rewrite Heq.
    case_eq (leqb y y) ; intros Heq2.
    + unfold le.
      rewrite Heq2 ; reflexivity.
    + exfalso.
      assert (Heq3 := total _ _ Heq2).
      rewrite Heq2 in Heq3 ; inversion Heq3.
  Qed.

End BOrder_to_UsualOrderedTypeFull.

Module UsualOrderedTypeFull_to_BOrder (T : UsualOrderedTypeFull).

  Definition leb x y :=
  match T.compare x y with
  | Gt => false
  | _  => true
  end.

  Lemma leb_le : forall x y, leb x y = true <-> T.le x y.
  Proof.
  intros.
  unfold leb.
  rewrite T.le_lteq.
  destruct (T.compare_spec x y) as [ Heq | Hlt | Hgt] ;
    split ; intros ; try reflexivity.
  - right ; assumption.
  - left ; assumption.
  - discriminate.
  - destruct (StrictOrder_Irreflexive x).
    destruct H as [ Hlt | Heq ].
    + transitivity y ; assumption.
    + rewrite <- Heq in Hgt ; assumption.
  Qed.

  Lemma nleb_lt : forall x y, leb x y = false <-> T.lt y x.
  Proof.
  intros.
  unfold leb.
  destruct (T.compare_spec x y) as [ Heq | Hlt | Hgt] ;
    split ; intros ; try reflexivity ; try discriminate ; subst.
  - apply StrictOrder_Irreflexive in H.
    destruct H.
  - apply (StrictOrder_Transitive _ _ _ H) in Hlt.
    apply StrictOrder_Irreflexive in Hlt.
    destruct Hlt.
  - assumption.
  Qed.

  Lemma to_BOrder : BOrder.
  Proof.
  split with T.t leb.
  - intros a b Hf.
    rewrite nleb_lt in Hf.
    rewrite leb_le.
    apply T.le_lteq.
    left ; assumption.
  - intros a b H1 H2.
    rewrite leb_le in H1.
    rewrite leb_le in H2.
    apply T.le_lteq in H1.
    apply T.le_lteq in H2.
    destruct H1 ; destruct H2 ;
      try subst ; try reflexivity ; try assumption.
    apply (StrictOrder_Transitive _ _ _ H0) in H.
    apply StrictOrder_Irreflexive in H.
    destruct H.
  - intros a b c H1 H2.
    rewrite leb_le ; apply T.le_lteq.
    rewrite leb_le in H1.
    rewrite leb_le in H2.
    apply T.le_lteq in H1.
    apply T.le_lteq in H2.
    destruct H1 ; destruct H2 ; subst.
    + left ; transitivity b ; assumption.
    + left ; assumption.
    + left ; assumption.
    + right ; reflexivity.
  Qed.

End UsualOrderedTypeFull_to_BOrder.

(** * [BOrder] structure over [nat]. *)
Instance border_nat : BOrder.
Proof with try eassumption.
split with nat Compare_dec.leb ; intros.
- apply leb_complete_conv in H.
  apply leb_correct.
  apply le_Sn_le...
- apply leb_complete in H.
  apply leb_complete in H0.
  apply le_antisym...
- apply leb_complete in H.
  apply leb_complete in H0.
  apply leb_correct.
  eapply le_trans...
Defined.

Lemma border_inj {A B} (f : A -> @carrier B) (Hi : injective f) : BOrder.
Proof with try eassumption.
split with A (fun x y => leqb (f x) (f y)) ; intros.
- apply total...
- apply Hi.
  apply asym...
- eapply trans...
Defined.




(** * Sorted lists over [BOrder] *)

(** ** Insertion sort *)

Fixpoint insert {B} (a : @carrier B) (l : list (@carrier B)) :=
match l with
| nil => a :: nil
| b :: t => if (leqb a b) then a :: b :: t
                          else b :: (insert a t)
end.

Lemma insert_insert {B} : forall (x y : @carrier B) l,
  insert y (insert x l) = insert x (insert y l).
Proof with try reflexivity.
induction l ; simpl.
- case_eq (leqb x y) ; intros Heqbb1 ;
  case_eq (leqb y x) ; intros Heqbb2...
  + apply (asym _ _ Heqbb1) in Heqbb2 ; subst...
  + apply total in Heqbb1.
    rewrite Heqbb1 in Heqbb2 ; now discriminate Heqbb2.
- case_eq (leqb x a) ; intros Heqbb1 ;
  case_eq (leqb y a) ; intros Heqbb2 ; simpl ;
    try rewrite Heqbb1 ; try rewrite Heqbb2...
  + case_eq (leqb x y) ; intros Heqbb ;
    case_eq (leqb y x) ; intros Heqbb' ;
      try rewrite Heqbb1 ; try rewrite Heqbb2...
    * apply (asym _ _ Heqbb) in Heqbb' ; subst...
    * apply total in Heqbb.
      rewrite Heqbb in Heqbb' ; now discriminate Heqbb'.
  + case_eq (leqb y x) ; intros Heqbb' ;
      try rewrite Heqbb1 ; try rewrite Heqbb2...
    apply (trans _ _ _ Heqbb') in Heqbb1.
    rewrite Heqbb1 in Heqbb2 ; now discriminate Heqbb2.
  + case_eq (leqb x y) ; intros Heqbb ;
      try rewrite Heqbb1 ; try rewrite Heqbb2...
    apply (trans _ _ _ Heqbb) in Heqbb2.
    rewrite Heqbb1 in Heqbb2 ; now discriminate Heqbb2.
  + rewrite IHl...
Qed.

(** ** Sorted lists *)

Fixpoint is_sorted {B} (l : list (@carrier B)) :=
match l with
| nil => true
| a :: nil => true
| a :: (b :: _) as r => leqb a b && is_sorted r
end.

Lemma is_sorted_tail {B} : forall a l,
  @is_sorted B (a :: l) = true -> is_sorted l = true.
Proof.
intros a l Hs.
destruct l.
- reflexivity.
- apply andb_true_iff in Hs.
  apply Hs.
Qed.

Definition SortedList B := { m | @is_sorted B m = true }.

Lemma sortedlist_equality : forall B (m1 m2 : SortedList B),
  proj1_sig m1 = proj1_sig m2 -> m1 = m2.
Proof.
intros B em1 em2 Heq.
destruct em1 as [m1 B1].
destruct em2 as [m2 B2].
simpl in Heq ; subst.
f_equal.
apply UIP_bool.
Qed.

Lemma insert_sorted {B} : forall s a (m : SortedList B),
  length (proj1_sig m) = s ->
  let l := insert a (proj1_sig m) in
    is_sorted l = true /\ l <> nil
 /\ forall c, In c l -> In c (proj1_sig m) \/ c = a.
Proof with try reflexivity ; try assumption.
induction s as [s IH] using (well_founded_induction lt_wf).
intros a m Hlen l.
destruct m as [l0 Hsort].
destruct l0 ; (split ; [ | split ])...
- intro Heq ; discriminate Heq.
- intros c Hc.
  inversion Hc.
  + right ; rewrite H...
  + inversion H.
- unfold l ; simpl.
  case_eq (leqb a c) ; intros Heqbb.
  + apply andb_true_iff ; split...
  + destruct s ; inversion Hlen.
    destruct (IH s (le_n _) a (exist _ l0 (is_sorted_tail _ _ Hsort)) H0)
      as [Hsort' _].
    apply total in Heqbb.
    destruct l0 ; try (apply andb_true_iff ; split)...
    simpl.
    simpl in Hsort'.
    destruct (leqb a c0) ; apply andb_true_iff ; split...
    clear Hlen l.
    simpl in Hsort.
    apply andb_true_iff in Hsort.
    apply Hsort.
- intro Heq.
  unfold l in Heq.
  simpl in Heq.
  destruct (leqb a c) ; discriminate Heq.
- intros d Hd.
  unfold l in Hd.
  simpl in Hd.
  destruct (leqb a c).
  + inversion Hd ; [ right ; rewrite H | left ]...
  + inversion Hd.
    * left ; left...
    * destruct s ; inversion Hlen.
      destruct (IH s (le_n _) a (exist _ l0 (is_sorted_tail _ _ Hsort)) H1)
        as [_ Hin].
      apply Hin in H.
      destruct H ; [ left ; apply in_cons | right ]...
Qed.


(** ** Sorted lists as finite multisets
  Sorted lists provide a finite multisets construction for [BOrder]. *)

Definition fmslist_empty {B} : SortedList B := exist _ (nil) eq_refl.

Lemma fmslist_add {B} : @carrier B -> SortedList B -> SortedList B.
Proof.
intros a m.
exists (insert a (proj1_sig m)).
apply (insert_sorted (length (proj1_sig m)) a m).
reflexivity.
Defined.

Lemma insert_add {B} : forall (a : @carrier B) l,
  proj1_sig (fmslist_add a l) = insert a (proj1_sig l).
Proof.
reflexivity.
Qed.

Theorem FMConstr_slist : FMConstructor _ SortedList (@carrier).
Proof with try reflexivity.
intros A.
split with (@fmslist_empty A) (@fmslist_add A) (fun m => proj1_sig m) ; intros.
- reflexivity.
- destruct m as [l Hsort].
  revert Hsort ; induction l ; intros Hsort ; simpl...
  destruct (leqb a a0)...
  change (a :: a0 :: l) with ((a :: nil) ++ a0 :: l).
  apply Permutation_cons_app.
  apply is_sorted_tail in Hsort.
  apply (IHl Hsort).
- destruct m as [l Hsort].
  revert Hsort ; induction l ; intros Hsort.
  + apply sortedlist_equality...
  + destruct l ; apply sortedlist_equality ; simpl...
    apply andb_true_iff in Hsort.
    destruct Hsort as [Ha Hsort].
    assert (H' := IHl Hsort).
    apply (f_equal (fun m => proj1_sig m)) in H'.
    simpl in H'.
    rewrite H'.
    simpl.
    destruct (leqb a c) ; [ reflexivity | discriminate Ha ].
- induction H ; simpl...
  + rewrite IHPermutation...
  + apply sortedlist_equality.
    apply insert_insert.
  + rewrite IHPermutation1 ; assumption.
Defined.


