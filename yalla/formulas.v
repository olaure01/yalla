(* formulas library for yalla *)


(** * Linear Logic formulas *)

Require Import RelationClasses.
Require Import List.
Require Import Lia.
Require Import EqNat.
Require Import Equalities.

Require Import Injective.
Require Import Bool_more.

Require yalla_ax.

(** ** Definition and main properties of formulas *)

(** A set of atoms for building formulas *)
Definition Atom := yalla_ax.Atom.

(** Formulas *)
Inductive formula : Set :=
| var : Atom -> formula
| covar : Atom -> formula
| one : formula
| bot : formula
| tens : formula -> formula -> formula
| parr : formula -> formula -> formula
| zero : formula
| top : formula
| aplus : formula -> formula -> formula
| awith : formula -> formula -> formula
| oc : formula -> formula
| wn : formula -> formula.


(** n-ary operators *)

Fixpoint tens_n n A :=
match n with
| 0 => one
| 1 => A
| S n => tens (tens_n n A) A
end.

Fixpoint parr_n n A :=
match n with
| 0 => bot
| 1 => A
| S n => parr A (parr_n n A)
end.

Fixpoint wn_n n A :=
match n with
| 0 => A
| S n => wn (wn_n n A)
end.

Lemma wn_n_wn : forall n A, wn_n n (wn A) = wn_n (S n) A.
Proof with try reflexivity.
intros n A.
induction n...
simpl in *; rewrite IHn...
Qed.

Fixpoint oc_n n A :=
match n with
| 0 => A
| S n => oc (oc_n n A)
end.

Lemma oc_n_oc : forall n A, oc_n n (oc A) = oc_n (S n) A.
Proof with try reflexivity.
intros n A.
induction n...
simpl in *; rewrite IHn...
Qed.


(** Orthogonal / dual of a [formula] *)

(** (the dual of [tens] and [parr] is the one compatible with non-commutative systems) *)
Fixpoint dual A :=
match A with
| var x     => covar x
| covar x   => var x
| one       => bot
| bot       => one
| tens A B  => parr (dual B) (dual A)
| parr A B  => tens (dual B) (dual A)
| zero      => top
| top       => zero
| aplus A B => awith (dual A) (dual B)
| awith A B => aplus (dual A) (dual B)
| oc A      => wn (dual A)
| wn A      => oc (dual A)
end.

Lemma bidual : forall A, dual (dual A) = A.
Proof.
induction A ; simpl ;
  try (rewrite IHA1 ; rewrite IHA2) ;
  try rewrite IHA ;
  try reflexivity.
Qed.

Lemma codual : forall A B, dual A = B <-> A = dual B.
Proof.
intros A B ; split ; intro H.
- rewrite <- bidual at 1.
  rewrite H; reflexivity.
- rewrite <- bidual.
  rewrite H; reflexivity.
Qed.

Lemma dual_inj : injective dual.
Proof.
intros A B H.
rewrite <- (bidual A).
rewrite <- (bidual B).
rewrite H; reflexivity.
Qed.

Lemma dual_tens_n : forall n A, dual (tens_n n A) = parr_n n (dual A).
Proof with try reflexivity.
induction n; intro A...
destruct n...
simpl in *; rewrite <- IHn...
Qed.

Lemma dual_parr_n : forall n A, dual (parr_n n A) = tens_n n (dual A).
Proof with try reflexivity.
induction n; intro A...
destruct n...
simpl in *; rewrite <- IHn...
Qed.

Lemma dual_wn_n : forall n A, dual (wn_n n A) = oc_n n (dual A).
Proof with try reflexivity.
induction n; intro A...
destruct n...
simpl in *; rewrite IHn...
Qed.

Lemma dual_oc_n : forall n A, dual (oc_n n A) = wn_n n (dual A).
Proof with try reflexivity.
induction n; intro A...
destruct n...
simpl in *; rewrite IHn...
Qed.

(** Size of a [formula] as its number of symbols *)
Fixpoint fsize A :=
match A with
| var X     => 1
| covar X   => 1
| one       => 1
| bot       => 1
| tens A B  => S (fsize A + fsize B)
| parr A B  => S (fsize A + fsize B)
| zero      => 1
| top       => 1
| aplus A B => S (fsize A + fsize B)
| awith A B => S (fsize A + fsize B)
| oc A      => S (fsize A)
| wn A      => S (fsize A)
end.

Lemma fsize_pos : forall A, 0 < fsize A.
Proof.
induction A ; simpl ; lia.
Qed.

Lemma fsize_dual : forall A, fsize (dual A) = fsize A.
Proof.
induction A ; simpl ;
  try (rewrite IHA1 ; rewrite IHA2) ;
  try rewrite IHA ;
  try reflexivity ;
  try lia.
Qed.

Lemma fsize_wn_n : forall n A, fsize (wn_n n A) = n + fsize A.
Proof with try reflexivity.
induction n; intros A; simpl...
rewrite <- IHn...
Qed.

Lemma fsize_oc_n : forall n A, fsize (oc_n n A) = n + fsize A.
Proof with try reflexivity.
induction n; intros A; simpl...
rewrite <- IHn...
Qed.

Ltac fsize_auto :=
  simpl ;
  repeat rewrite fsize_dual ;
  simpl ;
  match goal with
  | H: fsize _ < _ |- _ => simpl in H
  | H: fsize _ <= _ |- _ => simpl in H
  | H: fsize _ = _ |- _ => simpl in H
  end ;
  lia.

(** Atomic [formula] *)
Inductive atomic_Prop : formula -> Prop :=
| atomic_Prop_var : forall x, atomic_Prop (var x)
| atomic_Prop_covar : forall x, atomic_Prop (covar x).

Inductive atomic : formula -> Type :=
| atomic_var : forall x, atomic (var x)
| atomic_covar : forall x, atomic (covar x).

Lemma atomic_Prop_atomic : forall A, atomic_Prop A -> atomic A.
Proof.
induction A; intros Hat;
  try (exfalso; inversion Hat; fail);
  constructor.
Qed.


(** ** Sub-formulas *)

(** First argument is a sub-formula of the second: *)
Inductive subform : formula -> formula -> Prop :=
| sub_id : forall A, subform A A
| sub_tens_l : forall A B C, subform A B -> subform A (tens B C)
| sub_tens_r : forall A B C, subform A B -> subform A (tens C B)
| sub_parr_l : forall A B C, subform A B -> subform A (parr B C)
| sub_parr_r : forall A B C, subform A B -> subform A (parr C B)
| sub_plus_l : forall A B C, subform A B -> subform A (aplus B C)
| sub_plus_r : forall A B C, subform A B -> subform A (aplus C B)
| sub_with_l : forall A B C, subform A B -> subform A (awith B C)
| sub_with_r : forall A B C, subform A B -> subform A (awith C B)
| sub_oc : forall A B, subform A B -> subform A (oc B)
| sub_wn : forall A B, subform A B -> subform A (wn B).

Lemma sub_trans : forall A B C, subform A B -> subform B C -> subform A C.
Proof with try assumption.
intros A B C Hl Hr ; revert A Hl ; induction Hr ; intros A' Hl ;
  try (constructor ; apply IHHr)...
Qed.

Instance sub_po : PreOrder subform.
Proof.
split.
- intros l.
  apply sub_id.
- intros l1 l2 l3.
  apply sub_trans.
Qed.

(** Each element of the first list is a sub-formula of some element of the second. *)
Definition subform_list l1 l2 := Forall (fun A => Exists (subform A) l2) l1.

Lemma sub_id_list : forall l l0, subform_list l (l0 ++ l).
Proof.
induction l ; intros l0 ; constructor.
- induction l0.
  + constructor.
    apply sub_id.
  + apply Exists_cons_tl ; assumption.
- replace (l0 ++ a :: l) with ((l0 ++ a :: nil) ++ l).
  + apply IHl.
  + rewrite <- app_assoc ; reflexivity.
Qed.

Lemma sub_trans_list : forall l1 l2 l3,
  subform_list l1 l2 -> subform_list l2 l3 -> subform_list l1 l3.
Proof with try eassumption.
induction l1 ; intros l2 l3 Hl Hr ; constructor.
- inversion Hl ; subst.
  revert Hr H1 ; clear ; induction l2 ; intros Hr Hl ; inversion Hl ; subst.
  + inversion Hr ; subst.
    inversion H2 ; subst.
    * apply Exists_cons_hd.
      etransitivity...
    * apply Exists_cons_tl.
      revert H ; clear - H0 ; induction l ; intro H ; inversion H ; subst.
      apply Exists_cons_hd.
      etransitivity...
      apply Exists_cons_tl.
      apply IHl...
  + inversion Hr ; subst.
    apply IHl2...
- inversion Hl ; subst.
  eapply IHl1...
Qed.

Instance sub_list_po : PreOrder subform_list.
Proof.
split.
- intros l.
  rewrite <- app_nil_l.
  apply sub_id_list.
- intros l1 l2 l3.
  apply sub_trans_list.
Qed.

(* Unused
Require Import genperm_Type.

Lemma sub_perm_list :
  forall b l l1 l2, subform_list l l1 ->
    PCperm_Type b l1 l2 -> subform_list l l2.
Proof with try eassumption.
intros b l l1 l2 H1 HP ; revert H1 ; induction l ; intro H1.
- constructor.
- inversion H1 ; subst.
  constructor.
  + eapply PCperm_Type_Exists...
  + apply IHl...
Qed.
*)


(** ** Equality in [bool] *)

Fixpoint eqb_form A B :=
match A, B with
| var X, var Y => yalla_ax.ateq X Y
| covar X, covar Y => yalla_ax.ateq X Y
| one, one => true
| bot, bot => true
| tens A1 A2, tens B1 B2 => eqb_form A1 B1 && eqb_form A2 B2
| parr A1 A2, parr B1 B2 => eqb_form A1 B1 && eqb_form A2 B2
| top, top => true
| zero, zero => true
| awith A1 A2, awith B1 B2 => eqb_form A1 B1 && eqb_form A2 B2
| aplus A1 A2, aplus B1 B2 => eqb_form A1 B1 && eqb_form A2 B2
| oc A1, oc B1 => eqb_form A1 B1
| wn A1, wn B1 => eqb_form A1 B1
| _, _ => false
end.

Lemma eqb_eq_form : forall A B, eqb_form A B = true <-> A = B.
Proof with reflexivity.
induction A ; destruct B ; (split ; [ intros Heqb | intros Heq ]) ;
  try inversion Heqb ; try inversion Heq ; try reflexivity.
- apply yalla_ax.ateq_eq in H0 ; subst...
- subst ; simpl.
  apply yalla_ax.ateq_eq...
- apply yalla_ax.ateq_eq in H0 ; subst...
- subst ; simpl.
  apply yalla_ax.ateq_eq...
- apply andb_true_iff in H0.
  destruct H0 as [H1 H2].
  apply IHA1 in H1 ; apply IHA2 in H2 ; subst...
- subst ; simpl ; apply andb_true_iff.
  split ; [ apply IHA1 | apply IHA2 ]...
- apply andb_true_iff in H0.
  destruct H0 as [H1 H2].
  apply IHA1 in H1 ; apply IHA2 in H2 ; subst...
- subst ; simpl ; apply andb_true_iff.
  split ; [ apply IHA1 | apply IHA2 ]...
- apply andb_true_iff in H0.
  destruct H0 as [H1 H2].
  apply IHA1 in H1 ; apply IHA2 in H2 ; subst...
- subst ; simpl ; apply andb_true_iff.
  split ; [ apply IHA1 | apply IHA2 ]...
- apply andb_true_iff in H0.
  destruct H0 as [H1 H2].
  apply IHA1 in H1 ; apply IHA2 in H2 ; subst...
- subst ; simpl ; apply andb_true_iff.
  split ; [ apply IHA1 | apply IHA2 ]...
- apply IHA in H0 ; subst...
- subst ; simpl ; apply IHA...
- apply IHA in H0 ; subst...
- subst ; simpl ; apply IHA...
Qed.

Module Formula_beq <: UsualBoolEq.
  Definition t := formula.
  Definition eq := @eq formula.
  Definition eqb := eqb_form.
  Definition eqb_eq := eqb_eq_form.
End Formula_beq.

Module Formula_dec <: UsualDecidableTypeFull := Make_UDTF Formula_beq.

(* Unused
Fixpoint eqb_formlist l1 l2 :=
match l1, l2 with
| nil, nil => true
| cons A t1, cons B t2 => eqb_form A B && eqb_formlist t1 t2
| _, _ => false
end.

Lemma eqb_eq_formlist : forall l1 l2, eqb_formlist l1 l2 = true <-> l1 = l2.
Proof with reflexivity.
induction l1 ; destruct l2 ; (split ; [ intros Heqb | intros Heq ]) ;
  try inversion Heqb ; try inversion Heq ; try reflexivity.
- apply andb_true_iff in H0.
  destruct H0 as [H1 H2].
  apply eqb_eq_form in H1 ; apply IHl1 in H2 ; subst...
- subst ; simpl ; apply andb_true_iff.
  split ; [ apply eqb_eq_form | apply IHl1 ]...
Qed.
*)

(* Unused
(** * In with [bool] output for formula list *)
Fixpoint inb_form A l :=
match l with
| nil => false
| cons hd tl => eqb_form A hd || inb_form A tl
end.

Lemma inb_in_form : forall A l, is_true (inb_form A l) <-> In A l.
Proof with assumption.
induction l ; (split ; [ intros Heqb | intros Heq ]).
- inversion Heqb.
- inversion Heq.
- inversion Heqb ; subst.
  apply orb_true_iff in H0.
  destruct H0.
  + constructor.
    symmetry ; apply eqb_eq_form...
  + apply in_cons.
    apply IHl...
- inversion Heq ; subst.
  + simpl ; apply orb_true_iff ; left.
    apply eqb_eq_form ; reflexivity.
  + simpl ; apply orb_true_iff ; right.
    apply IHl...
Qed.
*)


(** ** Sub-formulas in [bool] *)

(** First argument is a sub-formula of the second: *)
Fixpoint subformb A B :=
eqb_form A B ||
match B with
| tens B1 B2 => subformb A B1 || subformb A B2
| parr B1 B2 => subformb A B1 || subformb A B2
| awith B1 B2 => subformb A B1 || subformb A B2
| aplus B1 B2 => subformb A B1 || subformb A B2
| oc B1 => subformb A B1
| wn B1 => subformb A B1
| _ => false
end.

Lemma subb_sub : forall A B, is_true (subformb A B) <-> subform A B.
Proof with try assumption; try reflexivity.
intros A B ; split ; intros H ; induction B ;
  try (now (inversion H ; constructor)) ;
  try (now (destruct A ; simpl in H ; inversion H));
  try (simpl in H;
       apply orb_true_elim in H ; destruct H as [ H | H ] ;
       [ | apply orb_true_elim in H ; destruct H as [ H | H ] ]; 
       (try (apply eqb_eq_form in H ; subst)) ; now constructor; auto).
- destruct A ; simpl in H ; try (now inversion H).
  rewrite orb_false_r in H.
  apply yalla_ax.ateq_eq in H ; subst ; constructor.
- destruct A ; simpl in H ; try (now inversion H).
  rewrite orb_false_r in H.
  apply yalla_ax.ateq_eq in H ; subst ; constructor.
- simpl in H.
  apply orb_true_elim in H ; destruct H as [ H | H ].
  + apply eqb_eq_form in H ; subst ; constructor.
  + now constructor; auto.
- simpl in H.
  apply orb_true_elim in H ; destruct H as [ H | H ].
  + apply eqb_eq_form in H ; subst ; constructor.
  + now constructor; auto.
- inversion H ; subst.
  simpl ; rewrite (proj2 (yalla_ax.ateq_eq _ _) eq_refl).
  constructor.
- inversion H ; subst.
  simpl ; rewrite (proj2 (yalla_ax.ateq_eq _ _) eq_refl).
  constructor.
- inversion H ; subst.
  + unfold subformb.
    replace (eqb_form (tens B1 B2) (tens B1 B2)) with true
      by (symmetry ; apply eqb_eq_form; reflexivity)...
  + apply IHB1 in H2.
    simpl ; rewrite H2 ; simpl.
    rewrite orb_true_r...
  + apply IHB2 in H2.
    simpl ; rewrite H2 ; simpl.
    rewrite 2 orb_true_r...
- inversion H ; subst.
  + unfold subformb.
    replace (eqb_form (parr B1 B2) (parr B1 B2)) with true
      by (symmetry ; apply eqb_eq_form ; reflexivity)...
  + apply IHB1 in H2.
    simpl ; rewrite H2 ; simpl.
    rewrite orb_true_r...
  + apply IHB2 in H2.
    simpl ; rewrite H2 ; simpl.
    rewrite 2 orb_true_r...
- inversion H ; subst.
  + unfold subformb.
    replace (eqb_form (aplus B1 B2) (aplus B1 B2)) with true
      by (symmetry ; apply eqb_eq_form; reflexivity)...
  + apply IHB1 in H2.
    simpl ; rewrite H2 ; simpl.
    rewrite orb_true_r...
  + apply IHB2 in H2.
    simpl ; rewrite H2 ; simpl.
    rewrite 2 orb_true_r...
- inversion H ; subst.
  + unfold subformb.
    replace (eqb_form (awith B1 B2) (awith B1 B2)) with true
      by (symmetry ; apply eqb_eq_form ; reflexivity)...
  + apply IHB1 in H2.
    simpl ; rewrite H2 ; simpl.
    rewrite orb_true_r...
  + apply IHB2 in H2.
    simpl ; rewrite H2 ; simpl.
    rewrite 2 orb_true_r...
- inversion H ; subst.
  + unfold subformb.
    replace (eqb_form (oc B) (oc B)) with true
      by (symmetry ; apply eqb_eq_form ; reflexivity)...
  + apply IHB in H2.
    simpl ; rewrite H2 ; simpl.
    rewrite orb_true_r...
- inversion H ; subst.
  + unfold subformb.
    replace (eqb_form (wn B) (wn B)) with true
      by (symmetry ; apply eqb_eq_form ; reflexivity)...
  + apply IHB in H2.
    simpl ; rewrite H2 ; simpl.
    rewrite orb_true_r...
Qed.

Lemma subb_trans : forall A B C,
  is_true (subformb A B) -> is_true (subformb B C) -> is_true (subformb A C).
Proof.
intros A B C Hl Hr.
apply subb_sub in Hl.
apply subb_sub in Hr.
apply subb_sub.
etransitivity ; eassumption.
Qed.

(** Each element of the first list is a sub-formula of some element of the second. *)
Definition subformb_list l1 l2 := Forallb (fun A => Existsb (subformb A) l2) l1.

Lemma subb_sub_list : forall l1 l2, is_true (subformb_list l1 l2) <-> subform_list l1 l2.
Proof with try assumption.
intros l1 l2 ; split ; intros H ; induction l1 ; try (now (inversion H ; constructor)).
- unfold subformb_list in H.
  apply Forallb_Forall in H.
  inversion H ; subst.
  apply Existsb_Exists in H2.
  constructor.
  + clear - H2 ; induction l2 ; inversion H2 ; subst.
    * constructor.
      apply subb_sub...
    * apply Exists_cons_tl.
      apply IHl2...
  + apply IHl1.
    apply Forallb_Forall...
- inversion H ; subst.
  unfold subformb_list ; simpl.
  apply andb_true_iff ; split.
  + apply Existsb_Exists.
    clear - H2 ; induction l2 ; inversion H2 ; subst.
    * constructor.
      apply subb_sub...
    * apply Exists_cons_tl.
      apply IHl2...
  + apply IHl1...
Qed.

Lemma subb_id_list : forall l l0, is_true (subformb_list l (l0 ++ l)).
Proof.
intros l l0.
apply subb_sub_list.
apply sub_id_list.
Qed.

Lemma subb_trans_list : forall l1 l2 l3,
  is_true (subformb_list l1 l2) -> is_true (subformb_list l2 l3) -> is_true (subformb_list l1 l3).
Proof.
intros l1 l2 l3 Hl Hr.
apply subb_sub_list in Hl.
apply subb_sub_list in Hr.
apply subb_sub_list.
etransitivity ; eassumption.
Qed.

