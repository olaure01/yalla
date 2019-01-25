(* iformulas library for yalla *)


(** * Intuitionistic Linear Logic formulas *)

Require Import RelationClasses.
Require Import List.
Require Import Lia.

Require Import Bool_more.

Require yalla_ax.

(** ** Definition and main properties of formulas *)

(** A set of atoms for building formulas *)
Definition IAtom := yalla_ax.IAtom.
Definition atN := yalla_ax.atN.


(** Intuitionistic formulas

(with implication in both directions for non-commutative systems) *)
Inductive iformula : Set :=
| ivar  : IAtom -> iformula
| ione  : iformula
| itens : iformula -> iformula -> iformula
| ilpam : iformula -> iformula -> iformula
| igen  : iformula -> iformula
| ilmap : iformula -> iformula -> iformula
| ineg  : iformula -> iformula
| itop  : iformula
| iwith : iformula -> iformula -> iformula
| izero : iformula
| iplus : iformula -> iformula -> iformula
| ioc   : iformula -> iformula.

Definition N := ivar atN.

(** Size of a [iformula] as its number of symbols *)
Fixpoint ifsize A :=
match A with
| ivar X     => 1
| ione       => 1
| itens A B  => S (ifsize A + ifsize B)
| ilpam A B  => S (ifsize A + ifsize B)
| igen A     => S (ifsize A)
| ilmap A B  => S (ifsize A + ifsize B)
| ineg A     => S (ifsize A)
| itop       => 1
| iwith A B  => S (ifsize A + ifsize B)
| izero      => 1
| iplus A B  => S (ifsize A + ifsize B)
| ioc A      => S (ifsize A)
end.

Ltac ifsize_auto :=
  simpl ;
  match goal with
  | H: ifsize _ < _ |- _ => simpl in H
  | H: ifsize _ <= _ |- _ => simpl in H
  | H: ifsize _ = _ |- _ => simpl in H
  end ;
  lia.

(** Atomic [iformula] *)
Inductive iatomic : iformula -> Prop :=
| iatomic_var : forall x, iatomic (ivar x).


(** ** Sub-formulas *)

(** First argument is a sub-formula of the second: *)
Inductive isubform : iformula -> iformula -> Prop :=
| isub_id : forall A, isubform A A
| isub_tens_l : forall A B C, isubform A B -> isubform A (itens B C)
| isub_tens_r : forall A B C, isubform A B -> isubform A (itens C B)
| isub_lpam_l : forall A B C, isubform A B -> isubform A (ilpam B C)
| isub_lpam_r : forall A B C, isubform A B -> isubform A (ilpam C B)
| isub_gen    : forall A B, isubform A B -> isubform A (igen B)
| isub_gen_N  : forall A, isubform N (igen A)
| isub_lmap_l : forall A B C, isubform A B -> isubform A (ilmap B C)
| isub_lmap_r : forall A B C, isubform A B -> isubform A (ilmap C B)
| isub_neg    : forall A B, isubform A B -> isubform A (ineg B)
| isub_neg_N  : forall A, isubform N (ineg A)
| isub_plus_l : forall A B C, isubform A B -> isubform A (iplus B C)
| isub_plus_r : forall A B C, isubform A B -> isubform A (iplus C B)
| isub_with_l : forall A B C, isubform A B -> isubform A (iwith B C)
| isub_with_r : forall A B C, isubform A B -> isubform A (iwith C B)
| isub_oc : forall A B, isubform A B -> isubform A (ioc B).

Lemma isub_trans : forall A B C, isubform A B -> isubform B C -> isubform A C.
Proof with try assumption.
intros A B C Hl Hr ; revert A Hl ; induction Hr ; intros A' Hl ;
  try (constructor ; apply IHHr)...
- inversion Hl.
  apply isub_gen_N.
- inversion Hl.
  apply isub_neg_N.
Qed.

Instance isub_po : PreOrder isubform.
Proof.
split.
- intros l.
  apply isub_id.
- intros l1 l2 l3.
  apply isub_trans.
Qed.

(** Each element of the first list is a sub-formula of some element of the second. *)
Definition isubform_list l1 l2 := Forall (fun A => Exists (isubform A) l2) l1.

Lemma isub_id_list : forall l l0, isubform_list l (l0 ++ l).
Proof.
induction l ; intros l0 ; constructor.
- induction l0.
  + constructor.
    apply isub_id.
  + apply Exists_cons_tl ; assumption.
- replace (l0 ++ a :: l) with ((l0 ++ a :: nil) ++ l).
  + apply IHl.
  + rewrite <- app_assoc ; reflexivity.
Qed.

Lemma isub_trans_list : forall l1 l2 l3,
  isubform_list l1 l2 -> isubform_list l2 l3 -> isubform_list l1 l3.
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

Instance isub_list_po : PreOrder isubform_list.
Proof.
split.
- intros l.
  rewrite <- app_nil_l.
  apply isub_id_list.
- intros l1 l2 l3.
  apply isub_trans_list.
Qed.

(* unused

Require Import genperm_Type.

Lemma isub_perm_list :
  forall b l l1 l2,
    isubform_list l l1 -> PCperm_Type b l1 l2 ->
    isubform_list l l2.
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

Fixpoint eqb_iform A B :=
match A, B with
| ivar X, ivar Y => yalla_ax.iateq X Y
| ione, ione => true
| itens A1 A2, itens B1 B2 => (eqb_iform A1 B1) && (eqb_iform A2 B2)
| ilpam A1 A2, ilpam B1 B2 => (eqb_iform A1 B1) && (eqb_iform A2 B2)
| igen A1, igen B1 => eqb_iform A1 B1
| ilmap A1 A2, ilmap B1 B2 => (eqb_iform A1 B1) && (eqb_iform A2 B2)
| ineg A1, ineg B1 => eqb_iform A1 B1
| itop, itop => true
| izero, izero => true
| iwith A1 A2, iwith B1 B2 => (eqb_iform A1 B1) && (eqb_iform A2 B2)
| iplus A1 A2, iplus B1 B2 => (eqb_iform A1 B1) && (eqb_iform A2 B2)
| ioc A1, ioc B1 => eqb_iform A1 B1
| _, _ => false
end.

Lemma eqb_eq_iform : forall A B, eqb_iform A B = true <-> A = B.
Proof with reflexivity.
induction A ; destruct B ; (split ; [ intros Heqb | intros Heq ]) ;
  try inversion Heqb ; try inversion Heq ; try reflexivity.
- apply yalla_ax.iateq_eq in H0 ; subst...
- subst ; simpl.
  apply yalla_ax.iateq_eq...
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
- apply andb_true_iff in H0.
  destruct H0 as [H1 H2].
  apply IHA1 in H1 ; apply IHA2 in H2 ; subst...
- subst ; simpl ; apply andb_true_iff.
  split ; [ apply IHA1 | apply IHA2 ]...
- apply IHA in H0 ; subst...
- subst ; simpl ; apply IHA...
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
Qed.

Fixpoint eqb_iformlist l1 l2 :=
match l1, l2 with
| nil, nil => true
| cons A t1, cons B t2 => (eqb_iform A B) && (eqb_iformlist t1 t2)
| _, _ => false
end.

Lemma eqb_eq_iformlist : forall l1 l2, eqb_iformlist l1 l2 = true <-> l1 = l2.
Proof with reflexivity.
induction l1 ; destruct l2 ; (split ; [ intros Heqb | intros Heq ]) ;
  try inversion Heqb ; try inversion Heq ; try reflexivity.
- apply andb_true_iff in H0.
  destruct H0 as [H1 H2].
  apply eqb_eq_iform in H1 ; apply IHl1 in H2 ; subst...
- subst ; simpl ; apply andb_true_iff.
  split ; [ apply eqb_eq_iform | apply IHl1 ]...
Qed.

(** * In with [bool] output for formula list *)
Fixpoint inb_iform A l :=
match l with
| nil => false
| cons hd tl => eqb_iform A hd || inb_iform A tl
end.

Lemma inb_in_iform : forall A l, inb_iform A l = true <-> In A l.
Proof with assumption.
induction l ; (split ; [ intros Heqb | intros Heq ]).
- inversion Heqb.
- inversion Heq.
- inversion Heqb ; subst.
  apply orb_true_iff in H0.
  destruct H0.
  + constructor.
    symmetry ; apply eqb_eq_iform...
  + apply in_cons.
    apply IHl...
- inversion Heq ; subst.
  + simpl ; apply orb_true_iff ; left.
    apply eqb_eq_iform.
    reflexivity.
  + simpl ; apply orb_true_iff ; right.
    apply IHl...
Qed.


(** ** Sub-formulas in [bool] *)

(** First argument is a sub-formula of the second: *)
Fixpoint isubformb A B :=
eqb_iform A B ||
match B with
| itens B1 B2 => isubformb A B1 || isubformb A B2
| ilpam B1 B2 => isubformb A B1 || isubformb A B2
| igen B1 => isubformb A B1 || eqb_iform A N
| ilmap B1 B2 => isubformb A B1 || isubformb A B2
| ineg B1 => isubformb A B1 || eqb_iform A N
| iwith B1 B2 => isubformb A B1 || isubformb A B2
| iplus B1 B2 => isubformb A B1 || isubformb A B2
| ioc B1 => isubformb A B1
| _ => false
end.

Lemma isubb_isub : forall A B, is_true (isubformb A B) <-> isubform A B.
Proof with try assumption ; try reflexivity.
intros A B ; split ; intros H ; induction B ; try (now (inversion H ; constructor)).
- destruct A ; simpl in H ; try (now inversion H).
  rewrite orb_false_r in H.
  apply yalla_ax.iateq_eq in H ; subst ; constructor.
- destruct A ; simpl in H ; try (now inversion H).
- simpl in H.
  apply orb_true_elim in H ; destruct H as [ H | H ] ;
    [ | apply orb_true_elim in H ; destruct H as [ H | H ] ].
  + apply eqb_eq_iform in H ; subst ; constructor.
  + apply isub_tens_l.
    apply IHB1...
  + apply isub_tens_r.
    apply IHB2...
- simpl in H.
  apply orb_true_elim in H ; destruct H as [ H | H ] ;
    [ | apply orb_true_elim in H ; destruct H as [ H | H ] ].
  + apply eqb_eq_iform in H ; subst ; constructor.
  + apply isub_lpam_l.
    apply IHB1...
  + apply isub_lpam_r.
    apply IHB2...
- simpl in H.
  apply orb_true_elim in H ; destruct H as [ H | H ] ;
    [ | apply orb_true_elim in H ; destruct H as [ H | H ] ].
  + apply eqb_eq_iform in H ; subst ; constructor.
  + apply isub_gen.
    apply IHB...
  + apply eqb_eq_iform in H ; subst.
    apply isub_gen_N.
- simpl in H.
  apply orb_true_elim in H ; destruct H as [ H | H ] ;
    [ | apply orb_true_elim in H ; destruct H as [ H | H ] ].
  + apply eqb_eq_iform in H ; subst ; constructor.
  + apply isub_lmap_l.
    apply IHB1...
  + apply isub_lmap_r.
    apply IHB2...
- simpl in H.
  apply orb_true_elim in H ; destruct H as [ H | H ] ;
    [ | apply orb_true_elim in H ; destruct H as [ H | H ] ].
  + apply eqb_eq_iform in H ; subst ; constructor.
  + apply isub_neg.
    apply IHB...
  + apply eqb_eq_iform in H ; subst.
    apply isub_neg_N.
- destruct A ; simpl in H ; try (now inversion H).
- simpl in H.
  apply orb_true_elim in H ; destruct H as [ H | H ] ;
    [ | apply orb_true_elim in H ; destruct H as [ H | H ] ].
  + apply eqb_eq_iform in H ; subst ; constructor.
  + apply isub_with_l.
    apply IHB1...
  + apply isub_with_r.
    apply IHB2...
- destruct A ; simpl in H ; try (now inversion H).
- simpl in H.
  apply orb_true_elim in H ; destruct H as [ H | H ] ;
    [ | apply orb_true_elim in H ; destruct H as [ H | H ] ].
  + apply eqb_eq_iform in H ; subst ; constructor.
  + apply isub_plus_l.
    apply IHB1...
  + apply isub_plus_r.
    apply IHB2...
- simpl in H.
  apply orb_true_elim in H ; destruct H as [ H | H ].
  + apply eqb_eq_iform in H ; subst ; constructor.
  + apply isub_oc.
    apply IHB...
- inversion H ; subst.
  simpl ; rewrite (proj2 (yalla_ax.iateq_eq _ _) eq_refl).
  constructor.
- inversion H ; subst.
  + unfold isubformb.
    replace (eqb_iform (itens B1 B2) (itens B1 B2)) with true...
    symmetry ; apply eqb_eq_iform...
  + apply IHB1 in H2.
    simpl ; rewrite H2 ; simpl.
    rewrite orb_true_r...
  + apply IHB2 in H2.
    simpl ; rewrite H2 ; simpl.
    rewrite 2 orb_true_r...
- inversion H ; subst.
  + unfold isubformb.
    replace (eqb_iform (ilpam B1 B2) (ilpam B1 B2)) with true...
    symmetry ; apply eqb_eq_iform...
  + apply IHB1 in H2.
    simpl ; rewrite H2 ; simpl.
    rewrite orb_true_r...
  + apply IHB2 in H2.
    simpl ; rewrite H2 ; simpl.
    rewrite 2 orb_true_r...
- inversion H ; subst.
  + unfold isubformb.
    replace (eqb_iform (igen B) (igen B)) with true...
    symmetry ; apply eqb_eq_iform...
  + apply IHB in H2.
    simpl ; rewrite H2 ; simpl.
    rewrite orb_true_r...
  + simpl.
    rewrite orb_true_r...
- inversion H ; subst.
  + unfold isubformb.
    replace (eqb_iform (ilmap B1 B2) (ilmap B1 B2)) with true...
    symmetry ; apply eqb_eq_iform...
  + apply IHB1 in H2.
    simpl ; rewrite H2 ; simpl.
    rewrite orb_true_r...
  + apply IHB2 in H2.
    simpl ; rewrite H2 ; simpl.
    rewrite 2 orb_true_r...
- inversion H ; subst.
  + unfold isubformb.
    replace (eqb_iform (ineg B) (ineg B)) with true...
    symmetry ; apply eqb_eq_iform...
  + apply IHB in H2.
    simpl ; rewrite H2 ; simpl.
    rewrite orb_true_r...
  + simpl.
    rewrite orb_true_r...
- inversion H ; subst.
  + unfold isubformb.
    replace (eqb_iform (iwith B1 B2) (iwith B1 B2)) with true...
    symmetry ; apply eqb_eq_iform...
  + apply IHB1 in H2.
    simpl ; rewrite H2 ; simpl.
    rewrite orb_true_r...
  + apply IHB2 in H2.
    simpl ; rewrite H2 ; simpl.
    rewrite 2 orb_true_r...
- inversion H ; subst.
  + unfold isubformb.
    replace (eqb_iform (iplus B1 B2) (iplus B1 B2)) with true...
    symmetry ; apply eqb_eq_iform...
  + apply IHB1 in H2.
    simpl ; rewrite H2 ; simpl.
    rewrite orb_true_r...
  + apply IHB2 in H2.
    simpl ; rewrite H2 ; simpl.
    rewrite 2 orb_true_r...
- inversion H ; subst.
  + unfold isubformb.
    replace (eqb_iform (ioc B) (ioc B)) with true...
    symmetry ; apply eqb_eq_iform...
  + apply IHB in H2.
    simpl ; rewrite H2 ; simpl.
    rewrite orb_true_r...
Qed.

Lemma isubb_trans : forall A B C,
  is_true (isubformb A B) -> is_true (isubformb B C) -> is_true (isubformb A C).
Proof.
intros A B C Hl Hr.
apply isubb_isub in Hl.
apply isubb_isub in Hr.
apply isubb_isub.
etransitivity ; eassumption.
Qed.

(** Each element of the first list is a sub-formula of some element of the second. *)
Definition isubformb_list l1 l2 := Forallb (fun A => Existsb (isubformb A) l2) l1.

Lemma isubb_isub_list : forall l1 l2, is_true (isubformb_list l1 l2) <-> isubform_list l1 l2.
Proof with try assumption.
intros l1 l2 ; split ; intros H ; induction l1 ; try (now (inversion H ; constructor)).
- unfold isubformb_list in H.
  apply Forallb_Forall in H.
  inversion H ; subst.
  apply Existsb_Exists in H2.
  constructor.
  + clear - H2 ; induction l2 ; inversion H2 ; subst.
    * constructor.
      apply isubb_isub...
    * apply Exists_cons_tl.
      apply IHl2...
  + apply IHl1.
    apply Forallb_Forall...
- inversion H ; subst.
  unfold isubformb_list ; simpl.
  apply andb_true_iff ; split.
  + apply Existsb_Exists.
    clear - H2 ; induction l2 ; inversion H2 ; subst.
    * constructor.
      apply isubb_isub...
    * apply Exists_cons_tl.
      apply IHl2...
  + apply IHl1...
Qed.

Lemma isubb_id_list : forall l l0, is_true (isubformb_list l (l0 ++ l)).
Proof.
intros l l0.
apply isubb_isub_list.
apply isub_id_list.
Qed.

Lemma isubb_trans_list : forall l1 l2 l3,
  is_true (isubformb_list l1 l2) -> is_true (isubformb_list l2 l3) -> is_true (isubformb_list l1 l3).
Proof.
intros l1 l2 l3 Hl Hr.
apply isubb_isub_list in Hl.
apply isubb_isub_list in Hr.
apply isubb_isub_list.
etransitivity ; eassumption.
Qed.




