(* iformulas library for yalla *)


(** * Intuitionistic Linear Logic formulas *)

From Coq Require Import Bool RelationClasses Lia.
From OLlibs Require Import dectype List_more.
From Yalla Require Export atoms.

Set Implicit Arguments.


Section Atoms.

Context { preiatom : DecType }.

(** ** Definition and main properties of formulas *)

(** A set of atoms for building formulas *)
#[global] Definition iatom := option preiatom.
#[global] Definition atN : iatom := None.

(** Intuitionistic formulas

(with implication in both directions for non-commutative systems) *)
Inductive iformula :=
| ivar (_ : iatom)
| ione | itens (_ _ : iformula)
| ilpam (_ _ : iformula) | igen (_ : iformula)
| ilmap (_ _ : iformula) | ineg (_ : iformula)
| itop | iwith (_ _ : iformula) | izero | iplus (_ _ : iformula)
| ioc (_ : iformula).

#[global] Definition N := ivar atN.

(** Size of a [iformula] as its number of symbols *)
Fixpoint ifsize A :=
match A with
| ivar X => 1
| ione | itop | izero => 1
| itens A B | ilpam A B | ilmap A B | iwith A B | iplus A B => S (ifsize A + ifsize B)
| igen A | ineg A | ioc A => S (ifsize A)
end.

Ltac ifsize_auto :=
  cbn;
  match goal with
  | H: ifsize _ < _ |- _ => cbn in H
  | H: ifsize _ <= _ |- _ => cbn in H
  | H: ifsize _ = _ |- _ => cbn in H
  end;
  lia.

(** Atomic [iformula] *)
Inductive iatomic : iformula -> Type :=
| iatomic_var : forall x, iatomic (ivar x).

(* Unused
Inductive iatomic_Prop : iformula -> Prop :=
| iatomic_Prop_var : forall x, iatomic_Prop (ivar x).

Lemma iatomic_Prop_iatomic A : iatomic_Prop A -> iatomic A.
Proof. induction A; intros Hat; try (exfalso; inversion Hat; fail); constructor. Qed.
*)


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

Lemma isub_trans A B C : isubform A B -> isubform B C -> isubform A C.
Proof.
intros Hl Hr; induction Hr in A, Hl |- * ;
  try (constructor; apply IHHr); try assumption.
- inversion Hl; apply isub_gen_N.
- inversion Hl; apply isub_neg_N.
Qed.

#[export] Instance isub_po : PreOrder isubform | 50.
Proof. split; intros ?; [ apply isub_id | apply isub_trans ]. Qed.

(** Each element of the first list is a sub-formula of some element of the second. *)
Definition isubform_list l1 l2 := Forall (fun A => Exists (isubform A) l2) l1.

Lemma isub_id_list l l0 : isubform_list l (l0 ++ l).
Proof.
induction l in l0 |- *; constructor.
- induction l0.
  + constructor.
    apply isub_id.
  + apply Exists_cons_tl; assumption.
- replace (l0 ++ a :: l) with ((l0 ++ a :: nil) ++ l).
  + apply IHl.
  + rewrite <- app_assoc; reflexivity.
Qed.

Lemma isub_trans_list l1 l2 l3 :
  isubform_list l1 l2 -> isubform_list l2 l3 -> isubform_list l1 l3.
Proof.
induction l1 in l2, l3 |- *; intros Hl Hr; constructor.
- inversion Hl; subst.
  clear - Hr H1; induction l2 in Hr, H1 |-*; inversion H1; subst.
  + inversion Hr; subst.
    clear - H0 H3; induction l3 in H0, H3 |- *; inversion H3; subst.
    * apply Exists_cons_hd.
      transitivity a0; assumption.
    * apply Exists_cons_tl.
      apply IHl3; assumption.
  + inversion Hr; subst.
    apply IHl2; assumption.
- inversion Hl; subst.
  eapply IHl1; eassumption.
Qed.

#[export] Instance isub_list_po : PreOrder isubform_list | 50.
Proof.
split.
- intros l; rewrite <- app_nil_l; apply isub_id_list.
- intros l1 l2 l3; apply isub_trans_list.
Qed.

(* Unused
From OLlibs Require Import GPermutation_Type.

Lemma isub_perm_list b l l1 l2 :
  isubform_list l l1 -> PCPermutation_Type b l1 l2 ->
  isubform_list l l2.
Proof.
intros HF HP; apply Forall_forall.
setoid_rewrite <- (PCPermutation_Type_Exists _ _ HP).
apply Forall_forall; assumption.
Qed.
*)


(** ** Equality in [bool] *)

Fixpoint eqb_iform A B :=
match A, B with
| ivar X, ivar Y => @eqb (option_dectype _) X Y
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

Lemma eqb_eq_iform A B : eqb_iform A B = true <-> A = B.
Proof.
induction A in B |- *; destruct B; (split; [ intros Heqb | intros Heq ]);
  try inversion Heqb; try inversion Heq; try reflexivity;
  try (subst; cbn; apply IHA; reflexivity);
  try (apply IHA in H0; subst; reflexivity);
  try (subst; cbn; apply andb_true_iff; split; [ apply IHA1 | apply IHA2 ]; reflexivity);
  try (apply andb_true_iff in H0; destruct H0 as [H1%IHA1 H2%IHA2]; subst; reflexivity).
- apply (@eqb_eq (option_dectype _)) in H0; subst; reflexivity.
- subst; cbn; apply (@eqb_eq (option_dectype _)); reflexivity.
Qed.

(* Unused
Fixpoint eqb_iformlist l1 l2 :=
match l1, l2 with
| nil, nil => true
| cons A t1, cons B t2 => (eqb_iform A B) && (eqb_iformlist t1 t2)
| _, _ => false
end.

Lemma eqb_eq_iformlist l1 l2 : eqb_iformlist l1 l2 = true <-> l1 = l2.
Proof.
induction l1 in l2 |- *; destruct l2; (split; [ intros Heqb | intros Heq ]);
  try inversion Heqb ; try inversion Heq ; try reflexivity.
- apply andb_true_iff in H0.
  destruct H0 as [H1 H2].
  apply eqb_eq_iform in H1; apply IHl1 in H2; subst; reflexivity.
- subst; cbn; apply andb_true_iff.
  split; [ apply eqb_eq_iform | apply IHl1 ]; reflexivity.
Qed.
*)

(* Unused
(** * In with [bool] output for formula list *)
Fixpoint inb_iform A l :=
match l with
| nil => false
| cons hd tl => eqb_iform A hd || inb_iform A tl
end.

Lemma inb_in_iform A l : inb_iform A l = true <-> In A l.
Proof.
induction l; (split; [ intros Heqb | intros Heq ]).
- inversion Heqb.
- inversion Heq.
- inversion Heqb; subst.
  apply orb_true_iff in H0.
  destruct H0.
  + constructor.
    symmetry; apply eqb_eq_iform; assumption.
  + apply in_cons, IHl, H.
- inversion Heq; subst.
  + cbn; apply orb_true_iff; left.
    apply eqb_eq_iform; reflexivity.
  + cbn; apply orb_true_iff; right.
    apply IHl, H.
Qed.
*)


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

Lemma isubb_isub A B : is_true (isubformb A B) <-> isubform A B.
Proof.
split; intros H; induction B; try (now (inversion H; constructor)).
- destruct A; cbn in H; try (now inversion H).
  rewrite orb_false_r in H.
  apply (@eqb_eq (option_dectype _)) in H; subst; constructor.
- now destruct A; inversion H.
- cbn in H.
  apply orb_true_elim in H; destruct H as [ H | H ];
    [ | apply orb_true_elim in H; destruct H as [ H | H ] ].
  + apply eqb_eq_iform in H; subst; constructor.
  + now apply isub_tens_l, IHB1.
  + now apply isub_tens_r, IHB2.
- cbn in H.
  apply orb_true_elim in H; destruct H as [ H | H ];
    [ | apply orb_true_elim in H; destruct H as [ H | H ] ].
  + apply eqb_eq_iform in H; subst; constructor.
  + now apply isub_lpam_l, IHB1.
  + now apply isub_lpam_r, IHB2.
- cbn in H.
  apply orb_true_elim in H; destruct H as [ H | H ];
    [ | apply orb_true_elim in H; destruct H as [ H | H ] ].
  + apply eqb_eq_iform in H; subst; constructor.
  + now apply isub_gen, IHB.
  + apply eqb_eq_iform in H; subst.
    apply isub_gen_N.
- cbn in H.
  apply orb_true_elim in H; destruct H as [ H | H ];
    [ | apply orb_true_elim in H; destruct H as [ H | H ] ].
  + apply eqb_eq_iform in H; subst; constructor.
  + now apply isub_lmap_l, IHB1.
  + now apply isub_lmap_r, IHB2.
- cbn in H.
  apply orb_true_elim in H; destruct H as [ H | H ];
    [ | apply orb_true_elim in H; destruct H as [ H | H ] ].
  + apply eqb_eq_iform in H; subst; constructor.
  + now apply isub_neg, IHB.
  + apply eqb_eq_iform in H; subst.
    apply isub_neg_N.
- now destruct A; inversion H.
- cbn in H.
  apply orb_true_elim in H; destruct H as [ H | H ];
    [ | apply orb_true_elim in H; destruct H as [ H | H ] ].
  + apply eqb_eq_iform in H; subst; constructor.
  + now apply isub_with_l, IHB1.
  + now apply isub_with_r, IHB2.
- now destruct A; inversion H.
- cbn in H.
  apply orb_true_elim in H; destruct H as [ H | H ];
    [ | apply orb_true_elim in H; destruct H as [ H | H ] ].
  + apply eqb_eq_iform in H; subst; constructor.
  + now apply isub_plus_l, IHB1.
  + now apply isub_plus_r, IHB2.
- cbn in H.
  apply orb_true_elim in H; destruct H as [ H | H ].
  + apply eqb_eq_iform in H; subst; constructor.
  + now apply isub_oc, IHB.
- inversion H; subst.
  cbn; rewrite orb_false_r.
  apply (@eqb_refl (option_dectype _ )).
- inversion H; subst.
  + unfold isubformb.
    replace (eqb_iform (itens B1 B2) (itens B1 B2)) with true; [ reflexivity | ].
    symmetry; apply eqb_eq_iform; reflexivity.
  + apply IHB1 in H2.
    cbn; rewrite H2; cbn; rewrite orb_true_r; reflexivity.
  + apply IHB2 in H2.
    cbn; rewrite H2; cbn; rewrite 2 orb_true_r; reflexivity.
- inversion H; subst.
  + unfold isubformb.
    replace (eqb_iform (ilpam B1 B2) (ilpam B1 B2)) with true; [ reflexivity | ].
    symmetry; apply eqb_eq_iform; reflexivity.
  + apply IHB1 in H2.
    cbn; rewrite H2; cbn; rewrite orb_true_r; reflexivity.
  + apply IHB2 in H2.
    cbn; rewrite H2; cbn; rewrite 2 orb_true_r; reflexivity.
- inversion H; subst.
  + unfold isubformb.
    replace (eqb_iform (igen B) (igen B)) with true; [ reflexivity | ].
    symmetry; apply eqb_eq_iform; reflexivity.
  + apply IHB in H2.
    cbn; rewrite H2; cbn; rewrite orb_true_r; reflexivity.
  + cbn; rewrite orb_true_r; reflexivity.
- inversion H; subst.
  + unfold isubformb.
    replace (eqb_iform (ilmap B1 B2) (ilmap B1 B2)) with true; [ reflexivity | ].
    symmetry; apply eqb_eq_iform; reflexivity.
  + apply IHB1 in H2.
    cbn; rewrite H2; cbn; rewrite orb_true_r; reflexivity.
  + apply IHB2 in H2.
    cbn; rewrite H2; cbn; rewrite 2 orb_true_r; reflexivity.
- inversion H; subst.
  + unfold isubformb.
    replace (eqb_iform (ineg B) (ineg B)) with true; [ reflexivity | ].
    symmetry; apply eqb_eq_iform; reflexivity.
  + apply IHB in H2.
    cbn; rewrite H2; cbn; rewrite orb_true_r; reflexivity.
  + cbn; rewrite orb_true_r; reflexivity.
- inversion H ; subst.
  + unfold isubformb.
    replace (eqb_iform (iwith B1 B2) (iwith B1 B2)) with true; [ reflexivity | ].
    symmetry; apply eqb_eq_iform; reflexivity.
  + apply IHB1 in H2.
    cbn; rewrite H2; cbn; rewrite orb_true_r; reflexivity.
  + apply IHB2 in H2.
    cbn; rewrite H2; cbn; rewrite 2 orb_true_r; reflexivity.
- inversion H; subst.
  + unfold isubformb.
    replace (eqb_iform (iplus B1 B2) (iplus B1 B2)) with true; [ reflexivity | ].
    symmetry; apply eqb_eq_iform; reflexivity.
  + apply IHB1 in H2.
    cbn; rewrite H2; cbn; rewrite orb_true_r; reflexivity.
  + apply IHB2 in H2.
    cbn; rewrite H2; cbn; rewrite 2 orb_true_r; reflexivity.
- inversion H; subst.
  + unfold isubformb.
    replace (eqb_iform (ioc B) (ioc B)) with true; [ reflexivity | ].
    symmetry; apply eqb_eq_iform; reflexivity.
  + apply IHB in H2.
    cbn; rewrite H2; cbn; rewrite orb_true_r; reflexivity.
Qed.

Lemma isubb_trans A B C :
  is_true (isubformb A B) -> is_true (isubformb B C) -> is_true (isubformb A C).
Proof. setoid_rewrite isubb_isub; apply isub_trans. Qed.

(** Each element of the first list is a sub-formula of some element of the second. *)
Definition isubformb_list l1 l2 := forallb (fun A => existsb (isubformb A) l2) l1.

Lemma isubb_isub_list l1 l2 : is_true (isubformb_list l1 l2) <-> isubform_list l1 l2.
Proof.
setoid_rewrite Forall_forall.
setoid_rewrite Exists_exists.
setoid_rewrite <- isubb_isub.
setoid_rewrite <- existsb_exists.
setoid_rewrite <- forallb_forall.
reflexivity.
Qed.

Lemma isubb_id_list l l0 : is_true (isubformb_list l (l0 ++ l)).
Proof. apply isubb_isub_list, isub_id_list. Qed.

Lemma isubb_trans_list l1 l2 l3 :
  is_true (isubformb_list l1 l2) -> is_true (isubformb_list l2 l3) -> is_true (isubformb_list l1 l3).
Proof. setoid_rewrite isubb_isub_list; apply isub_trans_list. Qed.

End Atoms.
