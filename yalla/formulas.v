From Stdlib Require Import List EqNat RelationClasses Lia.
From OLlibs Require Import Datatypes_more Bool_more funtheory dectype.
From Yalla Require Export atoms.

Set Implicit Arguments.

(** * Linear Logic formulas *)

Section Atoms.

(** A set of atoms for building formulas *)
Context {atom : DecType}.

(** ** Definition and main properties of formulas *)

(** Formulas *)
Inductive formula :=
| var (_ : atom) | covar (_ : atom)
| one | bot
| tens (_ _ : formula) | parr (_ _ : formula)
| zero | top
| aplus (_ _ : formula) | awith (_ _ : formula)
| oc (_ : formula) | wn (_ : formula).

Variant var_formula : formula -> Type := | isvar : forall X, var_formula (var X).
Variant covar_formula : formula -> Type := | iscovar X : covar_formula (covar X).
Variant wn_formula : formula -> Type := | iswn A : wn_formula (wn A).

Definition is_var (A : formula) :=
  match A with
  | var _ => true
  | _ => false
  end.

Lemma var_spec A : reflectT (var_formula A) (is_var A).
Proof. destruct A; cbn; constructor; try (intro H; inversion H); constructor. Qed.

Definition is_covar (A : formula) :=
  match A with
  | covar _ => true
  | _ => false
  end.

Lemma covar_spec A : reflectT (covar_formula A) (is_covar A).
Proof. destruct A; cbn; constructor; try (intro H; inversion H); constructor. Qed.

Definition is_wn (A : formula) :=
  match A with
  | wn _ => true
  | _ => false
  end.

Lemma wn_spec A : reflectT (wn_formula A) (is_wn A).
Proof. destruct A; cbn; constructor; try (intro H; inversion H); constructor. Qed.

(** Atomic [formula] *)
Variant atomic : formula -> Type := | atomic_var x : atomic (var x) | atomic_covar x : atomic (covar x).

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

Lemma wn_n_wn n A : wn_n n (wn A) = wn_n (S n) A.
Proof. induction n as [|n IHn]; [ | cbn; rewrite IHn ]; reflexivity. Qed.

Fixpoint oc_n n A :=
match n with
| 0 => A
| S n => oc (oc_n n A)
end.

Lemma oc_n_oc n A : oc_n n (oc A) = oc_n (S n) A.
Proof. induction n as [|n IHn]; [ | cbn; rewrite IHn ]; reflexivity. Qed.

(** Exponential modalities *)

(* lists of Booleans with false = oc and true = wn *)
Definition exp_mod := list bool.

Definition exp (m : exp_mod) A := fold_right (fun b : bool => if b then wn else oc) A m.


(** Orthogonal / dual of a [formula] *)

(** (the dual of [tens] and [parr] is the one compatible with non-commutative systems) *)
Fixpoint dual C :=
match C with
| var x => covar x
| covar x => var x
| one => bot
| bot => one
| tens A B  => parr (dual B) (dual A)
| parr A B  => tens (dual B) (dual A)
| zero => top
| top => zero
| aplus A B => awith (dual A) (dual B)
| awith A B => aplus (dual A) (dual B)
| oc A => wn (dual A)
| wn A => oc (dual A)
end.

Lemma bidual A : dual (dual A) = A.
Proof. induction A; cbn; rewrite ? IHA1, ? IHA2, ? IHA; reflexivity. Qed.

Lemma codual A B : dual A = B <-> A = dual B.
Proof. split; intro H; rewrite <- (bidual A), <- (bidual B), H, ? bidual; reflexivity. Qed.

Lemma dual_inj : injective dual.
Proof. intros A B H. rewrite <- (bidual A), <- (bidual B), H. reflexivity. Qed.

Lemma atomic_dual A : iffT (atomic A) (atomic (dual A)).
Proof. destruct A; split; intros Hat; inversion Hat; constructor. Qed.

Lemma dual_tens_n n A : dual (tens_n n A) = parr_n n (dual A).
Proof. induction n as [|[|n] IHn]; [ | | cbn in *; rewrite <- IHn ]; reflexivity. Qed.

Lemma dual_parr_n n A : dual (parr_n n A) = tens_n n (dual A).
Proof. induction n as [|[|n] IHn]; [ | | cbn in *; rewrite <- IHn ]; reflexivity. Qed.

Lemma dual_wn_n n A : dual (wn_n n A) = oc_n n (dual A).
Proof. induction n as [|n IHn]; [ | cbn; rewrite <- IHn ]; reflexivity. Qed.

Lemma dual_oc_n n A : dual (oc_n n A) = wn_n n (dual A).
Proof. induction n as [|n IHn]; [ | cbn; rewrite <- IHn ]; reflexivity. Qed.


(** Size of a [formula] as its number of symbols *)
Fixpoint fsize A :=
match A with
| var _ | covar _ => 1
| one | bot | zero | top => 1
| tens A B | parr A B | aplus A B | awith A B => S (fsize A + fsize B)
| oc A | wn A => S (fsize A)
end.

Lemma fsize_pos A : 0 < fsize A.
Proof. induction A; cbn; lia. Qed.

Lemma fsize_dual A : fsize (dual A) = fsize A.
Proof. induction A; cbn; rewrite ? IHA1, ? IHA2; lia. Qed.

Lemma fsize_wn_n n A : fsize (wn_n n A) = n + fsize A.
Proof. induction n as [|n IHn]; [ | cbn; rewrite IHn ]; reflexivity. Qed.

Lemma fsize_oc_n n A : fsize (oc_n n A) = n + fsize A.
Proof. induction n as [|n IHn]; [ | cbn; rewrite IHn ]; reflexivity. Qed.


(** Atoms in a formula *)
Fixpoint atom_list A : list atom :=
match A with
| var x | covar x => x :: nil
| one | bot | zero | top => nil
| parr B C | aplus B C | awith B C => atom_list B ++ atom_list C
| tens B C => atom_list C ++ atom_list B
| oc B | wn B => atom_list B
end.

Lemma atom_list_dual A : atom_list (dual A) = atom_list A.
Proof. now induction A; cbn; rewrite ? IHA1, ? IHA2. Qed.


(** ** Sub-formulas *)

(** First argument is a sub-formula of the second: *)
Inductive subform : formula -> formula -> Prop :=
| sub_id A : subform A A
| sub_tens_l A B C : subform A B -> subform A (tens B C)
| sub_tens_r A B C : subform A B -> subform A (tens C B)
| sub_parr_l A B C : subform A B -> subform A (parr B C)
| sub_parr_r A B C : subform A B -> subform A (parr C B)
| sub_plus_l A B C : subform A B -> subform A (aplus B C)
| sub_plus_r A B C : subform A B -> subform A (aplus C B)
| sub_with_l A B C : subform A B -> subform A (awith B C)
| sub_with_r A B C : subform A B -> subform A (awith C B)
| sub_oc A B : subform A B -> subform A (oc B)
| sub_wn A B : subform A B -> subform A (wn B).

Lemma sub_trans A B C : subform A B -> subform B C -> subform A C.
Proof. intros Hl Hr. induction Hr in A, Hl |- *; try (constructor; apply IHHr); assumption. Qed.

#[export] Instance sub_po : PreOrder subform | 50.
Proof. split; intro; [ apply sub_id | eapply sub_trans; eassumption ]. Qed.

(** Each element of the first list is a sub-formula of some element of the second. *)
Definition subform_list l1 l2 := Forall (fun A => Exists (subform A) l2) l1.

Lemma sub_id_list l l0 : subform_list l (l0 ++ l).
Proof.
induction l as [|a l IHl] in l0 |- *; constructor.
- induction l0.
  + constructor. apply sub_id.
  + apply Exists_cons_tl. assumption.
- replace (l0 ++ a :: l) with ((l0 ++ a :: nil) ++ l) by (rewrite <- app_assoc; reflexivity). apply IHl.
Qed.

Lemma sub_trans_list l1 l2 l3 : subform_list l1 l2 -> subform_list l2 l3 -> subform_list l1 l3.
Proof.
induction l1 in l2, l3 |- *; intros Hl Hr; constructor.
- inversion Hl. subst.
  revert Hr H1; clear; induction l2; intros Hr Hl; inversion Hl; subst.
  + inversion Hr. subst.
    inversion H2; subst.
    * apply Exists_cons_hd.
      transitivity a0; assumption.
    * apply Exists_cons_tl.
      revert H; clear - H0; induction l; intro H; inversion H; subst.
      -- apply Exists_cons_hd.
         transitivity a0; assumption.
      -- apply Exists_cons_tl, IHl. assumption.
  + inversion Hr. subst.
    apply IHl2; assumption.
- inversion Hl. subst.
  apply IHl1 with l2; assumption.
Qed.

Instance sub_list_po : PreOrder subform_list.
Proof. split; intro; [ rewrite <- app_nil_l; apply sub_id_list | apply sub_trans_list ]. Qed.

(* Unused
From OLlibs Require Import GPermutation_Type.

Lemma sub_perm_list b l l1 l2 : subform_list l l1 -> PCPermutation_Type b l1 l2 -> subform_list l l2.
Proof.
intros HF HP. apply Forall_forall.
setoid_rewrite <- (PCPermutation_Type_Exists _ _ HP).
apply Forall_forall; assumption.
Qed.
*)


(** ** Equality in [bool] *)

Fixpoint eqb_form A B :=
match A, B with
| var X, var Y | covar X, covar Y => eqb X Y
| one, one | bot, bot | zero, zero | top, top => true
| tens A1 A2, tens B1 B2 | parr A1 A2, parr B1 B2
| aplus A1 A2, aplus B1 B2 | awith A1 A2, awith B1 B2 => eqb_form A1 B1 && eqb_form A2 B2
| oc A1, oc B1 | wn A1, wn B1 => eqb_form A1 B1
| _, _ => false
end.

Lemma eqb_eq_form A B : eqb_form A B = true <-> A = B.
Proof.
induction A in B |- *; destruct B; (split; intros Heq);
  inversion Heq as [Heq']; subst;
  try apply eqb_eq in Heq' as ->;
  try apply IHA in Heq' as ->;
  try apply andb_true_iff in Heq' as [->%IHA1 ->%IHA2];
  try apply eqb_eq;
  try apply IHA;
  try (apply andb_true_iff; split; [ apply IHA1 | apply IHA2 ]);
  reflexivity.
Qed.

Definition formulas_dectype := {|
  car := formula;
  eqb := eqb_form;
  eqb_eq := eqb_eq_form |}.

End Atoms.
