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

(** Atomic [iformula] *)
Inductive iatomic : iformula -> Type :=
| iatomic_var x : iatomic (ivar x).

(* Unused
Inductive iatomic_Prop : iformula -> Prop :=
| iatomic_Prop_var : forall x, iatomic_Prop (ivar x).

Lemma iatomic_Prop_iatomic A : iatomic_Prop A -> iatomic A.
Proof. induction A; intros Hat; try (exfalso; inversion Hat; fail); constructor. Qed.
*)

(** Atoms in a formula *)
Fixpoint iatom_list A : list iatom :=
match A with
| ivar x => x :: nil
| ione | izero | itop => nil
| itens B C | ilpam B C | ilmap B C | iplus B C | iwith B C => iatom_list B ++ iatom_list C
| igen B | ineg B => atN :: iatom_list B
| ioc B => iatom_list B
end.


(** ** Sub-formulas *)

(** First argument is a sub-formula of the second: *)
Inductive isubform : iformula -> iformula -> Prop :=
| isub_id A : isubform A A
| isub_tens_l A B C : isubform A B -> isubform A (itens B C)
| isub_tens_r A B C : isubform A B -> isubform A (itens C B)
| isub_lpam_l A B C : isubform A B -> isubform A (ilpam B C)
| isub_lpam_r A B C : isubform A B -> isubform A (ilpam C B)
| isub_gen A B : isubform A B -> isubform A (igen B)
| isub_gen_N A : isubform N (igen A)
| isub_lmap_l A B C : isubform A B -> isubform A (ilmap B C)
| isub_lmap_r A B C : isubform A B -> isubform A (ilmap C B)
| isub_neg A B : isubform A B -> isubform A (ineg B)
| isub_neg_N A : isubform N (ineg A)
| isub_plus_l A B C : isubform A B -> isubform A (iplus B C)
| isub_plus_r A B C : isubform A B -> isubform A (iplus C B)
| isub_with_l A B C : isubform A B -> isubform A (iwith B C)
| isub_with_r A B C : isubform A B -> isubform A (iwith C B)
| isub_oc A B : isubform A B -> isubform A (ioc B).

Lemma isub_trans A B C : isubform A B -> isubform B C -> isubform A C.
Proof.
intros Hl Hr. induction Hr in A, Hl |- * ; try (constructor; apply IHHr); try assumption.
- inversion_clear Hl. apply isub_gen_N.
- inversion_clear Hl. apply isub_neg_N.
Qed.

#[export] Instance isub_po : PreOrder isubform | 50.
Proof. split; intro; [ apply isub_id | apply isub_trans ]. Qed.

(** Each element of the first list is a sub-formula of some element of the second. *)
Definition isubform_list l1 l2 := Forall (fun A => Exists (isubform A) l2) l1.

Lemma isub_id_list l l0 : isubform_list l (l0 ++ l).
Proof.
induction l as [|a l IHl] in l0 |- *; constructor.
- induction l0.
  + constructor. apply isub_id.
  + apply Exists_cons_tl. assumption.
- replace (l0 ++ a :: l) with ((l0 ++ a :: nil) ++ l) by (rewrite <- app_assoc; reflexivity). apply IHl.
Qed.

Lemma isub_trans_list l1 l2 l3 : isubform_list l1 l2 -> isubform_list l2 l3 -> isubform_list l1 l3.
Proof.
induction l1 in l2, l3 |- *; intros Hl Hr; constructor.
- inversion Hl. subst.
  clear - Hr H1. induction l2 in Hr, H1 |-*; inversion H1; subst.
  + inversion Hr. subst.
    clear - H0 H3. induction l3 in H0, H3 |- *; inversion H3; subst.
    * apply Exists_cons_hd.
      transitivity a0; assumption.
    * apply Exists_cons_tl.
      apply IHl3; assumption.
  + inversion Hr. subst.
    apply IHl2; assumption.
- inversion Hl. subst.
  eapply IHl1; eassumption.
Qed.

#[export] Instance isub_list_po : PreOrder isubform_list | 50.
Proof.
split.
- intros l. rewrite <- app_nil_l. apply isub_id_list.
- intros l1 l2 l3. apply isub_trans_list.
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
- apply (@eqb_eq (option_dectype _)) in H0 as ->. reflexivity.
- subst. cbn. apply (@eqb_eq (option_dectype _)). reflexivity.
Qed.

Definition iformulas_dectype := {|
  car := iformula;
  eqb := eqb_iform;
  eqb_eq := eqb_eq_iform |}.


End Atoms.
