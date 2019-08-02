(* Parameter definitions for yalla library *)

Require Import Arith_base.
Require Import Equalities.

Require Import Injective.

(* We provide a possible value for parameters of the library
as a consistency guarantee *)

Definition Atom : Set := nat. (* formulas.v *)
Definition IAtom : Set := option nat. (* iformulas.v *)
Definition atN : IAtom := None. (* iformulas.v *)
Definition TAtom : Set := nat. (* tl.v *)


Definition ateq : Atom -> Atom -> bool := beq_nat. (* subs.v *)
Definition iateq : IAtom -> IAtom -> bool := fun x y => (* isubs.v & tl.v *)
  match x , y with
  | None, None => true
  | Some n, Some m => beq_nat n m
  | _, _ => false
  end.

(* subs.v *)
Fact ateq_eq : forall x y, ateq x y = true <-> x = y.
Proof.
split ; simpl ; intros H.
- apply beq_nat_true in H ; subst ; reflexivity.
- symmetry ; subst.
  apply beq_nat_refl.
Qed.

(* isubs.v & tl.v *)
Fact iateq_eq : forall x y, iateq x y = true <-> x = y.
Proof.
destruct x ; destruct y ; split ; simpl ;
  intros H ; try (now inversion H).
- apply beq_nat_true in H ; subst ; reflexivity.
- inversion H ; subst.
  symmetry.
  apply beq_nat_refl.
Qed.

Module Atom_beq <: UsualBoolEq.
  Definition t := Atom.
  Definition eq := @eq Atom.
  Definition eqb := ateq.
  Definition eqb_eq := ateq_eq.
End Atom_beq.

Module Atom_dec <: UsualDecidableTypeFull := Make_UDTF Atom_beq.

Module IAtom_beq <: UsualBoolEq.
  Definition t := IAtom.
  Definition eq := @eq IAtom.
  Definition eqb := iateq.
  Definition eqb_eq := iateq_eq.
End IAtom_beq.

Module IAtom_dec <: UsualDecidableTypeFull := Make_UDTF IAtom_beq.


Definition a2n : Atom -> nat := id. (* fmformulas.v & nn.v *)
Definition n2a : nat -> Atom := id. (* fmformulas.v & nn.v *)
Definition i2n : IAtom -> nat := fun x => (* fmiformulas.v *)
  match x with
  | None => 0
  | Some x => S x
  end.
Definition n2i : nat -> IAtom := fun n => (* fmiformulas.v *)
  match n with
  | 0 => None
  | S k => Some k
  end.

Definition i2a : IAtom -> Atom := fun x => (* nn.v *)
  match x with
  | None => 0
  | Some x => x
  end.
Definition i2ac : IAtom -> Atom := fun x => (* lambek.v & nn.v & tl.v *)
  match x with
  | None => 0
  | Some x => S x
  end.
Definition t2i : TAtom -> IAtom := Some. (* tl.v *)
Definition a2t : Atom -> TAtom := id. (* tl.v *)
Definition t2a : TAtom -> Atom := id. (* tl.v *)
Definition a2i : Atom -> IAtom := fun n => t2i (a2t n). (* nn.v *)


(* fmformulas.v *)
Fact a2a_n : forall X, n2a (a2n X) = X.
Proof.
unfold n2a ; unfold a2n ; reflexivity.
Qed.

(* fmiformulas.v *)
Fact i2i_n : forall X, n2i (i2n X) = X.
Proof.
unfold n2i ; unfold i2n.
destruct X ; simpl ; reflexivity.
Qed.

(* lambek.v & nn.v & tl.v *)
Fact i2ac_inj : injective i2ac.
Proof.
intros x y Heq.
unfold i2a in Heq.
destruct x ; destruct y ; inversion Heq ; subst ; try reflexivity.
Qed.

(* nn.v *)
Fact a2a_i : forall x, i2a (a2i x) = x.
Proof.
destruct x ; simpl ; reflexivity.
Qed.

(* nn.v *)
Fact ateq_a2i : forall x y, ateq x y = true <-> iateq (a2i x) (a2i y) = true.
Proof.
intros x y ; split ; intros Heq.
- apply ateq_eq in Heq.
  apply iateq_eq.
  f_equal ; assumption.
- apply iateq_eq in Heq.
  apply ateq_eq.
  eapply (section_inj a2i i2a) in Heq.
  + assumption.
  + apply a2a_i.
Qed.

(* nn.v *)
Lemma i2i_not_atN : forall x, x <> atN -> a2i (i2a x) = x.
Proof.
intros x HatN.
destruct x ; [ | contradiction HatN ] ; reflexivity.
Qed.

(* nn.v *)
Fact n2n_a : forall n, a2n (n2a n) = n.
Proof.
reflexivity.
Qed.

(* tl.v *)
Fact t2i_inj : injective t2i.
Proof.
intros x y Heq.
unfold t2i in Heq.
destruct x ; destruct y ; inversion Heq ; subst ; try reflexivity.
Qed.

(* tl.v *)
Fact notatN : forall x, ~ atN = t2i x.
Proof.
intros x Heq ; inversion Heq.
Qed.

(* tl.v *)
Fact atN_or_t2i : forall x, (atN = x) + { y | x = t2i y }.
Proof.
destruct x ; [ right | left ].
- exists n ; reflexivity.
- reflexivity.
Qed.

(* tl.v *)
Fact a2t_inj : injective a2t.
Proof.
intros x y Heq.
unfold a2t in Heq.
unfold id in Heq.
assumption.
Qed.

(* tl.v *)
Fact a2a_t : forall x, t2a (a2t x) = x.
Proof.
intros x.
unfold t2a ; unfold a2t ; reflexivity.
Qed.

(* tl.v *)
Fact a2i_a2i : forall x, t2i (a2t x) = a2i x.
Proof.
intros x.
unfold a2i ; unfold t2i ; unfold a2t ; reflexivity.
Qed.


(** Make definitions opaque, so that only properties can be used *)
Global Opaque Atom IAtom atN TAtom ateq iateq a2n n2a i2n n2i i2a i2ac t2i a2t t2a a2i.


