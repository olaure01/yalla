(** * Various structures on atoms required in the Yalla library *)
(** and consistency checks *)

From OLlibs Require Import Datatypes_more funtheory List_Type.
From OLlibs Require Export infinite.


(** ** Classes containing constraints on atom sets *)

Class AtomType_self (A : DecType) := Atom_self_inj : self_injective A.

Definition AtomType_self_InfDecType (A : DecType) (As : AtomType_self A) := {|
  infcar := A;
  fresh := proj1_sig (nat_injective_choice _ (self_injective_nat _ Atom_self_inj));
  fresh_spec := proj2_sig (nat_injective_choice _ (self_injective_nat _ Atom_self_inj)) |}.

Class AtomType_into_nat (A : DecType) := Atom_into_nat : embedding A nat.

Class IAtomType_into_nat (I : DecType) := IAtom_into_nat : embedding (option I) nat.

Class IAtom2AtomType (A : DecType) (I : DecType) := IAtom2Atom : option I -> A.

Class IAtom2AtomType_fin (A : DecType) (I : DecType) := {
  IAtom2Atom_fin_base :> IAtom2AtomType A I;
  IAtom2Atom_fin x : { l & forall i, iffT (x = IAtom2Atom i) (In_inf i l) } }.

Class IAtom2AtomType_retract (A : DecType) (I : DecType) := {
  IAtom2Atom_retract_base :> IAtom2AtomType A I;
  IAtom2Atom_retract_base_inv : A -> option I;
  IAtom2Atom_retract : retract IAtom2Atom_retract_base_inv IAtom2Atom }.

Lemma retract_fin (A : Type) (B : DecType) (f : A -> B) g : retract g f ->
  forall x, { l & forall i, iffT (x = f i) (In_inf i l) }.
Proof.
intros Hr b.
destruct (eq_dt_dec b (f (g b))) as [Heq | Hneq].
- exists (g b :: nil). intros a. split.
  + intros ->. rewrite Hr. left. reflexivity.
  + intros [<-|[]]. assumption.
- exists nil. intros a. split.
  + intros ->. apply Hneq. rewrite Hr. reflexivity.
  + intros [].
Qed.

#[export] Instance IAtom2AtomType_retract_fin (A I : DecType) :
  IAtom2AtomType_retract A I -> IAtom2AtomType_fin A I | 50 := fun C => {|
  IAtom2Atom_fin_base := IAtom2Atom_retract_base;
  IAtom2Atom_fin := retract_fin _ _ _ _ (@IAtom2Atom_retract A I C) |}.

Class Atom2IAtomType_self (A : DecType) (I : DecType) := {
  Atom2IAtom_Atom_self :> AtomType_self A;
  Atom2PreIAtom : A -> I;
  Atom2PreIAtom_bij : bijective Atom2PreIAtom }.

Class TAtom2IAtomType (I : DecType) (T : DecType) := {
  TAtom2PreIAtom : T -> I;
  TAtom2PreIAtom_bij : bijective TAtom2PreIAtom }.

Class TLAtomType (A : DecType) (I : DecType) (T : DecType) := {
  TLAtom_base :> IAtom2AtomType_retract A I;
  TLAtom_TAtom :> TAtom2IAtomType I T }.

Class AtomIAtomTAtomType (A : DecType) (I : DecType) (T : DecType) := {
  AtomIAtomTAtom_IAtom2Atom :> IAtom2AtomType_retract A I;
  AtomIAtomTAtom_Atom2IAtom :> Atom2IAtomType_self A I;
  AtomIAtomTAtom_TAtom :> TLAtomType A I T }.


(** ** Consistency checks *)

(** *** A global class containing all required constraints *)

Class FullAtoms := {
  FAtom : InfDecType;
  FPreIAtom : InfDecType;
  FTAtom : InfDecType;
  FAtom_self : self_injective FAtom;
  FAtom2nat : embedding FAtom nat;
  FPreIAtom2nat : embedding (option FPreIAtom) nat;
  FIAtom2Atom : option FPreIAtom -> FAtom;
  FIAtom2Atom_section : { g & retract g FIAtom2Atom };
  FAtom2PreIAtom : FAtom -> FPreIAtom;
  FAtom2PreIAtom_bij : bijective FAtom2PreIAtom;
  FTAtom2PreIAtom : FTAtom -> FPreIAtom;
  FTAtom2PreIAtom_bij : bijective FTAtom2PreIAtom }.

(** *** Instances for all previous classes from the global one *)

#[local] Instance FAtomType_self (C : FullAtoms) : AtomType_self FAtom | 50 := FAtom_self.
#[local] Instance FAtomType_into_nat (C : FullAtoms) : AtomType_into_nat FAtom | 50 := FAtom2nat.
#[local] Instance FIAtomType_into_nat (C : FullAtoms) : IAtomType_into_nat FPreIAtom | 50 := FPreIAtom2nat.
#[local] Instance FIAtom2AtomType (C : FullAtoms) : IAtom2AtomType FAtom FPreIAtom | 50 := FIAtom2Atom.
#[local] Instance FIAtom2AtomType_retract (C : FullAtoms) : IAtom2AtomType_retract FAtom FPreIAtom | 50 :=
  let (g, Hr) := FIAtom2Atom_section in {|
  IAtom2Atom_retract_base := FIAtom2AtomType C;
  IAtom2Atom_retract_base_inv := g;
  IAtom2Atom_retract := Hr |}.
(*
#[local] Instance FIAtom2AtomType_fin (C : FullAtoms) : IAtom2AtomType_fin FAtom FPreIAtom | 50 := {|
  IAtom2Atom_fin_base := FIAtom2AtomType C;
  IAtom2Atom_fin := let (g, Hr) := FIAtom2Atom_retract in retract_fin _ _ _ _ Hr |}.
*)
#[local] Instance FAtom2IAtomType_self (C : FullAtoms) : Atom2IAtomType_self FAtom FPreIAtom | 50 := {|
  Atom2IAtom_Atom_self := FAtomType_self C;
  Atom2PreIAtom := FAtom2PreIAtom;
  Atom2PreIAtom_bij := FAtom2PreIAtom_bij |}.
#[local] Instance FTAtom2IAtomType (C : FullAtoms) : TAtom2IAtomType FPreIAtom FTAtom | 50 := {|
  TAtom2PreIAtom := FTAtom2PreIAtom;
  TAtom2PreIAtom_bij := FTAtom2PreIAtom_bij |}.
#[local] Instance FTLAtomType (C : FullAtoms) : TLAtomType FAtom FPreIAtom FTAtom | 50 := {|
  TLAtom_base := FIAtom2AtomType_retract C;
  TLAtom_TAtom := FTAtom2IAtomType C |}.
#[local] Instance FAtomIAtomTAtomType (C : FullAtoms) : AtomIAtomTAtomType FAtom FPreIAtom FTAtom | 50 := {|
  AtomIAtomTAtom_IAtom2Atom := FIAtom2AtomType_retract C;
  AtomIAtomTAtom_Atom2IAtom := FAtom2IAtomType_self C;
  AtomIAtomTAtom_TAtom := FTLAtomType C |}.

(** *** Consistency by concrete instance based on [nat] *)

Definition option_nat_to_nat := option_eval_default 0 S.

Definition nat_to_option_nat n :=
match n with
| 0 => None
| S k => Some k
end.

Lemma section_option_nat_to_nat : { g & retract g option_nat_to_nat }.
Proof. exists nat_to_option_nat. intros []; reflexivity. Qed.

Lemma option_nat_into_nat : embedding (option nat) nat.
Proof. destruct section_option_nat_to_nat as [g Hr]. exists (g, option_nat_to_nat). assumption. Qed.

Lemma nat_bijective_nat : nat_bijective nat.
Proof. exists id. apply id_bijective. Qed.


Definition Nat_FullAtoms := {|
  FAtom := nat_infdectype;
  FPreIAtom := nat_infdectype;
  FTAtom := nat_infdectype;
  FAtom_self := nat_bijective_self nat_bijective_nat;
  FAtom2nat := id_embedding nat;
  FPreIAtom2nat := option_nat_into_nat;
  FIAtom2Atom := option_nat_to_nat;
  FIAtom2Atom_section := section_option_nat_to_nat;
  FAtom2PreIAtom := id;
  FAtom2PreIAtom_bij := id_bijective;
  FTAtom2PreIAtom := id;
  FTAtom2PreIAtom_bij := id_bijective |}.
