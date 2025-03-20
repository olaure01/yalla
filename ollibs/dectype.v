(** Types with decidable equality formalized as types with Boolean valued equality
this is based on records rather than modules (as opposed to stdlib) *)

From Stdlib Require Import Bool PeanoNat Equalities.
From Stdlib Require Eqdep_dec.
From Yalla.OLlibs Require Export inhabited_Type.
From Yalla.OLlibs Require Import funtheory.

Set Implicit Arguments.
Set Default Proof Using "Type".

(** * Decidable Types *)
(** types with a boolean binary predicate equivalent to equality *)

Record DecType := {
  car :> Type;
  eqb : car -> car -> bool;
  eqb_eq : forall x y, eqb x y = true <-> x = y }.
Arguments eqb [_].
Arguments eqb_eq [_].

Section DecTypes.

  Variable X : DecType.
  Implicit Type x y : X.

  Lemma eqb_refl x : eqb x x = true.
  Proof. apply (proj2 (eqb_eq x x) eq_refl). Qed.

  Lemma eqb_neq x y : eqb x y = false <-> x <> y.
  Proof.
  destruct (eqb x y) eqn:Heq; split; intros Hb; [ discriminate Hb | | | reflexivity ].
  - apply eqb_eq in Heq as ->. contradiction Hb. reflexivity.
  - intros ->. rewrite eqb_refl in Heq. discriminate Heq.
  Qed.

  Lemma eqb_sym x y : eqb x y = eqb y x.
  Proof.
  destruct (eqb x y) eqn:Hxy; destruct (eqb y x) eqn:Hyx; [ reflexivity | | | reflexivity ]; exfalso.
  - apply eqb_eq in Hxy as ->. rewrite eqb_refl in Hyx. discriminate Hyx.
  - apply eqb_eq in Hyx as ->. rewrite eqb_refl in Hxy. discriminate Hxy.
  Qed.

  Lemma eq_dt_dec x y : {x = y} + {x <> y}.
  Proof. destruct (eqb x y) eqn:Heq; [ left; apply eqb_eq in Heq | right; apply eqb_neq in Heq ]; assumption. Qed.

  Lemma eq_dt_reflect x y : reflect (x = y) (eqb x y).
  Proof. destruct (eqb x y) eqn:Heq; [ apply ReflectT, eqb_eq | apply ReflectF, eqb_neq ]; assumption. Qed.

  Lemma if_eq_dt_dec_refl A x (u v : A) : (if eq_dt_dec x x then u else v) = u.
  Proof. now destruct (eq_dt_dec x x). Qed.

  Lemma if_eq_dt_dec_neq A x y : x <> y -> forall (u v : A), (if eq_dt_dec x y then u else v) = v.
  Proof. now intros Hneq u v; destruct (eq_dt_dec x y). Qed.


  (** Statements from [Module DecidableEqDep] in [Eqdep_dec] *)
  Lemma eq_rect_eq : forall x (P : X -> Type) p h, p = eq_rect x P p x h.
  Proof. exact (Eqdep_dec.eq_rect_eq_dec eq_dt_dec). Qed.

  Theorem eq_dep_eq : forall (P : X -> Type) x p q, EqdepFacts.eq_dep X P x p x q -> p = q.
  Proof. exact (EqdepFacts.eq_rect_eq__eq_dep_eq X eq_rect_eq). Qed.

  Lemma UIP : forall x y (p q : x = y), p = q.
  Proof. exact (Eqdep_dec.UIP_dec eq_dt_dec). Qed.

  Lemma UIP_refl : forall x p, p = eq_refl x.
  Proof. exact (EqdepFacts.UIP__UIP_refl _ UIP). Qed.

  Lemma Streicher_K : forall x (P : x = x -> Prop), P (eq_refl x) -> forall p, P p.
  Proof. exact (Eqdep_dec.K_dec_type eq_dt_dec). Qed.

  Lemma inj_pairT2 : forall (P : X -> Type) x p q, existT P x p = existT P x q -> p = q.
  Proof. exact (EqdepFacts.eq_dep_eq__inj_pairT2 X eq_dep_eq). Qed.

End DecTypes.

Arguments eqb_refl {_} _.
Arguments eqb_neq {_} _.
Arguments eq_dt_dec {_} _ _.
Arguments eq_dt_reflect {_} _ _.


(** * Instances and Constructions *)

(** the [Empty_set] instance *)
Definition Empty_set_dectype := {|
  car := Empty_set;
  eqb := fun _ _ => true;
  eqb_eq := fun a b => match a with end |}.

(** the [unit] instance *)
Definition unit_dectype := {|
  car := unit;
  eqb := fun _ _ => true;
  eqb_eq := fun a b => match a, b with
                       | tt, tt => conj (fun _ => eq_refl) (fun _ => eq_refl)
                       end |}.

(** the [bool] instance *)
Definition bool_dectype := {|
  car := bool;
  eqb := Bool.eqb;
  eqb_eq := Bool.eqb_true_iff |}.

(** the [nat] instance *)
Definition nat_dectype := {|
  car := nat;
  eqb := Nat.eqb;
  eqb_eq := Nat.eqb_eq |}.

(** the [option] construction *)
Scheme Equality for option.

Definition option_dectype (D : DecType) := {|
  car := option D.(car);
  eqb := option_beq D.(@eqb);
  eqb_eq := fun a b => conj
                      (internal_option_dec_bl _ (fun x y => proj1 (D.(@eqb_eq) x y)) a b)
                      (@internal_option_dec_lb _ _ (fun x y => proj2 (D.(@eqb_eq) x y)) a b) |}.

(** the [sum] construction *)
Scheme Equality for sum.

Definition sum_dectype (D1 D2 : DecType) := {|
  car := sum D1 D2;
  eqb := sum_beq D1.(@eqb) D2.(@eqb);
  eqb_eq := fun a b => conj
                       (internal_sum_dec_bl _ _ (fun x y => proj1 (D1.(@eqb_eq) x y))
                                                (fun x y => proj1 (D2.(@eqb_eq) x y)) a b)
                       (@internal_sum_dec_lb _ _ _ _ (fun x y => proj2 (D1.(@eqb_eq) x y))
                                                     (fun x y => proj2 (D2.(@eqb_eq) x y)) a b) |}.

(** the [prod] construction *)
Scheme Equality for prod.

Definition prod_dectype (D1 D2 : DecType) := {|
  car := prod D1 D2;
  eqb := prod_beq D1.(@eqb) D2.(@eqb);
  eqb_eq := fun a b => conj
                       (internal_prod_dec_bl _ _ (fun x y => proj1 (D1.(@eqb_eq) x y))
                                                 (fun x y => proj1 (D2.(@eqb_eq) x y)) a b)
                       (@internal_prod_dec_lb _ _ _ _ (fun x y => proj2 (D1.(@eqb_eq) x y))
                                                      (fun x y => proj2 (D2.(@eqb_eq) x y)) a b) |}.

(** the [list] construction *)
Scheme Equality for list.

Definition list_dectype (D : DecType) := {|
  car := list D;
  eqb := list_beq D.(@eqb);
  eqb_eq := fun a b => conj
                       (internal_list_dec_bl _ (fun x y => proj1 (D.(@eqb_eq) x y)) a b)
                       (@internal_list_dec_lb _ _ (fun x y => proj2 (D.(@eqb_eq) x y)) a b) |}.

(** the [minus] construction *)
(**   remove an element from a DecType *)
Section Minus.

  Variable D : DecType.
  Variable d : D.

  Lemma minus_eqb_eq (a b : { z | eqb d z = false }) : eqb (proj1_sig a) (proj1_sig b) = true <-> a = b.
  Proof.
  destruct a as [a Ha], b as [b Hb]. cbn. split; intros Heq.
  - apply eqb_eq in Heq as ->.
    f_equal. apply (@UIP bool_dectype _ _ Ha Hb).
  - inversion_clear Heq. apply eqb_refl.
  Qed.

  Definition minus := {|
    car := { z | eqb d z = false };
    eqb := fun a b => eqb (proj1_sig a) (proj1_sig b);
    eqb_eq := minus_eqb_eq |}.

End Minus.

Arguments minus {_} _.


(** * Tactics *)

(** a tactic for automatic case analysis on equalities on a [DecType] *)
Ltac case_analysis :=
let Heq := fresh "Heq" in
match goal with
| |- context f [?x =? ?y] => destruct (x =? y) eqn:Heq
| |- context f [?x <? ?y] => destruct (x <? y) eqn:Heq
| |- context f [?x ?= ?y] => destruct (x ?= y) eqn:Heq
| |- context f [eqb ?x ?x] => rewrite (eqb_refl x)
| |- context f [eqb ?x ?y] => case eq_dt_reflect; intros Heq; [ try subst x | ]
| |- context f [eq_dt_dec ?x ?x] => rewrite (if_eq_dt_dec_refl _ x)
| H : ?x <> ?y |- context f [eq_dt_dec ?x ?y] => rewrite (if_eq_dt_dec_neq _ H)
| H : ?y <> ?x |- context f [eq_dt_dec ?x ?y] => rewrite (if_eq_dt_dec_neq _ (not_eq_sym H))
| |- context f [eq_dt_dec ?x ?y] => destruct (eq_dt_dec x y) eqn:Heq; [ try subst x | ]
end; cbn.


(** * Inhabited Decidable Types *)
(** types with a boolean binary predicate equivalent to equality *)

Record InhDecType := {
  inhcar :> DecType;
  inh_dt : inhabited_inf inhcar }.
Arguments inh_dt {_}.

Definition unit_inhdectype := {|
  inhcar := unit_dectype;
  inh_dt := inhabited_inf_unit |}.

Definition bool_inhdectype := {|
  inhcar := bool_dectype;
  inh_dt := inhabited_inf_bool |}.

Definition nat_inhdectype := {|
  inhcar := nat_dectype;
  inh_dt := inhabited_inf_nat |}.

Definition option_inhdectype (D : DecType) := {|
  inhcar := option_dectype D;
  inh_dt := inhabited_inf_option D |}.

Definition suml_inhdectype (D1 : InhDecType) (D2 : DecType) := {|
  inhcar := sum_dectype D1 D2;
  inh_dt := inhabited_inf_suml inh_dt |}.

Definition sumr_inhdectype (D1 : DecType) (D2 : InhDecType) := {|
  inhcar := sum_dectype D1 D2;
  inh_dt := inhabited_inf_sumr inh_dt |}.

Definition sum_inhdectype (D1 D2 : InhDecType) := suml_inhdectype D1 D2.

Definition prod_inhdectype (D1 D2 : InhDecType) := {|
  inhcar := prod_dectype D1 D2;
  inh_dt := inhabited_inf_prod inh_dt inh_dt |}.

Definition list_inhdectype (D : DecType) := {|
  inhcar := list_dectype D;
  inh_dt := inhabited_inf_list D |}.


(** Equivalence between [DecType] and [UsualBoolEq]. *)

Module Type ModDecType.
  Parameter DT : DecType.
End ModDecType.

Module ModDecType_as_UsualBoolEq (T : ModDecType) : UsualBoolEq.
  Definition t := @car T.DT.
  Definition eq := @eq T.DT.
  Definition eqb := @eqb T.DT.
  Definition eqb_eq := @eqb_eq T.DT.
End ModDecType_as_UsualBoolEq.

Module ModDecType_as_UsualDecidableTypeFull (T : ModDecType) : UsualDecidableTypeFull.
  Module TMDT := ModDecType_as_UsualBoolEq T.
  Include Make_UDTF TMDT.
End ModDecType_as_UsualDecidableTypeFull.

Module UsualBoolEq_as_DecType (T : UsualBoolEq).
  Definition to_DecType := {|
    car := T.t;
    eqb := T.eqb;
    eqb_eq := T.eqb_eq |}.
End UsualBoolEq_as_DecType.

Module UsualBoolEq_as_ModDecType (T : UsualBoolEq).
  Module DT := UsualBoolEq_as_DecType T.
  Definition t := DT.to_DecType.
End UsualBoolEq_as_ModDecType.


(** Functions *)

Lemma section_coimage_option A (B : DecType) (f : A -> B) g : retract g f ->
  forall y, { s & forall x, s = Some x <-> y = f x }.
Proof.
intros Hr y.
destruct (eq_dt_dec y (f (g y))) as [-> | Hneq].
- exists (Some (g y)).
  intro x. split; intro Heq.
  + injection Heq as [= ->]. reflexivity.
  + f_equal. apply (section_injective Hr), Heq.
- exists None.
  intro x. split; intro Heq.
  + discriminate Heq.
  + contradiction Hneq.
    subst y. rewrite Hr. reflexivity.
Qed.

Lemma section_decidable_image A (B : DecType) (f : A -> B) g : retract g f -> decidable_image f.
Proof.
intros Hr y.
destruct (section_coimage_option _ Hr y) as [[x|] Hx]; [ left | right ].
- exists x. apply Hx. reflexivity.
- intros x ->. discriminate (proj2 (Hx x) eq_refl).
Qed.
