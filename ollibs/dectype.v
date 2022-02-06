(** Types with decidable equality formalized as types with Boolean valued equality
this is based on records rather than modules (as opposed to stdlib) *)

From Coq Require Import Bool PeanoNat Equalities.
From Coq Require Eqdep_dec.

Set Implicit Arguments.


(** * Inhabitation *)

Inductive inhabited_inf A : Type := inhabits_inf : A -> inhabited_inf A.
Arguments inhabits_inf [_] _.

Definition inhabitant_inf A (Hinh : inhabited_inf A) :=
  match Hinh with inhabits_inf a => a end.

Lemma inhabited_inf_unit : inhabited_inf unit.
Proof (inhabits_inf tt).

Lemma inhabited_inf_bool : inhabited_inf bool.
Proof (inhabits_inf false).

Lemma inhabited_inf_nat : inhabited_inf nat.
Proof (inhabits_inf 0).

Lemma inhabited_inf_option A : inhabited_inf (option A).
Proof (inhabits_inf None).

Lemma inhabited_inf_suml A B : inhabited_inf A -> inhabited_inf (sum A B).
Proof (fun Hinh => inhabits_inf (inl (inhabitant_inf Hinh))).
Arguments inhabited_inf_suml [_] {_} _.

Lemma inhabited_inf_sumr A B : inhabited_inf B -> inhabited_inf (sum A B).
Proof (fun Hinh => inhabits_inf (inr (inhabitant_inf Hinh))).
Arguments inhabited_inf_sumr {_} [_] _.

Lemma inhabited_inf_prod A B : inhabited_inf A -> inhabited_inf B -> inhabited_inf (prod A B).
Proof (fun HinhA HinhB => inhabits_inf (inhabitant_inf HinhA, inhabitant_inf HinhB)).

Lemma inhabited_inf_list A : inhabited_inf (list A).
Proof (inhabits_inf nil).

Lemma inhabited_inf_fun A B (f : A -> B) : inhabited_inf A -> inhabited_inf B.
Proof (fun Hinh => inhabits_inf (f (inhabitant_inf Hinh))).

Lemma inhabited_inf_img A B : inhabited_inf B -> inhabited_inf (A -> B).
Proof (fun Hinh => inhabits_inf (fun _ => (inhabitant_inf Hinh))).

Lemma inhabited_inf_id A : inhabited_inf (A -> A).
Proof (inhabits_inf id).


(** * Decidable Types *)
(** types with a boolean binary predicate equivalent to equality *)

Record DecType := {
  car :> Type;
  eqb : car -> car -> bool;
  eqb_eq : forall x y, eqb x y = true <-> x = y
}.
Arguments eqb [_].
Arguments eqb_eq [_].

Section DecTypes.

  Variable X : DecType.
  Implicit Type x y : X.

  Lemma eqb_refl : forall x, eqb x x = true.
  Proof. intros x; apply (proj2 (eqb_eq x x) eq_refl). Qed.

  Lemma eqb_neq : forall x y, eqb x y = false <-> x <> y.
  Proof.
  intros x y; case_eq (eqb x y); intros Heq; split; intros; intuition.
  - apply eqb_eq in Heq; subst; intuition.
  - subst; rewrite eqb_refl in Heq; inversion Heq.
  Qed.

  Lemma eq_dt_dec : forall x y, {x = y} + {x <> y}.
  Proof.
  intros x y; case_eq (eqb x y); intros Heq; [ left | right ].
  - now apply eqb_eq in Heq.
  - now apply eqb_neq in Heq.
  Qed.

  Lemma eq_dt_reflect : forall x y, reflect (x = y) (eqb x y).
  Proof.
  intros x y; case_eq (eqb x y); intros Heq.
  - now apply ReflectT, eqb_eq.
  - now apply ReflectF, eqb_neq.
  Qed.

  Lemma if_eq_dt_dec_refl A : forall x (u v : A),
    (if eq_dt_dec x x then u else v) = u.
  Proof. intros x u v; now destruct (eq_dt_dec x x). Qed.

  Lemma if_eq_dt_dec_neq A : forall x y, x <> y -> forall (u v : A),
    (if eq_dt_dec x y then u else v) = v.
  Proof. intros x y Hneq u v; now destruct (eq_dt_dec x y). Qed.


  (** Statements from [Module DecidableEqDep] in [Eqdep_dec] *)
  Lemma eq_rect_eq : forall x (P : X -> Type) p h, p = eq_rect x P p x h.
  Proof (Eqdep_dec.eq_rect_eq_dec eq_dt_dec).

  Theorem eq_dep_eq : forall (P : X -> Type) x p q, EqdepFacts.eq_dep X P x p x q -> p = q.
  Proof (EqdepFacts.eq_rect_eq__eq_dep_eq X eq_rect_eq).

  Lemma UIP : forall x y (p q : x = y), p = q.
  Proof (Eqdep_dec.UIP_dec eq_dt_dec).

  Lemma UIP_refl : forall x p, p = eq_refl x.
  Proof (EqdepFacts.UIP__UIP_refl _ UIP).

  Lemma Streicher_K : forall x (P : x = x -> Prop), P (eq_refl x) -> forall p, P p.
  Proof (Eqdep_dec.K_dec_type eq_dt_dec).

  Lemma inj_pairT2 : forall (P : X -> Type) x p q, existT P x p = existT P x q -> p = q.
  Proof (EqdepFacts.eq_dep_eq__inj_pairT2 X eq_dep_eq).

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
  eqb_eq := fun a b => match a with end
|}.

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

  Lemma minus_eqb_eq : forall (a b : { z | eqb d z = false }),
    eqb (proj1_sig a) (proj1_sig b) = true <-> a = b.
  Proof.
  intros [a Ha] [b Hb]; simpl; split; intros Heq.
  - apply eqb_eq in Heq; subst.
    f_equal; apply (@UIP bool_dectype _ _ Ha Hb).
  - inversion_clear Heq; apply eqb_refl.
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
let Heqeq := fresh "Heqeq" in
match goal with
| |- context f [?x =? ?y] => case_eq (x =? y); intros Heq
| |- context f [?x <? ?y] => case_eq (x <? y); intros Heq
| |- context f [?x ?= ?y] => case_eq (x ?= y); intros Heq
| |- context f [eqb ?x ?x] => rewrite (eqb_refl x)
| |- context f [eqb ?x ?y] => case eq_dt_reflect; intros Heq; [ try subst x | ]
| |- context f [eq_dt_dec ?x ?x] => rewrite (if_eq_dt_dec_refl x)
| H : ?x <> ?y |- context f [eq_dt_dec ?x ?y] => rewrite (if_eq_dt_dec_neq x y H)
| H : ?y <> ?x |- context f [eq_dt_dec ?x ?y] => rewrite (if_eq_dt_dec_neq x y (not_eq_sym H))
| |- context f [eq_dt_dec ?x ?y] => case_eq (eq_dt_dec x y); intros Heq Heqeq; [ try subst x | ]
end; simpl.


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


(** Equivalence between [DecType] and [UsualOrderedTypeFull]. *)

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
