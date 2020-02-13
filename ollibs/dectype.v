(* Types with decidable equality formalized as types with Boolean valued equality *)
(*   this is based on records rather than modules (as opposed to stdlib) *)

Require Import Bool PeanoNat.
Require Eqdep_dec.

Set Implicit Arguments.


(** * Inhabitation *)

Inductive inhabited_Type (A:Type) : Type := inhabits_Type : A -> inhabited_Type A.
Arguments inhabits_Type {_} _.

Definition inhabitant_Type {A:Type} (Hinh : inhabited_Type A) :=
  match Hinh with
  | inhabits_Type a => a
  end.

Lemma inhabited_Type_unit : inhabited_Type unit.
Proof (inhabits_Type tt).

Lemma inhabited_Type_bool : inhabited_Type bool.
Proof (inhabits_Type false).

Lemma inhabited_Type_nat : inhabited_Type nat.
Proof (inhabits_Type 0).

Lemma inhabited_Type_option A : inhabited_Type (option A).
Proof (inhabits_Type None).

Lemma inhabited_Type_suml {A B} : inhabited_Type A -> inhabited_Type (sum A B).
Proof (fun Hinh => inhabits_Type (inl (inhabitant_Type Hinh))).

Lemma inhabited_Type_sumr {A B} : inhabited_Type B -> inhabited_Type (sum A B).
Proof (fun Hinh => inhabits_Type (inr (inhabitant_Type Hinh))).

Lemma inhabited_Type_prod {A B} : inhabited_Type A -> inhabited_Type B -> inhabited_Type (prod A B).
Proof (fun HinhA HinhB => inhabits_Type (inhabitant_Type HinhA, inhabitant_Type HinhB)).

Lemma inhabited_Type_list A : inhabited_Type (list A).
Proof (inhabits_Type nil).

Lemma inhabited_Type_fun {A B} (f : A -> B) : inhabited_Type A -> inhabited_Type B.
Proof (fun Hinh => inhabits_Type (f (inhabitant_Type Hinh))).

Lemma inhabited_Type_img {A B} : inhabited_Type B -> inhabited_Type (A -> B).
Proof (fun Hinh => inhabits_Type (fun _ => (inhabitant_Type Hinh))).

Lemma inhabited_Type_id {A} : inhabited_Type (A -> A).
Proof (inhabits_Type id).


(** * Decidable Types *)
(* types with a boolean binary predicate equivalent to equality *)

Record DecType := {
  car :> Type;
  eqb : car -> car -> bool;
  eqb_eq : forall x y, eqb x y = true <-> x = y
}.
Arguments eqb {_}.
Arguments eqb_eq {_}.

Section DecTypes.

  Context { X : DecType }.
  Implicit Type x y : X.

  Lemma eqb_refl : forall x, eqb x x = true.
  Proof. intros x; apply (proj2 (eqb_eq x x) eq_refl). Qed.

  Lemma eqb_neq : forall x y, eqb x y = false <-> x <> y.
  Proof.
  intros x y; case_eq (eqb x y); intros Heq; split; intros; intuition.
  - apply eqb_eq in Heq; subst; intuition.
  - subst; rewrite eqb_refl in Heq; inversion Heq.
  Qed.

  Lemma eq_dt_dec : forall x y, { x = y } + { x <> y }.
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

  Lemma if_eq_dt_dec_refl {A}: forall x (u v : A),
    (if eq_dt_dec x x then u else v) = u.
  Proof. intros x u v; now destruct (eq_dt_dec x x). Qed.

  Lemma if_eq_dt_dec_neq {A}: forall x y, x <> y -> forall (u v : A),
    (if eq_dt_dec x y then u else v) = v.
  Proof. intros x y Hneq u v; now destruct (eq_dt_dec x y). Qed.


  (* Statements from [Module DecidableEqDep] in Eqdep_dec *)
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


(** * Instances and Constructions *)

(* the [Empty_set] instance *)
Definition Empty_set_dectype := {|
  car := Empty_set;
  eqb := fun _ _ => true;
  eqb_eq := fun a b => match a with end
|}.

(* the [unit] instance *)
Definition unit_dectype := {|
  car := unit;
  eqb := fun _ _ => true;
  eqb_eq := fun a b => match a, b with
                       | tt, tt => conj (fun _ => eq_refl) (fun _ => eq_refl)
                       end
|}.

(* the [bool] instance *)
Definition bool_dectype := {|
  car := bool;
  eqb := Bool.eqb;
  eqb_eq := Bool.eqb_true_iff
|}.

(* the [nat] instance *)
Definition nat_dectype := {|
  car := nat;
  eqb := Nat.eqb;
  eqb_eq := Nat.eqb_eq
|}.

(* the [option] construction *)
Scheme Equality for option.

Definition option_dectype (D : DecType) := {|
  car := option D.(car);
  eqb := option_beq D.(@eqb);
  eqb_eq := fun a b => conj
                      (internal_option_dec_bl _ (fun x y => proj1 (D.(@eqb_eq) x y)) a b)
                      (@internal_option_dec_lb _ _ (fun x y => proj2 (D.(@eqb_eq) x y)) a b)
|}.

(* the [sum] construction *)
Scheme Equality for sum.

Definition sum_dectype (D1 D2 : DecType) := {|
  car := sum D1 D2;
  eqb := sum_beq D1.(@eqb) D2.(@eqb);
  eqb_eq := fun a b => conj
                       (internal_sum_dec_bl _ _ (fun x y => proj1 (D1.(@eqb_eq) x y))
                                                (fun x y => proj1 (D2.(@eqb_eq) x y)) a b)
                       (@internal_sum_dec_lb _ _ _ _ (fun x y => proj2 (D1.(@eqb_eq) x y))
                                                     (fun x y => proj2 (D2.(@eqb_eq) x y)) a b)
|}.

(* the [prod] construction *)
Scheme Equality for prod.

Definition prod_dectype (D1 D2 : DecType) := {|
  car := prod D1 D2;
  eqb := prod_beq D1.(@eqb) D2.(@eqb);
  eqb_eq := fun a b => conj
                       (internal_prod_dec_bl _ _ (fun x y => proj1 (D1.(@eqb_eq) x y))
                                                 (fun x y => proj1 (D2.(@eqb_eq) x y)) a b)
                       (@internal_prod_dec_lb _ _ _ _ (fun x y => proj2 (D1.(@eqb_eq) x y))
                                                      (fun x y => proj2 (D2.(@eqb_eq) x y)) a b)
|}.

(* the [list] construction *)
Scheme Equality for list.

Definition list_dectype (D : DecType) := {|
  car := list D;
  eqb := list_beq D.(@eqb);
  eqb_eq := fun a b => conj
                       (internal_list_dec_bl _ (fun x y => proj1 (D.(@eqb_eq) x y)) a b)
                       (@internal_list_dec_lb _ _ (fun x y => proj2 (D.(@eqb_eq) x y)) a b)
|}.

(* the [minus] construction *)
(*   remove an element from a DecType *)
Section Minus.

  Context { D : DecType }.
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
    eqb_eq := minus_eqb_eq
  |}.

End Minus.


(** * Tactics *)

(* a tactic for automatic case analysis on equalities on a [DecType] *)
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
| |- context f [eq_dt_dec ?x ?y] => case_eq (eq_dt_dec x y); intros Heq Heqeq; [ subst x | ]
end; simpl.


(** * Inhabited Decidable Types *)
(* types with a boolean binary predicate equivalent to equality *)

Record InhDecType := {
  inhcar :> DecType;
  inh_dt : inhabited_Type inhcar
}.
Arguments inh_dt {_}.

Definition unit_inhdectype := {|
  inhcar := unit_dectype;
  inh_dt := inhabited_Type_unit
|}.

Definition bool_inhdectype := {|
  inhcar := bool_dectype;
  inh_dt := inhabited_Type_bool
|}.

Definition nat_inhdectype := {|
  inhcar := nat_dectype;
  inh_dt := inhabited_Type_nat
|}.

Definition option_inhdectype (D : DecType) := {|
  inhcar := option_dectype D;
  inh_dt := inhabited_Type_option D
|}.

Definition suml_inhdectype (D1 : InhDecType) (D2 : DecType) := {|
  inhcar := sum_dectype D1 D2;
  inh_dt := inhabited_Type_suml inh_dt
|}.

Definition sumr_inhdectype (D1 : DecType) (D2 : InhDecType) := {|
  inhcar := sum_dectype D1 D2;
  inh_dt := inhabited_Type_sumr inh_dt
|}.

Definition sum_inhdectype (D1 D2 : InhDecType) := suml_inhdectype D1 D2.

Definition prod_inhdectype (D1 D2 : InhDecType) := {|
  inhcar := prod_dectype D1 D2;
  inh_dt := inhabited_Type_prod inh_dt inh_dt
|}.

Definition list_inhdectype (D : DecType) := {|
  inhcar := list_dectype D;
  inh_dt := inhabited_Type_list D
|}.

