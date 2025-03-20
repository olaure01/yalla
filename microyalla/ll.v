(* microyalla library for linear logic *)
(*   Olivier Laurent *)


From Stdlib Require Export List.
Export ListNotations.

(* From ollibs/Permutation_Type.v *)

Inductive Permutation_Type {A} : list A -> list A -> Type :=
| Permutation_Type_nil_nil : Permutation_Type nil nil
| Permutation_Type_skip x l l' : Permutation_Type l l' -> Permutation_Type (x::l) (x::l')
| Permutation_Type_swap x y l : Permutation_Type (y::x::l) (x::y::l)
| Permutation_Type_trans l l' l'' :
    Permutation_Type l l' -> Permutation_Type l' l'' -> Permutation_Type l l''.


(* Adapted from yalla/formulas.v *)

(** A set of atoms for building formulas *)
Definition Atom := nat.

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


(* Adapted from yalla/ll_def.v *)

(** Rules *)
Inductive ll : list formula -> Type :=
| ax_r : forall X, ll (covar X :: var X :: nil)
| ex_r : forall l1 l2, ll l1 -> Permutation_Type l1 l2 -> ll l2
| one_r : ll (one :: nil)
| bot_r : forall l, ll l -> ll (bot :: l)
| tens_r : forall A B l1 l2, ll (A :: l1) -> ll (B :: l2) -> ll (tens A B :: l1 ++ l2)
| parr_r : forall A B l, ll (A :: B :: l) -> ll (parr A B :: l)
| top_r : forall l, ll (top :: l)
| plus_r1 : forall A B l, ll (A :: l) -> ll (aplus A B :: l)
| plus_r2 : forall A B l, ll (A :: l) -> ll (aplus B A :: l)
| with_r : forall A B l, ll (A :: l) -> ll (B :: l) -> ll (awith A B :: l)
| oc_r : forall A l, ll (A :: map wn l) -> ll (oc A :: map wn l)
| de_r : forall A l, ll (A :: l) -> ll (wn A :: l)
| wk_r : forall A l, ll l -> ll (wn A :: l)
| co_r : forall A l, ll (wn A :: wn A :: l) -> ll (wn A :: l).



