(* basic_misc library for yalla *)


(** * A few basic ingredients used in [yalla] *)

Require Import Lia.

Require Import Permutation_Type_solve.
Require Import genperm_Type.


(** ** Definitions *)
Definition option_Prop {A:Type} (P:A->Prop) o :=
match o with
| Some a => P a
| None => True
end.

Definition option_Type {A:Type} (P:A->Type) o :=
match o with
| Some a => P a
| None => True
end.

Definition Empty_fun {A} : Empty_set -> A := fun o => match o with end.


(** ** Tactics *)
(** Generalized version of [split] for [n] components *)

Ltac nsplit n := 
  match n with
  | 1 => idtac
  | S ?m => split ; [ | nsplit m ]
  end.

(** Personalised versions of [easy] *) 

Ltac myeasy_pattern assump :=
  try assump ;
  try reflexivity ;
  try lia.

Ltac myeasy := myeasy_pattern assumption.
Ltac myeeasy := myeasy_pattern eassumption.

(** An [easy] tactic with automated permutation solving **)

Ltac myeasy_perm_Type :=
  myeeasy ;
  try PCperm_Type_solve ;
  try (simpl_hyp_perm_all_Type ; PCperm_Type_solve).

