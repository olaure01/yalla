(* basic_tactics library for yalla *)
(* v 1.0   Olivier Laurent *)

(** * A few basic tactics used in [yalla] *)

Require Import Omega.
Require Import Psatz.

Require Import Permutation_Type_solve.
Require Import genperm_Type.

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
  try omega ;          (* omega quicker *)
  try lia.             (* but less powerful than lia *)

Ltac myeasy := myeasy_pattern assumption.
Ltac myeeasy := myeasy_pattern eassumption.

(** An [easy] tactic with automated permutation solving **)

Ltac myeasy_perm_Type :=
  myeeasy ;
  try PCperm_Type_solve ;
  try (simpl_hyp_perm_all_Type ; PCperm_Type_solve).


