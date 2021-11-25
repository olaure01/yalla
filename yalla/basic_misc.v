(* basic_misc library for yalla *)


(** * A few basic ingredients used in [yalla] *)

From Coq Require Import Lia.

Set Implicit Arguments.

(** ** Definitions *)
(* TODO remove once introduced in OLlibs *)
Definition option_eval_default A B default (f : A -> B) o :=
match o with
| Some a => f a
| None => default
end.

Definition option_test A := @option_eval_default A Type unit.

Definition Empty_fun {A} : Empty_set -> A := fun o => match o with end.
(* end TODO *)

(** ** Tactics *)
(** Generalized version of [split] for [n] components *)

Ltac nsplit n :=
match n with
| 1 => idtac
| S ?m => split; [ | nsplit m ]
end.

(** Personalised versions of [easy] *) 

Ltac myeasy_pattern assump := try assump; try reflexivity; try lia.

Ltac myeasy := myeasy_pattern assumption.
Ltac myeeasy := myeasy_pattern eassumption.
