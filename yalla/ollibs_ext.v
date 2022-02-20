(* TODO remove once introduced in OLlibs *)
From OLlibs Require Import funtheory.

Definition option_test [A] := @option_eval_default A Type unit.
(* end TODO *)
