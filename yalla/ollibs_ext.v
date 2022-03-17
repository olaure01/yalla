(* TODO remove once introduced in OLlibs *)
From OLlibs Require Import funtheory.

Set Implicit Arguments.

Definition option_test A := @option_eval_default A Prop True.
Definition option_testT A := @option_eval_default A Type unit.
(* end TODO *)
