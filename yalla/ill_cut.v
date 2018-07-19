(* ill library for yalla *)

(** * Intuitionistic Linear Logic *)
(* Cut elimination, see ill_prop.v for other properties *)

Require Export ill_def.

(* TODO
Axiom cut_ir_axfree : forall P, (forall l C, ~ ipgax P l C) -> forall A l0 l1 l2 C s1 s2,
  ill P l0 A s1 -> ill P (l1 ++ A :: l2) C s2 -> exists s,
    ill P (l1 ++ l0 ++ l2) C s.

Lemma cut_admissible_ill_axfree : forall P, (forall l C, ~ ipgax P l C) ->
  forall l C s, ill P l C s -> exists s', ill (cutrm_ipfrag P) l C s'.
Proof with myeeasy.
intros P Hgax l C s pi.
induction pi ;
  try (eexists ; constructor ; myeeasy ; fail) ;
  try (destruct IHpi as [s' IHpi] ; eexists ; constructor ; myeeasy ; fail) ;
  try (destruct IHpi1 as [s'1 IHpi1] ;
       destruct IHpi2 as [s'2 IHpi2] ; eexists ; constructor ; myeeasy ; fail).
- destruct IHpi as [s' IHpi].
  eexists.
  apply (ex_ir _ l1)...
- destruct IHpi1 as [s'1 IHpi1].
  destruct IHpi2 as [s'2 IHpi2].
  eapply cut_ir_axfree...
Qed.
*)

