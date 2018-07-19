(* ill library for yalla *)

(** * Intuitionistic Linear Logic *)
(* Cut elimination, see ill_prop.v for other properties *)

Require Import List.

Require Import genperm_Type.

Require Import basic_tactics.
Require Export ill_def.

(* TODO cut_ir_ill statement *)

Axiom cut_admissible_ill : forall {P},
    (forall a, Forall iqatomic (fst (projT2 (ipgax P) a))) ->
    (forall a, iatomic (snd (projT2 (ipgax P) a))) ->
    (forall a l, PEperm_Type (ipperm P) (fst (projT2 (ipgax P) a)) l ->
                 exists b, l = fst (projT2 (ipgax P) b)) ->
    (forall a b l0 l1 l2 x z, fst (projT2 (ipgax P) a) = ivar x :: l0 ->
                              snd (projT2 (ipgax P) a) = ivar z ->
                              fst (projT2 (ipgax P) b) = l1 ++ ilmap (ivar x) (ivar z) :: l2 -> 
                    exists c, l1 ++ l0 ++ l2 = fst (projT2 (ipgax P) c)
                           /\ snd (projT2 (ipgax P) b) = snd (projT2 (ipgax P) c)) ->
  forall l C, ill P l C -> ill (cutrm_ipfrag P) l C.

Inductive ipgax_sat ax P (f : ax -> projT1 (ipgax P)) : projT1 (ipgax P) -> Prop :=
| isat_ax : forall x, ipgax_sat ax P f (f x)
| isat_ex : forall a b, ipgax_sat ax P f a ->
               PEperm_Type (ipperm P) (fst (projT2 (ipgax P) a))
                                      (fst (projT2 (ipgax P) b)) -> ipgax_sat ax P f b
| isat_cut : forall a b c l0 l1 l2 x z, ipgax_sat ax P f a -> ipgax_sat ax P f b ->
                              fst (projT2 (ipgax P) a) = ivar x :: l0 ->
                              snd (projT2 (ipgax P) a) = ivar z ->
                              fst (projT2 (ipgax P) b) = l1 ++ ilmap (ivar x) (ivar z) :: l2 ->
                              l1 ++ l0 ++ l2 = fst (projT2 (ipgax P) c) ->
                              snd (projT2 (ipgax P) b) = snd (projT2 (ipgax P) c) -> ipgax_sat ax P f c.

Lemma cut_admissible_ipgax_sat : forall {P},
    (forall a, Forall iqatomic (fst (projT2 (ipgax P) a))) ->
    (forall a, iatomic (snd (projT2 (ipgax P) a))) ->
    (forall a l, PEperm_Type (ipperm P) (fst (projT2 (ipgax P) a)) l ->
                 exists b, l = fst (projT2 (ipgax P) b)) ->
    (forall a b l0 l1 l2 x z, fst (projT2 (ipgax P) a) = ivar x :: l0 ->
                              snd (projT2 (ipgax P) a) = ivar z ->
                              fst (projT2 (ipgax P) b) = l1 ++ ilmap (ivar x) (ivar z) :: l2 -> 
                    exists c, l1 ++ l0 ++ l2 = fst (projT2 (ipgax P) c)
                           /\ snd (projT2 (ipgax P) b) = snd (projT2 (ipgax P) c)) ->
  forall (Ax : {T : Type & T -> list iformula * iformula}) (f : projT1 Ax ->
    projT1 (ipgax P)), (forall x, projT2 Ax x = projT2 (ipgax P) (f x)) ->
    forall l C, ill (axupd_ipfrag P Ax) l C ->
    ill (cutrm_ipfrag (axupd_ipfrag P (existT (fun x => x -> list iformula * iformula)
                                              ({ a | ipgax_sat (projT1 Ax) P f a})
                                              (fun a => projT2 (ipgax P) (proj1_sig a))  ))) l C.
Proof with myeeasy.
intros P Hatl Hatr Hex Hcut Ax f Hax l C pi.
apply cut_admissible_ill ; simpl ; intuition.
- destruct a as [a Ha].
  destruct (Hex _ _ X) as [b Hb] ; subst.
  eapply isat_ex in X...
  exists (exist _ b X)...
- destruct a as [a Ha].
  destruct b as [b Hb].
  destruct (Hcut a b _ _ _ _ _ H H0 H1) as [c [Hc1 Hc2]].
  exists (exist _ c (isat_cut _ _ _ a b c _ _ _ _ _ Ha Hb H H0 H1 Hc1 Hc2)).
  simpl ; split...
- eapply stronger_ipfrag ; [ | exact pi ].
  nsplit 3...
  simpl ; intros a.
  exists (exist _ (f a) (isat_ax _ _ _ a)).
  rewrite (Hax a)...
Qed.

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

