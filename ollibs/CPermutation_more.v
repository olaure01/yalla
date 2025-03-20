(** Additional results about [CPermutation] *)

Set Implicit Arguments.

From Stdlib Require Export CPermutation.
From Yalla.OLlibs Require Import List_more funtheory.

Lemma CPermutation_app_app_inv A (l1 l2 l3 l4 : list A) :
  CPermutation (l1 ++ l2) (l3 ++ l4) ->
     (exists l3' l3'' l4' l4'',
        CPermutation l1 (l3' ++ l4')  /\ CPermutation l2 (l3'' ++ l4'')
     /\
        CPermutation l3 (l3' ++ l3'') /\ CPermutation l4 (l4' ++ l4''))
  \/ (exists l l',
        CPermutation l1 (l4 ++ l) /\ CPermutation l3 (l2 ++ l')
          /\ CPermutation l l')
  \/ (exists l l',
        CPermutation l2 (l4 ++ l) /\ CPermutation l3 (l1 ++ l')
          /\ CPermutation l l')
  \/ (exists l l',
        CPermutation l1 (l3 ++ l) /\ CPermutation l4 (l2 ++ l')
          /\ CPermutation l l')
  \/ (exists l l',
        CPermutation l2 (l3 ++ l) /\ CPermutation l4 (l1 ++ l')
          /\ CPermutation l l').
Proof.
intro HC. inversion HC as [lx ly Hx Hy].
dichot_app_exec Hx; dichot_app_exec Hy; subst.
- right. left. exists (l ++ l0), (l0 ++ l).
  repeat split; rewrite <- ? app_assoc; apply CPermutation_app_rot.
- dichot_app_exec Hy0; subst.
  + now left; exists l, l1, lx, l0; repeat split.
  + right. right. right. left. exists (l1 ++ lx), (lx ++ l1).
    repeat split; rewrite <- ? app_assoc; apply CPermutation_app_rot.
- dichot_app_exec Hy1; subst.
  + right. right. left. exists (ly ++ l2), (l2 ++ ly).
    repeat split; rewrite <- ? app_assoc; apply CPermutation_app_rot.
  + left. exists l0, ly, l2, l. repeat split; reflexivity.
- right. right. right. right. exists (l0 ++ l), (l ++ l0).
  repeat split; rewrite <- ? app_assoc; apply CPermutation_app_rot.
Qed.

Lemma CPermutation_vs_elt_subst A (a : A) l l1 l2 :
  CPermutation l (l1 ++ a :: l2) -> exists l3 l4,
    (forall l0, CPermutation (l1 ++ l0 ++ l2) (l3 ++ l0 ++ l4)) /\ l = l3 ++ a :: l4.
Proof.
intro HP. destruct (CPermutation_vs_elt_inv _ _ _ HP) as [l' [l'' [Heq ->]]].
exists l', l''. split; [ | reflexivity ].
intro l0.
etransitivity; [ apply CPermutation_app_comm | ].
list_simpl. rewrite Heq, app_assoc. constructor.
Qed.

Lemma CPermutation_map_inv_inj A B (f : A -> B) : injective f ->
  forall l1 l2, CPermutation (map f l1) (map f l2) -> CPermutation l1 l2.
Proof.
intros Hi l1 l2 HP. inversion HP as [l3 l4 Heq1 Heq2].
symmetry in Heq1. symmetry in Heq2. decomp_map Heq1. decomp_map Heq2 eqn:Heq.
destruct Heq as [->%(map_injective Hi) ->%(map_injective Hi)].
subst. constructor.
Qed.

Lemma CPermutation_map_inv_inj_local A B (f : A -> B) l1 l2 :
  (forall x y, In x l1 -> In y l2 -> f x = f y -> x = y) ->
    CPermutation (map f l1) (map f l2) -> CPermutation l1 l2.
Proof.
intros Hi HP. inversion HP as [l3 l4 Heq1 Heq2].
symmetry in Heq1. symmetry in Heq2. decomp_map Heq1. decomp_map Heq2 eqn:Heq. subst.
destruct Heq as [->%map_injective_in ->%map_injective_in]; [ constructor | | ].
- intros x y Hin1 Hin2 Heq. symmetry. apply Hi; [ apply in_or_app .. | ]; auto.
- intros x y Hin1 Hin2 Heq. symmetry. apply Hi; [ apply in_or_app .. | ]; auto.
Qed.
