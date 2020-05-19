(** Additional results about [CPermutation] *)

From Coq Require Export CPermutation.
From OLlibs Require Import List_more funtheory.

Set Implicit Arguments.

Lemma CPermutation_app_app_inv A : forall (l1 : list A) l2 l3 l4,
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
intros l1 l2 l3 l4 HC; inversion HC as [lx ly Hx Hy].
dichot_app_exec Hx; dichot_app_exec Hy; subst.
- right; left.
  exists (l ++ l0), (l0 ++ l).
  repeat split; rewrite <- ? app_assoc; apply CPermutation_app_rot.
- dichot_app_exec Hy0; subst.
  + now left; exists l, l0, lx, l5; repeat split.
  + right; right; right; left; exists (l1 ++ lx), (lx ++ l1).
    repeat split; rewrite <- ? app_assoc; apply CPermutation_app_rot.
- dichot_app_exec Hy1; subst.
  + right; right; left; exists (ly ++ l2), (l2 ++ ly).
    repeat split; rewrite <- ? app_assoc; apply CPermutation_app_rot.
  + now left; exists l, ly, l3, l0; repeat split.
- right; right; right; right; exists (l5 ++ l0), (l0 ++ l5).
  repeat split; rewrite <- ? app_assoc; apply CPermutation_app_rot.
Qed.

Lemma CPermutation_map_inv_inj A B : forall f : A -> B, injective f ->
  forall l1 l2, CPermutation (map f l1) (map f l2) -> CPermutation l1 l2.
Proof.
intros f Hi l1 l2 HP; inversion HP as [l3 l4 Heq1 Heq2].
symmetry in Heq1; symmetry in Heq2.
decomp_map Heq1; decomp_map Heq2; subst.
apply map_injective in Heq5; auto.
apply map_injective in Heq6; auto.
subst; constructor.
Qed.

Lemma CPermutation_map_inv_inj_local A B : forall (f : A -> B) l1 l2,
  (forall x y, In x l1 -> In y l2 -> f x = f y -> x = y) ->
    CPermutation (map f l1) (map f l2) -> CPermutation l1 l2.
Proof.
intros f l1 l2 Hi HP; inversion HP as [l3 l4 Heq1 Heq2].
symmetry in Heq1; symmetry in Heq2.
decomp_map Heq1; decomp_map Heq2; subst.
symmetry in Heq5; symmetry in Heq6.
apply map_injective_in in Heq5.
2:{ intros x y Hin1 Hin2 Heq; apply Hi; auto; apply in_or_app; auto. }
apply map_injective_in in Heq6.
2:{ intros x y Hin1 Hin2 Heq; apply Hi; auto; apply in_or_app; auto. }
subst; constructor.
Qed.
