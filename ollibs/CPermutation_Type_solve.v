(* CPermutation_solve library *)

(* output in Type *)

(** * Some tactics for tentative automatic solving of [CPermutation] goals
The main tactic is [cperm_solve] which fails is the goal is not solved. *)

Require Import List_more.
Require Import CyclicPerm_Type.


Ltac cperm_Type_rot :=
  cons2app ;
  rewrite <- ? app_assoc ;
  eapply cperm_Type_trans ;
    [ apply cperm_Type_app_rot
    | instantiate ].

(** The parameter [20] below is an arbitrary
 the higher, the longer, the more powerful *)
Ltac cperm_Type_solve :=
  match goal with
  | |- CPermutation_Type _ _ =>
    list_simpl ;
    cons2app_all ;
    first [
      try cperm_Type_run ;
      apply cperm_Type_sym ;
      cperm_Type_run ; fail 
    | match goal with
      | H:CPermutation_Type _ _ |- CPermutation_Type _ _ =>
           list_simpl in H ;
           try (apply (cperm_Type_trans H) ; cperm_Type_run ; fail) ;
           try (apply cperm_Type_sym ;
                apply (cperm_Type_trans H) ; cperm_Type_run ; fail) ;
           try (apply cperm_Type_sym in H ;
                apply (cperm_Type_trans H) ; cperm_Type_run ; fail) ;
           try (apply cperm_Type_sym ; apply cperm_Type_sym in H ;
                apply (cperm_Type_trans H) ; cperm_Type_run ; fail) ; fail
      end ]
  end
with cperm_Type_run :=
  do 20 (
  cons2app ;
  rewrite <- ? app_assoc ;
  match goal with
  | |- CPermutation_Type _ _ => apply cperm_Type_refl
  | |- CPermutation_Type (_ ++ _) _ => apply cperm_Type
  | H:CPermutation_Type _ _ |- CPermutation_Type _ _ => list_simpl in H ; apply H
  | |- CPermutation_Type (_ ++ _ ++ _) _ => cperm_Type_rot
  | |- CPermutation_Type (_ ++ _ ) _ => eapply cperm_Type_trans ;
                                  [ apply cperm_Type
                                  | instantiate ]
  | H:CPermutation_Type ?l1 _ |- CPermutation_Type ?l1 _
       => list_simpl in H ;
          eapply cperm_Type_trans ; 
          [ apply H
          | instantiate ]
  | H:CPermutation_Type _ ?l1 |- CPermutation_Type ?l1 _
       => list_simpl in H ;
          apply cperm_Type_sym in H ;
          eapply cperm_Type_trans ; 
          [ apply H
          | instantiate ]
  | _ => idtac
  end ).


