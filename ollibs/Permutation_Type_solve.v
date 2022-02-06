(** Automatic tactics for [Permutation_Type] *)

(** * Some tactics for tentative automatic solving of [Permutation_Type] goals
The main tactic is [Permutation_Type_solve] which fails is the goal is not solved. *)

From OLlibs Require Import List_more Permutation_Type_more.


Ltac pre_simpl_hyp_perm_Type H :=
  try apply Permutation_Type_cons_inv in H ;
  try apply Permutation_Type_app_inv in H ;
  try apply Permutation_Type_app_inv in H ;
  try apply Permutation_Type_app_middle_inv in H ;
  try apply Permutation_Type_cons_app_inv in H ;
  try (rewrite app_assoc in H ;
       apply Permutation_Type_cons_app_inv in H) ;
  try (rewrite app_comm_cons in H ;
       apply Permutation_Type_cons_app_inv in H) ;
  try (rewrite app_comm_cons in H ;
       rewrite app_assoc in H ;
       apply Permutation_Type_cons_app_inv in H).
Ltac simpl_hyp_perm_Type H :=
  list_simpl in H ;
  try pre_simpl_hyp_perm_Type H ;
  try (apply Permutation_Type_sym in H ;
       pre_simpl_hyp_perm_Type H ;
       apply Permutation_Type_sym in H).
Ltac simpl_hyp_perm_all_Type :=
  repeat (
    match goal with
    | H:Permutation_Type _ _ |- _ => simpl_hyp_perm_Type H
    end).

Ltac perm_Type_rot :=
  cons2app ;
  rewrite <- ? app_assoc ;
  eapply Permutation_Type_trans ;
    [ apply Permutation_Type_app_rot
    | instantiate ].

(** The parameter [20] below is arbitrary:
 the higher, the longer, the more powerful *)
Ltac Permutation_Type_solve :=
  match goal with
  | |- Permutation_Type _ _ =>
    list_simpl ;
    try simpl_hyp_perm_all_Type ;
    cons2app_all ;
    try simpl_hyp_perm_all_Type ;
    first [
      try apply Permutation_Type_app_tail ;
      try apply Permutation_Type_app_middle ;
      try perm_Type_run ;
      apply Permutation_Type_sym ;
      perm_Type_run ; fail 
    | match goal with
      | H:Permutation_Type _ _ |- Permutation_Type _ _ =>
            try (apply (Permutation_Type_trans H) ; perm_Type_run ; fail) ;
            try (apply Permutation_Type_sym ;
                 apply (Permutation_Type_trans H) ; perm_Type_run ; fail) ;
            try (apply Permutation_Type_sym in H ;
                 apply (Permutation_Type_trans H) ; perm_Type_run ; fail) ;
            try (apply Permutation_Type_sym ; apply Permutation_Type_sym in H ;
                 apply (Permutation_Type_trans H) ; perm_Type_run ; fail) ; fail
    end ]
  end
with perm_Type_run :=
  do 20 (
  cons2app ;
  rewrite <- ? app_assoc ;
  try apply Permutation_Type_app_head ;
  match goal with
  | |- Permutation_Type _ _ => apply Permutation_Type_refl
  | |- Permutation_Type (_ ++ _) _ => apply Permutation_Type_app_comm
  | H:Permutation_Type _ _ |- Permutation_Type _ _ => apply H
  | H:Permutation_Type ?l1 _ |- Permutation_Type (?l1 ++ _) _
       => eapply Permutation_Type_trans ; 
          [ apply Permutation_Type_app_tail ; apply H
          | instantiate ]
  | H:Permutation_Type _ ?l1 |- Permutation_Type (?l1 ++ _) _
       => apply Permutation_Type_sym in H ;
          eapply Permutation_Type_trans ; 
          [ apply Permutation_Type_app_tail ; apply H
          | instantiate ]
  | |- Permutation_Type (_ ++ _ ++ _) _ => perm_Type_rot
  | |- Permutation_Type (_ ++ _ ) _ => eapply Permutation_Type_trans ;
                                  [ apply Permutation_Type_app_comm
                                  | instantiate ]
  | H:Permutation_Type ?l1 _ |- Permutation_Type ?l1 _
       => eapply Permutation_Type_trans ; 
          [ apply H
          | instantiate ]
  | H:Permutation_Type _ ?l1 |- Permutation_Type ?l1 _
       => apply Permutation_Type_sym in H ;
          eapply Permutation_Type_trans ; 
          [ apply H
          | instantiate ]
  | _ => idtac
  end ).
