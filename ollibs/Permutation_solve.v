(** Automatic tactics for [Permutation] *)

(** * Some tactics for tentative automatic solving of [Permutation] goals
The main tactic is [Permutation_solve] which fails is the goal is not solved. *)

From Coq Require Import Permutation.
From OLlibs Require Import List_more.


Ltac pre_simpl_hyp_perm H :=
  try apply Permutation_cons_inv in H ;
  try apply Permutation_app_inv in H ;
  try apply Permutation_app_inv in H ;
  try apply Permutation_app_inv_m in H ;
  try apply Permutation_cons_app_inv in H ;
  try (rewrite app_assoc in H ;
       apply Permutation_cons_app_inv in H) ;
  try (rewrite app_comm_cons in H ;
       apply Permutation_cons_app_inv in H) ;
  try (rewrite app_comm_cons in H ;
       rewrite app_assoc in H ;
       apply Permutation_cons_app_inv in H).
Ltac simpl_hyp_perm H :=
  list_simpl in H ;
  try pre_simpl_hyp_perm H ;
  try (apply Permutation_sym in H ;
       pre_simpl_hyp_perm H ;
       apply Permutation_sym in H).
Ltac simpl_hyp_perm_all :=
  repeat (
    match goal with
    | H:Permutation _ _ |- _ => simpl_hyp_perm H
    end).

Ltac perm_rot :=
  cons2app ;
  rewrite <- ? app_assoc ;
  eapply Permutation_trans ;
    [ apply Permutation_app_rot
    | instantiate ].

(** The parameter [20] below is arbitrary:
 the higher, the longer, the more powerful *)
Ltac Permutation_solve :=
  match goal with
  | |- Permutation _ _ =>
    list_simpl ;
    try simpl_hyp_perm_all ;
    cons2app_all ;
    try simpl_hyp_perm_all ;
    first [
      try apply Permutation_app_tail ;
      try apply Permutation_app_middle ;
      try perm_run ;
      apply Permutation_sym ;
      perm_run ; fail 
    | match goal with
      | H:Permutation _ _ |- Permutation _ _ =>
            try (apply (Permutation_trans H) ; perm_run ; fail) ;
            try (apply Permutation_sym ;
                 apply (Permutation_trans H) ; perm_run ; fail) ;
            try (apply Permutation_sym in H ;
                 apply (Permutation_trans H) ; perm_run ; fail) ;
            try (apply Permutation_sym ; apply Permutation_sym in H ;
                 apply (Permutation_trans H) ; perm_run ; fail) ; fail
    end ]
  end
with perm_run :=
  do 20 (
  cons2app ;
  rewrite <- ? app_assoc ;
  try apply Permutation_app_head ;
  match goal with
  | |- Permutation _ _ => apply Permutation_refl
  | |- Permutation (_ ++ _) _ => apply Permutation_app_comm
  | H:Permutation _ _ |- Permutation _ _ => apply H
  | H:Permutation ?l1 _ |- Permutation (?l1 ++ _) _
       => eapply Permutation_trans ; 
          [ apply Permutation_app_tail ; apply H
          | instantiate ]
  | H:Permutation _ ?l1 |- Permutation (?l1 ++ _) _
       => apply Permutation_sym in H ;
          eapply Permutation_trans ; 
          [ apply Permutation_app_tail ; apply H
          | instantiate ]
  | |- Permutation (_ ++ _ ++ _) _ => perm_rot
  | |- Permutation (_ ++ _ ) _ => eapply Permutation_trans ;
                                  [ apply Permutation_app_comm
                                  | instantiate ]
  | H:Permutation ?l1 _ |- Permutation ?l1 _
       => eapply Permutation_trans ; 
          [ apply H
          | instantiate ]
  | H:Permutation _ ?l1 |- Permutation ?l1 _
       => apply Permutation_sym in H ;
          eapply Permutation_trans ; 
          [ apply H
          | instantiate ]
  | _ => idtac
  end ).
