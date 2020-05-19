(** Add-ons for Permutation library
Usefull properties apparently missing in the Permutation library. *)

Require Export Permutation List.
Require Import List_more funtheory.

Set Implicit Arguments.


Lemma Permutation_app_app_inv A : forall (l1 l2 l3 l4 : list A),
  Permutation (l1 ++ l2) (l3 ++ l4) -> exists l3' l3'' l4' l4'',
    Permutation l1 (l3' ++ l4')  /\ Permutation l2 (l3'' ++ l4'') /\
    Permutation l3 (l3' ++ l3'') /\ Permutation l4 (l4' ++ l4'').
Proof.
induction l1 ; intros.
- exists (@nil A) ; exists l3 ; exists (@nil A) ; exists l4.
  now repeat split.
- assert (Heq := H).
  apply (Permutation_in a) in Heq.
  + apply in_app_or in Heq.
    destruct Heq as [Heq | Heq] ; apply in_split in Heq ;
    destruct Heq as (l' & l'' & Heq) ; subst.
    * rewrite <- ?app_comm_cons in H.
      rewrite <- app_assoc in H.
      rewrite <- app_comm_cons in H.
      apply Permutation_cons_app_inv in H.
      rewrite app_assoc in H.
      apply IHl1 in H.
      destruct H as (l3' & l3'' & l4' & l4'' & H1 & H2 & H3 & H4).
      exists (a::l3') ; exists l3'' ; exists l4' ; exists l4''.
      repeat split; auto.
      -- rewrite <- app_comm_cons.
         now apply Permutation_cons.
      -- apply Permutation_sym.
         rewrite <- app_comm_cons.
         now apply Permutation_cons_app, Permutation_sym.
    * rewrite <- ?app_comm_cons, app_assoc in H.
      apply Permutation_cons_app_inv in H.
      rewrite <- app_assoc in H.
      apply IHl1 in H.
      destruct H as (l3' & l3'' & l4' & l4'' & H1 & H2 & H3 & H4).
      exists l3', l3'', (a :: l4'), l4''.
      repeat split; auto.
      -- now apply Permutation_cons_app.
      -- apply Permutation_sym.
         rewrite <- app_comm_cons.
         now apply Permutation_cons_app, Permutation_sym.
  + now constructor.
Qed.

Lemma Permutation_map_inv_inj A B : forall f : A -> B, injective f ->
  forall l1 l2, Permutation (map f l1) (map f l2) -> Permutation l1 l2.
Proof.
intros f Hi l1; induction l1; intros l2 HP.
- apply Permutation_nil in HP.
  now destruct l2; inversion HP.
- symmetry in HP.
  destruct (Permutation_vs_cons_inv HP) as (l3 & l4 & Heq).
  decomp_map Heq; subst.
  rewrite map_app in HP; simpl in HP.
  rewrite Heq3 in HP; symmetry in HP.
  apply Permutation_cons_app_inv in HP.
  specialize IHl1 with (l0 ++ l6).
  rewrite map_app in IHl1.
  apply IHl1 in HP.
  apply Hi in Heq3; subst.
  now apply Permutation_cons_app.
Qed.

Lemma Permutation_map_inv_inj_local A B : forall (f : A -> B) l1 l2,
  (forall x y, In x l1 -> In y l2 -> f x = f y -> x = y) ->
    Permutation (map f l1) (map f l2) -> Permutation l1 l2.
Proof.
induction l1 ; intros l2 Hi HP.
- apply Permutation_nil in HP.
  now destruct l2; inversion HP.
- assert (Heq := HP).
  symmetry in Heq.
  apply Permutation_vs_cons_inv in Heq.
  destruct Heq as (l3 & l4 & Heq).
  decomp_map Heq; subst.
  rewrite map_app in HP; simpl in HP.
  rewrite Heq3 in HP.
  apply Permutation_cons_app_inv in HP.
  specialize IHl1 with (l0 ++ l6).
  rewrite map_app in IHl1.
  apply IHl1 in HP.
  + symmetry in Heq3; apply Hi in Heq3; subst.
    * now apply Permutation_cons_app.
    * apply in_eq.
    * apply in_elt.
  + intros x' y' Hx' Hy' Hf.
    apply Hi; auto.
    * now apply in_cons.
    * apply in_app_or in Hy'.
      destruct Hy' as [ Hy' | Hy' ]; apply in_or_app; [left|right]; auto.
      now apply in_cons.
Qed.
