(** Add-ons for Permutation library
Usefull properties apparently missing in the Permutation library. *)

From Coq Require Export Permutation List.
From OLlibs Require Import List_more funtheory.

Set Implicit Arguments.


Lemma Permutation_app_app_inv A (l1 l2 l3 l4 : list A) :
  Permutation (l1 ++ l2) (l3 ++ l4) -> exists l3' l3'' l4' l4'',
    Permutation l1 (l3' ++ l4')  /\ Permutation l2 (l3'' ++ l4'') /\
    Permutation l3 (l3' ++ l3'') /\ Permutation l4 (l4' ++ l4'').
Proof.
revert l2 l3 l4; induction l1 as [|a l1 IHl1]; intros l2 l3 l4 HP.
- exists (@nil A), l3, (@nil A), l4.
  now repeat split.
- assert (Heq := HP).
  apply (Permutation_in a) in Heq.
  + apply in_app_or in Heq.
    destruct Heq as [Heq | Heq]; apply in_split in Heq;
    destruct Heq as (l' & l'' & Heq); subst.
    * rewrite <- ?app_comm_cons in HP.
      rewrite <- app_assoc, <- app_comm_cons in HP.
      apply Permutation_cons_app_inv in HP.
      rewrite app_assoc in HP.
      apply IHl1 in HP.
      destruct HP as (l3' & l3'' & l4' & l4'' & H1 & H2 & H3 & H4).
      exists (a::l3'), l3'', l4', l4''.
      repeat split; auto.
      -- rewrite <- app_comm_cons.
         now apply Permutation_cons.
      -- apply Permutation_sym.
         rewrite <- app_comm_cons.
         now apply Permutation_cons_app, Permutation_sym.
    * rewrite <- ?app_comm_cons, app_assoc in HP.
      apply Permutation_cons_app_inv in HP.
      rewrite <- app_assoc in HP.
      apply IHl1 in HP.
      destruct HP as (l3' & l3'' & l4' & l4'' & H1 & H2 & H3 & H4).
      exists l3', l3'', (a :: l4'), l4''.
      repeat split; auto.
      -- now apply Permutation_cons_app.
      -- apply Permutation_sym.
         rewrite <- app_comm_cons.
         now apply Permutation_cons_app, Permutation_sym.
  + now constructor.
Qed.

Lemma Permutation_vs_elt_subst A (a : A) l l1 l2 :
  Permutation l (l1 ++ a :: l2) -> exists l3 l4,
    (forall l0, Permutation (l1 ++ l0 ++ l2) (l3 ++ l0 ++ l4)) /\ l = l3 ++ a :: l4.
Proof.
intros HP.
destruct (Permutation_vs_elt_inv _ _ _ HP) as [l' [l'' ->]].
exists l', l''; split; [ | reflexivity ].
intros l0.
apply Permutation_app_inv, (Permutation_app_middle l0) in HP.
symmetry; assumption.
Qed.

Lemma Permutation_map_inv_inj A B (f : A -> B) (Hinj : injective f) l1 l2 :
  Permutation (map f l1) (map f l2) -> Permutation l1 l2.
Proof.
revert l2; induction l1; intros l2 HP.
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
  apply Hinj in Heq3; subst.
  now apply Permutation_cons_app.
Qed.

Lemma Permutation_map_inv_inj_local A B (f : A -> B) l1 l2 :
  (forall x y, In x l1 -> In y l2 -> f x = f y -> x = y) ->
    Permutation (map f l1) (map f l2) -> Permutation l1 l2.
Proof.
revert l2; induction l1; intros l2 Hi HP.
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

Lemma partition_Permutation A f (l l1 l2 : list A) : partition f l = (l1, l2) -> Permutation l (l1 ++ l2).
Proof.
induction l as [|a l IHl] in l1, l2 |- *; cbn; intros Hp.
- injection Hp as [= <- <-]. reflexivity.
- destruct (partition f l), (f a); injection Hp as [= <- <-].
  + apply Permutation_cons, IHl; reflexivity.
  + apply Permutation_cons_app, IHl. reflexivity.
Qed.

Lemma Permutation_partition A f (l l' l1 l2 l1' l2' : list A) :
  Permutation l l' -> partition f l = (l1, l2) -> partition f l' = (l1', l2') ->
  Permutation l1 l1' /\ Permutation l2 l2'.
Proof.
intros HP; induction HP as [ | x l l' HP IHHP | x y l
                           | l l' l'' HP1 IHHP1 HP2 IHHP2 ] in l1, l2, l1', l2' |- *;
  cbn; intros Hp1 Hp2.
- injection Hp1 as [= <- <-]. injection Hp2 as [= <- <-]. split; reflexivity.
- destruct (partition f l) as [l3 l4], (partition f l') as [l3' l4'], (f x);
    injection Hp1 as [= <- <-]; injection Hp2 as [= <- <-];
    destruct (IHHP l3 l4 l3' l4' eq_refl eq_refl); split; now try apply Permutation_cons.
- destruct (partition f l) as [l3 l4], (f x), (f y);
    injection Hp1 as [= <- <-]; injection Hp2 as [= <- <-]; split; (reflexivity + apply perm_swap).
- destruct (partition f l) as [l3 l4], (partition f l') as [l3' l4'],
           (partition f l'') as [l3'' l4''];
     injection Hp1 as [= <- <-]; injection Hp2 as [= <- <-];
     destruct (IHHP1 l3 l4 l3' l4' eq_refl eq_refl);
     destruct (IHHP2 l3' l4' l3'' l4'' eq_refl eq_refl); split; etransitivity; eassumption.
Qed.
