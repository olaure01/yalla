(* llfoc library for yalla *)

(** * Focusing in Linear Logic *)

From Coq Require Import CMorphisms Wf_nat Lia.
From OLlibs Require Import infinite List_more Permutation_Type_more Permutation_Type_solve.
From Yalla Require Import ll_fragments.


Section Atoms.

Context { atom : InfDecType }.
Notation formula := (@formula atom).

(** ** Synchronous and asynchronous formulas *)
Inductive sformula : formula -> Type :=
| pvar : forall x, sformula (var x)
| pone : sformula one
| ptens : forall A B, sformula (tens A B)
| pzero : sformula zero
| pplus : forall A B, sformula (aplus A B)
| poc : forall A, sformula (oc A).

Inductive aformula : formula -> Type :=
| ncovar : forall x, aformula (covar x)
| nbot : aformula bot
| nparr : forall A B, aformula (parr A B)
| ntop : aformula top
| nwith : forall A B, aformula (awith A B)
| nwn : forall A, aformula (wn A).

Lemma polarity : forall A, sformula A + aformula A.
Proof. induction A; now (left + right; constructor). Defined.

Lemma disj_polarity : forall A, sformula A -> aformula A -> False.
Proof. induction A; intros Hp Hn; inversion Hp; inversion Hn. Qed.

Lemma sformula_dual : forall A, sformula (dual A) -> aformula A.
Proof. intros A Hp; destruct A; inversion Hp; constructor. Qed.

Lemma aformula_dual : forall A, aformula (dual A) -> sformula A.
Proof. intros A Hn; destruct A; inversion Hn; constructor. Qed.


(** ** The weakly focused system [llfoc] *)

Definition tFoc x :=
  (sformula x + { X | x = covar X } + { y | x = wn y } + (x = top))%type.

Lemma tFoc_dec : forall x, tFoc x + (tFoc x -> False).
Proof with myeeasy.
induction x ;
  try (now (left ; left ; left ; left ; constructor)) ;
  try (now (left ; left ; left ; right ; eexists ; reflexivity)) ;
  try (now (left ; left ; right ; eexists ; reflexivity)) ;
  try (now (left ; right ; reflexivity)) ;
  try (now (right ; intros [[[ H | [X H] ] | [X H] ] | H] ; inversion H)).
Qed.

Lemma tFocl_dec : forall l, Forall_inf tFoc l + (Forall_inf tFoc l -> False).
Proof with myeasy.
induction l.
- left ; constructor.
- destruct (tFoc_dec a).
  + destruct IHl.
    * left ; constructor...
    * right ; intros H.
      inversion H ; subst ; intuition.
  + right ; intros H.
    inversion H ; subst ; intuition.
Qed.

Lemma not_tFoc : forall x, (tFoc x -> False) ->
  (x = bot) + {'(y1, y2) | x = parr y1 y2 } + {'(y1, y2) | x = awith y1 y2 }.
Proof.
destruct x ; intros HnF ;
  try (now (exfalso ; apply HnF ; left ; left ; left ; constructor)) ;
  try (now (exfalso ; apply HnF ; left ; left ; right ; eexists ; reflexivity)) ;
  try (now (exfalso ; apply HnF ; left ; right ; eexists ; reflexivity)) ;
  try (now (exfalso ; apply HnF ; right ; reflexivity)).
- left; left; reflexivity.
- left; right ; exists (x1, x2); reflexivity.
- right; eexists (x1, x2); reflexivity.
Qed.

Lemma not_tFocl l : (Forall_inf tFoc l -> False) ->
  {'(A, l1, l2) & l = l1 ++ A :: l2
                & ((A = bot) + {'(A1, A2) | A = parr A1 A2 }
                             + {'(A1, A2) | A = awith A1 A2 })%type }.
Proof.
intros HnF%Forall_inf_neg_Exists_inf.
- induction l; inversion HnF; subst.
  + exists (a, nil, l); [ reflexivity | ].
    apply (not_tFoc _ H0).
  + apply IHl in X as [[[b l1] l2] Heq Hf]; subst.
    now exists (b, a::l1, l2).
- intros x.
  destruct (tFoc_dec x); auto.
Qed.

Definition polcont l A :=
match polarity A with
| inl _ => l
| inr _ => A :: l
end.
Definition polfoc A :=
match polarity A with
| inl _ => Some A
| inr _ => None
end.
Lemma polconts A l : sformula A -> polcont l A = l.
Proof.
intros; unfold polcont; destruct (polarity A); auto.
exfalso; apply (disj_polarity A); assumption.
Qed.
Lemma polconta A l : aformula A -> polcont l A = A :: l.
Proof.
intros; unfold polcont; destruct (polarity A); auto.
exfalso; apply (disj_polarity A); assumption.
Qed.
Lemma polfocs A : sformula A -> polfoc A = Some A.
Proof.
intros; unfold polfoc; destruct (polarity A); auto.
exfalso; apply (disj_polarity A); assumption.
Qed.
Lemma polfoca A : aformula A -> polfoc A = None.
Proof.
intros; unfold polfoc; destruct (polarity A); auto.
exfalso; apply (disj_polarity A); assumption.
Qed.

Lemma Permutation_Type_middle_polcont l1 l2 A B :
  Permutation_Type (B :: polcont (l1 ++ l2) A) (polcont (l1 ++ B :: l2) A).
Proof.
unfold polcont; destruct (polarity A) as [Hs | Ha];
  [ | rewrite 2 (app_comm_cons _ _ A)]; apply Permutation_Type_middle.
Qed.

Inductive llfoc : list formula -> option formula -> Type :=
| ax_fr : forall X, llfoc (covar X :: nil) (Some (var X))
| ex_fr : forall l1 l2 Pi, llfoc l1 Pi -> Permutation_Type l1 l2 ->
                           llfoc l2 Pi
| foc_fr : forall A l, llfoc l (Some A) -> llfoc (A :: l) None
| one_fr : llfoc nil (Some one)
| bot_fr : forall l Pi, llfoc l Pi ->
                          llfoc (bot :: l) Pi
| tens_fr : forall A B l1 l2,
                    llfoc (polcont l1 A) (polfoc A) ->
                    llfoc (polcont l2 B) (polfoc B) ->
                    llfoc (l1 ++ l2) (Some (tens A B))
| parr_fr : forall A B l Pi,
                    llfoc (A :: B :: l) Pi ->
                    llfoc (parr A B :: l) Pi
| top_fr : forall l Pi, option_test sformula Pi -> Forall_inf tFoc l ->
                    llfoc (top :: l) Pi
| plus_fr1 : forall A B l, llfoc (polcont l A) (polfoc A) ->
                             llfoc l (Some (aplus A B))
| plus_fr2 : forall A B l, llfoc (polcont l A) (polfoc A) ->
                             llfoc l (Some (aplus B A))
| with_fr : forall A B l Pi, llfoc (A :: l) Pi -> llfoc (B :: l) Pi ->
                        llfoc (awith A B :: l) Pi
| oc_fr : forall A l, llfoc (A :: map wn l) None ->
                        llfoc (map wn l) (Some (oc A))
| de_fr : forall A l, llfoc (polcont l A) (polfoc A) ->
                         llfoc (wn A :: l) None
| wk_fr : forall A l Pi, llfoc l Pi -> llfoc (wn A :: l) Pi
| co_fr : forall A l Pi, llfoc (wn A :: wn A :: l) Pi ->
                           llfoc (wn A :: l) Pi.

Fixpoint fpsize {l Pi} (pi : llfoc l Pi) :=
match pi with
| ax_fr _ => 1
| ex_fr _ _ _ pi0 _ => S (fpsize pi0)
| foc_fr _ _ pi0 => S (fpsize pi0)
| one_fr => 1
| bot_fr _ _ pi0 => S (fpsize pi0)
| tens_fr _ _ _ _ pi1 pi2 => S (fpsize pi1 + fpsize pi2)
| parr_fr _ _ _ _ pi0 => S (fpsize pi0)
| top_fr _ _ _ _ => 1
| plus_fr1 _ _ _ pi0 => S (fpsize pi0)
| plus_fr2 _ _ _ pi0 => S (fpsize pi0)
| with_fr _ _ _ _ pi1 pi2 => S (max (fpsize pi1) (fpsize pi2))
| oc_fr _ _ pi0 => S (fpsize pi0)
| de_fr _ _ pi0 => S (fpsize pi0)
| wk_fr _ _ _ pi0 => S (fpsize pi0)
| co_fr _ _ _ pi0 => S (fpsize pi0)
end.

Lemma top_gen_fr : forall l Pi, option_test sformula Pi -> llfoc (top :: l) Pi.
Proof.
intros l.
remember (list_sum (map fsize l)) as n; revert l Heqn; induction n using lt_wf_rect;
  intros l -> Pi Hs; subst.
destruct (tFocl_dec l).
- apply top_fr; assumption.
- apply not_tFocl in f.
  destruct f as [ [[A l1] l2] -> [[-> | [[B C] ->]] | [[B C] ->]] ].
  + rewrite app_comm_cons.
    eapply ex_fr ; [ apply bot_fr | apply Permutation_Type_middle ].
    cbn ; eapply X; [ | reflexivity | assumption ].
    cbn; rewrite 2 map_app, 2 list_sum_app; simpl; lia.
  + rewrite app_comm_cons.
    eapply ex_fr; [ apply parr_fr | apply Permutation_Type_middle ].
    list_simpl; eapply ex_fr;
    [ eapply X; trivial
    | etransitivity ; [ apply Permutation_Type_swap
                      | apply (Permutation_Type_cons eq_refl) ;
                        etransitivity ; [ apply Permutation_Type_swap | reflexivity ]]].
    cbn; rewrite 2 map_app, 2 list_sum_app; simpl; lia.
  + rewrite app_comm_cons.
    eapply ex_fr; [ apply with_fr | apply Permutation_Type_middle ].
    * list_simpl; eapply ex_fr;
        [ eapply X; trivial
        | etransitivity; [ apply Permutation_Type_swap | apply Permutation_Type_cons; reflexivity ]].
      cbn; rewrite 2 map_app, 2 list_sum_app ; simpl; lia.
    * list_simpl; eapply ex_fr;
        [ eapply X; trivial
        | etransitivity; [ apply Permutation_Type_swap | apply Permutation_Type_cons; reflexivity ]].
    cbn; rewrite 2 map_app, 2 list_sum_app; simpl; lia.
Qed.

Lemma sync_focus : forall l A, llfoc l (Some A) -> sformula A.
Proof.
intros l A pi.
remember (Some A) as Pi ; revert HeqPi ; induction pi ;
  intros HeqPi ; inversion HeqPi ; subst ;
  try (now constructor) ;
  try apply IHpi ;
  try assumption.
apply IHpi1 ; assumption.
Qed.

Lemma llfoc_foc_is_llfoc_foc : forall l A, llfoc l (Some A) ->
  llfoc (polcont l A) (polfoc A).
Proof.
intros l A pi.
assert (Hs := sync_focus _ _ pi).
rewrite (polconts _ _ Hs).
rewrite (polfocs _ Hs).
apply pi.
Qed.

Lemma llfoc_cont_is_llfoc_cont : forall l A, aformula A ->
  llfoc (A :: l) None -> llfoc (polcont l A) (polfoc A).
Proof.
intros l A Ha pi.
rewrite (polconta _ _ Ha).
rewrite (polfoca _ Ha).
apply pi.
Qed.

Lemma bot_rev_f : forall l Pi (pi : llfoc l Pi),
  forall l1 l2, l = l1 ++ bot :: l2 ->
    { pi' : llfoc (l1 ++ l2) Pi | fpsize pi' < fpsize pi }.
Proof with myeeasy.
intros l Pi pi.
induction pi ; intros l1' l2' Heq ; subst.
- exfalso.
  destruct l1' ; inversion Heq.
  destruct l1' ; inversion H1.
- assert (HP := p).
  cbn ; apply Permutation_Type_vs_elt_inv in p.
  destruct p as ((l3 & l4) & Heq) ; subst.
  cbn in IHpi ; cbn in HP ; cbn.
  destruct (IHpi _ _ eq_refl) as [pi0 Hs].
  cbn in HP ; apply Permutation_Type_app_inv in HP.
  exists (ex_fr _ _ _ pi0 HP) ; cbn...
- destruct l1' ; inversion Heq ; subst.
  + exfalso.
    clear IHpi ; apply sync_focus in pi.
    inversion pi.
  + destruct (IHpi _ _ eq_refl) as [pi0 Hs].
    exists (foc_fr _ _ pi0) ; cbn...
- exfalso.
  destruct l1' ; inversion Heq.
- destruct l1' ; inversion Heq ; subst.
  + exists pi ; cbn...
  + destruct (IHpi _ _ eq_refl) as [pi0 Hs].
    exists (bot_fr _ _ pi0) ; cbn...
- dichot_elt_app_inf_exec Heq ; subst.
  + destruct (polarity A) as [Hs | Ha].
    * assert (H1 := IHpi1 _ _ (polconts _ _ Hs)).
      rewrite <- (polconts _ (l1' ++ l) Hs) in H1.
      destruct H1 as [pi1' Hs1].
      rewrite app_assoc.
      exists (tens_fr _ _ _ _ pi1' pi2) ; cbn...
    * assert (polcont (l1' ++ bot :: l) A = (A :: l1') ++ bot :: l) as Hpa
        by (rewrite (polconta _ _ Ha) ; rewrite app_comm_cons ; reflexivity).
      assert (H1 := IHpi1 _ _ Hpa).
      rewrite <- app_comm_cons in H1.
      rewrite <- (polconta _ (l1' ++ l) Ha) in H1.
      destruct H1 as [pi1' Hs1].
      rewrite app_assoc.
      exists (tens_fr _ _ _ _ pi1' pi2) ; cbn...
  + destruct (polarity B) as [Hs | Ha].
    * assert (H2 := IHpi2 _ _ (polconts _ _ Hs)).
      rewrite <- (polconts _ (l0 ++ l2') Hs) in H2.
      destruct H2 as [pi2' Hs2].
      rewrite <- app_assoc.
      exists (tens_fr _ _ _ _ pi1 pi2') ; cbn...
    * assert (polcont (l0 ++ bot :: l2') B = (B :: l0) ++ bot :: l2') as Hpa
        by (rewrite (polconta _ _ Ha) ; rewrite app_comm_cons ; reflexivity).
      assert (H2 := IHpi2 _ _ Hpa).
      rewrite <- app_comm_cons in H2.
      rewrite <- (polconta _ (l0 ++ l2') Ha) in H2.
      destruct H2 as [pi2' Hs2].
      rewrite <- app_assoc.
      exists (tens_fr _ _ _ _ pi1 pi2') ; cbn...
- destruct l1' ; inversion Heq ; subst.
  assert (A :: B :: l1' ++ bot :: l2' = (A :: B :: l1') ++ bot :: l2') as Heql
    by (list_simpl ; reflexivity).
  assert (H0 := IHpi _ _ Heql).
  rewrite <- 2 app_comm_cons in H0.
  destruct H0 as [pi0 Hs].
  exists (parr_fr _ _ _ _ pi0) ; cbn...
- exfalso.
  destruct l1' ; inversion Heq ; subst.
  apply Forall_inf_app_r in f.
  inversion f ; subst.
  inversion X as [[[Ht | Ht] | Ht] | Ht] ; try now (inversion Ht).
- destruct (polarity A) as [Hs | Ha].
  + assert (H1 := IHpi _ _ (polconts _ _ Hs)).
    rewrite <- (polconts _ (l1' ++ l2') Hs) in H1.
    destruct H1 as [pi1' Hs1].
    exists (plus_fr1 _ B _ pi1') ; cbn...
  + assert (polcont (l1' ++ bot :: l2') A = (A :: l1') ++ bot :: l2') as Hpa
      by (rewrite (polconta _ _ Ha) ; rewrite app_comm_cons ; reflexivity).
    assert (H1 := IHpi _ _ Hpa).
    rewrite <- app_comm_cons in H1.
    rewrite <- (polconta _ (l1' ++ l2') Ha) in H1.
    destruct H1 as [pi1' Hs1].
    exists (plus_fr1 _ B _ pi1') ; cbn...
- destruct (polarity A) as [Hs | Ha].
  + assert (H1 := IHpi _ _ (polconts _ _ Hs)).
    rewrite <- (polconts _ (l1' ++ l2') Hs) in H1.
    destruct H1 as [pi1' Hs1].
    exists (plus_fr2 _ B _ pi1') ; cbn...
  + assert (polcont (l1' ++ bot :: l2') A = (A :: l1') ++ bot :: l2') as Hpa
      by (rewrite (polconta _ _ Ha) ; rewrite app_comm_cons ; reflexivity).
    assert (H1 := IHpi _ _ Hpa).
    rewrite <- app_comm_cons in H1.
    rewrite <- (polconta _ (l1' ++ l2') Ha) in H1.
    destruct H1 as [pi1' Hs1].
    exists (plus_fr2 _ B _ pi1') ; cbn...
- destruct l1' ; inversion Heq ; subst.
  assert (A :: l1' ++ bot :: l2' = (A :: l1') ++ bot :: l2') as Heql1
    by (list_simpl ; reflexivity).
  assert (B :: l1' ++ bot :: l2' = (B :: l1') ++ bot :: l2') as Heql2
    by (list_simpl ; reflexivity).
  assert (H1 := IHpi1 _ _ Heql1).
  assert (H2 := IHpi2 _ _ Heql2).
  rewrite <- app_comm_cons in H1.
  rewrite <- app_comm_cons in H2.
  destruct H1 as [pi1' Hs1].
  destruct H2 as [pi2' Hs2].
  exists (with_fr _ _ _ _ pi1' pi2') ; cbn...
- exfalso.
  decomp_map Heq; inversion Heq3.
- destruct l1' ; inversion Heq ; subst.
  destruct (polarity A) as [Hs | Ha].
  + assert (H1 := IHpi _ _ (polconts _ _ Hs)).
    rewrite <- (polconts _ (l1' ++ l2') Hs) in H1.
    destruct H1 as [pi1' Hs1].
    exists (de_fr _ _ pi1') ; cbn...
  + assert (polcont (l1' ++ bot :: l2') A = (A :: l1') ++ bot :: l2') as Hpa
      by (rewrite (polconta _ _ Ha) ; rewrite app_comm_cons ; reflexivity).
    assert (H1 := IHpi _ _ Hpa).
    rewrite <- app_comm_cons in H1.
    rewrite <- (polconta _ (l1' ++ l2') Ha) in H1.
    destruct H1 as [pi1' Hs1].
    exists (de_fr _ _ pi1') ; cbn...
- destruct l1' ; inversion Heq ; subst.
  destruct (IHpi _ _ eq_refl) as [pi0 Hs].
  exists (wk_fr A _ _ pi0) ; cbn...
- destruct l1' ; inversion Heq ; subst.
  assert (wn A :: wn A :: l1' ++ bot :: l2' = (wn A :: wn A :: l1') ++ bot :: l2')
    as Heql by (list_simpl ; reflexivity).
  assert (H0 := IHpi _ _ Heql).
  rewrite <- 2 app_comm_cons in H0.
  destruct H0 as [pi0 Hs].
  exists (co_fr _ _ _ pi0) ; cbn...
Qed.

Lemma parr_rev_f : forall l Pi (pi : llfoc l Pi),
  forall A B l1 l2, l = l1 ++ parr A B :: l2 ->
    { pi' : llfoc (l1 ++ A :: B :: l2) Pi | fpsize pi' < fpsize pi }.
Proof with myeeasy.
intros l Pi pi.
induction pi ; intros A' B' l1' l2' Heq ; subst.
- exfalso.
  destruct l1' ; inversion Heq.
  destruct l1' ; inversion H1.
- assert (HP := p).
  cbn ; apply Permutation_Type_vs_elt_inv in p.
  destruct p as ((l3 & l4) & Heq) ; subst.
  cbn in IHpi ; cbn in HP ; cbn.
  destruct (IHpi _ _ _ _ eq_refl) as [pi0 Hs].
  cbn in HP ; apply Permutation_Type_app_inv in HP.
  apply (Permutation_Type_elt B') in HP.
  apply (Permutation_Type_elt A') in HP.
  exists (ex_fr _ _ _ pi0 HP) ; cbn...
- destruct l1' ; inversion Heq ; subst.
  + exfalso.
    clear IHpi ; apply sync_focus in pi.
    inversion pi.
  + destruct (IHpi _ _ _ _ eq_refl) as [pi0 Hs].
    exists (foc_fr _ _ pi0) ; cbn...
- exfalso.
  destruct l1' ; inversion Heq.
- destruct l1' ; inversion Heq ; subst.
  destruct (IHpi _ _ _ _ eq_refl) as [pi0 Hs].
  exists (bot_fr _ _ pi0) ; cbn...
- dichot_elt_app_inf_exec Heq ; subst.
  + destruct (polarity A) as [Hs | Ha].
    * assert (H1 := IHpi1 _ _ _ _ (polconts _ _ Hs)).
      rewrite <- (polconts _ (l1' ++ A' :: B' :: l) Hs) in H1.
      destruct H1 as [pi1' Hs1].
      rewrite 2 app_comm_cons ; rewrite app_assoc.
      exists (tens_fr _ _ _ _ pi1' pi2) ; cbn...
    * assert (polcont (l1' ++ parr A' B' :: l) A = (A :: l1') ++ parr A' B' :: l)
        as Hpa by (rewrite (polconta _ _ Ha) ; rewrite app_comm_cons ; reflexivity).
      assert (H1 := IHpi1 _ _ _ _ Hpa).
      rewrite <- app_comm_cons in H1.
      rewrite <- (polconta _ (l1' ++ A' :: B' :: l) Ha) in H1.
      destruct H1 as [pi1' Hs1].
      rewrite 2 app_comm_cons ; rewrite app_assoc.
      exists (tens_fr _ _ _ _ pi1' pi2) ; cbn...
  + destruct (polarity B) as [Hs | Ha].
    * assert (H2 := IHpi2 _ _ _ _ (polconts _ _ Hs)).
      rewrite <- (polconts _ (l0 ++ A' :: B' :: l2') Hs) in H2.
      destruct H2 as [pi2' Hs2].
      rewrite <- app_assoc.
      exists (tens_fr _ _ _ _ pi1 pi2') ; cbn...
    * assert (polcont (l0 ++ parr A' B' :: l2') B = (B :: l0) ++ parr A' B' :: l2')
        as Hpa by (rewrite (polconta _ _ Ha) ; rewrite app_comm_cons ; reflexivity).
      assert (H2 := IHpi2 _ _ _ _ Hpa).
      rewrite <- app_comm_cons in H2.
      rewrite <- (polconta _ (l0 ++ A' :: B' :: l2') Ha) in H2.
      destruct H2 as [pi2' Hs2].
      rewrite <- app_assoc.
      exists (tens_fr _ _ _ _ pi1 pi2') ; cbn...
- destruct l1' ; inversion Heq ; subst.
  + exists pi ; cbn...
  + assert (A :: B :: l1' ++ parr A' B' :: l2' = (A :: B :: l1') ++ parr A' B' :: l2')
      as Heql by (list_simpl ; reflexivity).
    assert (H0 := IHpi _ _ _ _ Heql).
    rewrite <- 2 app_comm_cons in H0.
    destruct H0 as [pi0 Hs].
    exists (parr_fr _ _ _ _ pi0) ; cbn...
- exfalso.
  destruct l1' ; inversion Heq ; subst.
  apply Forall_inf_app_r in f.
  inversion f ; subst.
  inversion X as [[[Ht | Ht] | Ht] | Ht] ; try now (inversion Ht).
- destruct (polarity A) as [Hs | Ha].
  + assert (H1 := IHpi _ _ _ _ (polconts _ _ Hs)).
    rewrite <- (polconts _ (l1' ++ A' :: B' :: l2') Hs) in H1.
    destruct H1 as [pi1' Hs1].
    exists (plus_fr1 _ B _ pi1') ; cbn...
  + assert (polcont (l1' ++ parr A' B' :: l2') A = (A :: l1') ++ parr A' B' :: l2')
      as Hpa by (rewrite (polconta _ _ Ha) ; rewrite app_comm_cons ; reflexivity).
    assert (H1 := IHpi _ _ _ _ Hpa).
    rewrite <- app_comm_cons in H1.
    rewrite <- (polconta _ (l1' ++ A' :: B' :: l2') Ha) in H1.
    destruct H1 as [pi1' Hs1].
    exists (plus_fr1 _ B _ pi1') ; cbn...
- destruct (polarity A) as [Hs | Ha].
  + assert (H1 := IHpi _ _ _ _ (polconts _ _ Hs)).
    rewrite <- (polconts _ (l1' ++ A' :: B' :: l2') Hs) in H1.
    destruct H1 as [pi1' Hs1].
    exists (plus_fr2 _ B _ pi1') ; cbn...
  + assert (polcont (l1' ++ parr A' B' :: l2') A = (A :: l1') ++ parr A' B' :: l2')
      as Hpa by (rewrite (polconta _ _ Ha) ; rewrite app_comm_cons ; reflexivity).
    assert (H1 := IHpi _ _ _ _ Hpa).
    rewrite <- app_comm_cons in H1.
    rewrite <- (polconta _ (l1' ++ A' :: B' :: l2') Ha) in H1.
    destruct H1 as [pi1' Hs1].
    exists (plus_fr2 _ B _ pi1') ; cbn...
- destruct l1' ; inversion Heq ; subst.
  assert (A :: l1' ++ parr A' B' :: l2' = (A :: l1') ++ parr A' B' :: l2') as Heql1
    by (list_simpl ; reflexivity).
  assert (B :: l1' ++ parr A' B' :: l2' = (B :: l1') ++ parr A' B' :: l2') as Heql2
    by (list_simpl ; reflexivity).
  assert (H1 := IHpi1 _ _ _ _ Heql1).
  assert (H2 := IHpi2 _ _ _ _ Heql2).
  rewrite <- app_comm_cons in H1.
  rewrite <- app_comm_cons in H2.
  destruct H1 as [pi1' Hs1].
  destruct H2 as [pi2' Hs2].
  exists (with_fr _ _ _ _ pi1' pi2') ; cbn...
- exfalso.
  decomp_map Heq; inversion Heq3.
- destruct l1' ; inversion Heq ; subst.
  destruct (polarity A) as [Hs | Ha].
  + assert (H1 := IHpi _ _ _ _ (polconts _ _ Hs)).
    rewrite <- (polconts _ (l1' ++ A' :: B' :: l2') Hs) in H1.
    destruct H1 as [pi1' Hs1].
    exists (de_fr _ _ pi1') ; cbn...
  + assert (polcont (l1' ++ parr A' B' :: l2') A = (A :: l1') ++ parr A' B' :: l2')
      as Hpa by (rewrite (polconta _ _ Ha) ; rewrite app_comm_cons ; reflexivity).
    assert (H1 := IHpi _ _ _ _ Hpa).
    rewrite <- app_comm_cons in H1.
    rewrite <- (polconta _ (l1' ++ A' :: B' :: l2') Ha) in H1.
    destruct H1 as [pi1' Hs1].
    exists (de_fr _ _ pi1') ; cbn...
- destruct l1' ; inversion Heq ; subst.
  destruct (IHpi _ _ _ _ eq_refl) as [pi0 Hs].
  exists (wk_fr A _ _ pi0) ; cbn...
- destruct l1' ; inversion Heq ; subst.
  assert (wn A :: wn A :: l1' ++ parr A' B' :: l2'
       = (wn A :: wn A :: l1') ++ parr A' B' :: l2')
    as Heql by (list_simpl ; reflexivity).
  assert (H0 := IHpi _ _ _ _ Heql).
  rewrite <- 2 app_comm_cons in H0.
  destruct H0 as [pi0 Hs].
  exists (co_fr _ _ _ pi0) ; cbn...
Qed.

Lemma with_rev_f : forall l Pi (pi : llfoc l Pi),
  forall A B l1 l2, l = l1 ++ awith A B :: l2 ->
    { pi' : llfoc (l1 ++ A :: l2) Pi | fpsize pi' < fpsize pi }
  * { pi' : llfoc (l1 ++ B :: l2) Pi | fpsize pi' < fpsize pi }.
Proof with myeeasy.
intros l Pi pi.
induction pi ; intros A' B' l1' l2' Heq ; subst.
- exfalso.
  destruct l1' ; inversion Heq.
  destruct l1' ; inversion H1.
- assert (HP := p).
  cbn ; apply Permutation_Type_vs_elt_inv in p.
  destruct p as ((l3 & l4) & Heq) ; subst.
  cbn in IHpi ; cbn in HP ; cbn.
  destruct (IHpi _ _ _ _ eq_refl) as [[pi01 Hs1] [pi02 Hs2]].
  cbn in HP ; apply Permutation_Type_app_inv in HP.
  assert (HP2 := HP).
  apply (Permutation_Type_elt B') in HP2.
  apply (Permutation_Type_elt A') in HP.
  split ; [ exists (ex_fr _ _ _ pi01 HP)
          | exists (ex_fr _ _ _ pi02 HP2) ] ; cbn...
- destruct l1' ; inversion Heq ; subst.
  + exfalso.
    clear IHpi ; apply sync_focus in pi.
    inversion pi.
  + destruct (IHpi _ _ _ _ eq_refl) as [[pi01 Hs1] [pi02 Hs2]].
    split ; [ exists (foc_fr _ _ pi01)
            | exists (foc_fr _ _ pi02) ] ; cbn...
- exfalso.
  destruct l1' ; inversion Heq.
- destruct l1' ; inversion Heq ; subst.
  destruct (IHpi _ _ _ _ eq_refl) as [[pi01 Hs1] [pi02 Hs2]].
    split ; [ exists (bot_fr _ _ pi01)
            | exists (bot_fr _ _ pi02) ] ; cbn...
- dichot_elt_app_inf_exec Heq ; subst.
  + destruct (polarity A) as [Hs | Ha].
    * assert (H1 := IHpi1 _ _ _ _ (polconts _ _ Hs)).
      rewrite <- (polconts _ (l1' ++ A' :: l) Hs) in H1.
      rewrite <- (polconts _ (l1' ++ B' :: l) Hs) in H1.
      destruct H1 as [[pi1' Hs1] [pi1'' Hs2]].
      rewrite ? app_comm_cons ; rewrite 2 app_assoc.
      split ; [ exists (tens_fr _ _ _ _ pi1' pi2)
              | exists (tens_fr _ _ _ _ pi1'' pi2) ] ; cbn...
    * assert (polcont (l1' ++ awith A' B' :: l) A = (A :: l1') ++ awith A' B' :: l)
        as Hpa by (rewrite (polconta _ _ Ha) ; rewrite app_comm_cons ; reflexivity).
      assert (H1 := IHpi1 _ _ _ _ Hpa).
      rewrite <- 2 app_comm_cons in H1.
      rewrite <- (polconta _ (l1' ++ A' :: l) Ha) in H1.
      rewrite <- (polconta _ (l1' ++ B' :: l) Ha) in H1.
      destruct H1 as [[pi1' Hs1] [pi2' Hs2]].
      rewrite ? app_comm_cons ; rewrite 2 app_assoc.
      split ; [ exists (tens_fr _ _ _ _ pi1' pi2)
              | exists (tens_fr _ _ _ _ pi2' pi2) ] ; cbn...
  + destruct (polarity B) as [Hs | Ha].
    * assert (H2 := IHpi2 _ _ _ _ (polconts _ _ Hs)).
      rewrite <- (polconts _ (l0 ++ A' :: l2') Hs) in H2.
      rewrite <- (polconts _ (l0 ++ B' :: l2') Hs) in H2.
      destruct H2 as [[pi1' Hs1] [pi1'' Hs2]].
      rewrite <- 2 app_assoc.
      split ; [ exists (tens_fr _ _ _ _ pi1 pi1')
              | exists (tens_fr _ _ _ _ pi1 pi1'') ] ; cbn...
    * assert (polcont (l0 ++ awith A' B' :: l2') B = (B :: l0) ++ awith A' B' :: l2')
        as Hpa by (rewrite (polconta _ _ Ha) ; rewrite app_comm_cons ; reflexivity).
      assert (H2 := IHpi2 _ _ _ _ Hpa).
      rewrite <- 2 app_comm_cons in H2.
      rewrite <- (polconta _ (l0 ++ A' :: l2') Ha) in H2.
      rewrite <- (polconta _ (l0 ++ B' :: l2') Ha) in H2.
      destruct H2 as [[pi1' Hs1] [pi1'' Hs2]].
      rewrite <- 2 app_assoc.
      split ; [ exists (tens_fr _ _ _ _ pi1 pi1')
              | exists (tens_fr _ _ _ _ pi1 pi1'') ] ; cbn...
- destruct l1' ; inversion Heq ; subst.
  assert (A :: B :: l1' ++ awith A' B' :: l2' = (A :: B :: l1') ++ awith A' B' :: l2')
    as Heql by (list_simpl ; reflexivity).
  assert (H0 := IHpi _ _ _ _ Heql).
  rewrite <- ? app_comm_cons in H0.
  destruct H0 as [[pi1' Hs1] [pi1'' Hs2]].
  split ; [ exists (parr_fr _ _ _ _ pi1')
          | exists (parr_fr _ _ _ _ pi1'') ] ; cbn...
- exfalso.
  destruct l1' ; inversion Heq ; subst.
  apply Forall_inf_app_r in f.
  inversion f ; subst.
  inversion X as [[[Ht | Ht] | Ht] | Ht] ; try now (inversion Ht).
- destruct (polarity A) as [Hs | Ha].
  + assert (H1 := IHpi _ _ _ _ (polconts _ _ Hs)).
    rewrite <- (polconts _ (l1' ++ A' :: l2') Hs) in H1.
    rewrite <- (polconts _ (l1' ++ B' :: l2') Hs) in H1.
    destruct H1 as [[pi1' Hs1] [pi1'' Hs2]].
    split ; [ exists (plus_fr1 _ _ _ pi1')
            | exists (plus_fr1 _ _ _ pi1'') ] ; cbn...
  + assert (polcont (l1' ++ awith A' B' :: l2') A = (A :: l1') ++ awith A' B' :: l2')
      as Hpa by (rewrite (polconta _ _ Ha) ; rewrite app_comm_cons ; reflexivity).
    assert (H1 := IHpi _ _ _ _ Hpa).
    rewrite <- 2 app_comm_cons in H1.
    rewrite <- (polconta _ (l1' ++ A' :: l2') Ha) in H1.
    rewrite <- (polconta _ (l1' ++ B' :: l2') Ha) in H1.
    destruct H1 as [[pi1' Hs1] [pi1'' Hs2]].
    split ; [ exists (plus_fr1 _ _ _ pi1')
            | exists (plus_fr1 _ _ _ pi1'') ] ; cbn...
- destruct (polarity A) as [Hs | Ha].
  + assert (H1 := IHpi _ _ _ _ (polconts _ _ Hs)).
    rewrite <- (polconts _ (l1' ++ A' :: l2') Hs) in H1.
    rewrite <- (polconts _ (l1' ++ B' :: l2') Hs) in H1.
    destruct H1 as [[pi1' Hs1] [pi1'' Hs2]].
    split ; [ exists (plus_fr2 _ _ _ pi1')
            | exists (plus_fr2 _ _ _ pi1'') ] ; cbn...
  + assert (polcont (l1' ++ awith A' B' :: l2') A = (A :: l1') ++ awith A' B' :: l2')
      as Hpa by (rewrite (polconta _ _ Ha) ; rewrite app_comm_cons ; reflexivity).
    assert (H1 := IHpi _ _ _ _ Hpa).
    rewrite <- 2 app_comm_cons in H1.
    rewrite <- (polconta _ (l1' ++ A' :: l2') Ha) in H1.
    rewrite <- (polconta _ (l1' ++ B' :: l2') Ha) in H1.
    destruct H1 as [[pi1' Hs1] [pi1'' Hs2]].
    split ; [ exists (plus_fr2 _ _ _ pi1')
            | exists (plus_fr2 _ _ _ pi1'') ] ; cbn...
- destruct l1' ; inversion Heq ; subst.
  + split ; [ exists pi1 | exists pi2 ] ; subst ; cbn...
  + assert (A :: l1' ++ awith A' B' :: l2' = (A :: l1') ++ awith A' B' :: l2') as Heql1
      by (list_simpl ; reflexivity).
    assert (B :: l1' ++ awith A' B' :: l2' = (B :: l1') ++ awith A' B' :: l2') as Heql2
      by (list_simpl ; reflexivity).
    assert (H1 := IHpi1 _ _ _ _ Heql1).
    assert (H2 := IHpi2 _ _ _ _ Heql2).
    rewrite <- 2 app_comm_cons in H1.
    rewrite <- 2 app_comm_cons in H2.
    destruct H1 as [[pi1' Hs1] [pi1'' Hs1']].
    destruct H2 as [[pi2' Hs2] [pi2'' Hs2']].
    split ; [ exists (with_fr _ _ _ _ pi1' pi2')
            | exists (with_fr _ _ _ _ pi1'' pi2'') ] ; cbn...
- exfalso.
  decomp_map Heq; inversion Heq3.
- destruct l1' ; inversion Heq ; subst.
  destruct (polarity A) as [Hs | Ha].
  + assert (H1 := IHpi _ _ _ _ (polconts _ _ Hs)).
    rewrite <- (polconts _ (l1' ++ A' :: l2') Hs) in H1.
    rewrite <- (polconts _ (l1' ++ B' :: l2') Hs) in H1.
    destruct H1 as [[pi1' Hs1] [pi1'' Hs2]].
    split ; [ exists (de_fr _ _ pi1')
            | exists (de_fr _ _ pi1'') ] ; cbn...
  + assert (polcont (l1' ++ awith A' B' :: l2') A = (A :: l1') ++ awith A' B' :: l2')
      as Hpa by (rewrite (polconta _ _ Ha) ; rewrite app_comm_cons ; reflexivity).
    assert (H1 := IHpi _ _ _ _ Hpa).
    rewrite <- 2 app_comm_cons in H1.
    rewrite <- (polconta _ (l1' ++ A' :: l2') Ha) in H1.
    rewrite <- (polconta _ (l1' ++ B' :: l2') Ha) in H1.
    destruct H1 as [[pi1' Hs1] [pi1'' Hs2]].
    split ; [ exists (de_fr _ _ pi1')
            | exists (de_fr _ _ pi1'') ] ; cbn...
- destruct l1' ; inversion Heq ; subst.
  destruct (IHpi _ _ _ _ eq_refl) as [[pi1' Hs1] [pi1'' Hs2]].
  split ; [ exists (wk_fr _ _ _ pi1')
          | exists (wk_fr _ _ _ pi1'') ] ; cbn...
- destruct l1' ; inversion Heq ; subst.
  assert (wn A :: wn A :: l1' ++ awith A' B' :: l2'
       = (wn A :: wn A :: l1') ++ awith A' B' :: l2')
    as Heql by (list_simpl ; reflexivity).
  assert (H0 := IHpi _ _ _ _ Heql).
  rewrite <- ? app_comm_cons in H0.
  destruct H0 as [[pi1' Hs1] [pi1'' Hs2]].
  split ; [ exists (co_fr _ _ _ pi1')
          | exists (co_fr _ _ _ pi1'') ] ; cbn...
Qed.

Lemma with_rev1_f : forall l Pi (pi : llfoc l Pi),
  forall A B l1 l2, l = l1 ++ awith A B :: l2 ->
    { pi' : llfoc (l1 ++ A :: l2) Pi | fpsize pi' < fpsize pi }.
Proof.
intros l Pi pi A B l1 l2 Heq.
eapply with_rev_f in Heq.
apply Heq.
Qed.

Lemma with_rev2_f : forall l Pi (pi : llfoc l Pi),
  forall A B l1 l2, l = l1 ++ awith A B :: l2 ->
    { pi' : llfoc (l1 ++ B :: l2) Pi | fpsize pi' < fpsize pi }.
Proof.
intros l Pi pi A B l1 l2 Heq.
eapply with_rev_f in Heq.
apply Heq.
Qed.

Lemma llfoc_to_ll : forall l Pi, llfoc l Pi ->
   (Pi = None -> ll_ll l)
 * (forall C, Pi = Some C -> ll_ll (C :: l)).
Proof with (try (cbn; Permutation_Type_solve)) ; myeeasy.
intros l Pi pi ; induction pi ;
  (split ; [ intros HN ; inversion HN ; subst
           | intros D HD ; inversion HD ; subst ]);
  try (destruct IHpi as [IHpiN IHpiS]) ;
  try (destruct IHpi1 as [IHpi1N IHpi1S]) ;
  try (destruct IHpi2 as [IHpi2N IHpi2S]) ;
  try (assert (pi0' := IHpiS _ eq_refl)) ;
  try (assert (pi1' := IHpi1S _ eq_refl)) ;
  try (assert (pi2' := IHpi2S _ eq_refl)) ;
  try (assert (pi0' := IHpiN eq_refl)) ;
  try (assert (pi1' := IHpi1N eq_refl)) ;
  try (assert (pi2' := IHpi2N eq_refl)) ;
  try (now (constructor ; myeeasy));
  try (now (eapply ex_r ;
             [ | apply Permutation_Type_swap ] ; constructor ; myeeasy))...
- eapply ex_r ; [ eassumption | ]...
- eapply ex_r ; [ eassumption | ]...
- destruct (polarity A) as [HsA | HaA].
  + rewrite_all (polconts A l1 HsA).
    rewrite_all (polfocs A HsA).
    assert (pi1' := IHpi1S _ eq_refl).
    destruct (polarity B) as [HsB | HaB].
    * rewrite_all (polconts B l2 HsB).
      rewrite_all (polfocs B HsB).
      assert (pi2' := IHpi2S _ eq_refl).
      eapply ex_r ; [ apply tens_r ; [ eapply pi1' | eapply pi2' ] | ]...
    * rewrite_all (polconta B l2 HaB).
      rewrite_all (polfoca B HaB).
      assert (pi2' := IHpi2N eq_refl).
      eapply ex_r ; [ apply tens_r ; [ eapply pi1' | eapply pi2' ] | ]...
  + rewrite_all (polconta A l1 HaA).
    rewrite_all (polfoca A HaA).
    assert (pi1' := IHpi1N eq_refl).
    destruct (polarity B) as [HsB | HaB].
    * rewrite_all (polconts B l2 HsB).
      rewrite_all (polfocs B HsB).
      assert (pi2' := IHpi2S _ eq_refl).
      eapply ex_r ; [ apply tens_r ; [ eapply pi1' | eapply pi2' ] | ]...
    * rewrite_all (polconta B l2 HaB).
      rewrite_all (polfoca B HaB).
      assert (pi2' := IHpi2N eq_refl).
      eapply ex_r ; [ apply tens_r ; [ eapply pi1' | eapply pi2' ] | ]...
- eapply ex_r ; [ apply parr_r | apply Permutation_Type_swap ].
  eapply ex_r ; [ eassumption | ]...
- destruct (polarity A) as [Hs | Ha].
  + rewrite_all (polconts A l Hs).
    rewrite_all (polfocs A Hs).
    apply plus_r1.
    apply IHpiS...
  + rewrite_all (polconta A l Ha).
    rewrite_all (polfoca A Ha).
    apply plus_r1.
    apply IHpiN...
- destruct (polarity A) as [Hs | Ha].
  + rewrite_all (polconts A l Hs).
    rewrite_all (polfocs A Hs).
    apply plus_r2.
    apply IHpiS...
  + rewrite_all (polconta A l Ha).
    rewrite_all (polfoca A Ha).
    apply plus_r2.
    apply IHpiN...
- eapply ex_r ; [ apply with_r | apply Permutation_Type_swap ].
  + eapply ex_r ; [ apply pi1' | apply Permutation_Type_swap ].
  + eapply ex_r ; [ apply pi2' | apply Permutation_Type_swap ].
- destruct (polarity A) as [Hs | Ha].
  + rewrite_all (polconts A l Hs).
    rewrite_all (polfocs A Hs).
    apply de_r.
    apply IHpiS...
  + rewrite_all (polconta A l Ha).
    rewrite_all (polfoca A Ha).
    apply de_r.
    apply IHpiN...
- eapply ex_r ; [ apply co_r | apply Permutation_Type_swap ].
  eapply ex_r ; [ eassumption | ]...
Qed.


(** ** The strongly focused system [llFoc] *)

Definition Foc x := (sformula x + { X | x = covar X } + { y | x = wn y })%type.

Lemma Foc_dec x : Foc x + (Foc x -> False).
Proof.
induction x ;
  try (now (left ; left ; left ; constructor)) ;
  try (now (left ; left ; right ; eexists ; reflexivity)) ;
  try (now (left ; right ; eexists ; reflexivity)) ;
  try (now (right ; reflexivity)) ;
  try (now (right ; intros [[ H | [X H] ] | [X H] ] ; inversion H)).
Qed.

Lemma Focl_dec l : Forall_inf Foc l + (Forall_inf Foc l -> False).
Proof.
induction l.
- left; constructor.
- destruct (Foc_dec a).
  + destruct IHl.
    * left; constructor; assumption.
    * now right; intros H; inversion_clear H.
  + now right; intros H; inversion_clear H.
Qed.

Lemma not_Foc x : (Foc x -> False) ->
  (x = bot) + {'(y1, y2) | x = parr y1 y2 } +
  (x = top) + {'(y1, y2) | x = awith y1 y2 }.
Proof.
destruct x; intros HnF ;
  try (now (exfalso; apply HnF; left; left; constructor));
  try (now (exfalso; apply HnF; left; left; right; eexists; reflexivity));
  try (now (exfalso; apply HnF; left; right; eexists; reflexivity));
  try (now (exfalso; apply HnF; right; eexists; reflexivity)).
- left; left; left; reflexivity.
- left; left; right; exists (x1,x2); reflexivity.
- left; right; reflexivity.
- right; exists (x1,x2); reflexivity.
Qed.

Lemma not_Focl l : (Forall_inf Foc l -> False) ->
  {'(A, l1, l2) & l = l1 ++ A :: l2
                & ((A = bot) + {'(A1, A2) | A = parr A1 A2 }
                 + (A = top) + {'(A1, A2) | A = awith A1 A2 })%type }.
Proof.
intros HnF%Forall_inf_neg_Exists_inf.
- induction l; inversion HnF; subst.
  + exists (a, nil, l); [ reflexivity | ].
    apply (not_Foc _ H0).
  + apply IHl in X as [[[b l1] l2] Heq Hf]; subst.
    now exists (b, a::l1, l2).
- intros x.
  destruct (Foc_dec x); auto.
Qed.

Inductive llFoc : list formula -> option formula -> Type :=
| ax_Fr : forall X, llFoc (covar X :: nil) (Some (var X))
| ex_Fr : forall l1 l2 Pi, llFoc l1 Pi -> Permutation_Type l1 l2 ->
                           llFoc l2 Pi
| foc_Fr : forall A l, llFoc l (Some A) ->
                       llFoc (A :: l) None
| one_Fr : llFoc nil (Some one)
| bot_Fr : forall l, llFoc l None -> llFoc (bot :: l) None
| tens_Fr : forall A B l1 l2,
                    llFoc (polcont l1 A) (polfoc A) ->
                    llFoc (polcont l2 B) (polfoc B) ->
                    Forall_inf Foc l1 -> Forall_inf Foc l2 ->
                    llFoc (l1 ++ l2) (Some (tens A B))
| parr_Fr : forall A B l, llFoc (A :: B :: l) None ->
                          llFoc (parr A B :: l) None
| top_Fr : forall l, Forall_inf tFoc l -> llFoc (top :: l) None
| plus_Fr1 : forall A B l, llFoc (polcont l A) (polfoc A) ->
                           Forall_inf Foc l ->
                           llFoc l (Some (aplus A B))
| plus_Fr2 : forall A B l, llFoc (polcont l A) (polfoc A) ->
                           Forall_inf Foc l ->
                           llFoc l (Some (aplus B A))
| with_Fr : forall A B l, llFoc (A :: l) None ->
                          llFoc (B :: l) None ->
                          llFoc (awith A B :: l) None
| oc_Fr : forall A l, llFoc (A :: map wn l) None ->
                      llFoc (map wn l) (Some (oc A))
| de_Fr : forall A l, llFoc (polcont l A) (polfoc A) ->
                      Forall_inf Foc l -> llFoc (wn A :: l) None
| wk_Fr : forall A l, llFoc l None -> Forall_inf Foc l -> llFoc (wn A :: l) None
| co_Fr : forall A l, llFoc (wn A :: wn A :: l) None ->
                      Forall_inf Foc l -> llFoc (wn A :: l) None.

Instance llFoc_perm {Pi} :
  Proper ((@Permutation_Type _) ==> arrow) (fun l => llFoc l Pi).
Proof. intros l1 l2 HP pi; apply (ex_Fr l1); assumption. Qed.

Lemma top_gen_Fr l : llFoc (top :: l) None.
Proof.
remember (list_sum (map fsize l)) as n; revert l Heqn ; induction n using lt_wf_rect; intros l ->.
destruct (tFocl_dec l).
- apply top_Fr; assumption.
- apply not_tFocl in f.
  destruct f as [ [[A l1] l2] -> [[-> | [[B C] ->]] | [[B C] ->]] ].
  + rewrite app_comm_cons.
    eapply ex_Fr; [ apply bot_Fr | apply Permutation_Type_middle ].
    list_simpl; eapply X; [ | reflexivity ].
    cbn; rewrite 2 map_app, 2 list_sum_app; simpl; lia.
  + rewrite app_comm_cons.
    eapply ex_Fr; [ apply parr_Fr | apply Permutation_Type_middle ].
    list_simpl; eapply ex_Fr;
    [ eapply X; trivial
    | etransitivity ; [ apply Permutation_Type_swap
                      | apply (Permutation_Type_cons eq_refl) ;
                        etransitivity ; [ apply Permutation_Type_swap | reflexivity ]]].
    cbn; rewrite 2 map_app, 2 list_sum_app; simpl; lia.
  + rewrite app_comm_cons.
    eapply ex_Fr; [ apply with_Fr | apply Permutation_Type_middle ].
    * list_simpl; eapply ex_Fr;
        [ eapply X; trivial
        | etransitivity; [ apply Permutation_Type_swap | apply Permutation_Type_cons; reflexivity ]].
      cbn; rewrite 2 map_app, 2 list_sum_app ; simpl; lia.
    * list_simpl; eapply ex_Fr;
        [ eapply X; trivial
        | etransitivity; [ apply Permutation_Type_swap | apply Permutation_Type_cons; reflexivity ]].
    cbn; rewrite 2 map_app, 2 list_sum_app ; simpl; lia.
Qed.

Lemma sync_focus_F l A : llFoc l (Some A) -> sformula A.
Proof.
intros pi.
remember (Some A) as Pi; revert HeqPi; induction pi; intros HeqPi ;inversion HeqPi; subst;
  try (now constructor); auto.
Qed.

Lemma Foc_context l A : llFoc l (Some A) -> Forall_inf Foc l.
Proof.
intros pi.
remember (Some A) as Pi; revert A HeqPi; induction pi; intros P HeqPi; subst;
  try (now inversion HeqPi).
- constructor ; [ | constructor ].
  left; right; exists X; reflexivity.
- specialize (IHpi P eq_refl).
  apply (Permutation_Type_Forall_inf p IHpi).
- apply Forall_inf_app; assumption.
- clear; remember (map wn l) as l0; revert l Heql0; induction l0; intros [ | B l ] Heql0 ;
    inversion Heql0; subst; constructor.
  + right; exists B; reflexivity.
  + apply (IHl0 l); reflexivity.
Qed.

Lemma llFoc_foc_is_llFoc_foc l A : llFoc l (Some A) -> llFoc (polcont l A) (polfoc A).
Proof.
intros pi.
assert (Hs := sync_focus_F _ _ pi).
rewrite (polconts _ _ Hs), (polfocs _ Hs); assumption.
Qed.


(** ** Reversing *)

Lemma bot_rev_F l1 l2 Pi : llFoc (l1 ++ bot :: l2) Pi -> llFoc (l1 ++ l2) Pi.
Proof.
intros pi; remember (l1 ++ bot :: l2) as l; revert l1 l2 Heql.
induction pi; intros l1' l2' Heql; subst.
- destruct l1'; inversion Heql.
  destruct l1'; inversion H1.
- destruct (Permutation_Type_vs_elt_inv _ _ _ p) as [(l1p, l2p) ->].
  apply Permutation_Type_app_inv in p.
  apply (ex_Fr (l1p ++ l2p)); auto.
- destruct l1'; inversion Heql; subst.
  + exfalso.
    apply sync_focus_F in pi.
    inversion pi.
  + cbn; apply foc_Fr, IHpi; reflexivity.
- exfalso; destruct l1'; inversion Heql.
- destruct l1'; inversion Heql; subst; auto.
  cbn; apply bot_Fr, IHpi; reflexivity.
- exfalso.
  dichot_elt_app_inf_exec Heql; subst.
  + apply Forall_inf_app_r in f.
    inversion f.
    destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
  + apply Forall_inf_app_r in f0.
    inversion f0.
    destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
- destruct l1'; inversion Heql; subst.
  cbn; apply parr_Fr.
  rewrite 2 app_comm_cons.
  apply IHpi; reflexivity.
- destruct l1'; inversion Heql; subst.
  cbn; apply top_gen_Fr.
- exfalso.
  apply Forall_inf_app_r in f; inversion f.
  destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
- exfalso.
  apply Forall_inf_app_r in f; inversion f.
  destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
- destruct l1'; inversion Heql; subst.
  cbn; apply with_Fr.
  + rewrite app_comm_cons; apply IHpi1; reflexivity.
  + rewrite app_comm_cons; apply IHpi2; reflexivity.
- exfalso; decomp_map_inf Heql; subst.
  inversion Heql3.
- exfalso; destruct l1'; inversion Heql; subst.
  apply Forall_inf_app_r in f; inversion f.
  destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
- exfalso; destruct l1'; inversion Heql; subst.
  apply Forall_inf_app_r in f; inversion f.
  destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
- exfalso; destruct l1'; inversion Heql; subst.
  apply Forall_inf_app_r in f; inversion f.
  destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
Qed.

Lemma parr_rev_F A1 A2 l1 l2 Pi :
  llFoc (l1 ++ parr A1 A2 :: l2) Pi -> llFoc (l1 ++ A1 :: A2 :: l2) Pi.
Proof.
intros pi; remember (l1 ++ parr A1 A2 :: l2) as l; revert A1 A2 l1 l2 Heql.
induction pi; intros A1 A2 l1' l2' Heql; subst.
- destruct l1'; inversion Heql.
  destruct l1'; inversion H1.
- destruct (Permutation_Type_vs_elt_inv _ _ _ p) as [(l1p, l2p) ->].
  apply Permutation_Type_app_inv, (Permutation_Type_elt A2), (Permutation_Type_elt A1) in p.
  apply (ex_Fr (l1p ++ A1 :: A2 :: l2p)); auto.
- destruct l1'; inversion Heql; subst.
  + exfalso.
    apply sync_focus_F in pi.
    inversion pi.
  + cbn; apply foc_Fr, IHpi; reflexivity.
- exfalso; destruct l1'; inversion Heql.
- destruct l1'; inversion Heql; subst.
  cbn; apply bot_Fr, IHpi; reflexivity.
- exfalso.
  dichot_elt_app_inf_exec Heql; subst.
  + apply Forall_inf_app_r in f.
    inversion f.
    destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
  + apply Forall_inf_app_r in f0.
    inversion f0.
    destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
- destruct l1'; inversion Heql; subst; auto.
  cbn; apply parr_Fr.
  rewrite 2 app_comm_cons.
  apply IHpi; reflexivity.
- destruct l1'; inversion Heql; subst.
  cbn; apply top_gen_Fr.
- exfalso.
  apply Forall_inf_app_r in f; inversion f.
  destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
- exfalso.
  apply Forall_inf_app_r in f; inversion f.
  destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
- destruct l1'; inversion Heql; subst.
  cbn; apply with_Fr.
  + rewrite app_comm_cons; apply IHpi1; reflexivity.
  + rewrite app_comm_cons; apply IHpi2; reflexivity.
- exfalso; decomp_map_inf Heql; subst.
  inversion Heql3.
- exfalso; destruct l1'; inversion Heql; subst.
  apply Forall_inf_app_r in f; inversion f.
  destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
- exfalso; destruct l1'; inversion Heql; subst.
  apply Forall_inf_app_r in f; inversion f.
  destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
- exfalso; destruct l1'; inversion Heql; subst.
  apply Forall_inf_app_r in f; inversion f.
  destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
Qed.

Lemma with_rev_F A1 A2 l1 l2 Pi :
  llFoc (l1 ++ awith A1 A2 :: l2) Pi -> llFoc (l1 ++ A1 :: l2) Pi * llFoc (l1 ++ A2 :: l2) Pi.
Proof.
intros pi; remember (l1 ++ awith A1 A2 :: l2) as l; revert A1 A2 l1 l2 Heql.
induction pi; intros A1 A2 l1' l2' Heql; subst.
- destruct l1'; inversion Heql.
  destruct l1'; inversion H1.
- destruct (Permutation_Type_vs_elt_inv _ _ _ p) as [(l1p, l2p) ->].
  apply Permutation_Type_app_inv in p.
  split.
  + apply (Permutation_Type_elt A1) in p.
    apply (ex_Fr (l1p ++ A1 :: l2p)); [ apply (IHpi A1 A2) | ]; auto.
  + apply (Permutation_Type_elt A2) in p.
    apply (ex_Fr (l1p ++ A2 :: l2p)); [ apply (IHpi A1 A2) | ]; auto.
- destruct l1'; inversion Heql; subst.
  + exfalso.
    apply sync_focus_F in pi.
    inversion pi.
  + cbn; split; apply foc_Fr, (IHpi A1 A2); reflexivity.
- exfalso; destruct l1'; inversion Heql.
- destruct l1'; inversion Heql; subst.
  cbn; split; apply bot_Fr, (IHpi A1 A2); reflexivity.
- exfalso.
  dichot_elt_app_inf_exec Heql; subst.
  + apply Forall_inf_app_r in f.
    inversion f.
    destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
  + apply Forall_inf_app_r in f0.
    inversion f0.
    destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
- destruct l1'; inversion Heql; subst.
  cbn; split; apply parr_Fr; rewrite 2 app_comm_cons; apply (IHpi A1 A2); reflexivity.
- destruct l1'; inversion Heql; subst.
  cbn; split; apply top_gen_Fr.
- exfalso.
  apply Forall_inf_app_r in f; inversion f.
  destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
- exfalso.
  apply Forall_inf_app_r in f; inversion f.
  destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
- destruct l1'; inversion Heql; subst; auto.
  cbn; split; apply with_Fr.
  + rewrite app_comm_cons; apply (IHpi1 A1 A2); reflexivity.
  + rewrite app_comm_cons; apply (IHpi2 A1 A2); reflexivity.
  + rewrite app_comm_cons; apply (IHpi1 A1 A2); reflexivity.
  + rewrite app_comm_cons; apply (IHpi2 A1 A2); reflexivity.
- exfalso; decomp_map_inf Heql; subst.
  inversion Heql3.
- exfalso; destruct l1'; inversion Heql; subst.
  apply Forall_inf_app_r in f; inversion f.
  destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
- exfalso; destruct l1'; inversion Heql; subst.
  apply Forall_inf_app_r in f; inversion f.
  destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
- exfalso; destruct l1'; inversion Heql; subst.
  apply Forall_inf_app_r in f; inversion f.
  destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
Qed.

Lemma reversing l1 l2 l0:
  (forall lf, Forall_inf Foc lf -> llFoc (l1 ++ lf) None -> llFoc (l2 ++ lf) None) ->
  llFoc (l1 ++ l0) None -> llFoc (l2 ++ l0) None.
Proof.
enough (forall l l1 l2 l0 lf,
  (forall lf, Forall_inf Foc lf -> llFoc (l1 ++ lf) None -> llFoc (l2 ++ lf) None) ->
  Forall_inf Foc lf -> Permutation_Type l (l1 ++ lf ++ l0) ->
  llFoc l None -> llFoc (l2 ++ lf ++ l0) None) as Hgen.
{ intros.
  rewrite <- (app_nil_l l0).
  apply Hgen with (l1 ++ l0) l1; auto. }
clear l1 l2 l0; intros l l1 l2 l0 lf.
remember (list_sum (map fsize l0)) as n; revert l0 lf l Heqn.
induction n using lt_wf_rect; intros l0 lf l -> HFoc HF HP pi.
destruct l0 as [|A l0].
- apply HFoc; [ now rewrite app_nil_r | ].
  apply (ex_Fr _ _ _ pi HP).
- destruct (Foc_dec A).
  + replace (l2 ++ lf ++ A :: l0) with (l2 ++ (lf ++ A :: nil) ++ l0) by now rewrite <- app_assoc.
    apply X with (list_sum (map fsize l0)) l; rewrite <- ? app_assoc; auto.
    * assert (Hs := fsize_pos A); simpl; lia.
    * apply Forall_inf_app; auto.
  + apply not_Foc in f as [[[ -> | [(A1, A2) ->]] | ->] | [(A1, A2) ->]]; cbn.
    * apply (ex_Fr (bot :: l2 ++ lf ++ l0)); [ | Permutation_Type_solve ].
      apply bot_Fr.
      apply X with (list_sum (map fsize l0)) (l1 ++ lf ++ l0); auto.
      rewrite app_assoc; apply bot_rev_F; rewrite <- app_assoc.
      apply (ex_Fr _ _ _ pi HP).
    * apply (ex_Fr (parr A1 A2 :: l2 ++ lf ++ l0)); [ | Permutation_Type_solve ].
      apply parr_Fr.
      apply (ex_Fr (l2 ++ lf ++ A1 :: A2 :: l0)); [ | Permutation_Type_solve ].
      apply X with (list_sum (map fsize (A1 :: A2 :: l0))) (l1 ++ lf ++ A1 :: A2 :: l0);
        simpl; auto; try lia.
      rewrite app_assoc; apply parr_rev_F; rewrite <- app_assoc.
      apply (ex_Fr _ _ _ pi HP).
    * apply (ex_Fr (top :: l2 ++ lf ++ l0)); [ | Permutation_Type_solve ].
      apply top_gen_Fr.
    * apply (ex_Fr (awith A1 A2 :: l2 ++ lf ++ l0)); [ | Permutation_Type_solve ].
      apply with_Fr.
      -- apply (ex_Fr (l2 ++ lf ++ A1 :: l0)); [ | Permutation_Type_solve ].
         apply X with (list_sum (map fsize (A1 :: l0))) (l1 ++ lf ++ A1 :: l0);
           simpl; auto; try lia.
         rewrite app_assoc; apply (with_rev_F A1 A2); rewrite <- app_assoc.
         apply (ex_Fr _ _ _ pi HP).
      -- apply (ex_Fr (l2 ++ lf ++ A2 :: l0)); [ | Permutation_Type_solve ].
         apply X with (list_sum (map fsize (A2 :: l0))) (l1 ++ lf ++ A2 :: l0);
           simpl; auto; try lia.
         rewrite app_assoc; apply (with_rev_F A1 A2); rewrite <- app_assoc.
         apply (ex_Fr _ _ _ pi HP).
Qed.

Lemma wk_gen_Fr A l : llFoc l None -> llFoc (wn A :: l) None.
Proof.
rewrite <- (app_nil_l l), app_comm_cons; apply reversing.
clear l; cbn; intros l Hf pi; apply wk_Fr; auto.
Qed.

Lemma co_gen_Fr A l : llFoc (wn A :: wn A :: l) None -> llFoc (wn A :: l) None.
Proof.
rewrite <- (app_nil_l l), ? app_comm_cons; apply reversing.
clear l; cbn; intros l Hf pi; apply co_Fr; auto.
Qed.


(** ** Strong focusing *)

Lemma incl_Foc : forall l l0 lw lw', llFoc l None ->
  Permutation_Type l (map wn lw ++ l0) -> incl_inf lw lw' ->
    llFoc (map wn lw' ++ l0) None.
Proof.
intros l l0 lw; revert l l0; induction lw; intros l l0 lw' pi HP Hsub.
- clear Hsub; induction lw'.
  + apply (ex_Fr _ _ _ pi HP).
  + cbn; apply wk_gen_Fr; assumption.
- destruct (incl_inf_cons_inv Hsub) as [Hin Hi].
  apply (IHlw l (wn a :: l0) lw') in pi ; [ | | apply Hi ].
  + apply in_inf_split in Hin as [(l1, l2) ->].
    apply (ex_Fr ((wn a :: nil) ++ map wn l1 ++ map wn l2 ++ l0));
      [ | list_simpl; apply Permutation_Type_cons_app; reflexivity ].
    cbn; apply co_gen_Fr.
    apply (ex_Fr _ _ _ pi); list_simpl.
    symmetry ; apply Permutation_Type_cons_app.
    rewrite 2 app_assoc; apply Permutation_Type_cons_app; reflexivity.
  + etransitivity ; [ apply HP | ].
    cbn ; apply Permutation_Type_middle.
Qed.

Theorem llfoc_to_llFoc : forall s l Pi (pi : llfoc l Pi), fpsize pi < s ->
   (Pi = None -> llFoc l None)
 * (forall C, Pi = Some C -> Forall_inf Foc l ->
       { l' & { lw1 & { lw2 & prod (Permutation_Type l (map wn lw1 ++ l'))
                             (prod (incl_inf lw2 lw1)
                                   (llFoc (map wn lw2 ++ l') (Some C))) }}})
 * (forall C, Pi = Some C -> (Forall_inf Foc l -> False) ->
      (llFoc (C :: l) None) * llFoc (wn C :: l) None).
Proof with myeeasy.
  induction s using lt_wf_rect;
    intros l pi ; split ; [ split | ] ;
    [ intros Heq ; destruct pi0 ; inversion Heq ; subst ; cbn in H
    | intros PPi Heq HF ; destruct pi0 ; inversion Heq ; subst ; cbn in H
    | intros C Heq HnF ].
(* first conjunct *)
- specialize X with (S (fpsize pi0)) _ _ pi0.
  apply X in H...
  apply H in H0.
  eapply ex_Fr ; [ apply H0 | ]...
- specialize X with (S (fpsize pi0)) _ _ pi0.
  apply X in H...
  destruct (Focl_dec l).
  + eapply (snd (fst H)) in f...
    destruct f as (l1 & lw & lw' & HP & Hi & IH).
    cbn in HP ; cbn in Hi ; cbn in IH.
    apply (Permutation_Type_cons_app _ _ A) in HP.
    symmetry in HP.
    eapply ex_Fr...
    eapply incl_Foc...
    eapply ex_Fr ; [ apply foc_Fr | ]...
    apply Permutation_Type_cons_app...
  + eapply (snd H) in f...
    apply f.
- specialize X with (S (fpsize pi0)) _ _ pi0.
  apply X in H...
  apply H in H0...
  apply bot_Fr...
- specialize X with (S (fpsize pi0)) _ _ pi0.
  apply X in H...
  apply H in H0...
  apply parr_Fr...
- apply top_Fr...
- assert (X' := X).
  assert (H' := H).
  assert (H0' := H0).
  specialize X with (S (max (fpsize pi0_1) (fpsize pi0_2))) _ _ pi0_1.
  apply X in H...
  specialize X' with (S (max (fpsize pi0_1) (fpsize pi0_2))) _ _ pi0_2.
  apply X' in H'...
  apply H in H0...
  apply H' in H0'...
  apply with_Fr...
- specialize X with (S (fpsize pi0)) _ _ pi0.
  apply X in H...
  destruct (polarity A) as [Hs | Ha].
  + rewrite (polconts _ _ Hs), (polfocs _ Hs) in H.
    destruct (Focl_dec l).
    * eapply (snd (fst H)) in f...
      destruct f as (l1 & lw & lw' & HP & Hi & IH).
      apply (Permutation_Type_cons_app _ _ (wn A)) in HP.
      symmetry in HP.
      eapply ex_Fr...
      eapply incl_Foc...
      apply (ex_Fr (wn A :: map wn lw' ++ l1)).
      apply de_Fr.
      -- apply (llFoc_foc_is_llFoc_foc _ _ IH).
      -- apply (Foc_context _ _ IH).
      -- apply Permutation_Type_cons_app; reflexivity.
    * eapply (snd H) in f...
      apply f.
  + rewrite (polconta _ _ Ha),(polfoca _ Ha) in H.
    apply H in Heq...
    change (wn A :: l) with ((wn A :: nil) ++ l).
    apply (reversing (A :: nil)); auto.
    clear - Ha; cbn; intros l Hf pi.
    apply de_Fr; auto.
    rewrite (polconta _ _ Ha), (polfoca _ Ha); assumption.
- specialize X with (S (fpsize pi0)) _ _ pi0.
  apply X in H...
  apply wk_gen_Fr.
  apply H...
- specialize X with (S (fpsize pi0)) _ _ pi0.
  apply X in H...
  apply co_gen_Fr.
  apply H...
(* second conjunct *)
- exists (covar X0 :: nil), nil, nil ; nsplit 3...
  + apply incl_inf_nil_l.
  + apply ax_Fr.
- symmetry in p.
  specialize X with (S (fpsize pi0)) _ _ pi0.
  apply X in H...
  apply (snd (fst H)) in H0.
  + destruct H0 as (l0 & lw & lw' & HP & Hi & IH).
    cbn in HP ; cbn in Hi ; cbn in IH.
    exists l0, lw, lw' ; cbn ; nsplit 3...
    etransitivity...
  + apply (Permutation_Type_Forall_inf p)...
- exists nil, nil, nil ; cbn ; nsplit 3...
  + apply incl_inf_nil_l.
  + apply one_Fr.
- exfalso.
  inversion HF; subst.
  destruct X0 as [[H' | [X' H']] | [X' H']]; inversion H'.
- assert (HF1 := Forall_inf_app_l _ _ HF).
  assert (HF2 := Forall_inf_app_r _ _ HF).
  assert (X':=X).
  assert (H' := H).
  assert (Heq' := Heq).
  specialize X with (S (fpsize pi0_1 + fpsize pi0_2)) _ _ pi0_1.
  apply X in H...
  specialize X' with (S (fpsize pi0_1 + fpsize pi0_2)) _ _ pi0_2.
  apply X' in H'...
  destruct (polarity A) as [HsA | HaA] ; destruct (polarity B) as [HsB | HaB].
  + rewrite (polconts _ _ HsA) in H.
    rewrite (polfocs _ HsA) in H.
    rewrite (polconts _ _ HsB) in H'.
    rewrite (polfocs _ HsB) in H'.
    eapply (snd (fst H)) in HF1...
    eapply (snd (fst H')) in HF2...
    destruct HF1 as (l01 & lw1 & lw1' & HP1 & Hi1 & pi1).
    cbn in HP1 ; cbn in Hi1 ; cbn in pi1.
    destruct HF2 as (l02 & lw2 & lw2' & HP2 & Hi2 & pi2).
    cbn in HP2 ; cbn in Hi2 ; cbn in pi2.
    exists (l01 ++ l02), (lw1 ++ lw2), (lw1' ++ lw2') ; cbn ; nsplit 3.
    * etransitivity ; [ apply (Permutation_Type_app HP1 HP2) | ].
      list_simpl.
      apply Permutation_Type_app_head.
      rewrite ? app_assoc.
      apply Permutation_Type_app_tail.
      apply Permutation_Type_app_comm.
    * apply incl_inf_app_app...
    * eapply ex_Fr ; [ apply tens_Fr | ].
      -- rewrite (polconts _ _ HsA).
         rewrite (polfocs _ HsA)...
      -- rewrite (polconts _ _ HsB).
         rewrite (polfocs _ HsB)...
      -- apply Foc_context in pi1...
      -- apply Foc_context in pi2...
      -- list_simpl.
         apply Permutation_Type_app_head.
         rewrite 2 app_assoc.
         apply Permutation_Type_app_tail.
         apply Permutation_Type_app_comm.
  + rewrite (polconts _ _ HsA) in H.
    rewrite (polfocs _ HsA) in H.
    rewrite (polconta _ _ HaB) in H'.
    rewrite (polfoca _ HaB) in H'.
    eapply (snd (fst H)) in HF1...
    destruct HF1 as (l01 & lw1 & lw1' & HP1 & Hi1 & pi1).
    cbn in HP1 ; cbn in Hi1 ; cbn in pi1.
    assert (pi2 := fst (fst H') eq_refl).
    exists (l01 ++ l2), lw1, lw1' ; cbn ; nsplit 3...
    * etransitivity ; [ apply (Permutation_Type_app_tail _ HP1) | ].
      rewrite <- app_assoc...
    * eapply ex_Fr ; [ apply tens_Fr | ].
      -- rewrite (polconts _ _ HsA), (polfocs _ HsA)...
      -- rewrite (polconta _ _ HaB), (polfoca _ HaB)...
      -- apply Foc_context in pi1...
      -- assumption.
      -- rewrite <- app_assoc...
  + rewrite (polconta _ _ HaA), (polfoca _ HaA) in H.
    rewrite (polconts _ _ HsB), (polfocs _ HsB) in H'.
    assert (pi1 := fst (fst H) eq_refl).
    eapply (snd (fst H')) in HF2...
    destruct HF2 as (l02 & lw2 & lw2' & HP2 & Hi2 & pi2).
    cbn in HP2 ; cbn in Hi2 ; cbn in pi2.
    exists (l1 ++ l02), lw2, lw2' ; cbn ; nsplit 3...
    * etransitivity ; [ apply (Permutation_Type_app_head _ HP2) | ].
      rewrite 2 app_assoc...
      apply Permutation_Type_app_tail.
      apply Permutation_Type_app_comm.
    * eapply ex_Fr ; [ apply tens_Fr | ].
      -- rewrite (polconta _ _ HaA), (polfoca _ HaA)...
      -- rewrite (polconts _ _ HsB), (polfocs _ HsB)...
      -- assumption.
      -- apply Foc_context in pi2...
      -- rewrite 2 app_assoc...
         apply Permutation_Type_app_tail.
         apply Permutation_Type_app_comm.
  + rewrite (polconta _ _ HaA) in H.
    rewrite (polfoca _ HaA) in H.
    rewrite (polconta _ _ HaB) in H'.
    rewrite (polfoca _ HaB) in H'.
    assert (pi1 := fst (fst H) eq_refl).
    assert (pi2 := fst (fst H') eq_refl).
    exists (l1 ++ l2), nil, nil ; cbn ; nsplit 3...
    * apply incl_inf_nil_l.
    * apply tens_Fr; auto.
      -- rewrite (polconta _ _ HaA), (polfoca _ HaA)...
      -- rewrite (polconta _ _ HaB), (polfoca _ HaB)...
- exfalso.
  inversion HF ; subst.
  destruct X0 as [[H' | [X' H']] | [X' H']] ; inversion H'.
- exfalso.
  inversion HF ; subst.
  destruct X0 as [[H' | [X' H']] | [X' H']] ; inversion H'.
- specialize X with (S (fpsize pi0)) _ _ pi0.
  apply X in H...
  destruct (polarity A) as [HsA | HaA].
  + rewrite (polconts _ _ HsA) in H.
    rewrite (polfocs _ HsA) in H.
    eapply (snd (fst H)) in HF ; [ | reflexivity ].
    destruct HF as (l0 & lw & lw' & HP & Hi & pi).
    cbn in HP ; cbn in Hi ; cbn in pi.
    exists l0, lw, lw' ; cbn ; nsplit 3...
    apply plus_Fr1.
    * rewrite (polconts _ _ HsA).
      rewrite (polfocs _ HsA)...
    * apply Foc_context in pi...
  + rewrite (polconta _ _ HaA) in H.
    rewrite (polfoca _ HaA) in H.
    assert (pi := fst (fst H) eq_refl).
    exists l, nil, nil ; cbn ; nsplit 3...
    * apply incl_inf_nil_l.
    * apply plus_Fr1...
      rewrite (polconta _ _ HaA).
      rewrite (polfoca _ HaA)...
- specialize X with (S (fpsize pi0)) _ _ pi0.
  apply X in H...
  destruct (polarity A) as [HsA | HaA].
  + rewrite (polconts _ _ HsA) in H.
    rewrite (polfocs _ HsA) in H.
    eapply (snd (fst H)) in HF ; [ | reflexivity ].
    destruct HF as (l0 & lw & lw' & HP & Hi & pi).
    cbn in HP ; cbn in Hi ; cbn in pi.
    exists l0, lw, lw' ; cbn ; nsplit 3...
    apply plus_Fr2.
    * rewrite (polconts _ _ HsA).
      rewrite (polfocs _ HsA)...
    * apply Foc_context in pi...
  + rewrite (polconta _ _ HaA) in H.
    rewrite (polfoca _ HaA) in H.
    assert (pi := fst (fst H) eq_refl).
    exists l, nil, nil ; cbn ; nsplit 3...
    * apply incl_inf_nil_l.
    * apply plus_Fr2...
      rewrite (polconta _ _ HaA).
      rewrite (polfoca _ HaA)...
- exfalso.
  inversion HF ; subst.
  destruct X0 as [[H' | [X' H']] | [X' H']] ; inversion H'.
- specialize X with (S (fpsize pi0)) _ _ pi0.
  apply X in H...
  assert (pi := fst (fst H) eq_refl).
  exists (map wn l), nil, nil ; cbn ; nsplit 3...
  * apply incl_inf_nil_l.
  * apply oc_Fr...
- inversion HF ; subst.
  specialize X with (S (fpsize pi0)) _ _ pi0.
  apply X in H...
  eapply (snd (fst H)) in X1 ; [ | reflexivity ].
  destruct X1 as (l0 & lw & lw' & HP & Hi & pi).
  cbn in HP ; cbn in Hi ; cbn in pi.
  exists l0, (A :: lw), lw' ; cbn ; nsplit 3...
  + list_simpl ; apply Permutation_Type_cons...
  + apply incl_inf_tl...
- inversion HF ; subst.
  assert (Forall_inf Foc (wn A :: wn A :: l)) as HF'
    by (constructor ; assumption).
  specialize X with (S (fpsize pi0)) _ _ pi0.
  apply X in H...
  eapply (snd (fst H)) in HF'...
  destruct HF' as (l0 & lw & lw' & HP & Hi & pi).
  cbn in HP ; cbn in Hi ; cbn in pi.
  symmetry in HP.
  assert (HP' := HP).
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as ((l1' & l2') & Heq) ; cbn in Heq.
  dichot_elt_app_inf_exec Heq ; subst.
  + symmetry in Heq0; decomp_map_inf Heq0 ; subst.
    inversion Heq0 ; subst.
    assert (HP' := HP).
    list_simpl in HP'.  
    symmetry in HP'.
    apply Permutation_Type_cons_app_inv in HP'.
    symmetry in HP'.
    apply Permutation_Type_vs_cons_inv in HP'.
    destruct HP' as ((l1' & l2') & Heq) ; cbn in Heq.
    rewrite app_assoc in Heq.
    dichot_elt_app_inf_exec Heq ; subst.
    * rewrite <- map_app in Heq1.
      symmetry in Heq1; decomp_map_inf Heq1 ; subst.
      inversion Heq1 ; subst.
      exists l0, (l3 ++ l5), lw' ; cbn ; nsplit 3...
      -- symmetry in HP.
         list_simpl in HP.
         apply Permutation_Type_cons_app_inv in HP.
         list_simpl...
      -- cbn in Hi ; cbn in Heq4 ; revert Hi Heq4 ; clear ;
           induction lw' ; intros Hi Heq.
         ++ apply incl_inf_nil_l.
         ++ destruct (incl_inf_cons_inv Hi) as [Hin Hi'].
            assert (HP := Permutation_Type_middle l3 l5 A).
            symmetry in HP ; apply (Permutation_Type_in_inf _ HP) in Hin.
            inversion Hin ; subst.
            ** apply incl_inf_cons.
               --- rewrite <- Heq.
                   apply in_inf_elt.
               --- apply IHlw'...
            ** apply incl_inf_cons...
               apply IHlw'...
    * exists (l2 ++ l2'), (l3 ++ A :: l5), (A :: lw') ; cbn ; nsplit 3...
      -- symmetry in HP.
         list_simpl in HP.
         apply Permutation_Type_cons_app_inv in HP.
         list_simpl.
         etransitivity ; [ apply HP | ].
         rewrite ? app_assoc.
         apply Permutation_Type_elt.
         list_simpl...
      -- apply incl_inf_cons...
         apply in_inf_elt.
      -- eapply ex_Fr...
         symmetry.
         rewrite ? app_assoc.
         apply Permutation_Type_cons_app...
  + assert (HP' := HP).
    list_simpl in HP'.  
    symmetry in HP'.
    rewrite app_assoc in HP'.
    apply Permutation_Type_cons_app_inv in HP'.
    symmetry in HP'.
    apply Permutation_Type_vs_cons_inv in HP'.
    destruct HP' as ((l1'' & l2'') & Heq).
    rewrite <- app_assoc in Heq.
    dichot_elt_app_inf_exec Heq ; subst.
    * symmetry in Heq0; decomp_map_inf Heq0 ; subst.
      inversion Heq0 ; subst.
      exists (l2 ++ l2'), (l3 ++ A :: l5), (A :: lw') ; cbn ; nsplit 3...
      -- symmetry in HP.
         list_simpl in HP.
         apply Permutation_Type_cons_app_inv in HP.
         list_simpl.
         etransitivity ; [ apply HP | ].
         rewrite ? app_assoc.
         apply Permutation_Type_elt.
         list_simpl...
      -- apply incl_inf_cons...
         apply in_inf_elt.
      -- eapply ex_Fr...
         symmetry.
         rewrite ? app_assoc.
         apply Permutation_Type_cons_app...
    * exists (l1 ++ l2''), (A :: lw), (A :: A :: lw') ; cbn ; nsplit 3...
      -- symmetry in HP.
         rewrite app_assoc in HP.
         apply Permutation_Type_cons_app_inv in HP.
         list_simpl.
         etransitivity ; [ apply HP | ].
         cbn in Heq1 ; list_simpl.
         rewrite <- Heq1...
         symmetry.
         rewrite ? app_assoc. 
         apply Permutation_Type_cons_app...
      -- apply incl_inf_cons ; [ | apply incl_inf_cons ]...
         ++ constructor...
         ++ constructor...
         ++ apply incl_inf_tl...
      -- eapply ex_Fr...
         symmetry.
         rewrite ? app_assoc.
         apply Permutation_Type_cons_app.
         list_simpl.
         rewrite <- Heq1.
         rewrite ? app_assoc.
         apply Permutation_Type_cons_app...
(* third conjunct *)
- apply not_Focl in HnF as [[[A l1] l2] -> [[[-> | ([B' C'] & Hp)] | Ht ] | ([B' C'] & Hw)]];
    subst; cbn; cbn in H; cbn in pi0.
  + destruct (bot_rev_f _ _ pi0 _ _ eq_refl) as [pi Hs].
    specialize X with (S (fpsize pi)) _ _ pi.
    assert (S (fpsize pi) < s) as Hs'...
    apply X in Hs'...
    destruct (Focl_dec (l1 ++ l2)) as [HF | HnF].
    * eapply (snd (fst Hs')) in HF...
      destruct HF as (l0 & lw & lw' & HP & Hi & pi').
      cbn in HP ; cbn in Hi ; cbn in pi'.
      split.
      -- apply foc_Fr in pi'.
         eapply (incl_Foc _ (C :: l0)) in pi'...
         ++ eapply ex_Fr ; [ apply bot_Fr | ]...
            rewrite (app_comm_cons _ _ C).
            apply Permutation_Type_cons_app.
            list_simpl ; symmetry.
            apply Permutation_Type_cons_app...
         ++ apply Permutation_Type_cons_app...
      -- assert (HC := sync_focus_F _ _ pi').
         apply llFoc_foc_is_llFoc_foc in pi'.
         apply de_Fr in pi'.
         ++ eapply (incl_Foc _ (wn C :: l0)) in pi'...
            ** eapply ex_Fr ; [ apply bot_Fr | ]...
               rewrite (app_comm_cons _ _ (wn C)).
               apply Permutation_Type_cons_app.
               list_simpl ; symmetry.
               apply Permutation_Type_cons_app...
            ** apply Permutation_Type_cons_app...
         ++ rewrite (polconts _ _ HC), (polfocs _ HC) in pi'.
            apply (Foc_context _ _ pi').
    * eapply (snd Hs') in HnF...
      destruct HnF as [pi1 pi2] ; split.
      -- eapply ex_Fr ; [ apply bot_Fr ; apply pi1 | ].
         rewrite (app_comm_cons _ (bot :: _) C).
         apply Permutation_Type_cons_app...
      -- eapply ex_Fr ; [ apply bot_Fr ; apply pi2 | ].
         rewrite (app_comm_cons _ (bot :: _) (wn C)).
         apply Permutation_Type_cons_app...
  + destruct (parr_rev_f _ _ pi0 _ _ _ _ eq_refl) as [pi Hs].
    specialize X with (S (fpsize pi)) _ _ pi.
    assert (S (fpsize pi) < s) as Hs'...
    apply X in Hs'...
    destruct (Focl_dec (l1 ++ B' :: C' :: l2)) as [HF | HnF].
    * eapply (snd (fst Hs')) in HF...
      destruct HF as (l0 & lw & lw' & HP & Hi & pi').
      cbn in HP ; cbn in Hi ; cbn in pi'.
      split.
      -- apply foc_Fr in pi'.
         eapply (incl_Foc _ (C :: l0)) in pi'...
         ++ eapply ex_Fr ; [ apply parr_Fr ; eapply ex_Fr | ]...
            ** symmetry.
               etransitivity ; [ | apply Permutation_Type_middle ].
               symmetry in HP ; symmetry.
               apply (@Permutation_Type_cons _ _ C eq_refl) in HP.
               etransitivity ; [ apply HP | ].
               rewrite app_comm_cons.
               symmetry.
               apply Permutation_Type_cons_app.
               apply Permutation_Type_cons_app...
            ** rewrite (app_comm_cons _ _ C).
               apply Permutation_Type_cons_app...
         ++ apply Permutation_Type_cons_app...
      -- assert (HC := sync_focus_F _ _ pi').
         apply llFoc_foc_is_llFoc_foc in pi'.
         apply de_Fr in pi'.
         ++ eapply (incl_Foc _ (wn C :: l0)) in pi'...
            ** eapply ex_Fr ; [ apply parr_Fr ; eapply ex_Fr | ]...
               --- symmetry.
                   etransitivity ; [ | apply Permutation_Type_middle ].
                   symmetry in HP ; symmetry.
                   apply (@Permutation_Type_cons _ _ (wn C) eq_refl) in HP.
                   etransitivity ; [ apply HP | ].
                   rewrite app_comm_cons.
                   symmetry.
                   apply Permutation_Type_cons_app.
                   apply Permutation_Type_cons_app...
               --- rewrite (app_comm_cons _ _ (wn C)).
                   apply Permutation_Type_cons_app...
            ** apply Permutation_Type_cons_app...
         ++ rewrite (polconts _ _ HC), (polfocs _ HC) in pi'.
            apply (Foc_context _ _ pi').
    * destruct ((snd Hs') _ eq_refl HnF) as [pi1 pi2] ; split.
      -- eapply ex_Fr ; [ apply parr_Fr ; eapply ex_Fr ; [ apply pi1 | ] | ]...
         ++ rewrite app_comm_cons.
            symmetry.
            apply Permutation_Type_cons_app.
            apply Permutation_Type_cons_app...
         ++ rewrite (app_comm_cons _ _ C).
            apply Permutation_Type_cons_app...
      -- eapply ex_Fr; [ apply parr_Fr; eapply ex_Fr; [ apply pi2 | ] | ]...
         ++ rewrite app_comm_cons.
            symmetry.
            apply Permutation_Type_cons_app.
            apply Permutation_Type_cons_app...
         ++ rewrite (app_comm_cons _ _ (wn C)).
            apply Permutation_Type_cons_app...
  + split ; (eapply ex_Fr ; [ apply top_gen_Fr | ])...
    * symmetry ; rewrite app_comm_cons.
      symmetry ; apply Permutation_Type_middle.
    * symmetry ; rewrite app_comm_cons.
      symmetry ; apply Permutation_Type_middle.
  + destruct (with_rev1_f _ _ pi0 _ _ _ _ eq_refl) as [pi1 Hs1].
    destruct (with_rev2_f _ _ pi0 _ _ _ _ eq_refl) as [pi2 Hs2].
    assert (X' := X).
    specialize X with (S (fpsize pi1)) _ _ pi1.
    assert (S (fpsize pi1) < s) as Hs1'...
    apply X in Hs1'...
    specialize X' with (S (fpsize pi2)) _ _ pi2.
    assert (S (fpsize pi2) < s) as Hs2'...
    apply X' in Hs2'...
    destruct (Focl_dec (l1 ++ l2)) as [HF | HnF].
    * assert (HF' := Forall_inf_app_l _ _ HF).
      assert (HF'' := Forall_inf_app_r _ _ HF).
      destruct (Foc_dec B') as [HFB | HnFB].
      -- assert (Forall_inf Foc (l1 ++ B' :: l2)) as HF1.
         { apply Forall_inf_app...
           constructor... }
         eapply (snd (fst Hs1')) in HF1...
         destruct HF1 as (l01 & lw1 & lw1' & HP1 & Hi1 & pi1').
         cbn in HP1 ; cbn in Hi1 ; cbn in pi1'.
         destruct (Foc_dec C') as [HFC | HnFC].
         ++ assert (Forall_inf Foc (l1 ++ C' :: l2)) as HF2.
            { apply Forall_inf_app...
              constructor... }
            eapply (snd (fst Hs2')) in HF2...
            destruct HF2 as (l02 & lw2 & lw2' & HP2 & Hi2 & pi2').
            cbn in HP2 ; cbn in Hi2 ; cbn in pi2'.
            split.
            ** apply foc_Fr in pi1'.
               apply foc_Fr in pi2'.
               eapply (incl_Foc _ (C :: l01) lw1') in pi1' ; 
                 [ eapply (incl_Foc _ (C :: l02) lw2') in pi2' | | ]...
               --- eapply ex_Fr ; [ apply with_Fr ; eapply ex_Fr | ].
                   +++ apply pi1'.
                   +++ symmetry.
                       etransitivity ; [ | apply Permutation_Type_middle ].
                       symmetry in HP1 ; symmetry.
                       apply (@Permutation_Type_cons _ _ C eq_refl) in HP1.
                       etransitivity ; [ apply HP1 | ].
                       rewrite app_comm_cons.
                       symmetry.
                       apply Permutation_Type_cons_app...
                   +++ apply pi2'.
                   +++ symmetry.
                       etransitivity ; [ | apply Permutation_Type_middle ].
                       symmetry in HP2 ; symmetry.
                       apply (@Permutation_Type_cons _ _ C eq_refl) in HP2.
                       etransitivity ; [ apply HP2 | ].
                       rewrite app_comm_cons.
                       symmetry.
                       apply Permutation_Type_cons_app...
                   +++ rewrite (app_comm_cons _ (awith _ _ :: _) C).
                       apply Permutation_Type_cons_app...
               --- apply Permutation_Type_cons_app...
               --- apply Permutation_Type_cons_app...
            ** assert (HC := sync_focus_F _ _ pi1').
               apply llFoc_foc_is_llFoc_foc in pi1'.
               apply llFoc_foc_is_llFoc_foc in pi2'.
               apply de_Fr in pi1'; [ apply de_Fr in pi2' | ].
               --- eapply (incl_Foc _ (wn C :: l01) lw1') in pi1' ; 
                     [ eapply (incl_Foc _ (wn C :: l02) lw2') in pi2' | | ]...
                   +++ eapply ex_Fr ; [ apply with_Fr ; eapply ex_Fr | ].
                       *** apply pi1'.
                       *** symmetry.
                           etransitivity ; [ | apply Permutation_Type_middle ].
                           symmetry in HP1 ; symmetry.
                           apply (@Permutation_Type_cons _ _ (wn C) eq_refl) in HP1.
                           etransitivity ; [ apply HP1 | ].
                           rewrite app_comm_cons.
                           symmetry.
                           apply Permutation_Type_cons_app...
                       *** apply pi2'.
                       *** symmetry.
                           etransitivity ; [ | apply Permutation_Type_middle ].
                           symmetry in HP2 ; symmetry.
                           apply (@Permutation_Type_cons _ _ (wn C) eq_refl) in HP2.
                           etransitivity ; [ apply HP2 | ].
                           rewrite app_comm_cons.
                           symmetry.
                           apply Permutation_Type_cons_app...
                       *** rewrite (app_comm_cons _ (awith _ _ :: _) (wn C)).
                           apply Permutation_Type_cons_app...
                   +++ apply Permutation_Type_cons_app...
                   +++ apply Permutation_Type_cons_app...
               --- rewrite (polconts _ _ HC), (polfocs _ HC) in pi2'.
                   apply (Foc_context _ _ pi2').
               --- rewrite (polconts _ _ HC), (polfocs _ HC) in pi1'.
                   apply (Foc_context _ _ pi1').
         ++ assert (Forall_inf Foc (l1 ++ C' :: l2) -> False) as HF2.
            { intros HF0.
              apply Forall_inf_app_r in HF0.
              inversion HF0 ; subst.
              apply HnFC... }
            eapply (snd Hs2') in HF2...
            destruct HF2 as [pi2' pi2''] ; split.
            ** eapply ex_Fr ; [ apply with_Fr | ].
               --- apply foc_Fr in pi1'.
                   eapply (incl_Foc _ (C :: l01) lw1') in pi1'.
                   +++ eapply ex_Fr ; [ apply pi1' | ].
                       etransitivity ; [ symmetry ; apply Permutation_Type_middle | ].
                       symmetry in HP1.
                       apply (@Permutation_Type_cons _ _ C eq_refl) in HP1.
                       etransitivity ; [ apply HP1 | ].
                       rewrite app_comm_cons.
                       symmetry.
                       apply Permutation_Type_middle.
                   +++ apply Permutation_Type_middle.
                   +++ apply Hi1.
               --- eapply ex_Fr ; [ apply pi2' | ].
                   rewrite app_comm_cons.
                   symmetry ; apply Permutation_Type_middle.
               --- rewrite (app_comm_cons _ _ C).
                   apply Permutation_Type_middle.
            ** eapply ex_Fr ; [ apply with_Fr | ].
               --- assert (HC := sync_focus_F _ _ pi1').
                   apply llFoc_foc_is_llFoc_foc in pi1'.
                   apply de_Fr in pi1'.
                   +++ eapply (incl_Foc _ (wn C :: l01) lw1') in pi1'.
                       *** eapply ex_Fr ; [ apply pi1' | ].
                           etransitivity ; [ symmetry ; apply Permutation_Type_middle | ].
                           symmetry in HP1.
                           apply (@Permutation_Type_cons _ _ (wn C) eq_refl) in HP1.
                           etransitivity ; [ apply HP1 | ].
                           rewrite app_comm_cons.
                           symmetry; apply Permutation_Type_middle.
                       *** apply Permutation_Type_middle.
                       *** apply Hi1.
                   +++ rewrite (polconts _ _ HC), (polfocs _ HC) in pi1'.
                       apply (Foc_context _ _ pi1').
               --- eapply ex_Fr ; [ apply pi2'' | ].
                   rewrite app_comm_cons.
                   symmetry ; apply Permutation_Type_middle.
               --- rewrite (app_comm_cons _ _ (wn C)).
                   apply Permutation_Type_middle.
      -- assert (Forall_inf Foc (l1 ++ B' :: l2) -> False) as HF1.
         { intros HF0.
           apply Forall_inf_app_r in HF0.
           inversion HF0; subst.
           apply HnFB... }
         eapply (snd Hs1') in HF1...
         destruct HF1 as [pi1' pi1''].
         destruct (Foc_dec C') as [HFC | HnFC].
         ++ assert (Forall_inf Foc (l1 ++ C' :: l2)) as HF2.
            { apply Forall_inf_app...
              constructor... }
            eapply (snd (fst Hs2')) in HF2...
            destruct HF2 as (l02 & lw2 & lw2' & HP2 & Hi2 & pi2').
            cbn in HP2 ; cbn in Hi2 ; cbn in pi2'.
            split.
            ** apply foc_Fr in pi2'.
               eapply (incl_Foc _ (C :: l02) lw2') in pi2'...
               --- eapply ex_Fr ; [ apply with_Fr ; eapply ex_Fr | ].
                   +++ apply pi1'.
                   +++ rewrite app_comm_cons.
                       symmetry ; apply Permutation_Type_middle.
                   +++ apply pi2'.
                   +++ etransitivity ; [ symmetry ; apply Permutation_Type_middle | ].
                       symmetry in HP2.
                       apply (@Permutation_Type_cons _ _ C eq_refl) in HP2.
                       etransitivity ; [ apply HP2 | ].
                       rewrite app_comm_cons.
                       symmetry.
                       apply Permutation_Type_middle.
                   +++ rewrite (app_comm_cons _ (awith _ _ :: _) C).
                       apply Permutation_Type_cons_app...
               --- apply Permutation_Type_cons_app...
            ** assert (HC := sync_focus_F _ _ pi2').
               apply llFoc_foc_is_llFoc_foc in pi2'.
               apply de_Fr in pi2'.
               --- eapply (incl_Foc _ (wn C :: l02) lw2') in pi2'...
                   +++ eapply ex_Fr ; [ apply with_Fr ; eapply ex_Fr | ].
                       *** apply pi1''.
                       *** rewrite app_comm_cons.
                           symmetry ; apply Permutation_Type_middle.
                       *** apply pi2'.
                       *** etransitivity ; [ symmetry ; apply Permutation_Type_middle | ].
                           symmetry in HP2.
                           apply (@Permutation_Type_cons _ _ (wn C) eq_refl) in HP2.
                           etransitivity ; [ apply HP2 | ].
                           rewrite app_comm_cons.
                           symmetry; apply Permutation_Type_middle.
                       *** rewrite (app_comm_cons _ (awith _ _ :: _) (wn C)).
                           apply Permutation_Type_cons_app...
                   +++ apply Permutation_Type_cons_app...
               --- rewrite (polconts _ _ HC), (polfocs _ HC) in pi2'.
                   apply (Foc_context _ _ pi2').
         ++ assert (Forall_inf Foc (l1 ++ C' :: l2) -> False) as HF2.
            { intros HF0.
              apply Forall_inf_app_r in HF0.
              inversion HF0; subst.
              apply HnFC... }
            eapply (snd Hs2') in HF2...
            destruct HF2 as [pi2' pi2''] ; split.
            ** eapply ex_Fr ; [ apply with_Fr | ].
               --- eapply ex_Fr ; [ apply pi1' | ].
                   rewrite app_comm_cons.
                   symmetry ; apply Permutation_Type_middle.
               --- eapply ex_Fr ; [ apply pi2' | ].
                   rewrite app_comm_cons.
                   symmetry ; apply Permutation_Type_middle.
               --- rewrite (app_comm_cons _ _ C).
                   apply Permutation_Type_middle.
            ** eapply ex_Fr ; [ apply with_Fr | ].
               --- eapply ex_Fr ; [ apply pi1'' | ].
                   rewrite app_comm_cons.
                   symmetry ; apply Permutation_Type_middle.
               --- eapply ex_Fr ; [ apply pi2'' | ].
                   rewrite app_comm_cons.
                   symmetry ; apply Permutation_Type_middle.
               --- rewrite (app_comm_cons _ _ (wn C)).
                   apply Permutation_Type_middle.
    * assert (Forall_inf Foc (l1 ++ B' :: l2) -> False) as HF1.
      { intros HF0.
        assert (HF'1 := Forall_inf_app_l _ _ HF0).
        assert (HF'2 := Forall_inf_app_r _ _ HF0).
        inversion HF'2.
        apply HnF.
        apply Forall_inf_app... }
      assert (Forall_inf Foc (l1 ++ C' :: l2) -> False) as HF2.
      { intros HF0.
        assert (HF'1 := Forall_inf_app_l _ _ HF0).
        assert (HF'2 := Forall_inf_app_r _ _ HF0).
        inversion HF'2.
        apply HnF.
        apply Forall_inf_app... }
      eapply (snd Hs1') in HF1...
      destruct HF1 as [pi1' pi1''].
      eapply (snd Hs2') in HF2...
      destruct HF2 as [pi2' pi2''].
      split ; (eapply ex_Fr ; [ apply with_Fr | ]).
      -- eapply ex_Fr ; [ apply pi1' | ].
         rewrite app_comm_cons.
         symmetry ; apply Permutation_Type_middle.
      -- eapply ex_Fr ; [ apply pi2' | ].
         rewrite app_comm_cons.
         symmetry ; apply Permutation_Type_middle.
      -- rewrite (app_comm_cons _ _ C).
         apply Permutation_Type_middle.
      -- eapply ex_Fr ; [ apply pi1'' | ].
         rewrite app_comm_cons.
         symmetry ; apply Permutation_Type_middle.
      -- eapply ex_Fr ; [ apply pi2'' | ].
         rewrite app_comm_cons.
         symmetry ; apply Permutation_Type_middle.
      -- rewrite (app_comm_cons _ _ (wn C)).
         apply Permutation_Type_middle.
Qed.


(** ** Unfocusing *)

Lemma llFoc_to_ll : forall l Pi, llFoc l Pi ->
  (Pi = None -> ll_ll l) * (forall C, Pi = Some C -> ll_ll (C :: l)).
Proof with myeeasy.
intros l Pi pi ; induction pi ;
  (split ; [ intros HN ; inversion HN ; subst
           | intros D HD ; inversion HD ; subst ]) ;
  try (destruct IHpi as [IHpiN IHpiS]) ;
  try (destruct IHpi1 as [IHpi1N IHpi1S]) ;
  try (destruct IHpi2 as [IHpi2N IHpi2S]) ;
  try (assert (pi0' := IHpiS _ eq_refl)) ;
  try (assert (pi0' := IHpiN eq_refl)) ;
  try (assert (pi1' := IHpi1N eq_refl)) ;
  try (assert (pi2' := IHpi2N eq_refl)) ;
  try (now (constructor ; myeeasy)) ;
  try (now (eapply ex_r ; [ | apply Permutation_Type_swap ] ; constructor ; myeeasy)) ;
  try (now (eapply ex_r ; myeeasy)).
- eapply ex_r...
  apply Permutation_Type_cons...
- destruct (polarity A) as [HsA | HaA] ; destruct (polarity B) as [HsB | HaB].
  + rewrite_all (polfocs A HsA).
    rewrite_all (polfocs B HsB).
    assert (pi1' := IHpi1S _ eq_refl).
    assert (pi2' := IHpi2S _ eq_refl).
    eapply ex_r ; [ apply tens_r ; [ apply pi1' | apply pi2' ] | ].
    rewrite (polconts _ _ HsA).
    rewrite (polconts _ _ HsB).
    cbn; Permutation_Type_solve.
  + rewrite_all (polfocs A HsA).
    rewrite_all (polfoca B HaB).
    assert (pi1' := IHpi1S _ eq_refl).
    assert (pi2' := IHpi2N eq_refl).
    eapply ex_r ; [ apply tens_r | ].
    * apply pi1'.
    * rewrite (polconta _ _ HaB) in pi2'.
      apply pi2'.
    * rewrite (polconts _ _ HsA).
      cbn; Permutation_Type_solve.
  + rewrite_all (polfoca A HaA).
    rewrite_all (polfocs B HsB).
    assert (pi1' := IHpi1N eq_refl).
    assert (pi2' := IHpi2S _ eq_refl).
    eapply ex_r ; [ apply tens_r | ].
    * rewrite (polconta _ _ HaA) in pi1'.
      apply pi1'.
    * apply pi2'.
    * rewrite (polconts _ _ HsB).
      cbn; Permutation_Type_solve.
  + rewrite_all (polfoca A HaA).
    rewrite_all (polfoca B HaB).
    assert (pi1' := IHpi1N eq_refl).
    assert (pi2' := IHpi2N eq_refl).
    eapply ex_r ; [ apply tens_r | ].
    * rewrite (polconta _ _ HaA) in pi1'.
      apply pi1'.
    * rewrite (polconta _ _ HaB) in pi2'.
      apply pi2'.
    * cbn; Permutation_Type_solve.
- destruct (polarity A) as [HsA | HaA].
  + rewrite_all (polfocs A HsA).
    assert (pi' := IHpiS _ eq_refl).
    eapply ex_r ; [ apply plus_r1 | ].
    * apply pi'.
    * rewrite (polconts _ _ HsA).
      cbn; Permutation_Type_solve.
  + rewrite_all (polfoca A HaA).
    assert (pi' := IHpiN eq_refl).
    eapply ex_r ; [ apply plus_r1 | ].
    * rewrite (polconta _ _ HaA) in pi'.
      apply pi'.
    * cbn; Permutation_Type_solve.
- destruct (polarity A) as [HsA | HaA].
  + rewrite_all (polfocs A HsA).
    assert (pi' := IHpiS _ eq_refl).
    eapply ex_r ; [ apply plus_r2 | ].
    * apply pi'.
    * rewrite (polconts _ _ HsA).
      cbn; Permutation_Type_solve.
  + rewrite_all (polfoca A HaA).
    assert (pi' := IHpiN eq_refl).
    eapply ex_r ; [ apply plus_r2 | ].
    * rewrite (polconta _ _ HaA) in pi'.
      apply pi'.
    * cbn; Permutation_Type_solve.
- destruct (polarity A) as [HsA | HaA].
  + rewrite_all (polfocs A HsA).
    assert (pi' := IHpiS _ eq_refl).
    eapply ex_r ; [ apply de_r | ].
    * apply pi'.
    * rewrite (polconts _ _ HsA).
      cbn; Permutation_Type_solve.
  + rewrite_all (polfoca A HaA).
    assert (pi' := IHpiN eq_refl).
    eapply ex_r ; [ apply de_r | ].
    * rewrite (polconta _ _ HaA) in pi'.
      apply pi'.
    * cbn; Permutation_Type_solve.
Qed.


(** ** Direct Focusing *)

Lemma unary_focusing A B l0 l1 l2 Pi:
  sformula A -> Forall_inf Foc (B :: l0) ->
  (forall l, llFoc l (Some A) -> llFoc (B :: l0 ++ l) None) ->
  llFoc (l1 ++ A :: l2) Pi -> llFoc (l1 ++ B :: l0 ++ l2) Pi.
Proof.
intros Hs HF Hf pi.
remember (l1 ++ A :: l2) as l; revert A B l0 l1 l2 Hs HF Hf Heql.
induction pi; intros A0 B0 l0 l1' l2' Hs HF Hf Heql; subst.
- destruct l1'; inversion Heql; subst; [ exfalso; inversion Hs | ].
  destruct l1'; inversion H1.
- destruct (Permutation_Type_vs_elt_inv _ _ _ p) as [(l1p, l2p) ->].
  apply Permutation_Type_app_inv,
       (Permutation_Type_app_middle l0), (Permutation_Type_elt B0) in p.
  refine (ex_Fr _ _ _ _ p).
  apply IHpi with A0; auto.
- destruct l1'; inversion Heql; subst.
  + cbn; apply Hf; assumption.
  + cbn; apply foc_Fr, (IHpi A0); auto.
- exfalso; destruct l1'; inversion Heql.
- destruct l1'; inversion Heql; subst; [ exfalso; inversion Hs | ].
  cbn; apply bot_Fr, (IHpi A0); auto.
- dichot_elt_app_inf_exec Heql; subst.
  + rewrite app_comm_cons, 2 app_assoc, <- (app_assoc _ _ l); apply tens_Fr; auto.
    * unfold polcont; destruct (polarity A); [ | rewrite app_comm_cons ]; apply (IHpi1 A0);
        auto; unfold polcont; destruct (polarity A); auto;
        exfalso; apply (disj_polarity A); auto.
    * apply Forall_inf_app.
      -- apply (Forall_inf_app_l _ _ f).
      -- apply Forall_inf_app; auto.
         now apply Forall_inf_app_r in f; inversion f.
  + rewrite <- app_assoc; apply tens_Fr; auto.
    * unfold polcont; destruct (polarity B); [ | rewrite app_comm_cons ]; apply (IHpi2 A0);
      auto; unfold polcont; destruct (polarity B); auto;
      exfalso; apply (disj_polarity B); auto.
    * apply Forall_inf_app.
      -- apply (Forall_inf_app_l _ _ f0).
      -- rewrite app_comm_cons; apply Forall_inf_app; auto.
         now apply Forall_inf_app_r in f0; inversion f0.
- destruct l1'; inversion Heql; subst; [ exfalso; inversion Hs | ].
  cbn; apply parr_Fr; rewrite 2 app_comm_cons; apply (IHpi A0); auto.
- destruct l1'; inversion Heql; subst; [ exfalso; inversion Hs | ].
  cbn; apply top_gen_Fr.
- apply plus_Fr1.
  + unfold polcont; destruct (polarity A); [ | rewrite app_comm_cons ]; apply (IHpi A0);
      auto; unfold polcont; destruct (polarity A); auto;
      exfalso; apply (disj_polarity A); auto.
  + apply Forall_inf_app.
    * apply (Forall_inf_app_l _ _ f).
    * rewrite app_comm_cons; apply Forall_inf_app; auto.
      now apply Forall_inf_app_r in f; inversion f.
- apply plus_Fr2.
  + unfold polcont; destruct (polarity A); [ | rewrite app_comm_cons ]; apply (IHpi A0);
      auto; unfold polcont; destruct (polarity A); auto;
      exfalso; apply (disj_polarity A); auto.
  + apply Forall_inf_app.
    * apply (Forall_inf_app_l _ _ f).
    * rewrite app_comm_cons; apply Forall_inf_app; auto.
      now apply Forall_inf_app_r in f; inversion f.
- destruct l1'; inversion Heql; subst; [ exfalso; inversion Hs | ].
  cbn; apply with_Fr; rewrite app_comm_cons; [apply (IHpi1 A0) | apply (IHpi2 A0)]; auto.
- exfalso; decomp_map_inf Heql; subst; inversion Hs.
- destruct l1'; inversion Heql; subst; [ exfalso; inversion Hs | ].
  cbn; apply de_Fr.
  + unfold polcont; destruct (polarity A); [ | rewrite app_comm_cons ]; apply (IHpi A0);
      auto; unfold polcont; destruct (polarity A); auto;
      exfalso; apply (disj_polarity A); auto.
  + apply Forall_inf_app; [ apply Forall_inf_app_l in f | apply Forall_inf_app_r in f ]; auto.
    inversion f; inversion HF; constructor; [ | apply Forall_inf_app ]; auto.
- destruct l1'; inversion Heql; subst; [ exfalso; inversion Hs | ].
  cbn; apply wk_gen_Fr, (IHpi A0); auto.
- destruct l1'; inversion Heql; subst; [ exfalso; inversion Hs | ].
  cbn; apply co_gen_Fr; rewrite 2 app_comm_cons; apply (IHpi A0); auto.
Qed.

Lemma focusing l : ll_ll l -> llFoc l None.
Proof.
intros pi; induction pi; (try now inversion f); (try now constructor).
- apply (ex_Fr (var X :: covar X :: nil)); [ | Permutation_Type_solve ].
  apply foc_Fr, ax_Fr.
- now apply (ex_Fr l1).
- apply (ex_Fr (l1 ++ List.map wn lw ++ l2)); auto.
  now apply Permutation_Type_app_head, Permutation_Type_app_tail, Permutation_Type_map.
- apply foc_Fr, one_Fr.
- clear pi1 pi2.
  destruct (polarity A).
  + apply (ex_Fr (tens A B :: l1 ++ l2)); [ | Permutation_Type_solve ].
    rewrite app_comm_cons; apply reversing with (B :: nil); auto.
    clear l2 IHpi2.
    intros l2 Hf pi; cbn in pi; cbn.
    apply (ex_Fr (tens A B :: l2 ++ l1)); [ | Permutation_Type_solve ].
    rewrite <- (app_nil_l _).
    apply (unary_focusing A); auto.
    * now constructor; [ left; left; constructor | ].
    * clear - Hf pi; intros l pi1.
      apply (ex_Fr (tens A B :: l ++ l2)); [ | Permutation_Type_solve ].
      destruct (polarity B).
      -- rewrite <- (app_nil_l _).
         apply (unary_focusing B); auto.
         ++ constructor; [ left; left; constructor | ].
            apply (Foc_context _ _ pi1).
         ++ clear l2 Hf pi; intros l2 pi2.
            apply foc_Fr, tens_Fr.
            ** apply (llFoc_foc_is_llFoc_foc _ _ pi1).
            ** apply (llFoc_foc_is_llFoc_foc _ _ pi2).
            ** apply (Foc_context _ _ pi1).
            ** apply (Foc_context _ _ pi2).
      -- apply foc_Fr, tens_Fr; auto.
         ++ apply (llFoc_foc_is_llFoc_foc _ _ pi1).
         ++ now rewrite (polconta _ _ a), (polfoca _ a).
         ++ apply (Foc_context _ _ pi1).
  + destruct (polarity B).
    * rewrite app_comm_cons; apply reversing with (A :: nil); auto.
      clear l1 IHpi1.
      intros l1 Hf pi; cbn in pi; cbn.
      apply (ex_Fr (nil ++ tens A B :: l1 ++ l2)); [ | Permutation_Type_solve ].
      apply (unary_focusing B); auto.
      -- now constructor; [ left; left; constructor | ].
      -- intros l pi'.
         apply foc_Fr, tens_Fr; auto.
         ++ now rewrite (polconta _ _ a), (polfoca _ a).
         ++ apply (llFoc_foc_is_llFoc_foc _ _ pi').
         ++ apply (Foc_context _ _ pi').
    * rewrite app_comm_cons; apply (reversing (A :: nil)); auto.
      clear l1 IHpi1; intros l1 HF pi1; cbn in pi1.
      apply (ex_Fr (tens A B :: l1 ++ l2)); [ | Permutation_Type_solve ].
      rewrite app_comm_cons; apply (reversing (B :: nil)); auto.
      clear l2 IHpi2; intros l2 HF2 pi2; cbn in pi2; cbn.
      apply foc_Fr, tens_Fr; auto.
      -- now rewrite (polconta _ _ a), (polfoca _ a).
      -- now rewrite (polconta _ _ a0), (polfoca _ a0).
- apply top_gen_Fr.
- clear pi.
  destruct (polarity A).
  + rewrite <- (app_nil_l _), <- (app_nil_l l).
    apply (unary_focusing A); auto.
    * constructor; try left; try left; constructor.
    * clear; intros l pi.
      apply foc_Fr, plus_Fr1.
      -- apply (llFoc_foc_is_llFoc_foc _ _ pi).
      -- apply (Foc_context _ _ pi).
  + change (aplus A B :: l) with ((aplus A B :: nil) ++ l).
    apply reversing with (A :: nil); auto.
    intros; apply foc_Fr, plus_Fr1; auto.
    now rewrite (polconta _ _ a), (polfoca _ a).
- clear pi.
  destruct (polarity A).
  + rewrite <- (app_nil_l _), <- (app_nil_l l).
    apply (unary_focusing A); auto.
    * constructor; try left; try left; constructor.
    * clear; intros l pi.
      apply foc_Fr, plus_Fr2.
      -- apply (llFoc_foc_is_llFoc_foc _ _ pi).
      -- apply (Foc_context _ _ pi).
  + change (aplus B A :: l) with ((aplus B A :: nil) ++ l).
    apply reversing with (A :: nil); auto.
    intros; apply foc_Fr, plus_Fr2; auto.
    now rewrite (polconta _ _ a), (polfoca _ a).
- now apply foc_Fr, oc_Fr.
- clear pi.
  destruct (polarity A).
  + rewrite <- (app_nil_l _), <- (app_nil_l l).
    apply (unary_focusing A); auto.
    * constructor; [ right; exists A; reflexivity | constructor ].
    * clear; intros l pi.
      apply de_Fr; [ apply (llFoc_foc_is_llFoc_foc _ _ pi) | ].
      apply (Foc_context _ _ pi).
  + change (wn A :: l) with ((wn A :: nil) ++ l).
    apply (reversing (A :: nil)); auto.
    clear l IHpi; intros l Hf pi.
    apply de_Fr; auto.
    now rewrite (polconta _ _ a), (polfoca _ a).
- apply wk_gen_Fr; assumption.
- apply co_gen_Fr; assumption.
- destruct a.
Qed.

End Atoms.
