(* llfoc library for yalla *)


(* output in Type *)


(** * Focusing in Linear Logic *)

From Stdlib Require Import Arith_base.
From Stdlib Require Import CMorphisms.

Require Import List_more.
Require Import List_Type.
Require Import Permutation_Type_more.
Require Import Permutation_Type_solve.
Require Import GPermutation_Type.

Require Import ll_fragments.


(** ** Synchronous and asynchronous formulas *)
Inductive sformula : formula -> Prop :=
| pvar : forall x, sformula (var x)
| pone : sformula one
| ptens : forall A B, sformula (tens A B)
| pzero : sformula zero
| pplus : forall A B, sformula (aplus A B)
| poc : forall A, sformula (oc A).

Inductive aformula : formula -> Prop :=
| ncovar : forall x, aformula (covar x)
| nbot : aformula bot
| nparr : forall A B, aformula (parr A B)
| ntop : aformula top
| nwith : forall A B, aformula (awith A B)
| nwn : forall A, aformula (wn A).

Lemma polarity : forall A, {sformula A} + {aformula A}.
Proof.
induction A ;
  try (now (left ; constructor)) ;
  try (now (right ; constructor)).
Defined.

Lemma disj_polarity : forall A, ~ (sformula A /\ aformula A).
Proof.
induction A ; intros [Hp Hn] ; inversion Hp ; inversion Hn.
Qed.

Lemma sformula_dual : forall A, sformula (dual A) -> aformula A.
Proof.
intros A Hp ; destruct A ; inversion Hp ; constructor.
Qed.

Lemma aformula_dual : forall A, aformula (dual A) -> sformula A.
Proof.
intros A Hn ; destruct A ; inversion Hn ; constructor.
Qed.


(** ** The weakly focused system [llfoc] *)

Definition tFoc x :=
  { sformula x } + { exists X, x = covar X } + { exists y, x = wn y } + { x = top }.

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
  (x = bot) + { y | x = parr (fst y) (snd y) } + { y | x = awith (fst y) (snd y) }.
Proof with myeasy.
destruct x ; intros HnF ;
  try (now (exfalso ; apply HnF ; left ; left ; left ; constructor)) ;
  try (now (exfalso ; apply HnF ; left ; left ; right ; eexists ; reflexivity)) ;
  try (now (exfalso ; apply HnF ; left ; right ; eexists ; reflexivity)) ;
  try (now (exfalso ; apply HnF ; right ; reflexivity)).
- left ; left...
- left ; right ; exists (x1,x2)...
- right ; eexists (x1,x2)...
Qed.

Lemma not_tFocl : forall l, (Forall_inf tFoc l -> False) ->
  { l' : _ & l = fst (snd l') ++ fst l' :: (snd (snd l'))
           & sum (sum (fst l' = bot) { B | fst l' = parr (fst B) (snd B) })
                                     { B | fst l' = awith (fst B) (snd B) } }.
Proof with myeeasy.
intros l HnF.
apply Forall_inf_neg_Exists_inf in HnF.
- induction l ; inversion HnF ; subst.
  + exists (a,(nil,l))...
    simpl ; apply not_tFoc...
  + apply IHl in X as [l' Heq Hf] ; subst.
    exists (fst l',(a::fst (snd l'),snd (snd l')))...
- intros x.
  assert (Hd := tFoc_dec x).
  destruct Hd ; intuition.
Qed.

Definition polcont l A :=
match polarity A with
| left _ => l
| right _ => A :: l
end.
Definition polfoc A :=
match polarity A with
| left _ => Some A
| right _ => None
end.
Lemma polconts : forall A l, sformula A -> polcont l A = l.
Proof.
intros.
unfold polcont.
case (polarity A).
- intros ; reflexivity.
- intros.
  exfalso.
  eapply disj_polarity ; split ; eassumption.
Qed.
Lemma polconta : forall A l, aformula A -> polcont l A = A :: l.
Proof.
intros.
unfold polcont.
case (polarity A).
- intros.
  exfalso.
  eapply disj_polarity ; split ; eassumption.
- intros ; reflexivity.
Qed.
Lemma polfocs : forall A, sformula A -> polfoc A = Some A.
Proof.
intros.
unfold polfoc.
case (polarity A).
- intros ; reflexivity.
- intros.
  exfalso.
  eapply disj_polarity ; split ; eassumption.
Qed.
Lemma polfoca : forall A, aformula A -> polfoc A = None.
Proof.
intros.
unfold polfoc.
case (polarity A).
- intros.
  exfalso.
  eapply disj_polarity ; split ; eassumption.
- intros ; reflexivity.
Qed.

Lemma Permutation_Type_middle_polcont : forall l1 l2 A B,
  Permutation_Type (B :: polcont (l1 ++ l2) A) (polcont (l1 ++ B :: l2) A).
Proof.
intros l1 l2 A B.
destruct (polarity A) as [Hs | Ha].
- rewrite 2 (polconts _ _ Hs).
  apply Permutation_Type_middle.
- rewrite 2 (polconta _ _ Ha).
  rewrite 2 (app_comm_cons _ _ A).
  apply Permutation_Type_middle.
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
| top_fr : forall l Pi, option_prop sformula Pi -> Forall_inf tFoc l ->
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

Lemma top_gen_fr : forall l Pi, option_prop sformula Pi -> llfoc (top :: l) Pi.
Proof with myeeasy.
intros l.
remember (list_sum (map fsize l)) as n.
revert l Heqn ; induction n using lt_wf_rect;
  intros l Heqn Pi Hs ; subst.
destruct (tFocl_dec l).
- apply top_fr...
- apply not_tFocl in f.
  destruct f as [(A & l1 & l2) Heq [[Hb | ([B C] & Hp)] | ([B C] & Hw)]] ;
    subst ; simpl ; simpl in X ; [simpl in Hb | simpl in Hp | simpl in Hw] ; subst.
  + apply (ex_fr (bot :: l2 ++ top :: l1)) ; [ apply bot_fr | Permutation_Type_solve ].
    apply (ex_fr (top :: l1 ++ l2)) ; [ eapply X | Permutation_Type_solve ]...
    rewrite 2 map_app ; rewrite 2 list_sum_app ; simpl...
  + apply (ex_fr (parr B C :: l2 ++ top :: l1)) ; [ apply parr_fr | Permutation_Type_solve ].
    apply (ex_fr (top :: l1 ++ B :: C :: l2)) ; [ eapply X | Permutation_Type_solve ]...
    rewrite 2 map_app ; rewrite 2 list_sum_app ; simpl...
  + apply (ex_fr (awith B C :: l2 ++ top :: l1)) ; [ apply with_fr | Permutation_Type_solve ].
    * apply (ex_fr (top :: l1 ++ B :: l2)) ; [ eapply X | Permutation_Type_solve ]...
      rewrite 2 map_app ; rewrite 2 list_sum_app ; simpl...
    * apply (ex_fr (top :: l1 ++ C :: l2)) ; [ eapply X | Permutation_Type_solve ]...
      rewrite 2 map_app ; rewrite 2 list_sum_app ; simpl...
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
  simpl ; apply Permutation_Type_vs_elt_inv in p.
  destruct p as ((l3 & l4) & Heq) ; subst.
  simpl in IHpi ; simpl in HP ; simpl.
  destruct (IHpi _ _ eq_refl) as [pi0 Hs].
  simpl in HP ; apply Permutation_Type_app_inv in HP.
  exists (ex_fr _ _ _ pi0 HP) ; simpl...
- destruct l1' ; inversion Heq ; subst.
  + exfalso.
    clear IHpi ; apply sync_focus in pi.
    inversion pi.
  + destruct (IHpi _ _ eq_refl) as [pi0 Hs].
    exists (foc_fr _ _ pi0) ; simpl...
- exfalso.
  destruct l1' ; inversion Heq.
- destruct l1' ; inversion Heq ; subst.
  + exists pi ; simpl...
  + destruct (IHpi _ _ eq_refl) as [pi0 Hs].
    exists (bot_fr _ _ pi0) ; simpl...
- dichot_elt_app_inf_exec Heq ; subst.
  + destruct (polarity A) as [Hs | Ha].
    * assert (H1 := IHpi1 _ _ (polconts _ _ Hs)).
      rewrite <- (polconts _ (l1' ++ l) Hs) in H1.
      destruct H1 as [pi1' Hs1].
      rewrite app_assoc.
      exists (tens_fr _ _ _ _ pi1' pi2) ; simpl...
    * assert (polcont (l1' ++ bot :: l) A = (A :: l1') ++ bot :: l) as Hpa
        by (rewrite (polconta _ _ Ha) ; rewrite app_comm_cons ; reflexivity).
      assert (H1 := IHpi1 _ _ Hpa).
      rewrite <- app_comm_cons in H1.
      rewrite <- (polconta _ (l1' ++ l) Ha) in H1.
      destruct H1 as [pi1' Hs1].
      rewrite app_assoc.
      exists (tens_fr _ _ _ _ pi1' pi2) ; simpl...
  + destruct (polarity B) as [Hs | Ha].
    * assert (H2 := IHpi2 _ _ (polconts _ _ Hs)).
      rewrite <- (polconts _ (l ++ l2') Hs) in H2.
      destruct H2 as [pi2' Hs2].
      rewrite <- app_assoc.
      exists (tens_fr _ _ _ _ pi1 pi2') ; simpl...
    * assert (polcont (l ++ bot :: l2') B = (B :: l) ++ bot :: l2') as Hpa
        by (rewrite (polconta _ _ Ha) ; rewrite app_comm_cons ; reflexivity).
      assert (H2 := IHpi2 _ _ Hpa).
      rewrite <- app_comm_cons in H2.
      rewrite <- (polconta _ (l ++ l2') Ha) in H2.
      destruct H2 as [pi2' Hs2].
      rewrite <- app_assoc.
      exists (tens_fr _ _ _ _ pi1 pi2') ; simpl...
- destruct l1' ; inversion Heq ; subst.
  assert (A :: B :: l1' ++ bot :: l2' = (A :: B :: l1') ++ bot :: l2') as Heql
    by (list_simpl ; reflexivity).
  assert (H0 := IHpi _ _ Heql).
  rewrite <- 2 app_comm_cons in H0.
  destruct H0 as [pi0 Hs].
  exists (parr_fr _ _ _ _ pi0) ; simpl...
- exfalso.
  destruct l1' ; inversion Heq ; subst.
  apply Forall_inf_app_r in f.
  inversion f ; subst.
  inversion H0 as [[[Ht | Ht] | Ht] | Ht] ; try now (inversion Ht).
- destruct (polarity A) as [Hs | Ha].
  + assert (H1 := IHpi _ _ (polconts _ _ Hs)).
    rewrite <- (polconts _ (l1' ++ l2') Hs) in H1.
    destruct H1 as [pi1' Hs1].
    exists (plus_fr1 _ B _ pi1') ; simpl...
  + assert (polcont (l1' ++ bot :: l2') A = (A :: l1') ++ bot :: l2') as Hpa
      by (rewrite (polconta _ _ Ha) ; rewrite app_comm_cons ; reflexivity).
    assert (H1 := IHpi _ _ Hpa).
    rewrite <- app_comm_cons in H1.
    rewrite <- (polconta _ (l1' ++ l2') Ha) in H1.
    destruct H1 as [pi1' Hs1].
    exists (plus_fr1 _ B _ pi1') ; simpl...
- destruct (polarity A) as [Hs | Ha].
  + assert (H1 := IHpi _ _ (polconts _ _ Hs)).
    rewrite <- (polconts _ (l1' ++ l2') Hs) in H1.
    destruct H1 as [pi1' Hs1].
    exists (plus_fr2 _ B _ pi1') ; simpl...
  + assert (polcont (l1' ++ bot :: l2') A = (A :: l1') ++ bot :: l2') as Hpa
      by (rewrite (polconta _ _ Ha) ; rewrite app_comm_cons ; reflexivity).
    assert (H1 := IHpi _ _ Hpa).
    rewrite <- app_comm_cons in H1.
    rewrite <- (polconta _ (l1' ++ l2') Ha) in H1.
    destruct H1 as [pi1' Hs1].
    exists (plus_fr2 _ B _ pi1') ; simpl...
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
  exists (with_fr _ _ _ _ pi1' pi2') ; simpl...
- exfalso. decomp_map Heq eqn:Hw. discriminate Hw.
- destruct l1' ; inversion Heq ; subst.
  destruct (polarity A) as [Hs | Ha].
  + assert (H1 := IHpi _ _ (polconts _ _ Hs)).
    rewrite <- (polconts _ (l1' ++ l2') Hs) in H1.
    destruct H1 as [pi1' Hs1].
    exists (de_fr _ _ pi1') ; simpl...
  + assert (polcont (l1' ++ bot :: l2') A = (A :: l1') ++ bot :: l2') as Hpa
      by (rewrite (polconta _ _ Ha) ; rewrite app_comm_cons ; reflexivity).
    assert (H1 := IHpi _ _ Hpa).
    rewrite <- app_comm_cons in H1.
    rewrite <- (polconta _ (l1' ++ l2') Ha) in H1.
    destruct H1 as [pi1' Hs1].
    exists (de_fr _ _ pi1') ; simpl...
- destruct l1' ; inversion Heq ; subst.
  destruct (IHpi _ _ eq_refl) as [pi0 Hs].
  exists (wk_fr A _ _ pi0) ; simpl...
- destruct l1' ; inversion Heq ; subst.
  assert (wn A :: wn A :: l1' ++ bot :: l2' = (wn A :: wn A :: l1') ++ bot :: l2')
    as Heql by (list_simpl ; reflexivity).
  assert (H0 := IHpi _ _ Heql).
  rewrite <- 2 app_comm_cons in H0.
  destruct H0 as [pi0 Hs].
  exists (co_fr _ _ _ pi0) ; simpl...
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
  simpl ; apply Permutation_Type_vs_elt_inv in p.
  destruct p as ((l3 & l4) & Heq) ; subst.
  simpl in IHpi ; simpl in HP ; simpl.
  destruct (IHpi _ _ _ _ eq_refl) as [pi0 Hs].
  simpl in HP ; apply Permutation_Type_app_inv in HP.
  apply (Permutation_Type_elt B') in HP.
  apply (Permutation_Type_elt A') in HP.
  exists (ex_fr _ _ _ pi0 HP) ; simpl...
- destruct l1' ; inversion Heq ; subst.
  + exfalso.
    clear IHpi ; apply sync_focus in pi.
    inversion pi.
  + destruct (IHpi _ _ _ _ eq_refl) as [pi0 Hs].
    exists (foc_fr _ _ pi0) ; simpl...
- exfalso.
  destruct l1' ; inversion Heq.
- destruct l1' ; inversion Heq ; subst.
  destruct (IHpi _ _ _ _ eq_refl) as [pi0 Hs].
  exists (bot_fr _ _ pi0) ; simpl...
- dichot_elt_app_inf_exec Heq ; subst.
  + destruct (polarity A) as [Hs | Ha].
    * assert (H1 := IHpi1 _ _ _ _ (polconts _ _ Hs)).
      rewrite <- (polconts _ (l1' ++ A' :: B' :: l) Hs) in H1.
      destruct H1 as [pi1' Hs1].
      rewrite 2 app_comm_cons ; rewrite app_assoc.
      exists (tens_fr _ _ _ _ pi1' pi2) ; simpl...
    * assert (polcont (l1' ++ parr A' B' :: l) A = (A :: l1') ++ parr A' B' :: l)
        as Hpa by (rewrite (polconta _ _ Ha) ; rewrite app_comm_cons ; reflexivity).
      assert (H1 := IHpi1 _ _ _ _ Hpa).
      rewrite <- app_comm_cons in H1.
      rewrite <- (polconta _ (l1' ++ A' :: B' :: l) Ha) in H1.
      destruct H1 as [pi1' Hs1].
      rewrite 2 app_comm_cons ; rewrite app_assoc.
      exists (tens_fr _ _ _ _ pi1' pi2) ; simpl...
  + destruct (polarity B) as [Hs | Ha].
    * assert (H2 := IHpi2 _ _ _ _ (polconts _ _ Hs)).
      rewrite <- (polconts _ (l ++ A' :: B' :: l2') Hs) in H2.
      destruct H2 as [pi2' Hs2].
      rewrite <- app_assoc.
      exists (tens_fr _ _ _ _ pi1 pi2') ; simpl...
    * assert (polcont (l ++ parr A' B' :: l2') B = (B :: l) ++ parr A' B' :: l2')
        as Hpa by (rewrite (polconta _ _ Ha) ; rewrite app_comm_cons ; reflexivity).
      assert (H2 := IHpi2 _ _ _ _ Hpa).
      rewrite <- app_comm_cons in H2.
      rewrite <- (polconta _ (l ++ A' :: B' :: l2') Ha) in H2.
      destruct H2 as [pi2' Hs2].
      rewrite <- app_assoc.
      exists (tens_fr _ _ _ _ pi1 pi2') ; simpl...
- destruct l1' ; inversion Heq ; subst.
  + exists pi ; simpl...
  + assert (A :: B :: l1' ++ parr A' B' :: l2' = (A :: B :: l1') ++ parr A' B' :: l2')
      as Heql by (list_simpl ; reflexivity).
    assert (H0 := IHpi _ _ _ _ Heql).
    rewrite <- 2 app_comm_cons in H0.
    destruct H0 as [pi0 Hs].
    exists (parr_fr _ _ _ _ pi0) ; simpl...
- exfalso.
  destruct l1' ; inversion Heq ; subst.
  apply Forall_inf_app_r in f.
  inversion f ; subst.
  inversion H0 as [[[Ht | Ht] | Ht] | Ht] ; try now (inversion Ht).
- destruct (polarity A) as [Hs | Ha].
  + assert (H1 := IHpi _ _ _ _ (polconts _ _ Hs)).
    rewrite <- (polconts _ (l1' ++ A' :: B' :: l2') Hs) in H1.
    destruct H1 as [pi1' Hs1].
    exists (plus_fr1 _ B _ pi1') ; simpl...
  + assert (polcont (l1' ++ parr A' B' :: l2') A = (A :: l1') ++ parr A' B' :: l2')
      as Hpa by (rewrite (polconta _ _ Ha) ; rewrite app_comm_cons ; reflexivity).
    assert (H1 := IHpi _ _ _ _ Hpa).
    rewrite <- app_comm_cons in H1.
    rewrite <- (polconta _ (l1' ++ A' :: B' :: l2') Ha) in H1.
    destruct H1 as [pi1' Hs1].
    exists (plus_fr1 _ B _ pi1') ; simpl...
- destruct (polarity A) as [Hs | Ha].
  + assert (H1 := IHpi _ _ _ _ (polconts _ _ Hs)).
    rewrite <- (polconts _ (l1' ++ A' :: B' :: l2') Hs) in H1.
    destruct H1 as [pi1' Hs1].
    exists (plus_fr2 _ B _ pi1') ; simpl...
  + assert (polcont (l1' ++ parr A' B' :: l2') A = (A :: l1') ++ parr A' B' :: l2')
      as Hpa by (rewrite (polconta _ _ Ha) ; rewrite app_comm_cons ; reflexivity).
    assert (H1 := IHpi _ _ _ _ Hpa).
    rewrite <- app_comm_cons in H1.
    rewrite <- (polconta _ (l1' ++ A' :: B' :: l2') Ha) in H1.
    destruct H1 as [pi1' Hs1].
    exists (plus_fr2 _ B _ pi1') ; simpl...
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
  exists (with_fr _ _ _ _ pi1' pi2') ; simpl...
- exfalso. decomp_map Heq eqn:Hw. discriminate Hw.
- destruct l1' ; inversion Heq ; subst.
  destruct (polarity A) as [Hs | Ha].
  + assert (H1 := IHpi _ _ _ _ (polconts _ _ Hs)).
    rewrite <- (polconts _ (l1' ++ A' :: B' :: l2') Hs) in H1.
    destruct H1 as [pi1' Hs1].
    exists (de_fr _ _ pi1') ; simpl...
  + assert (polcont (l1' ++ parr A' B' :: l2') A = (A :: l1') ++ parr A' B' :: l2')
      as Hpa by (rewrite (polconta _ _ Ha) ; rewrite app_comm_cons ; reflexivity).
    assert (H1 := IHpi _ _ _ _ Hpa).
    rewrite <- app_comm_cons in H1.
    rewrite <- (polconta _ (l1' ++ A' :: B' :: l2') Ha) in H1.
    destruct H1 as [pi1' Hs1].
    exists (de_fr _ _ pi1') ; simpl...
- destruct l1' ; inversion Heq ; subst.
  destruct (IHpi _ _ _ _ eq_refl) as [pi0 Hs].
  exists (wk_fr A _ _ pi0) ; simpl...
- destruct l1' ; inversion Heq ; subst.
  assert (wn A :: wn A :: l1' ++ parr A' B' :: l2'
       = (wn A :: wn A :: l1') ++ parr A' B' :: l2')
    as Heql by (list_simpl ; reflexivity).
  assert (H0 := IHpi _ _ _ _ Heql).
  rewrite <- 2 app_comm_cons in H0.
  destruct H0 as [pi0 Hs].
  exists (co_fr _ _ _ pi0) ; simpl...
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
  simpl ; apply Permutation_Type_vs_elt_inv in p.
  destruct p as ((l3 & l4) & Heq) ; subst.
  simpl in IHpi ; simpl in HP ; simpl.
  destruct (IHpi _ _ _ _ eq_refl) as [[pi01 Hs1] [pi02 Hs2]].
  simpl in HP ; apply Permutation_Type_app_inv in HP.
  assert (HP2 := HP).
  apply (Permutation_Type_elt B') in HP2.
  apply (Permutation_Type_elt A') in HP.
  split ; [ exists (ex_fr _ _ _ pi01 HP)
          | exists (ex_fr _ _ _ pi02 HP2) ] ; simpl...
- destruct l1' ; inversion Heq ; subst.
  + exfalso.
    clear IHpi ; apply sync_focus in pi.
    inversion pi.
  + destruct (IHpi _ _ _ _ eq_refl) as [[pi01 Hs1] [pi02 Hs2]].
    split ; [ exists (foc_fr _ _ pi01)
            | exists (foc_fr _ _ pi02) ] ; simpl...
- exfalso.
  destruct l1' ; inversion Heq.
- destruct l1' ; inversion Heq ; subst.
  destruct (IHpi _ _ _ _ eq_refl) as [[pi01 Hs1] [pi02 Hs2]].
    split ; [ exists (bot_fr _ _ pi01)
            | exists (bot_fr _ _ pi02) ] ; simpl...
- dichot_elt_app_inf_exec Heq ; subst.
  + destruct (polarity A) as [Hs | Ha].
    * assert (H1 := IHpi1 _ _ _ _ (polconts _ _ Hs)).
      rewrite <- (polconts _ (l1' ++ A' :: l) Hs) in H1.
      rewrite <- (polconts _ (l1' ++ B' :: l) Hs) in H1.
      destruct H1 as [[pi1' Hs1] [pi1'' Hs2]].
      rewrite ? app_comm_cons ; rewrite 2 app_assoc.
      split ; [ exists (tens_fr _ _ _ _ pi1' pi2)
              | exists (tens_fr _ _ _ _ pi1'' pi2) ] ; simpl...
    * assert (polcont (l1' ++ awith A' B' :: l) A = (A :: l1') ++ awith A' B' :: l)
        as Hpa by (rewrite (polconta _ _ Ha) ; rewrite app_comm_cons ; reflexivity).
      assert (H1 := IHpi1 _ _ _ _ Hpa).
      rewrite <- 2 app_comm_cons in H1.
      rewrite <- (polconta _ (l1' ++ A' :: l) Ha) in H1.
      rewrite <- (polconta _ (l1' ++ B' :: l) Ha) in H1.
      destruct H1 as [[pi1' Hs1] [pi2' Hs2]].
      rewrite ? app_comm_cons ; rewrite 2 app_assoc.
      split ; [ exists (tens_fr _ _ _ _ pi1' pi2)
              | exists (tens_fr _ _ _ _ pi2' pi2) ] ; simpl...
  + destruct (polarity B) as [Hs | Ha].
    * assert (H2 := IHpi2 _ _ _ _ (polconts _ _ Hs)).
      rewrite <- (polconts _ (l ++ A' :: l2') Hs) in H2.
      rewrite <- (polconts _ (l ++ B' :: l2') Hs) in H2.
      destruct H2 as [[pi1' Hs1] [pi1'' Hs2]].
      rewrite <- 2 app_assoc.
      split ; [ exists (tens_fr _ _ _ _ pi1 pi1')
              | exists (tens_fr _ _ _ _ pi1 pi1'') ] ; simpl...
    * assert (polcont (l ++ awith A' B' :: l2') B = (B :: l) ++ awith A' B' :: l2')
        as Hpa by (rewrite (polconta _ _ Ha) ; rewrite app_comm_cons ; reflexivity).
      assert (H2 := IHpi2 _ _ _ _ Hpa).
      rewrite <- 2 app_comm_cons in H2.
      rewrite <- (polconta _ (l ++ A' :: l2') Ha) in H2.
      rewrite <- (polconta _ (l ++ B' :: l2') Ha) in H2.
      destruct H2 as [[pi1' Hs1] [pi1'' Hs2]].
      rewrite <- 2 app_assoc.
      split ; [ exists (tens_fr _ _ _ _ pi1 pi1')
              | exists (tens_fr _ _ _ _ pi1 pi1'') ] ; simpl...
- destruct l1' ; inversion Heq ; subst.
  assert (A :: B :: l1' ++ awith A' B' :: l2' = (A :: B :: l1') ++ awith A' B' :: l2')
    as Heql by (list_simpl ; reflexivity).
  assert (H0 := IHpi _ _ _ _ Heql).
  rewrite <- ? app_comm_cons in H0.
  destruct H0 as [[pi1' Hs1] [pi1'' Hs2]].
  split ; [ exists (parr_fr _ _ _ _ pi1')
          | exists (parr_fr _ _ _ _ pi1'') ] ; simpl...
- exfalso.
  destruct l1' ; inversion Heq ; subst.
  apply Forall_inf_app_r in f.
  inversion f ; subst.
  inversion H0 as [[[Ht | Ht] | Ht] | Ht] ; try now (inversion Ht).
- destruct (polarity A) as [Hs | Ha].
  + assert (H1 := IHpi _ _ _ _ (polconts _ _ Hs)).
    rewrite <- (polconts _ (l1' ++ A' :: l2') Hs) in H1.
    rewrite <- (polconts _ (l1' ++ B' :: l2') Hs) in H1.
    destruct H1 as [[pi1' Hs1] [pi1'' Hs2]].
    split ; [ exists (plus_fr1 _ _ _ pi1')
            | exists (plus_fr1 _ _ _ pi1'') ] ; simpl...
  + assert (polcont (l1' ++ awith A' B' :: l2') A = (A :: l1') ++ awith A' B' :: l2')
      as Hpa by (rewrite (polconta _ _ Ha) ; rewrite app_comm_cons ; reflexivity).
    assert (H1 := IHpi _ _ _ _ Hpa).
    rewrite <- 2 app_comm_cons in H1.
    rewrite <- (polconta _ (l1' ++ A' :: l2') Ha) in H1.
    rewrite <- (polconta _ (l1' ++ B' :: l2') Ha) in H1.
    destruct H1 as [[pi1' Hs1] [pi1'' Hs2]].
    split ; [ exists (plus_fr1 _ _ _ pi1')
            | exists (plus_fr1 _ _ _ pi1'') ] ; simpl...
- destruct (polarity A) as [Hs | Ha].
  + assert (H1 := IHpi _ _ _ _ (polconts _ _ Hs)).
    rewrite <- (polconts _ (l1' ++ A' :: l2') Hs) in H1.
    rewrite <- (polconts _ (l1' ++ B' :: l2') Hs) in H1.
    destruct H1 as [[pi1' Hs1] [pi1'' Hs2]].
    split ; [ exists (plus_fr2 _ _ _ pi1')
            | exists (plus_fr2 _ _ _ pi1'') ] ; simpl...
  + assert (polcont (l1' ++ awith A' B' :: l2') A = (A :: l1') ++ awith A' B' :: l2')
      as Hpa by (rewrite (polconta _ _ Ha) ; rewrite app_comm_cons ; reflexivity).
    assert (H1 := IHpi _ _ _ _ Hpa).
    rewrite <- 2 app_comm_cons in H1.
    rewrite <- (polconta _ (l1' ++ A' :: l2') Ha) in H1.
    rewrite <- (polconta _ (l1' ++ B' :: l2') Ha) in H1.
    destruct H1 as [[pi1' Hs1] [pi1'' Hs2]].
    split ; [ exists (plus_fr2 _ _ _ pi1')
            | exists (plus_fr2 _ _ _ pi1'') ] ; simpl...
- destruct l1' ; inversion Heq ; subst.
  + split ; [ exists pi1 | exists pi2 ] ; subst ; simpl...
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
            | exists (with_fr _ _ _ _ pi1'' pi2'') ] ; simpl...
- exfalso. decomp_map Heq eqn:Hw. discriminate Hw.
- destruct l1' ; inversion Heq ; subst.
  destruct (polarity A) as [Hs | Ha].
  + assert (H1 := IHpi _ _ _ _ (polconts _ _ Hs)).
    rewrite <- (polconts _ (l1' ++ A' :: l2') Hs) in H1.
    rewrite <- (polconts _ (l1' ++ B' :: l2') Hs) in H1.
    destruct H1 as [[pi1' Hs1] [pi1'' Hs2]].
    split ; [ exists (de_fr _ _ pi1')
            | exists (de_fr _ _ pi1'') ] ; simpl...
  + assert (polcont (l1' ++ awith A' B' :: l2') A = (A :: l1') ++ awith A' B' :: l2')
      as Hpa by (rewrite (polconta _ _ Ha) ; rewrite app_comm_cons ; reflexivity).
    assert (H1 := IHpi _ _ _ _ Hpa).
    rewrite <- 2 app_comm_cons in H1.
    rewrite <- (polconta _ (l1' ++ A' :: l2') Ha) in H1.
    rewrite <- (polconta _ (l1' ++ B' :: l2') Ha) in H1.
    destruct H1 as [[pi1' Hs1] [pi1'' Hs2]].
    split ; [ exists (de_fr _ _ pi1')
            | exists (de_fr _ _ pi1'') ] ; simpl...
- destruct l1' ; inversion Heq ; subst.
  destruct (IHpi _ _ _ _ eq_refl) as [[pi1' Hs1] [pi1'' Hs2]].
  split ; [ exists (wk_fr _ _ _ pi1')
          | exists (wk_fr _ _ _ pi1'') ] ; simpl...
- destruct l1' ; inversion Heq ; subst.
  assert (wn A :: wn A :: l1' ++ awith A' B' :: l2'
       = (wn A :: wn A :: l1') ++ awith A' B' :: l2')
    as Heql by (list_simpl ; reflexivity).
  assert (H0 := IHpi _ _ _ _ Heql).
  rewrite <- ? app_comm_cons in H0.
  destruct H0 as [[pi1' Hs1] [pi1'' Hs2]].
  split ; [ exists (co_fr _ _ _ pi1')
          | exists (co_fr _ _ _ pi1'') ] ; simpl...
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
Proof with (try GPermutation_Type_solve) ; myeeasy.
intros l Pi pi ; induction pi ;
  (split ; [ intros HN ; inversion HN ; subst
           | intros D HD ; inversion HD ; subst ]) ;
  try (destruct IHpi as [IHpiN IHpiS]) ;
  try (destruct IHpi1 as [IHpi1N IHpi1S]) ;
  try (destruct IHpi2 as [IHpi2N IHpi2S]) ;
  try (assert (pi0' := IHpiS _ eq_refl)) ;
  try (assert (pi1' := IHpi1S _ eq_refl)) ;
  try (assert (pi2' := IHpi2S _ eq_refl)) ;
  try (assert (pi0' := IHpiN eq_refl)) ;
  try (assert (pi1' := IHpi1N eq_refl)) ;
  try (assert (pi2' := IHpi2N eq_refl)) ;
  try (now (constructor ; myeeasy)) ;
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

Definition Foc x :=
  { sformula x } + { exists X, x = covar X } + { exists y, x = wn y }.

Lemma Foc_dec : forall x, Foc x + (Foc x -> False).
Proof with myeeasy.
induction x ;
  try (now (left ; left ; left ; constructor)) ;
  try (now (left ; left ; right ; eexists ; reflexivity)) ;
  try (now (left ; right ; eexists ; reflexivity)) ;
  try (now (right ; reflexivity)) ;
  try (now (right ; intros [[ H | [X H] ] | [X H] ] ; inversion H)).
Qed.

Lemma Focl_dec : forall l, Forall_inf Foc l + (Forall_inf Foc l -> False).
Proof with myeasy.
induction l.
- left ; constructor.
- destruct (Foc_dec a).
  + destruct IHl.
    * left ; constructor...
    * right ; intros H.
      inversion H ; subst ; intuition.
  + right ; intros H.
    inversion H ; subst ; intuition.
Qed.

Lemma not_Foc : forall x, (Foc x -> False) ->
  (x = bot) + { y | x = parr (fst y) (snd y) } +
  (x = top) + { y | x = awith (fst y) (snd y) }.
Proof with myeasy.
destruct x ; intros HnF ;
  try (now (exfalso ; apply HnF ; left ; left ; constructor)) ;
  try (now (exfalso ; apply HnF ; left ; left ; right ; eexists ; reflexivity)) ;
  try (now (exfalso ; apply HnF ; left ; right ; eexists ; reflexivity)) ;
  try (now (exfalso ; apply HnF ; right ; eexists ; reflexivity)).
- left ; left ; left...
- left ; left ; right ; exists (x1,x2)...
- left ; right...
- right ; eexists (x1,x2)...
Qed.

Lemma not_Focl : forall l, (Forall_inf Foc l -> False) ->
  { l' : _ & l = fst (snd l') ++ fst l' :: (snd (snd l'))
           & sum (sum (sum (fst l' = bot) { B | fst l' = parr (fst B) (snd B) })
                           (fst l' = top)) { B | fst l' = awith (fst B) (snd B) } }.
Proof with myeeasy.
intros l HnF.
apply Forall_inf_neg_Exists_inf in HnF.
- induction l ; inversion HnF ; subst.
  + exists (a,(nil,l))...
    simpl ; apply not_Foc...
  + apply IHl in X as [l' Heq Hf] ; subst.
    exists (fst l',(a::fst (snd l'),snd (snd l')))...
- intros x.
  assert (Hd := Foc_dec x).
  destruct Hd ; intuition.
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
                      llFoc (wn A :: l) None
| wk_Fr : forall A l, llFoc l None -> llFoc (wn A :: l) None
| co_Fr : forall A l, llFoc (wn A :: wn A :: l) None ->
                      llFoc (wn A :: l) None.

#[export] Instance llFoc_perm {Pi} :
  Proper ((@Permutation_Type _) ==> Basics.arrow) (fun l => llFoc l Pi).
Proof.
intros l1 l2 HP pi.
eapply ex_Fr ; eassumption.
Qed.

Lemma top_gen_Fr : forall l, llFoc (top :: l) None.
Proof with myeeasy.
intros l.
remember (list_sum (map fsize l)) as n.
revert l Heqn ; induction n using lt_wf_rect;
  intros l Heqn ; subst.
destruct (tFocl_dec l).
- apply top_Fr...
- apply not_tFocl in f.
  destruct f as [ (A & l1 & l2) Heq [[Hb | [[B C] Hp] ] | [[B C] Hw]]] ;
    subst ; simpl.
  + simpl in Hb ; subst ; rewrite app_comm_cons.
    eapply ex_Fr ; [ apply bot_Fr | apply Permutation_Type_middle ].
    list_simpl ; eapply X...
    simpl ; rewrite 2 map_app ; rewrite 2 list_sum_app ; simpl...
  + simpl in Hp ; subst ; rewrite app_comm_cons.
    eapply ex_Fr ; [ apply parr_Fr | apply Permutation_Type_middle ].
    list_simpl ; eapply ex_Fr ;
    [ eapply X
    | etransitivity ; [ apply Permutation_Type_swap
                      | apply (Permutation_Type_cons eq_refl) ;
                        etransitivity ; [ apply Permutation_Type_swap |  ]]]...
    simpl ; rewrite 2 map_app ; rewrite 2 list_sum_app ; simpl...
  + simpl in Hw ; subst ; rewrite app_comm_cons.
    eapply ex_Fr ; [ apply with_Fr | apply Permutation_Type_middle ].
    * list_simpl ; eapply ex_Fr ;
        [ eapply X
        | etransitivity ; [ apply Permutation_Type_swap | apply Permutation_Type_cons ; reflexivity ]]...
    simpl ; rewrite 2 map_app ; rewrite 2 list_sum_app ; simpl...
    * list_simpl ; eapply ex_Fr ;
        [ eapply X
        | etransitivity ; [ apply Permutation_Type_swap | apply Permutation_Type_cons ; reflexivity ]]...
    simpl ; rewrite 2 map_app ; rewrite 2 list_sum_app ; simpl...
Qed.

Lemma sync_focus_F : forall l A, llFoc l (Some A) -> sformula A.
Proof.
intros l A pi.
remember (Some A) as Pi ; revert HeqPi ; induction pi ;
  intros HeqPi ; inversion HeqPi ; subst ;
  try (now constructor) ;
  try apply IHpi ;
  try assumption.
Qed.

Lemma Foc_context : forall l A, llFoc l (Some A) -> Forall_inf Foc l.
Proof with myeeasy.
intros l A pi.
remember (Some A) as Pi.
revert A HeqPi ; induction pi ; intros P HeqPi ; subst ;
  try (now inversion HeqPi).
- constructor ; [ | constructor ].
  left ; right.
  eexists...
- eapply Permutation_Type_Forall_inf...
  eapply IHpi...
- apply Forall_inf_app...
- clear ; remember (map wn l) as l0.
  revert l Heql0 ; induction l0 ; intros l Heql0 ;
    destruct l ; inversion Heql0 ; subst ; constructor.
  + right ; eexists...
  + eapply IHl0...
Qed.

Lemma llFoc_foc_is_llFoc_foc : forall l A, llFoc l (Some A) ->
  llFoc (polcont l A) (polfoc A).
Proof.
intros l A pi.
assert (Hs := sync_focus_F _ _ pi).
rewrite (polconts _ _ Hs).
rewrite (polfocs _ Hs).
apply pi.
Qed.

Lemma incl_Foc : forall l l0 lw lw', llFoc l None ->
  Permutation_Type l (map wn lw ++ l0) -> incl_inf lw lw' ->
    llFoc (map wn lw' ++ l0) None.
Proof with myeeasy.
intros l l0 lw ; revert l l0 ; induction lw ; intros l l0 lw' pi HP Hsub.
- clear Hsub ; induction lw'.
  + eapply ex_Fr...
  + apply wk_Fr...
- destruct (incl_inf_cons_inv Hsub) as [Hin Hi].
  eapply IHlw in pi ; [ | | apply Hi ].
  + apply in_inf_split in Hin.
    destruct Hin as ((l1 & l2) & Heq) ; subst.
    eapply ex_Fr ; [ apply co_Fr | ].
    * eapply ex_Fr ; [ apply pi | ].
      rewrite map_app ; simpl.
      rewrite <- app_assoc.
      rewrite <- app_comm_cons.
      symmetry ; apply Permutation_Type_cons_app.
      rewrite app_assoc.
      apply Permutation_Type_cons_app.
      reflexivity.
    * rewrite <- app_assoc.
      rewrite map_app ; simpl.
      rewrite <- app_assoc.
      rewrite <- app_comm_cons.
      apply Permutation_Type_cons_app.
      reflexivity.
  + etransitivity ; [ apply HP | ].
    simpl ; apply Permutation_Type_middle.
Qed.

Theorem llfoc_to_llFoc : forall s l Pi (pi : llfoc l Pi), fpsize pi < s ->
   (Pi = None -> llFoc l None)
 * (forall C, Pi = Some C -> Forall_inf Foc l ->
       { llw & prod (prod (Permutation_Type l (map wn (fst (snd llw)) ++ (fst llw)))
                          (incl_inf (snd (snd llw)) (fst (snd llw))))
                          (llFoc (map wn (snd (snd llw)) ++ (fst llw)) (Some C)) })
 * (forall C, Pi = Some C -> (Forall_inf Foc l -> False) ->
      (llFoc (C :: l) None) * llFoc (wn C :: l) None).
Proof with myeeasy.
  induction s using (well_founded_induction_type lt_wf) ;
    intros l pi ; split ; [ split | ] ;
    [ intros Heq ; destruct pi0 ; inversion Heq ; subst ; simpl in H
    | intros PPi Heq HF ; destruct pi0 ; inversion Heq ; subst ; simpl in H
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
    destruct f as ((l1 & lw & lw') & (HP & Hi) & IH).
    simpl in HP ; simpl in Hi ; simpl in IH.
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
  + rewrite (polconts _ _ Hs) in H.
    rewrite (polfocs _ Hs) in H.
    destruct (Focl_dec l).
    * eapply (snd (fst H)) in f...
      destruct f as ((l1 & lw & lw') & (HP & Hi) & IH).
      simpl in HP ; simpl in Hi ; simpl in IH.
      apply (Permutation_Type_cons_app _ _ (wn A)) in HP.
      symmetry in HP.
      eapply ex_Fr...
      eapply incl_Foc...
      rewrite <- (polconts A _ Hs) in IH.
      rewrite <- (polfocs A Hs) in IH.
      eapply ex_Fr ; [ apply de_Fr | ]...
      apply Permutation_Type_cons_app...
    * eapply (snd H) in f...
      apply f.
  + rewrite (polconta _ _ Ha) in H.
    rewrite (polfoca _ Ha) in H.
    apply H in Heq...
    rewrite <- (polconta A l Ha) in Heq.
    rewrite <- (polfoca A Ha) in Heq.
    apply de_Fr...
- specialize X with (S (fpsize pi0)) _ _ pi0.
  apply X in H...
  apply wk_Fr.
  apply H...
- specialize X with (S (fpsize pi0)) _ _ pi0.
  apply X in H...
  apply co_Fr.
  apply H...
(* second conjunct *)
- exists (covar X0 :: nil,(nil , nil)) ; split ; [ split | ]...
  + apply incl_inf_nil_l.
  + apply ax_Fr.
- symmetry in p.
  specialize X with (S (fpsize pi0)) _ _ pi0.
  apply X in H...
  apply (snd (fst H)) in H0.
  + destruct H0 as ((l0 & lw & lw') & (HP & Hi) & IH).
    simpl in HP ; simpl in Hi ; simpl in IH.
    exists (l0,(lw,lw')) ; simpl ; split ; [ split | ]...
    etransitivity...
  + apply (Permutation_Type_Forall_inf p)...
- exists (nil,(nil,nil)) ; simpl ; split ; [ split | ]...
  + apply incl_inf_nil_l.
  + apply one_Fr.
- exfalso.
  inversion HF ; subst.
  destruct H2 as [[H' | [X' H']] | [X' H']] ; inversion H'.
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
    destruct HF1 as ((l01 & lw1 & lw1') & (HP1 & Hi1) & pi1).
    simpl in HP1 ; simpl in Hi1 ; simpl in pi1.
    destruct HF2 as ((l02 & lw2 & lw2') & (HP2 & Hi2) & pi2).
    simpl in HP2 ; simpl in Hi2 ; simpl in pi2.
    exists (l01 ++ l02,(lw1 ++ lw2,lw1' ++ lw2')) ; simpl ; split ; [ split | ].
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
    destruct HF1 as ((l01 & lw1 & lw1') & (HP1 & Hi1) & pi1).
    simpl in HP1 ; simpl in Hi1 ; simpl in pi1.
    assert (pi2 := fst (fst H') eq_refl).
    exists (l01 ++ l2,(lw1,lw1')) ; simpl ; split ; [ split | ]...
    * etransitivity ; [ apply (Permutation_Type_app_tail _ HP1) | ].
      rewrite <- app_assoc...
    * eapply ex_Fr ; [ apply tens_Fr | ].
      -- rewrite (polconts _ _ HsA).
         rewrite (polfocs _ HsA)...
      -- rewrite (polconta _ _ HaB).
         rewrite (polfoca _ HaB)...
      -- apply Foc_context in pi1...
      -- assumption.
      -- rewrite <- app_assoc...
  + rewrite (polconta _ _ HaA) in H.
    rewrite (polfoca _ HaA) in H.
    rewrite (polconts _ _ HsB) in H'.
    rewrite (polfocs _ HsB) in H'.
    assert (pi1 := fst (fst H) eq_refl).
    eapply (snd (fst H')) in HF2...
    destruct HF2 as ((l02 & lw2 & lw2') & (HP2 & Hi2) & pi2).
    simpl in HP2 ; simpl in Hi2 ; simpl in pi2.
    exists (l1 ++ l02,(lw2,lw2')) ; simpl ; split ; [ split | ]...
    * etransitivity ; [ apply (Permutation_Type_app_head _ HP2) | ].
      rewrite 2 app_assoc...
      apply Permutation_Type_app_tail.
      apply Permutation_Type_app_comm.
    * eapply ex_Fr ; [ apply tens_Fr | ].
      -- rewrite (polconta _ _ HaA).
         rewrite (polfoca _ HaA)...
      -- rewrite (polconts _ _ HsB).
         rewrite (polfocs _ HsB)...
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
    exists (l1 ++ l2,(nil,nil)) ; simpl ; split ; [ split | ]...
    * apply incl_inf_nil_l.
    * eapply ex_Fr ; [ apply tens_Fr | ].
      -- rewrite (polconta _ _ HaA).
         rewrite (polfoca _ HaA)...
      -- rewrite (polconta _ _ HaB).
         rewrite (polfoca _ HaB)...
      -- assumption.
      -- assumption.
      -- reflexivity.
- exfalso.
  inversion HF ; subst.
  destruct H2 as [[H' | [X' H']] | [X' H']] ; inversion H'.
- exfalso.
  inversion HF ; subst.
  destruct H2 as [[H' | [X' H']] | [X' H']] ; inversion H'.
- specialize X with (S (fpsize pi0)) _ _ pi0.
  apply X in H...
  destruct (polarity A) as [HsA | HaA].
  + rewrite (polconts _ _ HsA) in H.
    rewrite (polfocs _ HsA) in H.
    eapply (snd (fst H)) in HF ; [ | reflexivity ].
    destruct HF as ((l0 & lw & lw') & (HP & Hi) & pi).
    simpl in HP ; simpl in Hi ; simpl in pi.
    exists (l0,(lw,lw')) ; simpl ; split ; [ split | ]...
    apply plus_Fr1.
    * rewrite (polconts _ _ HsA).
      rewrite (polfocs _ HsA)...
    * apply Foc_context in pi...
  + rewrite (polconta _ _ HaA) in H.
    rewrite (polfoca _ HaA) in H.
    assert (pi := fst (fst H) eq_refl).
    exists (l,(nil,nil)) ; simpl ; split ; [ split | ]...
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
    destruct HF as ((l0 & lw & lw') & (HP & Hi) & pi).
    simpl in HP ; simpl in Hi ; simpl in pi.
    exists (l0,(lw,lw')) ; simpl ; split ; [ split | ]...
    apply plus_Fr2.
    * rewrite (polconts _ _ HsA).
      rewrite (polfocs _ HsA)...
    * apply Foc_context in pi...
  + rewrite (polconta _ _ HaA) in H.
    rewrite (polfoca _ HaA) in H.
    assert (pi := fst (fst H) eq_refl).
    exists (l,(nil,nil)) ; simpl ; split ; [ split | ]...
    * apply incl_inf_nil_l.
    * apply plus_Fr2...
      rewrite (polconta _ _ HaA).
      rewrite (polfoca _ HaA)...
- exfalso.
  inversion HF ; subst.
  destruct H2 as [[H' | [X' H']] | [X' H']] ; inversion H'.
- specialize X with (S (fpsize pi0)) _ _ pi0.
  apply X in H...
  assert (pi := fst (fst H) eq_refl).
  exists (map wn l,(nil,nil)) ; simpl ; split ; [ split | ]...
  * apply incl_inf_nil_l.
  * apply oc_Fr...
- inversion HF ; subst.
  specialize X with (S (fpsize pi0)) _ _ pi0.
  apply X in H...
  eapply (snd (fst H)) in X0 ; [ | reflexivity ].
  destruct X0 as ((l0 & lw & lw') & (HP & Hi) & pi).
  simpl in HP ; simpl in Hi ; simpl in pi.
  exists (l0,(A :: lw,lw')) ; simpl ; split ; [ split | ]...
  + list_simpl ; apply Permutation_Type_cons...
  + apply incl_inf_tl...
- inversion HF ; subst.
  assert (Forall_inf Foc (wn A :: wn A :: l)) as HF'
    by (constructor ; assumption).
  specialize X with (S (fpsize pi0)) _ _ pi0.
  apply X in H...
  eapply (snd (fst H)) in HF'...
  destruct HF' as ((l0 & lw & lw') & (HP & Hi) & pi).
  simpl in HP ; simpl in Hi ; simpl in pi.
  symmetry in HP.
  assert (HP' := HP).
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as ((l1' & l2') & Heq) ; simpl in Heq.
  dichot_elt_app_inf_exec Heq ; subst.
  + decomp_map Heq0 eqn:Hw. subst. injection Hw as [= ->].
    assert (HP' := HP).
    list_simpl in HP'.
    symmetry in HP'.
    apply Permutation_Type_cons_app_inv in HP'.
    symmetry in HP'.
    apply Permutation_Type_vs_cons_inv in HP'.
    destruct HP' as ((l1'' & l2'') & Heq) ; simpl in Heq.
    rewrite app_assoc in Heq.
    dichot_elt_app_inf_exec Heq ; subst.
    * rewrite <- map_app in Heq0.
      decomp_map Heq0 eqn:Hw. injection Hw as [= ->].
      exists (l0,(l1' ++ l1,lw')) ; simpl ; split ; [ split | ]...
      -- symmetry in HP.
         list_simpl in HP.
         apply Permutation_Type_cons_app_inv in HP.
         list_simpl...
      -- revert Hi Heq0 ; clear ; induction lw' ; intros Hi Heq.
         ++ apply incl_inf_nil_l.
         ++ destruct (incl_inf_cons_inv Hi) as [Hin Hi'].
            assert (HP := Permutation_Type_middle l1' l1 A).
            symmetry in HP ; apply (Permutation_Type_in_inf _ HP) in Hin.
            inversion Hin ; subst.
            ** apply incl_inf_cons.
               --- rewrite <- Heq.
                   apply in_inf_elt.
               --- apply IHlw'...
            ** apply incl_inf_cons...
               apply IHlw'...
    * exists (l2 ++ l2'', (l1' ++ A :: l1, A :: lw')) ; simpl ; split ; [ split | ]...
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
    * decomp_map Heq0 eqn:Hw. subst. injection Hw as [= ->].
      exists (l1 ++ l2', (l1'' ++ A :: l0, A :: lw')) ; simpl ; split ; [ split | ]...
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
    * exists (l0 ++ l2'',(A :: lw,A :: A :: lw')) ; simpl ; split ; [ split | ]...
      -- symmetry in HP.
         rewrite app_assoc in HP.
         apply Permutation_Type_cons_app_inv in HP.
         list_simpl.
         etransitivity ; [ apply HP | ].
         simpl in Heq1 ; list_simpl.
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
- apply not_Focl in HnF.
  destruct HnF as [(A & l1 & l2) Heq' [[[Hb | ([B' C'] & Hp)] | Ht ] | ([B' C'] & Hw)]] ;
    subst ; simpl ; simpl in H ; simpl in pi0 ;
    [simpl in Hb | simpl in Hp | simpl in Ht | simpl in Hw] ; subst.
  + destruct (bot_rev_f _ _ pi0 _ _ eq_refl) as [pi Hs].
    specialize X with (S (fpsize pi)) _ _ pi.
    assert (S (fpsize pi) < s) as Hs'...
    apply X in Hs'...
    destruct (Focl_dec (l1 ++ l2)) as [HF | HnF].
    * eapply (snd (fst Hs')) in HF...
      destruct HF as ((l0 & lw & lw') & (HP & Hi) & pi').
      simpl in HP ; simpl in Hi ; simpl in pi'.
      split.
      -- apply foc_Fr in pi'.
         eapply (incl_Foc _ (C :: l0)) in pi'...
         ++ eapply ex_Fr ; [ apply bot_Fr | ]...
            rewrite (app_comm_cons _ _ C).
            apply Permutation_Type_cons_app.
            list_simpl ; symmetry.
            apply Permutation_Type_cons_app...
         ++ apply Permutation_Type_cons_app...
      -- apply llFoc_foc_is_llFoc_foc in pi'.
         apply de_Fr in pi'.
         eapply (incl_Foc _ (wn C :: l0)) in pi'...
         ++ eapply ex_Fr ; [ apply bot_Fr | ]...
            rewrite (app_comm_cons _ _ (wn C)).
            apply Permutation_Type_cons_app.
            list_simpl ; symmetry.
            apply Permutation_Type_cons_app...
         ++ apply Permutation_Type_cons_app...
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
      destruct HF as ((l0 & lw & lw') & (HP & Hi) & pi').
      simpl in HP ; simpl in Hi ; simpl in pi'.
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
      -- apply llFoc_foc_is_llFoc_foc in pi'.
         apply de_Fr in pi'.
         eapply (incl_Foc _ (wn C :: l0)) in pi'...
         ++ eapply ex_Fr ; [ apply parr_Fr ; eapply ex_Fr | ]...
            ** symmetry.
               etransitivity ; [ | apply Permutation_Type_middle ].
               symmetry in HP ; symmetry.
               apply (@Permutation_Type_cons _ _ (wn C) eq_refl) in HP.
               etransitivity ; [ apply HP | ].
               rewrite app_comm_cons.
               symmetry.
               apply Permutation_Type_cons_app.
               apply Permutation_Type_cons_app...
            ** rewrite (app_comm_cons _ _ (wn C)).
               apply Permutation_Type_cons_app...
         ++ apply Permutation_Type_cons_app...
    * destruct ((snd Hs') _ eq_refl HnF) as [pi1 pi2] ; split.
      -- eapply ex_Fr ; [ apply parr_Fr ; eapply ex_Fr ; [ apply pi1 | ] | ]...
         ++ rewrite app_comm_cons.
            symmetry.
            apply Permutation_Type_cons_app.
            apply Permutation_Type_cons_app...
         ++ rewrite (app_comm_cons _ _ C).
            apply Permutation_Type_cons_app...
      -- eapply ex_Fr ; [ apply parr_Fr ; eapply ex_Fr ;
                          [ apply pi2 | ] | ]...
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
         destruct HF1 as ((l01 & lw1 & lw1') & (HP1 & Hi1) & pi1').
         simpl in HP1 ; simpl in Hi1 ; simpl in pi1'.
         destruct (Foc_dec C') as [HFC | HnFC].
         ++ assert (Forall_inf Foc (l1 ++ C' :: l2)) as HF2.
            { apply Forall_inf_app...
              constructor... }
            eapply (snd (fst Hs2')) in HF2...
            destruct HF2 as ((l02 & lw2 & lw2') & (HP2 & Hi2) & pi2').
            simpl in HP2 ; simpl in Hi2 ; simpl in pi2'.
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
            ** apply llFoc_foc_is_llFoc_foc in pi1'.
               apply de_Fr in pi1'.
               apply llFoc_foc_is_llFoc_foc in pi2'.
               apply de_Fr in pi2'.
               eapply (incl_Foc _ (wn C :: l01) lw1') in pi1' ; 
                 [ eapply (incl_Foc _ (wn C :: l02) lw2') in pi2' | | ]...
               --- eapply ex_Fr ; [ apply with_Fr ; eapply ex_Fr | ].
                   +++ apply pi1'.
                   +++ symmetry.
                       etransitivity ; [ | apply Permutation_Type_middle ].
                       symmetry in HP1 ; symmetry.
                       apply (@Permutation_Type_cons _ _ (wn C) eq_refl) in HP1.
                       etransitivity ; [ apply HP1 | ].
                       rewrite app_comm_cons.
                       symmetry.
                       apply Permutation_Type_cons_app...
                   +++ apply pi2'.
                   +++ symmetry.
                       etransitivity ; [ | apply Permutation_Type_middle ].
                       symmetry in HP2 ; symmetry.
                       apply (@Permutation_Type_cons _ _ (wn C) eq_refl) in HP2.
                       etransitivity ; [ apply HP2 | ].
                       rewrite app_comm_cons.
                       symmetry.
                       apply Permutation_Type_cons_app...
                   +++ rewrite (app_comm_cons _ (awith _ _ :: _) (wn C)).
                       apply Permutation_Type_cons_app...
               --- apply Permutation_Type_cons_app...
               --- apply Permutation_Type_cons_app...
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
               --- apply llFoc_foc_is_llFoc_foc in pi1'.
                   apply de_Fr in pi1'.
                   eapply (incl_Foc _ (wn C :: l01) lw1') in pi1'.
                   +++ eapply ex_Fr ; [ apply pi1' | ].
                       etransitivity ; [ symmetry ; apply Permutation_Type_middle | ].
                       symmetry in HP1.
                       apply (@Permutation_Type_cons _ _ (wn C) eq_refl) in HP1.
                       etransitivity ; [ apply HP1 | ].
                       rewrite app_comm_cons.
                       symmetry.
                       apply Permutation_Type_middle.
                   +++ apply Permutation_Type_middle.
                   +++ apply Hi1.
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
            destruct HF2 as ((l02 & lw2 & lw2') & (HP2 & Hi2) & pi2').
            simpl in HP2 ; simpl in Hi2 ; simpl in pi2'.
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
            ** apply llFoc_foc_is_llFoc_foc in pi2'.
               apply de_Fr in pi2'.
               eapply (incl_Foc _ (wn C :: l02) lw2') in pi2'...
               --- eapply ex_Fr ; [ apply with_Fr ; eapply ex_Fr | ].
                   +++ apply pi1''.
                   +++ rewrite app_comm_cons.
                       symmetry ; apply Permutation_Type_middle.
                   +++ apply pi2'.
                   +++ etransitivity ; [ symmetry ; apply Permutation_Type_middle | ].
                       symmetry in HP2.
                       apply (@Permutation_Type_cons _ _ (wn C) eq_refl) in HP2.
                       etransitivity ; [ apply HP2 | ].
                       rewrite app_comm_cons.
                       symmetry.
                       apply Permutation_Type_middle.
                   +++ rewrite (app_comm_cons _ (awith _ _ :: _) (wn C)).
                       apply Permutation_Type_cons_app...
               --- apply Permutation_Type_cons_app...
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
    GPermutation_Type_solve.
  + rewrite_all (polfocs A HsA).
    rewrite_all (polfoca B HaB).
    assert (pi1' := IHpi1S _ eq_refl).
    assert (pi2' := IHpi2N eq_refl).
    eapply ex_r ; [ apply tens_r | ].
    * apply pi1'.
    * rewrite (polconta _ _ HaB) in pi2'.
      apply pi2'.
    * rewrite (polconts _ _ HsA).
      GPermutation_Type_solve.
  + rewrite_all (polfoca A HaA).
    rewrite_all (polfocs B HsB).
    assert (pi1' := IHpi1N eq_refl).
    assert (pi2' := IHpi2S _ eq_refl).
    eapply ex_r ; [ apply tens_r | ].
    * rewrite (polconta _ _ HaA) in pi1'.
      apply pi1'.
    * apply pi2'.
    * rewrite (polconts _ _ HsB).
      GPermutation_Type_solve.
  + rewrite_all (polfoca A HaA).
    rewrite_all (polfoca B HaB).
    assert (pi1' := IHpi1N eq_refl).
    assert (pi2' := IHpi2N eq_refl).
    eapply ex_r ; [ apply tens_r | ].
    * rewrite (polconta _ _ HaA) in pi1'.
      apply pi1'.
    * rewrite (polconta _ _ HaB) in pi2'.
      apply pi2'.
    * GPermutation_Type_solve.
- destruct (polarity A) as [HsA | HaA].
  + rewrite_all (polfocs A HsA).
    assert (pi' := IHpiS _ eq_refl).
    eapply ex_r ; [ apply plus_r1 | ].
    * apply pi'.
    * rewrite (polconts _ _ HsA).
      GPermutation_Type_solve.
  + rewrite_all (polfoca A HaA).
    assert (pi' := IHpiN eq_refl).
    eapply ex_r ; [ apply plus_r1 | ].
    * rewrite (polconta _ _ HaA) in pi'.
      apply pi'.
    * GPermutation_Type_solve.
- destruct (polarity A) as [HsA | HaA].
  + rewrite_all (polfocs A HsA).
    assert (pi' := IHpiS _ eq_refl).
    eapply ex_r ; [ apply plus_r2 | ].
    * apply pi'.
    * rewrite (polconts _ _ HsA).
      GPermutation_Type_solve.
  + rewrite_all (polfoca A HaA).
    assert (pi' := IHpiN eq_refl).
    eapply ex_r ; [ apply plus_r2 | ].
    * rewrite (polconta _ _ HaA) in pi'.
      apply pi'.
    * GPermutation_Type_solve.
- destruct (polarity A) as [HsA | HaA].
  + rewrite_all (polfocs A HsA).
    assert (pi' := IHpiS _ eq_refl).
    eapply ex_r ; [ apply de_r | ].
    * apply pi'.
    * rewrite (polconts _ _ HsA).
      GPermutation_Type_solve.
  + rewrite_all (polfoca A HaA).
    assert (pi' := IHpiN eq_refl).
    eapply ex_r ; [ apply de_r | ].
    * rewrite (polconta _ _ HaA) in pi'.
      apply pi'.
    * GPermutation_Type_solve.
Qed.
