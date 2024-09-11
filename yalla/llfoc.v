(** * Focusing in Linear Logic *)

From Coq Require Import CMorphisms Wf_nat Lia.
From OLlibs Require Import infinite funtheory Bool_more List_more Permutation_Type_more.
From Yalla Require Import ll_fragments.

Set Default Proof Using "Type".
Set Implicit Arguments.


Section Atoms.

Context {atom : InfDecType}.
Notation formula := (@formula atom).

(** ** Synchronous and asynchronous formulas *)
Variant sformula : formula -> Type :=
| pvar x : sformula (var x)
| pone : sformula one
| ptens A B : sformula (tens A B)
| pzero : sformula zero
| pplus A B : sformula (aplus A B)
| poc A : sformula (oc A).

Variant aformula : formula -> Type :=
| ncovar x : aformula (covar x)
| nbot : aformula bot
| nparr A B : aformula (parr A B)
| ntop : aformula top
| nwith A B : aformula (awith A B)
| nwn A : aformula (wn A).

Lemma polarity A : sformula A + aformula A.
Proof. destruct A; (left + right; constructor). Defined.

Lemma disj_polarity A : notT (sformula A * aformula A).
Proof. destruct A; intros [Hp Hn]; inversion Hp; inversion Hn. Qed.

Lemma sformula_dual A : sformula (dual A) -> aformula A.
Proof. intro Hp. destruct A; inversion Hp; constructor. Qed.

Lemma aformula_dual A : aformula (dual A) -> sformula A.
Proof. intro Hn. destruct A; inversion Hn; constructor. Qed.

Definition Foc x := (sformula x + covar_formula x)%type.

Definition is_Foc (A : formula) :=
  match A with
  | covar _ | var _ | one | tens _ _ | zero | aplus _ _ | oc _ => true
  | _ => false
  end.

Lemma Foc_spec A : reflectT (Foc A) (is_Foc A).
Proof. destruct A; cbn; constructor; try (now repeat constructor); intros [H|H]; inversion H. Qed.

Lemma Foc_not_wn A : notT (Foc A * wn_formula A).
Proof. intros [[Hf|Hf] Hwn]; inversion Hwn; subst; inversion Hf. Qed.

Definition wFoc x := (Foc x + wn_formula x)%type.

Lemma wFoc_wn x : wFoc (wn x).
Proof. right. constructor. Qed.

Lemma wFoc_dec x : wFoc x + notT (wFoc x).
Proof. destruct x; try (now repeat constructor); now right; intros [H|H]; inversion H. Qed.

Lemma wFocl_dec l : Forall_inf wFoc l + notT (Forall_inf wFoc l).
Proof.
induction l as [|a l IHl].
- left. constructor.
- destruct (wFoc_dec a).
  + destruct IHl.
    * left. constructor; assumption.
    * right. intro H. now inversion H.
  + right. intro H. now inversion H.
Qed.

Lemma not_wFoc x : notT (wFoc x) ->
  (x = bot) + {'(y1, y2) | x = parr y1 y2 } + (x = top) + {'(y1, y2) | x = awith y1 y2 }.
Proof.
destruct x; intros HnF;
  try (now exfalso; apply HnF; left; left; constructor);
  try (now exfalso; apply HnF; left; left; right; eexists);
  try (now exfalso; apply HnF; left; right; eexists);
  try (now exfalso; apply HnF; right; eexists).
- left. left. left. reflexivity.
- left. left. right. exists (x1,x2). reflexivity.
- left. right. reflexivity.
- right. exists (x1,x2). reflexivity.
Qed.

Lemma not_wFocl l : notT (Forall_inf wFoc l) ->
  {'(A, l1, l2) & l = l1 ++ A :: l2
                & ((A = bot) + {'(A1, A2) | A = parr A1 A2 }
                 + (A = top) + {'(A1, A2) | A = awith A1 A2 })%type }.
Proof.
intros HnF%Forall_inf_neg_Exists_inf.
- induction l as [|a l IHl]; inversion HnF; subst.
  + exists (a, nil, l); [ reflexivity | ].
    apply not_wFoc. assumption.
  + apply IHl in X as [[[b l1] l2] -> Hf].
    now exists (b, a::l1, l2).
- exact wFoc_dec.
Qed.

Lemma Foc_wFoc A : Foc A -> wFoc A.
Proof. intro. left. assumption. Qed.

Lemma wFoc_not_wn_Foc A : wFoc A -> notT (wn_formula A) -> Foc A.
Proof. intros [|] Hwn; [ assumption | contradiction Hwn ]. Qed.

Definition wtFoc x := (wFoc x + (x = top))%type.

Lemma wtFoc_dec x : wtFoc x + notT (wtFoc x).
Proof.
destruct x; try (now repeat constructor); now right; intros [H'|H']; inversion H'; inversion X.
Qed.

Lemma wtFocl_dec l : Forall_inf wtFoc l + notT (Forall_inf wtFoc l).
Proof.
induction l as [| a l IHl].
- left. constructor.
- destruct (wtFoc_dec a).
  + destruct IHl.
    * left. constructor; assumption.
    * right. intro H. now inversion H.
  + right. intro H. now inversion H.
Qed.

Lemma not_wtFoc x : notT (wtFoc x) ->
  (x = bot) + {'(y1, y2) | x = parr y1 y2 } + {'(y1, y2) | x = awith y1 y2 }.
Proof.
destruct x; intros HnF;
  try (now (exfalso; apply HnF; left; left; left; constructor));
  try (now (exfalso; apply HnF; left; left; right; eexists; reflexivity));
  try (now (exfalso; apply HnF; left; right; eexists; reflexivity));
  try (now (exfalso; apply HnF; right; reflexivity)).
- left. left. reflexivity.
- left. right. exists (x1, x2). reflexivity.
- right. exists (x1, x2). reflexivity.
Qed.

Lemma not_wtFocl l : notT (Forall_inf wtFoc l) ->
  {'(A, l1, l2) & l = l1 ++ A :: l2
                & ((A = bot) + {'(A1, A2) | A = parr A1 A2 }
                             + {'(A1, A2) | A = awith A1 A2 })%type }.
Proof.
intros HnF%Forall_inf_neg_Exists_inf.
- induction l as [|a l IHl]; inversion HnF; subst.
  + exists (a, nil, l); [ reflexivity | ].
    apply not_wtFoc. assumption.
  + apply IHl in X as [[[b l1] l2] -> Hf].
    now exists (b, a :: l1, l2).
- exact wtFoc_dec.
Qed.


(** ** The weakly focused system [llfoc] *)

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
intros. unfold polcont. destruct (polarity A); [ reflexivity | ].
exfalso. eapply disj_polarity. split; eassumption.
Qed.
Lemma polconta A l : aformula A -> polcont l A = A :: l.
Proof.
intros. unfold polcont. destruct (polarity A); [ | reflexivity ].
exfalso. eapply disj_polarity. split; eassumption.
Qed.
Lemma polfocs A : sformula A -> polfoc A = Some A.
Proof.
intros. unfold polfoc. destruct (polarity A); [ reflexivity | ].
exfalso. eapply disj_polarity. split; eassumption.
Qed.
Lemma polfoca A : aformula A -> polfoc A = None.
Proof.
intros. unfold polfoc. destruct (polarity A); [ | reflexivity ].
exfalso. eapply disj_polarity. split; eassumption.
Qed.

Ltac pol_simpl :=
  match goal with
  | Hs : sformula _ |- _ => rewrite ? (fun l => polconts l Hs), ? (polfocs Hs) in *;
                            revert Hs; pol_simpl; intro Hs
  | Ha : aformula _ |- _ => rewrite ? (fun l => polconta l Ha), ? (polfoca Ha) in *;
                            revert Ha; pol_simpl; intro Ha
  | _ => idtac
  end.

Lemma Permutation_Type_polcont l1 l2 A :
  Permutation_Type l1 l2 -> Permutation_Type (polcont l1 A) (polcont l2 A).
Proof. intro HP. now destruct (polarity A); pol_simpl; [ | apply Permutation_Type_cons ]. Qed.

Lemma Permutation_Type_middle_polcont l1 l2 A B :
  Permutation_Type (B :: polcont (l1 ++ l2) A) (polcont (l1 ++ B :: l2) A).
Proof.
unfold polcont. destruct (polarity A); [ | rewrite 2 (app_comm_cons _ _ A)]; apply Permutation_Type_middle.
Qed.

Inductive llfoc : list formula -> option formula -> Type :=
| ax_fr X : llfoc (covar X :: nil) (Some (var X))
| ex_fr l1 l2 Pi : llfoc l1 Pi -> Permutation_Type l1 l2 -> llfoc l2 Pi
| foc_fr A l : llfoc l (Some A) -> llfoc (A :: l) None
| one_fr : llfoc nil (Some one)
| bot_fr l Pi : llfoc l Pi -> llfoc (bot :: l) Pi
| tens_fr A B l1 l2 : llfoc (polcont l1 A) (polfoc A) -> llfoc (polcont l2 B) (polfoc B) ->
                      llfoc (l1 ++ l2) (Some (tens A B))
| parr_fr A B l Pi : llfoc (A :: B :: l) Pi -> llfoc (parr A B :: l) Pi
| top_fr l Pi : option_testT sformula Pi -> Forall_inf wtFoc l -> llfoc (top :: l) Pi
| plus_fr1 A B l : llfoc (polcont l A) (polfoc A) -> llfoc l (Some (aplus A B))
| plus_fr2 A B l : llfoc (polcont l A) (polfoc A) -> llfoc l (Some (aplus B A))
| with_fr A B l Pi : llfoc (A :: l) Pi -> llfoc (B :: l) Pi -> llfoc (awith A B :: l) Pi
| oc_fr A l : llfoc (A :: map wn l) None -> llfoc (map wn l) (Some (oc A))
| de_fr A l : llfoc (polcont l A) (polfoc A) -> llfoc (wn A :: l) None
| wk_fr A l Pi : llfoc l Pi -> llfoc (wn A :: l) Pi
| co_fr A l Pi : llfoc (wn A :: wn A :: l) Pi -> llfoc (wn A :: l) Pi.

Notation llfoc_pol l A := (llfoc (polcont l A) (polfoc A)).

Fixpoint fpsize l Pi (pi : llfoc l Pi) :=
match pi with
| ax_fr _ | one_fr | top_fr _ _ _ => 1
| ex_fr pi0 _ | foc_fr pi0 | bot_fr pi0 | parr_fr pi0 | plus_fr1 _ _ _ pi0 | plus_fr2 _ _ _ pi0
| oc_fr _ pi0 | de_fr _ _ pi0 | wk_fr _ pi0 | co_fr pi0 => S (fpsize pi0)
| tens_fr _ _ _ _ pi1 pi2 => S (fpsize pi1 + fpsize pi2)
| with_fr pi1 pi2 => S (max (fpsize pi1) (fpsize pi2))
end.

Lemma foc_gen_fr l A : llfoc_pol l A -> llfoc (A :: l) None.
Proof. destruct (polarity A); pol_simpl; intro pi; [ apply foc_fr | ]; assumption. Qed.

Lemma top_gen_fr l Pi : option_testT sformula Pi -> llfoc (top :: l) Pi.
Proof.
remember (list_sum (map fsize l)) as n eqn:Heqn.
revert l Pi Heqn; induction n using lt_wf_rect; intros l Pi -> Hs.
destruct (wtFocl_dec l).
- apply top_fr; assumption.
- apply not_wtFocl in n as [ [[A l1] l2] -> [[-> | [[B C] ->]] | [[B C] ->]] ].
  + rewrite app_comm_cons.
    eapply ex_fr; [ apply bot_fr | apply Permutation_Type_middle ].
    cbn. eapply X; [ | reflexivity | assumption ].
    cbn. rewrite 2 map_app, 2 list_sum_app. simpl. lia.
  + rewrite app_comm_cons.
    eapply ex_fr; [ apply parr_fr | apply Permutation_Type_middle ].
    list_simpl. eapply ex_fr;
      [ eapply X; trivial
      | etransitivity; [ apply Permutation_Type_swap
                       | apply (Permutation_Type_cons eq_refl);
                         etransitivity; [ apply Permutation_Type_swap | reflexivity ]]].
    cbn. rewrite 2 map_app, 2 list_sum_app. simpl. lia.
  + rewrite app_comm_cons.
    eapply ex_fr; [ apply with_fr | apply Permutation_Type_middle ].
    * list_simpl. eapply ex_fr;
        [ eapply X; trivial
        | etransitivity; [ apply Permutation_Type_swap
                         | apply Permutation_Type_cons; reflexivity ]].
      cbn. rewrite 2 map_app, 2 list_sum_app. simpl. lia.
    * list_simpl. eapply ex_fr;
        [ eapply X; trivial
        | etransitivity; [ apply Permutation_Type_swap
                         | apply Permutation_Type_cons; reflexivity ]].
    cbn. rewrite 2 map_app, 2 list_sum_app. simpl. lia.
Qed.

Lemma sync_focus l A : llfoc l (Some A) -> sformula A.
Proof.
intro pi. remember (Some A) as Pi eqn:HeqPi.
induction pi in HeqPi |- *; inversion HeqPi; subst; try (constructor; fail); try (now apply IHpi); auto.
Qed.

Lemma llfoc_foc_is_llfoc_foc l A : llfoc l (Some A) -> llfoc_pol l A.
Proof. intro pi. assert (Hs := sync_focus pi). pol_simpl. exact pi. Qed.

Lemma llfoc_cont_is_llfoc_cont l A : aformula A -> llfoc (A :: l) None -> llfoc_pol l A.
Proof. intros Ha pi. pol_simpl. exact pi. Qed.

Lemma bot_rev_f l Pi (pi : llfoc l Pi) l1 l2 : l = l1 ++ bot :: l2 ->
  { pi' : llfoc (l1 ++ l2) Pi | fpsize pi' < fpsize pi }.
Proof.
revert l1 l2. induction pi; intros l1' l2' Heq; subst.
- exfalso. destruct l1'; destr_eq Heq. nil_vs_elt_inv H.
- assert (HP := p).
  cbn; apply Permutation_Type_vs_elt_inv in p as ((l3 & l4) & ->).
  cbn in IHpi, HP; cbn.
  destruct (IHpi _ _ eq_refl) as [pi0 Hs].
  cbn in HP; apply Permutation_Type_app_inv in HP.
  exists (ex_fr pi0 HP); cbn; lia.
- destruct l1'; destr_eq Heq; subst.
  + exfalso. clear IHpi. apply sync_focus in pi. inversion pi.
  + destruct (IHpi _ _ eq_refl) as [pi0 Hs].
    exists (foc_fr pi0). cbn. lia.
- exfalso. destruct l1'; discriminate Heq.
- destruct l1'; destr_eq Heq; subst.
  + exists pi. cbn. lia.
  + destruct (IHpi _ _ eq_refl) as [pi0 Hs].
    exists (bot_fr pi0). cbn. lia.
- dichot_elt_app_inf_exec Heq; subst.
  + destruct (polarity A) as [Hs | Ha].
    * assert (H1 := IHpi1 _ _ (polconts _ Hs)).
      rewrite <- (polconts (l1' ++ l) Hs) in H1.
      destruct H1 as [pi1' Hs1].
      rewrite app_assoc.
      exists (tens_fr _ _ _ _ pi1' pi2). cbn. lia.
    * assert (polcont (l1' ++ bot :: l) A = (A :: l1') ++ bot :: l) as Hpa
        by (rewrite (polconta _ Ha), app_comm_cons; reflexivity).
      assert (H1 := IHpi1 _ _ Hpa).
      rewrite <- app_comm_cons, <- (polconta (l1' ++ l) Ha) in H1.
      destruct H1 as [pi1' Hs1].
      rewrite app_assoc.
      exists (tens_fr _ _ _ _ pi1' pi2); cbn; lia.
  + destruct (polarity B) as [Hs | Ha].
    * assert (H2 := IHpi2 _ _ (polconts _ Hs)).
      rewrite <- (polconts (l ++ l2') Hs) in H2.
      destruct H2 as [pi2' Hs2].
      rewrite <- app_assoc.
      exists (tens_fr _ _ _ _ pi1 pi2'); cbn; lia.
    * assert (polcont (l ++ bot :: l2') B = (B :: l) ++ bot :: l2') as Hpa
        by (rewrite (polconta _ Ha), app_comm_cons; reflexivity).
      assert (H2 := IHpi2 _ _ Hpa).
      rewrite <- app_comm_cons, <- (polconta (l ++ l2') Ha) in H2.
      destruct H2 as [pi2' Hs2].
      rewrite <- app_assoc.
      exists (tens_fr _ _ _ _ pi1 pi2'); cbn; lia.
- destruct l1'; destr_eq Heq; subst.
  assert (A :: B :: l1' ++ bot :: l2' = (A :: B :: l1') ++ bot :: l2') as Heql
    by (list_simpl; reflexivity).
  assert (H0 := IHpi _ _ Heql).
  rewrite <- 2 app_comm_cons in H0.
  destruct H0 as [pi0 Hs].
  exists (parr_fr pi0); cbn; lia.
- exfalso.
  destruct l1'; destr_eq Heq. subst.
  apply Forall_inf_app_r in f. inversion f. subst.
  inversion X as [[[Ht | Ht] | Ht] | Ht]; now inversion Ht.
- destruct (polarity A) as [Hs | Ha].
  + assert (H1 := IHpi _ _ (polconts _ Hs)).
    rewrite <- (polconts (l1' ++ l2') Hs) in H1.
    destruct H1 as [pi1' Hs1].
    exists (plus_fr1 _ B _ pi1'); cbn; lia.
  + assert (polcont (l1' ++ bot :: l2') A = (A :: l1') ++ bot :: l2') as Hpa
      by (rewrite (polconta _ Ha), app_comm_cons; reflexivity).
    assert (H1 := IHpi _ _ Hpa).
    rewrite <- app_comm_cons, <- (polconta (l1' ++ l2') Ha) in H1.
    destruct H1 as [pi1' Hs1].
    exists (plus_fr1 _ B _ pi1'); cbn; lia.
- destruct (polarity A) as [Hs | Ha].
  + assert (H1 := IHpi _ _ (polconts _ Hs)).
    rewrite <- (polconts (l1' ++ l2') Hs) in H1.
    destruct H1 as [pi1' Hs1].
    exists (plus_fr2 _ B _ pi1'); cbn; lia.
  + assert (polcont (l1' ++ bot :: l2') A = (A :: l1') ++ bot :: l2') as Hpa
      by (rewrite (polconta _ Ha), app_comm_cons; reflexivity).
    assert (H1 := IHpi _ _ Hpa).
    rewrite <- app_comm_cons, <- (polconta (l1' ++ l2') Ha) in H1.
    destruct H1 as [pi1' Hs1].
    exists (plus_fr2 _ B _ pi1'); cbn; lia.
- destruct l1'; destr_eq Heq; subst.
  assert (A :: l1' ++ bot :: l2' = (A :: l1') ++ bot :: l2') as Heql1
    by (list_simpl; reflexivity).
  assert (B :: l1' ++ bot :: l2' = (B :: l1') ++ bot :: l2') as Heql2
    by (list_simpl; reflexivity).
  assert (H1 := IHpi1 _ _ Heql1).
  assert (H2 := IHpi2 _ _ Heql2).
  rewrite <- app_comm_cons in H1.
  rewrite <- app_comm_cons in H2.
  destruct H1 as [pi1' Hs1].
  destruct H2 as [pi2' Hs2].
  exists (with_fr pi1' pi2'); cbn; lia.
- exfalso.
  decomp_map Heq eqn:Hx. discriminate Hx.
- destruct l1'; destr_eq Heq; subst.
  destruct (polarity A) as [Hs | Ha].
  + assert (H1 := IHpi _ _ (polconts _ Hs)).
    rewrite <- (polconts (l1' ++ l2') Hs) in H1.
    destruct H1 as [pi1' Hs1].
    exists (de_fr _ _ pi1'); cbn; lia.
  + assert (polcont (l1' ++ bot :: l2') A = (A :: l1') ++ bot :: l2') as Hpa
      by (rewrite (polconta _ Ha), app_comm_cons; reflexivity).
    assert (H1 := IHpi _ _ Hpa).
    rewrite <- app_comm_cons, <- (polconta (l1' ++ l2') Ha) in H1.
    destruct H1 as [pi1' Hs1].
    exists (de_fr _ _ pi1'); cbn; lia.
- destruct l1'; destr_eq Heq; subst.
  destruct (IHpi _ _ eq_refl) as [pi0 Hs].
  exists (wk_fr _ pi0); cbn; lia.
- destruct l1'; destr_eq Heq; subst.
  assert (wn A :: wn A :: l1' ++ bot :: l2' = (wn A :: wn A :: l1') ++ bot :: l2')
    as Heql by (list_simpl; reflexivity).
  assert (H0 := IHpi _ _ Heql).
  rewrite <- 2 app_comm_cons in H0.
  destruct H0 as [pi0 Hs].
  exists (co_fr pi0); cbn; lia.
Qed.

Lemma parr_rev_f l Pi (pi : llfoc l Pi) A B l1 l2 : l = l1 ++ parr A B :: l2 ->
  { pi' : llfoc (l1 ++ A :: B :: l2) Pi | fpsize pi' < fpsize pi }.
Proof.
revert A B l1 l2; induction pi; intros A' B' l1' l2' Heq; subst; cbn.
- exfalso. destruct l1'; destr_eq Heq. nil_vs_elt_inv H.
- assert (HP := p).
  apply Permutation_Type_vs_elt_inv in p as [(l3, l4) ->].
  destruct (IHpi _ _ _ _ eq_refl) as [pi0 Hs].
  apply Permutation_Type_app_inv, (Permutation_Type_elt B'), (Permutation_Type_elt A') in HP.
  exists (ex_fr pi0 HP); cbn; lia.
- destruct l1'; destr_eq Heq; subst.
  + exfalso.
    clear IHpi; apply sync_focus in pi.
    inversion pi.
  + destruct (IHpi _ _ _ _ eq_refl) as [pi0 Hs].
    exists (foc_fr pi0); cbn; lia.
- exfalso.
  destruct l1'; destr_eq Heq.
- destruct l1'; destr_eq Heq; subst.
  destruct (IHpi _ _ _ _ eq_refl) as [pi0 Hs].
  exists (bot_fr pi0); cbn; lia.
- dichot_elt_app_inf_exec Heq; subst.
  + destruct (polarity A) as [Hs | Ha].
    * assert (H1 := IHpi1 _ _ _ _ (polconts _ Hs)).
      rewrite <- (polconts (l1' ++ A' :: B' :: l) Hs) in H1.
      destruct H1 as [pi1' Hs1].
      rewrite 2 app_comm_cons, app_assoc.
      exists (tens_fr _ _ _ _ pi1' pi2); cbn; lia.
    * assert (polcont (l1' ++ parr A' B' :: l) A = (A :: l1') ++ parr A' B' :: l)
        as Hpa by now rewrite (polconta _ Ha), app_comm_cons.
      assert (H1 := IHpi1 _ _ _ _ Hpa).
      rewrite <- app_comm_cons, <- (polconta (l1' ++ A' :: B' :: l) Ha) in H1.
      destruct H1 as [pi1' Hs1].
      rewrite 2 app_comm_cons, app_assoc.
      exists (tens_fr _ _ _ _ pi1' pi2); cbn; lia.
  + destruct (polarity B) as [Hs | Ha].
    * assert (H2 := IHpi2 _ _ _ _ (polconts _ Hs)).
      rewrite <- (polconts (l ++ A' :: B' :: l2') Hs) in H2.
      destruct H2 as [pi2' Hs2].
      rewrite <- app_assoc.
      exists (tens_fr _ _ _ _ pi1 pi2'); cbn; lia.
    * assert (polcont (l ++ parr A' B' :: l2') B = (B :: l) ++ parr A' B' :: l2')
        as Hpa by now rewrite (polconta _ Ha), app_comm_cons.
      assert (H2 := IHpi2 _ _ _ _ Hpa).
      rewrite <- app_comm_cons, <- (polconta (l ++ A' :: B' :: l2') Ha) in H2.
      destruct H2 as [pi2' Hs2].
      rewrite <- app_assoc.
      exists (tens_fr _ _ _ _ pi1 pi2'); cbn; lia.
- destruct l1'; destr_eq Heq; subst.
  + exists pi; cbn; lia.
  + assert (A :: B :: l1' ++ parr A' B' :: l2' = (A :: B :: l1') ++ parr A' B' :: l2')
      as Heql by (list_simpl; reflexivity).
    assert (H0 := IHpi _ _ _ _ Heql).
    rewrite <- 2 app_comm_cons in H0.
    destruct H0 as [pi0 Hs].
    exists (parr_fr pi0); cbn; lia.
- exfalso.
  destruct l1'; destr_eq Heq; subst.
  apply Forall_inf_app_r in f.
  inversion f; subst.
  inversion X as [[[Ht | Ht] | Ht] | Ht]; now (inversion Ht).
- destruct (polarity A) as [Hs | Ha].
  + assert (H1 := IHpi _ _ _ _ (polconts _ Hs)).
    rewrite <- (polconts (l1' ++ A' :: B' :: l2') Hs) in H1.
    destruct H1 as [pi1' Hs1].
    exists (plus_fr1 _ B _ pi1'); cbn; lia.
  + assert (polcont (l1' ++ parr A' B' :: l2') A = (A :: l1') ++ parr A' B' :: l2')
      as Hpa by now rewrite (polconta _ Ha), app_comm_cons.
    assert (H1 := IHpi _ _ _ _ Hpa).
    rewrite <- app_comm_cons, <- (polconta (l1' ++ A' :: B' :: l2') Ha) in H1.
    destruct H1 as [pi1' Hs1].
    exists (plus_fr1 _ B _ pi1'); cbn; lia.
- destruct (polarity A) as [Hs | Ha].
  + assert (H1 := IHpi _ _ _ _ (polconts _ Hs)).
    rewrite <- (polconts (l1' ++ A' :: B' :: l2') Hs) in H1.
    destruct H1 as [pi1' Hs1].
    exists (plus_fr2 _ B _ pi1'); cbn; lia.
  + assert (polcont (l1' ++ parr A' B' :: l2') A = (A :: l1') ++ parr A' B' :: l2')
      as Hpa by now rewrite (polconta _ Ha), app_comm_cons.
    assert (H1 := IHpi _ _ _ _ Hpa).
    rewrite <- app_comm_cons, <- (polconta (l1' ++ A' :: B' :: l2') Ha) in H1.
    destruct H1 as [pi1' Hs1].
    exists (plus_fr2 _ B _ pi1'); cbn; lia.
- destruct l1'; destr_eq Heq; subst.
  assert (A :: l1' ++ parr A' B' :: l2' = (A :: l1') ++ parr A' B' :: l2') as Heql1
    by (list_simpl; reflexivity).
  assert (B :: l1' ++ parr A' B' :: l2' = (B :: l1') ++ parr A' B' :: l2') as Heql2
    by (list_simpl; reflexivity).
  assert (H1 := IHpi1 _ _ _ _ Heql1).
  assert (H2 := IHpi2 _ _ _ _ Heql2).
  rewrite <- app_comm_cons in H1.
  rewrite <- app_comm_cons in H2.
  destruct H1 as [pi1' Hs1].
  destruct H2 as [pi2' Hs2].
  exists (with_fr pi1' pi2'); cbn; lia.
- exfalso. decomp_map Heq eqn:Hx. discriminate Hx.
- destruct l1'; destr_eq Heq; subst.
  destruct (polarity A) as [Hs | Ha].
  + assert (H1 := IHpi _ _ _ _ (polconts _ Hs)).
    rewrite <- (polconts (l1' ++ A' :: B' :: l2') Hs) in H1.
    destruct H1 as [pi1' Hs1].
    exists (de_fr _ _ pi1'); cbn; lia.
  + assert (polcont (l1' ++ parr A' B' :: l2') A = (A :: l1') ++ parr A' B' :: l2')
      as Hpa by now rewrite (polconta _ Ha), app_comm_cons.
    assert (H1 := IHpi _ _ _ _ Hpa).
    rewrite <- app_comm_cons, <- (polconta (l1' ++ A' :: B' :: l2') Ha) in H1.
    destruct H1 as [pi1' Hs1].
    exists (de_fr _ _ pi1'); cbn; lia.
- destruct l1'; destr_eq Heq; subst.
  destruct (IHpi _ _ _ _ eq_refl) as [pi0 Hs].
  exists (wk_fr A pi0); cbn; lia.
- destruct l1'; destr_eq Heq. subst.
  assert (wn A :: wn A :: l1' ++ parr A' B' :: l2'
       = (wn A :: wn A :: l1') ++ parr A' B' :: l2')
    as Heql by (list_simpl; reflexivity).
  assert (H0 := IHpi _ _ _ _ Heql).
  rewrite <- 2 app_comm_cons in H0. destruct H0 as [pi0 Hs].
  exists (co_fr pi0). cbn. lia.
Qed.

Lemma with_rev_f l Pi (pi : llfoc l Pi) A B l1 l2 : l = l1 ++ awith A B :: l2 ->
   { pi' : llfoc (l1 ++ A :: l2) Pi | fpsize pi' < fpsize pi }
 * { pi' : llfoc (l1 ++ B :: l2) Pi | fpsize pi' < fpsize pi }.
Proof.
revert A B l1 l2. induction pi; intros A' B' l1' l2' Heq; subst; cbn.
- exfalso. destruct l1'; destr_eq Heq. nil_vs_elt_inv H.
- assert (HP := p).
  apply Permutation_Type_vs_elt_inv in p as ((l3 & l4) & ->).
  destruct (IHpi _ _ _ _ eq_refl) as [[pi01 Hs1] [pi02 Hs2]].
  apply Permutation_Type_app_inv in HP.
  assert (HP2 := HP).
  apply (Permutation_Type_elt B') in HP2.
  apply (Permutation_Type_elt A') in HP.
  split; [ exists (ex_fr pi01 HP) | exists (ex_fr pi02 HP2) ]; cbn; lia.
- destruct l1'; destr_eq Heq; subst.
  + exfalso.
    clear IHpi. apply sync_focus in pi. inversion pi.
  + destruct (IHpi _ _ _ _ eq_refl) as [[pi01 Hs1] [pi02 Hs2]].
    split; [ exists (foc_fr pi01) | exists (foc_fr pi02) ]; cbn; lia.
- exfalso.
  destruct l1'; destr_eq Heq.
- destruct l1'; destr_eq Heq; subst.
  destruct (IHpi _ _ _ _ eq_refl) as [[pi01 Hs1] [pi02 Hs2]].
  split; [ exists (bot_fr pi01) | exists (bot_fr pi02) ]; cbn; lia.
- dichot_elt_app_inf_exec Heq; subst.
  + destruct (polarity A) as [Hs | Ha].
    * assert (H1 := IHpi1 _ _ _ _ (polconts _ Hs)).
      rewrite <- (polconts (l1' ++ A' :: l) Hs), <- (polconts (l1' ++ B' :: l) Hs) in H1.
      destruct H1 as [[pi1' Hs1] [pi1'' Hs2]].
      rewrite ? app_comm_cons, 2 app_assoc.
      split; [ exists (tens_fr _ _ _ _ pi1' pi2)
             | exists (tens_fr _ _ _ _ pi1'' pi2) ]; cbn; lia.
    * assert (polcont (l1' ++ awith A' B' :: l) A = (A :: l1') ++ awith A' B' :: l)
        as Hpa by now rewrite (polconta _ Ha), app_comm_cons.
      assert (H1 := IHpi1 _ _ _ _ Hpa).
      rewrite <- 2 app_comm_cons, <- (polconta (l1' ++ A' :: l) Ha),
                                  <- (polconta (l1' ++ B' :: l) Ha) in H1.
      destruct H1 as [[pi1' Hs1] [pi2' Hs2]].
      rewrite ? app_comm_cons, 2 app_assoc.
      split; [ exists (tens_fr _ _ _ _ pi1' pi2)
             | exists (tens_fr _ _ _ _ pi2' pi2) ]; cbn; lia.
  + destruct (polarity B) as [Hs | Ha].
    * assert (H2 := IHpi2 _ _ _ _ (polconts _ Hs)).
      rewrite <- (polconts (l ++ A' :: l2') Hs), <- (polconts (l ++ B' :: l2') Hs) in H2.
      destruct H2 as [[pi1' Hs1] [pi1'' Hs2]].
      rewrite <- 2 app_assoc.
      split; [ exists (tens_fr _ _ _ _ pi1 pi1')
             | exists (tens_fr _ _ _ _ pi1 pi1'') ]; cbn; lia.
    * assert (polcont (l ++ awith A' B' :: l2') B = (B :: l) ++ awith A' B' :: l2')
        as Hpa by now rewrite (polconta _ Ha), app_comm_cons.
      assert (H2 := IHpi2 _ _ _ _ Hpa).
      rewrite <- 2 app_comm_cons, <- (polconta (l ++ A' :: l2') Ha),
                                  <- (polconta (l ++ B' :: l2') Ha) in H2.
      destruct H2 as [[pi1' Hs1] [pi1'' Hs2]].
      rewrite <- 2 app_assoc.
      split; [ exists (tens_fr _ _ _ _ pi1 pi1')
             | exists (tens_fr _ _ _ _ pi1 pi1'') ]; cbn; lia.
- destruct l1'; destr_eq Heq; subst.
  assert (A :: B :: l1' ++ awith A' B' :: l2' = (A :: B :: l1') ++ awith A' B' :: l2')
    as Heql by (list_simpl; reflexivity).
  assert (H0 := IHpi _ _ _ _ Heql).
  rewrite <- ? app_comm_cons in H0.
  destruct H0 as [[pi1' Hs1] [pi1'' Hs2]].
  split; [ exists (parr_fr pi1') | exists (parr_fr pi1'') ]; cbn; lia.
- exfalso.
  destruct l1'; destr_eq Heq; subst.
  apply Forall_inf_app_r in f. inversion f. subst.
  inversion X as [[[Ht | Ht] | Ht] | Ht]; now (inversion Ht).
- destruct (polarity A) as [Hs | Ha].
  + assert (H1 := IHpi _ _ _ _ (polconts _ Hs)).
    rewrite <- (polconts (l1' ++ A' :: l2') Hs), <- (polconts (l1' ++ B' :: l2') Hs) in H1.
    destruct H1 as [[pi1' Hs1] [pi1'' Hs2]].
    split; [ exists (plus_fr1 _ _ _ pi1')
           | exists (plus_fr1 _ _ _ pi1'') ]; cbn; lia.
  + assert (polcont (l1' ++ awith A' B' :: l2') A = (A :: l1') ++ awith A' B' :: l2')
      as Hpa by now rewrite (polconta _ Ha), app_comm_cons.
    assert (H1 := IHpi _ _ _ _ Hpa).
    rewrite <- 2 app_comm_cons, <- (polconta (l1' ++ A' :: l2') Ha),
                                <- (polconta (l1' ++ B' :: l2') Ha) in H1.
    destruct H1 as [[pi1' Hs1] [pi1'' Hs2]].
    split; [ exists (plus_fr1 _ _ _ pi1') | exists (plus_fr1 _ _ _ pi1'') ]; cbn; lia.
- destruct (polarity A) as [Hs | Ha].
  + assert (H1 := IHpi _ _ _ _ (polconts _ Hs)).
    rewrite <- (polconts (l1' ++ A' :: l2') Hs) in H1.
    rewrite <- (polconts (l1' ++ B' :: l2') Hs) in H1.
    destruct H1 as [[pi1' Hs1] [pi1'' Hs2]].
    split; [ exists (plus_fr2 _ _ _ pi1') | exists (plus_fr2 _ _ _ pi1'') ]; cbn; lia.
  + assert (polcont (l1' ++ awith A' B' :: l2') A = (A :: l1') ++ awith A' B' :: l2')
      as Hpa by now rewrite (polconta _ Ha), app_comm_cons.
    assert (H1 := IHpi _ _ _ _ Hpa).
    rewrite <- 2 app_comm_cons, <- (polconta (l1' ++ A' :: l2') Ha),
                                <- (polconta (l1' ++ B' :: l2') Ha) in H1.
    destruct H1 as [[pi1' Hs1] [pi1'' Hs2]].
    split; [ exists (plus_fr2 _ _ _ pi1') | exists (plus_fr2 _ _ _ pi1'') ]; cbn; lia.
- destruct l1'; destr_eq Heq; subst.
  + split; [ exists pi1 | exists pi2 ]; subst; cbn; lia.
  + assert (A :: l1' ++ awith A' B' :: l2' = (A :: l1') ++ awith A' B' :: l2') as Heql1
      by (list_simpl; reflexivity).
    assert (B :: l1' ++ awith A' B' :: l2' = (B :: l1') ++ awith A' B' :: l2') as Heql2
      by (list_simpl; reflexivity).
    assert (H1 := IHpi1 _ _ _ _ Heql1).
    assert (H2 := IHpi2 _ _ _ _ Heql2).
    rewrite <- 2 app_comm_cons in H1.
    rewrite <- 2 app_comm_cons in H2.
    destruct H1 as [[pi1' Hs1] [pi1'' Hs1']].
    destruct H2 as [[pi2' Hs2] [pi2'' Hs2']].
    split; [ exists (with_fr pi1' pi2') | exists (with_fr pi1'' pi2'') ]; cbn; lia.
- exfalso. decomp_map Heq eqn:Hx. discriminate Hx.
- destruct l1'; destr_eq Heq; subst.
  destruct (polarity A) as [Hs | Ha].
  + assert (H1 := IHpi _ _ _ _ (polconts _ Hs)).
    rewrite <- (polconts (l1' ++ A' :: l2') Hs), <- (polconts (l1' ++ B' :: l2') Hs) in H1.
    destruct H1 as [[pi1' Hs1] [pi1'' Hs2]].
    split; [ exists (de_fr _ _ pi1') | exists (de_fr _ _ pi1'') ]; cbn; lia.
  + assert (polcont (l1' ++ awith A' B' :: l2') A = (A :: l1') ++ awith A' B' :: l2')
      as Hpa by now rewrite (polconta _ Ha), app_comm_cons.
    assert (H1 := IHpi _ _ _ _ Hpa).
    rewrite <- 2 app_comm_cons, <- (polconta (l1' ++ A' :: l2') Ha),
                                <- (polconta (l1' ++ B' :: l2') Ha) in H1.
    destruct H1 as [[pi1' Hs1] [pi1'' Hs2]].
    split; [ exists (de_fr _ _ pi1') | exists (de_fr _ _ pi1'') ]; cbn; lia.
- destruct l1'; destr_eq Heq; subst.
  destruct (IHpi _ _ _ _ eq_refl) as [[pi1' Hs1] [pi1'' Hs2]].
  split; [ exists (wk_fr _ pi1') | exists (wk_fr _ pi1'') ]; cbn; lia.
- destruct l1'; destr_eq Heq; subst.
  assert (wn A :: wn A :: l1' ++ awith A' B' :: l2'
       = (wn A :: wn A :: l1') ++ awith A' B' :: l2')
    as Heql by (list_simpl; reflexivity).
  assert (H0 := IHpi _ _ _ _ Heql).
  rewrite <- ? app_comm_cons in H0.
  destruct H0 as [[pi1' Hs1] [pi1'' Hs2]].
  split; [ exists (co_fr pi1') | exists (co_fr pi1'') ]; cbn; lia.
Qed.

Lemma with_rev1_f l Pi (pi : llfoc l Pi) A B l1 l2 : l = l1 ++ awith A B :: l2 ->
  { pi' : llfoc (l1 ++ A :: l2) Pi | fpsize pi' < fpsize pi }.
Proof. intros [pi' _]%(with_rev_f pi). exact pi'. Qed.

Lemma with_rev2_f l Pi (pi : llfoc l Pi) A B l1 l2 : l = l1 ++ awith A B :: l2 ->
  { pi' : llfoc (l1 ++ B :: l2) Pi | fpsize pi' < fpsize pi }.
Proof. intros [_ pi']%(with_rev_f pi). exact pi'. Qed.

Lemma unfoc_sequent l A :
  match polfoc A with Some C => C :: nil | None => nil end ++ polcont l A = A :: l.
Proof. destruct (polarity A) as [HsA | HaA]; pol_simpl; reflexivity. Qed.

Lemma llfoc_to_ll l Pi : llfoc l Pi ->
  ll_ll (match Pi with Some C => C :: nil | None => nil end ++ l).
Proof.
intro pi. induction pi; rewrite ? unfoc_sequent in *;
  try (now try destruct Pi; (constructor + (eapply ex_r; [ | apply Permutation_Type_swap ]; constructor))).
- eapply ex_r; [ eassumption | ].
  apply Permutation_Type_app; [ reflexivity | assumption ].
- assumption.
- eapply ex_r; [ apply tens_r; [ apply IHpi1 | apply IHpi2 ] | ].
  apply Permutation_Type_cons, Permutation_Type_app_comm. reflexivity.
- eapply ex_r; [ apply parr_r | apply Permutation_Type_middle ].
  eapply ex_r; [ eassumption | ].
  cons2app. rewrite ? (app_assoc (A :: nil)). apply Permutation_Type_app_swap_app.
- eapply ex_r; [ apply with_r | apply Permutation_Type_middle ].
  + eapply ex_r; [ apply IHpi1 | symmetry; apply Permutation_Type_middle ].
  + eapply ex_r; [ apply IHpi2 | symmetry; apply Permutation_Type_middle ].
- eapply ex_r; [ apply co_r | apply Permutation_Type_middle ].
  eapply ex_r; [ eassumption | ].
  cons2app. rewrite ? (app_assoc (wn A :: nil)). apply Permutation_Type_app_swap_app.
Qed.


(** ** The strongly focused system [llFoc] *)

Inductive llFoc : list formula -> option formula -> Type :=
| ax_Fr X : llFoc (covar X :: nil) (Some (var X))
| ex_Fr l1 l2 : llFoc l1 None -> Permutation_Type l1 l2 -> llFoc l2 None
| foc_Fr A l : llFoc l (Some A) -> llFoc (A :: l) None
| one_Fr : llFoc nil (Some one)
| bot_Fr l : llFoc l None -> llFoc (bot :: l) None
| tens_Fr A B l1 l2 : llFoc (polcont l1 A) (polfoc A) -> llFoc (polcont l2 B) (polfoc B) ->
                      Forall_inf wFoc l1 -> Forall_inf wFoc l2 -> llFoc (l1 ++ l2) (Some (tens A B))
| parr_Fr A B l : llFoc (A :: B :: l) None -> llFoc (parr A B :: l) None
| top_Fr l : Forall_inf wtFoc l -> llFoc (top :: l) None
| plus_Fr1 A B l : llFoc (polcont l A) (polfoc A) -> Forall_inf wFoc l -> llFoc l (Some (aplus A B))
| plus_Fr2 A B l : llFoc (polcont l A) (polfoc A) -> Forall_inf wFoc l -> llFoc l (Some (aplus B A))
| with_Fr A B l : llFoc (A :: l) None -> llFoc (B :: l) None -> llFoc (awith A B :: l) None
| oc_Fr A l : llFoc (A :: map wn l) None -> llFoc (map wn l) (Some (oc A))
| de_Fr A l : llFoc (polcont l A) (polfoc A) -> Forall_inf wFoc l -> llFoc (wn A :: l) None
| wk_Fr A l : llFoc l None -> Forall_inf wFoc l -> llFoc (wn A :: l) None
| co_Fr A l : llFoc (wn A :: wn A :: l) None -> Forall_inf wFoc l -> llFoc (wn A :: l) None.

Notation llFoc_pol l A := (llFoc (polcont l A) (polfoc A)).

Instance llFoc_perm : Proper ((@Permutation_Type _) ==> arrow) (fun l => llFoc l None).
Proof. intros l1 l2 HP pi. apply ex_Fr with l1; assumption. Qed.

Lemma top_gen_Fr l : llFoc (top :: l) None.
Proof.
remember (list_sum (map fsize l)) as n eqn:Heqn.
revert l Heqn. induction n using lt_wf_rect; intros l ->.
destruct (wtFocl_dec l).
- apply top_Fr. assumption.
- apply not_wtFocl in n as [ [[A l1] l2] -> [[-> | [[B C] ->]] | [[B C] ->]] ].
  + rewrite app_comm_cons.
    eapply ex_Fr; [ apply bot_Fr | apply Permutation_Type_middle ].
    list_simpl. eapply X; [ | reflexivity ].
    rewrite 2 map_app, 2 list_sum_app. simpl. lia.
  + rewrite app_comm_cons.
    eapply ex_Fr; [ apply parr_Fr | apply Permutation_Type_middle ].
    list_simpl. eapply ex_Fr;
    [ eapply X; trivial
    | etransitivity; [ apply Permutation_Type_swap
                     | apply (Permutation_Type_cons eq_refl);
                       etransitivity; [ apply Permutation_Type_swap | reflexivity ]]].
    cbn. rewrite 2 map_app, 2 list_sum_app. simpl. lia.
  + rewrite app_comm_cons.
    eapply ex_Fr; [ apply with_Fr | apply Permutation_Type_middle ].
    * list_simpl. eapply ex_Fr;
        [ eapply X; trivial
        | etransitivity; [ apply Permutation_Type_swap
                         | apply Permutation_Type_cons; reflexivity ]].
      cbn. rewrite 2 map_app, 2 list_sum_app. simpl. lia.
    * list_simpl. eapply ex_Fr;
        [ eapply X; trivial
        | etransitivity; [ apply Permutation_Type_swap
                         | apply Permutation_Type_cons; reflexivity ]].
    cbn. rewrite 2 map_app, 2 list_sum_app. simpl. lia.
Qed.

Lemma foc_gen_Fr l A : llFoc_pol l A -> llFoc (A :: l) None.
Proof. destruct (polarity A); pol_simpl; intro pi; [ apply foc_Fr | ]; assumption. Qed.

Lemma sync_focus_F l A : llFoc l (Some A) -> sformula A.
Proof.
intro pi. remember (Some A) as Pi eqn:HeqPi.
induction pi in HeqPi |- *; inversion HeqPi; subst; (now constructor + exact (IHpi eq_refl)).
Qed.

Lemma wFoc_context l A : llFoc l (Some A) -> Forall_inf wFoc l.
Proof.
intro pi. remember (Some A) as Pi eqn:HeqPi.
induction pi in A, HeqPi |- *; subst;
  try (now inversion HeqPi).
- now repeat constructor.
- apply Forall_inf_app; assumption.
- clear. remember (map wn l) as l0 eqn:Heql0.
  induction l0 as [|A l0 IHl0] in l, Heql0 |- *; destruct l as [|B l]; destr_eq Heql0; subst; constructor.
  + right. constructor.
  + exact (IHl0 l eq_refl).
Qed.

Lemma llFoc_foc_is_llFoc_foc l A : llFoc l (Some A) -> llFoc_pol l A.
Proof. intro pi. assert (Hs := sync_focus_F pi). pol_simpl. exact pi. Qed.

Lemma llFoc_cont_is_llFoc_cont l A : aformula A -> llFoc (A :: l) None -> llFoc_pol l A.
Proof. intros Ha pi. pol_simpl. exact pi. Qed.


(** ** Reversing *)

Lemma bot_rev_F l1 l2 Pi : llFoc (l1 ++ bot :: l2) Pi -> llFoc (l1 ++ l2) Pi.
Proof.
intro pi. remember (l1 ++ bot :: l2) as l eqn:Heql.
revert l1 l2 Heql; induction pi; intros l1' l2' Heql; subst.
- destruct l1'; destr_eq Heql.
  destruct l1'; destr_eq H.
- destruct (Permutation_Type_vs_elt_inv _ _ _ p) as [(l1p, l2p) ->].
  apply Permutation_Type_app_inv in p.
  apply ex_Fr with (l1p ++ l2p); auto.
- destruct l1'; destr_eq Heql; subst.
  + exfalso. apply sync_focus_F in pi. inversion pi.
  + cbn. apply foc_Fr, IHpi. reflexivity.
- exfalso. destruct l1'; destr_eq Heql.
- destruct l1'; destr_eq Heql; subst; auto.
  cbn; apply bot_Fr, IHpi; reflexivity.
- exfalso.
  dichot_elt_app_inf_exec Heql; subst.
  + apply Forall_inf_app_r in f.
    inversion f.
    destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
  + apply Forall_inf_app_r in f0.
    inversion f0.
    destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
- destruct l1'; destr_eq Heql; subst.
  cbn; apply parr_Fr.
  rewrite 2 app_comm_cons.
  apply IHpi; reflexivity.
- destruct l1'; destr_eq Heql; subst.
  cbn. apply top_gen_Fr.
- exfalso.
  apply Forall_inf_app_r in f; inversion f.
  destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
- exfalso.
  apply Forall_inf_app_r in f; inversion f.
  destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
- destruct l1'; destr_eq Heql; subst.
  cbn. apply with_Fr.
  + rewrite app_comm_cons. apply IHpi1. reflexivity.
  + rewrite app_comm_cons. apply IHpi2. reflexivity.
- exfalso. decomp_map Heql eqn:Hx. discriminate Hx.
- exfalso. destruct l1'; destr_eq Heql; subst.
  apply Forall_inf_app_r in f; inversion f.
  destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
- exfalso. destruct l1'; destr_eq Heql; subst.
  apply Forall_inf_app_r in f; inversion f.
  destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
- exfalso. destruct l1'; destr_eq Heql; subst.
  apply Forall_inf_app_r in f; inversion f.
  destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
Qed.

Lemma parr_rev_F A1 A2 l1 l2 Pi :
  llFoc (l1 ++ parr A1 A2 :: l2) Pi -> llFoc (l1 ++ A1 :: A2 :: l2) Pi.
Proof.
intro pi. remember (l1 ++ parr A1 A2 :: l2) as l eqn:Heql.
revert A1 A2 l1 l2 Heql; induction pi; intros A1 A2 l1' l2' Heql; subst.
- destruct l1'; destr_eq Heql.
  destruct l1'; destr_eq H.
- destruct (Permutation_Type_vs_elt_inv _ _ _ p) as [(l1p, l2p) ->].
  apply Permutation_Type_app_inv, (Permutation_Type_elt A2), (Permutation_Type_elt A1) in p.
  apply ex_Fr with (l1p ++ A1 :: A2 :: l2p); auto.
- destruct l1'; destr_eq Heql; subst.
  + exfalso. apply sync_focus_F in pi. inversion pi.
  + cbn. apply foc_Fr, IHpi. reflexivity.
- exfalso. destruct l1'; destr_eq Heql.
- destruct l1'; destr_eq Heql; subst.
  cbn. apply bot_Fr, IHpi. reflexivity.
- exfalso.
  dichot_elt_app_inf_exec Heql; subst.
  + apply Forall_inf_app_r in f.
    inversion f.
    destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
  + apply Forall_inf_app_r in f0.
    inversion f0.
    destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
- destruct l1'; destr_eq Heql; subst; [ assumption | ].
  cbn. apply parr_Fr.
  rewrite 2 app_comm_cons. apply IHpi. reflexivity.
- destruct l1'; destr_eq Heql; subst.
  cbn. apply top_gen_Fr.
- exfalso.
  apply Forall_inf_app_r in f; inversion f.
  destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
- exfalso.
  apply Forall_inf_app_r in f; inversion f.
  destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
- destruct l1'; destr_eq Heql; subst.
  cbn. apply with_Fr.
  + rewrite app_comm_cons. apply IHpi1. reflexivity.
  + rewrite app_comm_cons. apply IHpi2. reflexivity.
- exfalso. decomp_map Heql eqn:Hx. discriminate Hx.
- exfalso. destruct l1'; destr_eq Heql; subst.
  apply Forall_inf_app_r in f; inversion f.
  destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
- exfalso. destruct l1'; destr_eq Heql; subst.
  apply Forall_inf_app_r in f; inversion f.
  destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
- exfalso. destruct l1'; destr_eq Heql; subst.
  apply Forall_inf_app_r in f; inversion f.
  destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
Qed.

Lemma with_rev_F A1 A2 l1 l2 Pi :
  llFoc (l1 ++ awith A1 A2 :: l2) Pi -> llFoc (l1 ++ A1 :: l2) Pi * llFoc (l1 ++ A2 :: l2) Pi.
Proof.
intro pi. remember (l1 ++ awith A1 A2 :: l2) as l eqn:Heql.
revert A1 A2 l1 l2 Heql; induction pi; intros A1 A2 l1' l2' Heql; subst.
- destruct l1'; destr_eq Heql.
  destruct l1'; destr_eq H.
- destruct (Permutation_Type_vs_elt_inv _ _ _ p) as [(l1p, l2p) ->].
  apply Permutation_Type_app_inv in p.
  split.
  + apply (Permutation_Type_elt A1) in p.
    apply ex_Fr with (l1p ++ A1 :: l2p); [ apply (IHpi A1 A2) | ]; auto.
  + apply (Permutation_Type_elt A2) in p.
    apply ex_Fr with (l1p ++ A2 :: l2p); [ apply (IHpi A1 A2) | ]; auto.
- destruct l1'; destr_eq Heql; subst.
  + exfalso. apply sync_focus_F in pi. inversion pi.
  + cbn. split; apply foc_Fr, (IHpi A1 A2); reflexivity.
- exfalso. destruct l1'; destr_eq Heql.
- destruct l1'; destr_eq Heql; subst.
  cbn. split; apply bot_Fr, (IHpi A1 A2); reflexivity.
- exfalso.
  dichot_elt_app_inf_exec Heql; subst.
  + apply Forall_inf_app_r in f.
    inversion f.
    destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
  + apply Forall_inf_app_r in f0.
    inversion f0.
    destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
- destruct l1'; destr_eq Heql; subst.
  cbn. split; apply parr_Fr; rewrite 2 app_comm_cons; apply (IHpi A1 A2); reflexivity.
- destruct l1'; destr_eq Heql; subst.
  cbn. split; apply top_gen_Fr.
- exfalso.
  apply Forall_inf_app_r in f; inversion f.
  destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
- exfalso.
  apply Forall_inf_app_r in f; inversion f.
  destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
- destruct l1'; destr_eq Heql; subst; auto.
  cbn. split; apply with_Fr.
  + rewrite app_comm_cons. apply (IHpi1 A1 A2). reflexivity.
  + rewrite app_comm_cons. apply (IHpi2 A1 A2). reflexivity.
  + rewrite app_comm_cons. apply (IHpi1 A1 A2). reflexivity.
  + rewrite app_comm_cons. apply (IHpi2 A1 A2). reflexivity.
- exfalso. decomp_map Heql eqn:Hx. discriminate Hx.
- exfalso. destruct l1'; destr_eq Heql; subst.
  apply Forall_inf_app_r in f; inversion f.
  destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
- exfalso. destruct l1'; destr_eq Heql; subst.
  apply Forall_inf_app_r in f; inversion f.
  destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
- exfalso. destruct l1'; destr_eq Heql; subst.
  apply Forall_inf_app_r in f; inversion f.
  destruct X as [[Hf | Hf] | Hf]; inversion Hf; inversion H.
Qed.

Lemma reversing l1 l2 l0:
  (forall lf, Forall_inf wFoc lf -> llFoc (l1 ++ lf) None -> llFoc (l2 ++ lf) None) ->
  llFoc (l1 ++ l0) None -> llFoc (l2 ++ l0) None.
Proof.
enough (forall l l1 l2 l0 lf,
  (forall lf, Forall_inf wFoc lf -> llFoc (l1 ++ lf) None -> llFoc (l2 ++ lf) None) ->
  Forall_inf wFoc lf -> Permutation_Type l (l1 ++ lf ++ l0) ->
  llFoc l None -> llFoc (l2 ++ lf ++ l0) None) as Hgen
  by (intros; rewrite <- (app_nil_l l0); apply Hgen with (l1 ++ l0) l1; auto).
clear l1 l2 l0. intros l l1 l2 l0 lf.
remember (list_sum (map fsize l0)) as n eqn:Heqn.
revert l0 lf l Heqn; induction n using lt_wf_rect; intros [|A l0] lf l -> HFoc HF HP pi.
- apply HFoc, (ex_Fr pi HP); now rewrite app_nil_r.
- destruct (wFoc_dec A).
  + replace (l2 ++ lf ++ A :: l0) with (l2 ++ (lf ++ A :: nil) ++ l0) by now rewrite <- app_assoc.
    apply X with (list_sum (map fsize l0)) l; rewrite <- ? app_assoc; auto.
    * assert (Hs := fsize_pos A); simpl; lia.
    * apply Forall_inf_app; auto.
  + apply not_wFoc in n as [[[ -> | [(A1, A2) ->]] | ->] | [(A1, A2) ->]]; cbn.
    * apply ex_Fr with (bot :: l2 ++ lf ++ l0);
        [ | rewrite ? app_assoc; apply Permutation_Type_middle ].
      apply bot_Fr.
      apply X with (list_sum (map fsize l0)) (l1 ++ lf ++ l0); auto.
      rewrite app_assoc; apply bot_rev_F; rewrite <- app_assoc.
      apply (ex_Fr pi HP).
    * apply ex_Fr with (parr A1 A2 :: l2 ++ lf ++ l0);
        [ | rewrite ? app_assoc; apply Permutation_Type_middle ].
      apply parr_Fr.
      apply ex_Fr with (l2 ++ lf ++ A1 :: A2 :: l0).
      -- apply X with (list_sum (map fsize (A1 :: A2 :: l0))) (l1 ++ lf ++ A1 :: A2 :: l0);
            simpl; auto; try lia.
         rewrite app_assoc; apply parr_rev_F; rewrite <- app_assoc.
         apply (ex_Fr pi HP).
      -- symmetry; rewrite ? app_assoc.
         etransitivity; [ apply Permutation_Type_cons, Permutation_Type_cons_app; reflexivity | ].
         apply Permutation_Type_cons_app; reflexivity.
    * apply ex_Fr with (top :: l2 ++ lf ++ l0);
        [ | rewrite ? app_assoc; apply Permutation_Type_middle ].
      apply top_gen_Fr.
    * apply ex_Fr with (awith A1 A2 :: l2 ++ lf ++ l0);
        [ | rewrite ? app_assoc; apply Permutation_Type_middle ].
      apply with_Fr.
      -- apply ex_Fr with (l2 ++ lf ++ A1 :: l0);
        [ | rewrite ? app_assoc; symmetry; apply Permutation_Type_middle ].
         apply X with (list_sum (map fsize (A1 :: l0))) (l1 ++ lf ++ A1 :: l0);
           simpl; auto; try lia.
         rewrite app_assoc; apply (with_rev_F A1 A2); rewrite <- app_assoc.
         apply (ex_Fr pi HP).
      -- apply ex_Fr with (l2 ++ lf ++ A2 :: l0);
           [ | rewrite ? app_assoc; symmetry; apply Permutation_Type_middle ].
         apply X with (list_sum (map fsize (A2 :: l0))) (l1 ++ lf ++ A2 :: l0);
           simpl; auto; try lia.
         rewrite app_assoc; apply (with_rev_F A1 A2); rewrite <- app_assoc.
         apply (ex_Fr pi HP).
Qed.

Lemma dea_gen_Fr A l : aformula A -> llFoc (A :: l) None -> llFoc (wn A :: l) None.
Proof.
intro Ha. cons2app. apply reversing.
clear l. cbn. intros l Hf pi. apply de_Fr; [ pol_simpl | ]; assumption.
Qed.

Lemma wk_gen_Fr A l : llFoc l None -> llFoc (wn A :: l) None.
Proof.
rewrite <- (app_nil_l l), app_comm_cons. apply reversing.
clear l. cbn. intros l Hf pi. now apply wk_Fr.
Qed.

Lemma wk_gen_list_Fr lw l : llFoc l None -> llFoc (map wn lw ++ l) None.
Proof. intro pi. induction lw; [ | apply wk_gen_Fr ];  assumption. Qed.

Lemma co_gen_Fr A l : llFoc (wn A :: wn A :: l) None -> llFoc (wn A :: l) None.
Proof.
rewrite <- (app_nil_l l), ? app_comm_cons. apply reversing.
clear l. cbn. intros l Hf pi. apply co_Fr; assumption.
Qed.


(** ** Strong focusing *)

Lemma incl_Foc l l0 la lw lw' : llFoc l None ->
 Permutation_Type l (map wn lw ++ la ++ l0) -> incl_inf lw lw' -> incl_inf la lw' -> Forall_inf aformula la ->
 llFoc (map wn lw' ++ l0) None.
Proof.
induction lw as [|A lw IHlw] in l, l0, la |- *; intros pi HP Hsub Hsubd Ha.
- clear Hsub. induction la as [|N la IHla] in l0, HP, Hsubd, Ha |- *.
  + apply wk_gen_list_Fr, (ex_Fr pi HP).
  + destruct (incl_inf_cons_inv Hsubd) as [Hin Hi]. inversion_clear Ha.
    apply in_inf_split in Hin as [(la1, la2) ->].
    apply ex_Fr with ((wn N :: nil) ++ map wn la1 ++ map wn la2 ++ l0);
      [ | list_simpl; apply Permutation_Type_middle ].
    cbn. apply co_gen_Fr, dea_gen_Fr; [ assumption | ].
    apply ex_Fr with (map wn (la1 ++ N :: la2) ++ N :: l0).
    * apply IHla; [ | assumption | assumption ].
      etransitivity; [ apply HP | ].
      cbn. apply Permutation_Type_middle.
    * symmetry. etransitivity; [ | apply Permutation_Type_middle ].
      list_simpl. apply Permutation_Type_cons, Permutation_Type_middle. reflexivity.
- destruct (incl_inf_cons_inv Hsub) as [Hin Hi].
  apply (IHlw l (wn A :: l0) la) in pi; try assumption.
  + apply in_inf_split in Hin as [(lw1, lw2) ->].
    apply ex_Fr with ((wn A :: nil) ++ map wn lw1 ++ map wn lw2 ++ l0);
      [ | list_simpl; apply Permutation_Type_middle ].
    cbn. apply co_gen_Fr.
    apply (ex_Fr pi). list_simpl.
    symmetry. apply Permutation_Type_cons_app.
    rewrite 2 app_assoc. apply Permutation_Type_middle.
  + etransitivity; [ apply HP | ].
    cbn. rewrite ? app_assoc. apply Permutation_Type_middle.
Qed.

Lemma llfoc_to_llFoc s l Pi (pi : llfoc l Pi) : fpsize pi < s ->
   (Pi = None -> llFoc l None)
 * (forall C, Pi = Some C -> Forall_inf wFoc l ->
      {'(l', l0, lw, lw') & (((Permutation_Type l (map wn lw ++ l0)) *
                              (Permutation_Type l' (map wn lw' ++ l0))) * (incl_inf lw' lw))%type
                          & llFoc l' (Some C) })
 * (forall C, Pi = Some C -> notT (Forall_inf wFoc l) ->
      llFoc (C :: l) None * llFoc (wn C :: l) None).
Proof.
revert l Pi pi. induction s using lt_wf_rect; intros l Pi pi; split; [ split | ];
  [ intro Heq; destruct pi; inversion Heq; subst; cbn in H
  | intros PPi Heq HF; destruct pi; inversion Heq; subst; cbn in H;
      try (exfalso; inversion HF; subst; destruct X0 as [[H'|H']|H']; inversion H'; fail)
  | intros C Heq HnF ].
(* first conjunct *)
- specialize X with (S (fpsize pi)) _ _ pi.
  apply X in H; [ | lia ].
  apply H in H0.
  eapply ex_Fr; [ apply H0 | assumption ].
- specialize X with (S (fpsize pi)) _ _ pi.
  apply X in H; [ | lia ].
  destruct (wFocl_dec l) as [Hwf|Hnwf].
  + eapply (snd (fst H)) in Hwf as [(((l', l0), lw), lw') [[HP1 HP2] Hi] IH]; [ | reflexivity ].
    apply (Permutation_Type_cons_app _ _ A) in HP1. symmetry in HP1.
    eapply ex_Fr; [ | exact HP1 ].
    eapply incl_Foc with (la := nil); [ | reflexivity | eassumption | intros ? [] | constructor ].
    apply (Permutation_Type_cons_app _ _ A) in HP2. eapply ex_Fr; [ | exact HP2 ].
    apply foc_Fr, IH.
  + apply (snd H _ eq_refl Hnwf).
- specialize X with (S (fpsize pi)) _ _ pi.
  apply X in H; [ | lia ].
  apply H in H0.
  apply bot_Fr. assumption.
- specialize X with (S (fpsize pi)) _ _ pi.
  apply X in H; [ | lia ].
  apply H in H0.
  apply parr_Fr. assumption.
- apply top_Fr. assumption.
- assert (X' := X).
  assert (H' := H).
  assert (H0' := H0).
  specialize X with (S (max (fpsize pi1) (fpsize pi2))) _ _ pi1.
  apply X in H; [ | lia ].
  specialize X' with (S (max (fpsize pi1) (fpsize pi2))) _ _ pi2.
  apply X' in H'; [ | lia ].
  apply H in H0.
  apply H' in H0'.
  apply with_Fr; assumption.
- specialize X with (S (fpsize pi)) _ _ pi.
  apply X in H; [ | lia ].
  destruct (polarity A) as [Hs | Ha]; pol_simpl.
  + destruct (wFocl_dec l) as [Hwf|Hnwf].
    * eapply (snd (fst H)) in Hwf as [(((l', l0), lw), lw') [[HP1 HP2] Hi] IH]; [ | reflexivity ].
      apply (Permutation_Type_cons_app _ _ (wn A)) in HP1. symmetry in HP1.
      eapply ex_Fr; [ | exact HP1 ].
      eapply incl_Foc with (la := nil); [ | reflexivity | eassumption | intros ? [] | constructor ].
      apply (Permutation_Type_cons_app _ _ (wn A)) in HP2. eapply ex_Fr; [ | exact HP2 ].
      apply de_Fr, (wFoc_context IH).
      pol_simpl. exact IH.
    * apply (snd H _ eq_refl Hnwf).
  + apply H in Heq.
    change (wn A :: l) with ((wn A :: nil) ++ l).
    apply (reversing (A :: nil)); [ | assumption ].
    clear - Ha. cbn. intros l Hf pi.
    apply de_Fr; [ pol_simpl | ]; assumption.
- specialize X with (S (fpsize pi)) _ _ pi.
  apply X in H; [ | lia ].
  apply wk_gen_Fr, H. reflexivity.
- specialize X with (S (fpsize pi)) _ _ pi.
  apply X in H; [ | lia ].
  apply co_gen_Fr, H. reflexivity.
(* second conjunct *)
- exists ((covar X0 :: nil), (covar X0 :: nil), nil, nil). repeat split; [ reflexivity .. | ].
  + apply incl_inf_nil_l.
  + apply ax_Fr.
- symmetry in p.
  specialize X with (S (fpsize pi)) _ _ pi.
  apply X in H; [ | lia ].
  apply (snd (fst H)) in H0 as [(((l', l0), lw), lw') [[HP1 HP2] Hi] IH].
  + exists (l', l0, lw, lw'); repeat split; [ | assumption .. ].
    etransitivity; eassumption.
  + apply (Permutation_Type_Forall_inf p). assumption.
- exists (nil, nil, nil, nil). repeat split; [ reflexivity .. | ].
  + apply incl_inf_nil_l.
  + apply one_Fr.
- assert (HF1 := Forall_inf_app_l _ _ HF).
  assert (HF2 := Forall_inf_app_r _ _ HF).
  assert (X':=X).
  assert (H' := H).
  assert (Heq' := Heq).
  specialize X with (S (fpsize pi1 + fpsize pi2)) _ _ pi1.
  apply X in H; [ | lia ].
  specialize X' with (S (fpsize pi1 + fpsize pi2)) _ _ pi2.
  apply X' in H'; [ | lia ].
  destruct (polarity A) as [HsA | HaA], (polarity B) as [HsB | HaB]; pol_simpl.
  + eapply (snd (fst H)) in HF1 as [(((l1', l01), lw1), lw1') [[HP11 HP12] Hi1] pi1']; [ | reflexivity ].
    eapply (snd (fst H')) in HF2 as [(((l2', l02), lw2), lw2') [[HP21 HP22] Hi2] pi2']; [ | reflexivity ].
    exists (l1' ++ l2', l01 ++ l02, lw1 ++ lw2, lw1' ++ lw2'); repeat split.
    * etransitivity; [ apply (Permutation_Type_app HP11 HP21) | ].
      list_simpl. apply Permutation_Type_app_head.
      rewrite ? app_assoc. apply Permutation_Type_app_tail, Permutation_Type_app_comm.
    * etransitivity; [ apply (Permutation_Type_app HP12 HP22) | ].
      list_simpl. apply Permutation_Type_app_head.
      rewrite ? app_assoc. apply Permutation_Type_app_tail, Permutation_Type_app_comm.
    * apply incl_inf_app_app; assumption.
    * apply tens_Fr; pol_simpl; [ .. | apply wFoc_context in pi1' | apply wFoc_context in pi2' ]; assumption.
  + eapply (snd (fst H)) in HF1 as [(((l1', l01), lw1), lw1') [[HP1 HP2] Hi1] pi1']; [ | reflexivity ].
    assert (pi2' := fst (fst H') eq_refl).
    exists (l1' ++ l2, l01 ++ l2, lw1, lw1'); repeat split.
    * etransitivity; [ apply (Permutation_Type_app_tail _ HP1) | ].
      rewrite <- app_assoc. reflexivity.
    * etransitivity; [ apply (Permutation_Type_app_tail _ HP2) | ].
      rewrite <- app_assoc. reflexivity.
    * assumption.
    * apply tens_Fr; pol_simpl; [ .. | apply wFoc_context in pi1' | ]; assumption.
  + assert (pi1' := fst (fst H) eq_refl).
    eapply (snd (fst H')) in HF2 as [(((l2', l02), lw2), lw2') [[HP1 HP2] Hi2] pi2']; [ | reflexivity ].
    exists (l1 ++ l2', l1 ++ l02, lw2, lw2'); repeat split.
    * etransitivity; [ apply (Permutation_Type_app_head _ HP1) | ].
      rewrite 2 app_assoc. apply Permutation_Type_app_tail, Permutation_Type_app_comm.
    * etransitivity; [ apply (Permutation_Type_app_head _ HP2) | ].
      rewrite 2 app_assoc. apply Permutation_Type_app_tail, Permutation_Type_app_comm.
    * assumption.
    * apply tens_Fr; pol_simpl; [ .. | apply wFoc_context in pi2' ]; assumption.
  + assert (pi1' := fst (fst H) eq_refl).
    assert (pi2' := fst (fst H') eq_refl).
    exists (l1 ++ l2, l1 ++ l2, nil, nil); repeat split; [ reflexivity .. | | ].
    * apply incl_inf_nil_l.
    * apply tens_Fr; pol_simpl; assumption.
- specialize X with (S (fpsize pi)) _ _ pi.
  apply X in H; [ | lia ].
  destruct (polarity A) as [HsA | HaA]; pol_simpl.
  + eapply (snd (fst H)) in HF as [(((l', l0), lw), lw') [[HP1 HP2] Hi] pi']; [ | reflexivity ].
    exists (l', l0, lw, lw'); repeat split; [ assumption .. | ].
    apply plus_Fr1.
    * pol_simpl. assumption.
    * apply wFoc_context in pi'. assumption.
  + assert (pi' := fst (fst H) eq_refl).
    exists (l, l, nil, nil); repeat split; [ reflexivity .. | | ].
    * apply incl_inf_nil_l.
    * apply plus_Fr1; [ pol_simpl | ]; assumption.
- specialize X with (S (fpsize pi)) _ _ pi.
  apply X in H; [ | lia ].
  destruct (polarity A) as [HsA | HaA]; pol_simpl.
  + eapply (snd (fst H)) in HF as [(((l', l0), lw), lw') [[HP1 HP2] Hi] pi']; [ | reflexivity ].
    exists (l', l0, lw, lw'); repeat split; [ assumption .. | ].
    apply plus_Fr2.
    * pol_simpl. assumption.
    * apply wFoc_context in pi'. assumption.
  + assert (pi' := fst (fst H) eq_refl).
    exists (l, l, nil, nil); repeat split; [ reflexivity .. | | ].
    * apply incl_inf_nil_l.
    * apply plus_Fr2; [ pol_simpl | ]; assumption.
- specialize X with (S (fpsize pi)) _ _ pi.
  apply X in H; [ | lia ].
  assert (pi' := fst (fst H) eq_refl).
  exists (map wn l, map wn l, nil, nil); repeat split; [ reflexivity .. | | ].
  * apply incl_inf_nil_l.
  * apply oc_Fr. assumption.
- inversion HF. subst.
  specialize X with (S (fpsize pi)) _ _ pi.
  apply X in H; [ | lia ].
  eapply (snd (fst H)) in X1 as [(((l', l0), lw), lw') [[HP1 HP2] Hi] pi']; [ | reflexivity ].
  exists (l', l0, A :: lw, lw'); repeat split.
  + list_simpl. apply Permutation_Type_cons; [ reflexivity | assumption ].
  + assumption.
  + apply incl_inf_tl. assumption.
  + assumption.
- inversion HF. subst.
  assert (Forall_inf wFoc (wn A :: wn A :: l)) as HF'
    by (constructor; assumption).
  specialize X with (S (fpsize pi)) _ _ pi.
  apply X in H; [ | lia ].
  eapply (snd (fst H)) in HF' as [(((l', l0), lw), lw') [[HP1 HP2] Hi] pi']; [ | reflexivity ].
  symmetry in HP1. assert (HP' := HP1).
  apply Permutation_Type_vs_cons_inv in HP' as [(l1', l2') Heq].
  dichot_elt_app_inf_exec Heq; subst.
  + decomp_map Heq0 eqn:Hx. subst.
    injection Hx as [= ->].
    assert (HP' := HP1). list_simpl in HP'. symmetry in HP'.
    apply Permutation_Type_cons_app_inv in HP'. symmetry in HP'.
    apply Permutation_Type_vs_cons_inv in HP' as [(l1'', l2'') Heq].
    rewrite app_assoc in Heq. dichot_elt_app_inf_exec Heq; subst.
    * rewrite <- map_app in Heq0.
      decomp_map Heq0 eqn:Heq. injection Heq as [= ->].
      exists (l', l0, l1' ++ l1, lw'); repeat split.
      -- symmetry in HP1. list_simpl in HP1. apply Permutation_Type_cons_app_inv in HP1.
         list_simpl. assumption.
      -- assumption.
      -- revert Hi Heq0; clear; induction lw'; intros Hi Heq.
         ++ apply incl_inf_nil_l.
         ++ destruct (incl_inf_cons_inv Hi) as [Hin Hi'].
            assert (HP := Permutation_Type_middle l1' l1 A).
            symmetry in HP. apply (Permutation_Type_in_inf _ HP) in Hin.
            inversion Hin; subst.
            ** apply incl_inf_cons.
               --- rewrite <- Heq. apply in_inf_elt.
               --- apply IHlw'; assumption.
            ** apply incl_inf_cons, IHlw'; assumption.
      -- assumption.
    * exists (l', l2 ++ l2'', l1' ++ A :: l1, A :: lw'); repeat split.
      -- symmetry in HP1. list_simpl in HP1. apply Permutation_Type_cons_app_inv in HP1.
         list_simpl. etransitivity; [ apply HP1 | ].
         rewrite ? app_assoc. apply Permutation_Type_elt. list_simpl. reflexivity.
      -- cbn. etransitivity; [ exact HP2 | ].
         symmetry. rewrite ? app_assoc. apply Permutation_Type_middle.
      -- apply incl_inf_cons; [ apply in_inf_elt | assumption ].
      -- assumption.
  + assert (HP' := HP1).
    list_simpl in HP'. symmetry in HP'. rewrite app_assoc in HP'. apply Permutation_Type_cons_app_inv in HP'.
    symmetry in HP'. apply Permutation_Type_vs_cons_inv in HP' as [(l1'', l2'') Heq].
    rewrite <- app_assoc in Heq. dichot_elt_app_inf_exec Heq; subst.
    * decomp_map Heq0 eqn:Hx. subst. injection Hx as [= ->].
      exists (l', l1 ++ l2', l1'' ++ A :: l0, A :: lw'); repeat split.
      -- symmetry in HP1. list_simpl in HP1. apply Permutation_Type_cons_app_inv in HP1.
         list_simpl. etransitivity; [ apply HP1 | ].
         rewrite ? app_assoc. apply Permutation_Type_elt. list_simpl. reflexivity.
      -- cbn. etransitivity; [ exact HP2 | ].
         symmetry. rewrite ? app_assoc. apply Permutation_Type_middle.
      -- apply incl_inf_cons; [ apply in_inf_elt | assumption ].
      -- assumption.
    * exists (l', l0 ++ l2'', A :: lw, A :: A :: lw'); repeat split.
      -- symmetry in HP1. rewrite app_assoc in HP1. apply Permutation_Type_cons_app_inv in HP1.
         list_simpl. etransitivity; [ apply HP1 | ].
         list_simpl. rewrite <- Heq1. symmetry. rewrite ? app_assoc.
         apply Permutation_Type_cons_app. reflexivity.
      -- cbn. etransitivity; [ exact HP2 | ].
         symmetry. rewrite ? app_assoc. apply Permutation_Type_cons_app.
         rewrite <- ? app_assoc, <- Heq1.
         rewrite ? app_assoc. apply Permutation_Type_middle.
      -- apply incl_inf_cons, incl_inf_cons.
         ++ constructor. reflexivity.
         ++ constructor. reflexivity.
         ++ apply incl_inf_tl. assumption.
      -- assumption.
(* third conjunct *)
- apply not_wFocl in HnF as [[[A l1] l2] -> [[[-> | [[B' C'] Hp]] | Ht ] | [[B' C'] Hw]]]; subst.
  + destruct (bot_rev_f pi _ _ eq_refl) as [pi' Hs].
    specialize X with (S (fpsize pi')) _ _ pi'.
    assert (S (fpsize pi') < s) as Hs' by lia.
    apply X in Hs'; [ | lia ].
    destruct (wFocl_dec (l1 ++ l2)) as [HF | HnF].
    * eapply (snd (fst Hs')) in HF as [(((l',l0), lw), lw') [[HP1 HP2] Hi] pi'']; split.
      -- apply foc_Fr in pi''.
         eapply (incl_Foc (C :: l0)) with (la := nil) in pi''; [ | | eassumption | intros ? [] | constructor ].
         ++ eapply ex_Fr; [ apply bot_Fr; eassumption | ].
            rewrite (app_comm_cons _ _ C). apply Permutation_Type_cons_app.
            list_simpl. symmetry. apply Permutation_Type_cons_app. assumption.
         ++ etransitivity; [ | apply Permutation_Type_middle ].
            apply Permutation_Type_cons; [ reflexivity | assumption ].
      -- assert (HC := sync_focus_F pi'').
         apply llFoc_foc_is_llFoc_foc in pi''.
         apply de_Fr in pi''.
         ++ eapply (incl_Foc (wn C :: l0)) with (la := nil) in pi'';
              [ | | eassumption | intros ? [] | constructor ].
            ** eapply ex_Fr; [ apply bot_Fr; eassumption | ].
               rewrite (app_comm_cons _ _ (wn C)). apply Permutation_Type_cons_app.
               list_simpl. symmetry. apply Permutation_Type_cons_app. assumption.
            ** etransitivity; [ | apply Permutation_Type_middle ].
               apply Permutation_Type_cons; [ reflexivity | assumption ].
         ++ pol_simpl. exact (wFoc_context pi'').
    * eapply (snd Hs') in HnF as [pi1 pi2]; split.
      -- eapply ex_Fr; [ apply bot_Fr, pi1 | ].
         rewrite (app_comm_cons _ (bot :: _) C).
         apply Permutation_Type_cons_app; reflexivity.
      -- eapply ex_Fr; [ apply bot_Fr, pi2 | ].
         rewrite (app_comm_cons _ (bot :: _) (wn C)).
         apply Permutation_Type_cons_app; reflexivity.
  + destruct (parr_rev_f pi _ _ _ _ eq_refl) as [pi' Hs].
    specialize X with (S (fpsize pi')) _ _ pi'.
    assert (S (fpsize pi') < s) as Hs' by lia.
    apply X in Hs'; [ | lia ].
    destruct (wFocl_dec (l1 ++ B' :: C' :: l2)) as [HF | HnF].
    * eapply (snd (fst Hs')) in HF as [(((l', l0), lw), lw') [[HP1 HP2] Hi] pi'']; split.
      -- apply foc_Fr in pi''.
         eapply (incl_Foc (C :: l0)) with (la := nil) in pi''; [ | | eassumption | intros ? [] | constructor ].
         ++ eapply ex_Fr; [ apply parr_Fr; eapply ex_Fr; [ eassumption | ] | ].
            ** symmetry. etransitivity; [ | apply Permutation_Type_middle ].
               symmetry in HP1. symmetry. apply (@Permutation_Type_cons _ _ C eq_refl) in HP1.
               etransitivity; [ apply HP1 | ].
               rewrite app_comm_cons. symmetry. apply Permutation_Type_cons_app, Permutation_Type_middle.
            ** rewrite (app_comm_cons _ _ C). apply Permutation_Type_middle.
         ++ etransitivity; [ | apply Permutation_Type_middle ].
            apply Permutation_Type_cons; [ reflexivity | assumption ].
      -- assert (HC := sync_focus_F pi'').
         apply llFoc_foc_is_llFoc_foc, de_Fr in pi''.
         ++ eapply (incl_Foc (wn C :: l0)) with (la := nil) in pi'';
              [ | | eassumption | intros ? [] | constructor ].
            ** eapply ex_Fr; [ apply parr_Fr; eapply ex_Fr; [ eassumption | ] | ].
               --- symmetry. etransitivity; [ | apply Permutation_Type_middle ].
                   symmetry in HP1. symmetry. apply (@Permutation_Type_cons _ _ (wn C) eq_refl) in HP1.
                   etransitivity; [ apply HP1 | ].
                   rewrite app_comm_cons. symmetry. apply Permutation_Type_cons_app, Permutation_Type_middle.
               --- rewrite (app_comm_cons _ _ (wn C)). apply Permutation_Type_middle.
            ** etransitivity; [ | apply Permutation_Type_middle ].
               apply Permutation_Type_cons; [ reflexivity | assumption ].
         ++ pol_simpl. exact (wFoc_context pi'').
    * destruct ((snd Hs') _ eq_refl HnF) as [pi1 pi2]; split.
      -- eapply ex_Fr; [ apply parr_Fr; eapply ex_Fr; [ apply pi1 | ] | ].
         ++ rewrite app_comm_cons.
            symmetry. apply Permutation_Type_cons_app, Permutation_Type_middle.
         ++ rewrite (app_comm_cons _ _ C).
            apply Permutation_Type_middle.
      -- eapply ex_Fr; [ apply parr_Fr; eapply ex_Fr; [ apply pi2 | ] | ].
         ++ rewrite app_comm_cons.
            symmetry. apply Permutation_Type_cons_app, Permutation_Type_middle.
         ++ rewrite (app_comm_cons _ _ (wn C)).
            apply Permutation_Type_middle.
  + split; (eapply ex_Fr; [ apply top_gen_Fr | ]).
    * symmetry. rewrite app_comm_cons.
      symmetry. apply Permutation_Type_middle.
    * symmetry. rewrite app_comm_cons.
      symmetry. apply Permutation_Type_middle.
  + destruct (with_rev1_f pi _ _ _ _ eq_refl) as [pi1 Hs1].
    destruct (with_rev2_f pi _ _ _ _ eq_refl) as [pi2 Hs2].
    assert (X' := X).
    specialize X with (S (fpsize pi1)) _ _ pi1.
    assert (S (fpsize pi1) < s) as Hs1' by lia.
    apply X in Hs1'; [ | lia ].
    specialize X' with (S (fpsize pi2)) _ _ pi2.
    assert (S (fpsize pi2) < s) as Hs2' by lia.
    apply X' in Hs2'; [ | lia ].
    destruct (wFocl_dec (l1 ++ l2)) as [HF | HnF].
    * assert (HF' := Forall_inf_app_l _ _ HF).
      assert (HF'' := Forall_inf_app_r _ _ HF).
      destruct (wFoc_dec B') as [HFB | HnFB].
      -- assert (Forall_inf wFoc (l1 ++ B' :: l2)) as HF1
           by (apply Forall_inf_app; [ | constructor ]; assumption).
         eapply (snd (fst Hs1')) in HF1 as [(((l1', l01), lw1), lw1') [[HP11 HP12] Hi1] pi1']; [ | reflexivity ].
         destruct (wFoc_dec C') as [HFC | HnFC].
         ++ assert (Forall_inf wFoc (l1 ++ C' :: l2)) as HF2
              by (apply Forall_inf_app; [ | constructor ]; assumption).
            eapply (snd (fst Hs2')) in HF2 as [(((l2', l02), lw2), lw2') [[HP21 HP22] Hi2] pi2']; split.
            ** apply foc_Fr in pi1'. apply foc_Fr in pi2'.
               eapply (@incl_Foc _ (C :: l01) nil lw1') in pi1';
                 [ eapply (@incl_Foc _ (C :: l02) nil lw2') in pi2' | | | | ]; eauto.
               --- eapply ex_Fr; [ apply with_Fr; eapply ex_Fr | ].
                   +++ apply pi1'.
                   +++ symmetry. etransitivity; [ | apply Permutation_Type_middle ].
                       symmetry in HP11. symmetry. apply (@Permutation_Type_cons _ _ C eq_refl) in HP11.
                       etransitivity; [ apply HP11 | ].
                       rewrite app_comm_cons. symmetry. apply Permutation_Type_middle.
                   +++ apply pi2'.
                   +++ symmetry. etransitivity; [ | apply Permutation_Type_middle ].
                       symmetry in HP21. symmetry. apply (@Permutation_Type_cons _ _ C eq_refl) in HP21.
                       etransitivity; [ apply HP21 | ].
                       rewrite app_comm_cons. symmetry. apply Permutation_Type_middle.
                   +++ rewrite (app_comm_cons _ (awith _ _ :: _) C). apply Permutation_Type_middle.
               --- etransitivity; [ | apply Permutation_Type_middle ].
                   apply Permutation_Type_cons; [ reflexivity | assumption ].
               --- intros ? [].
               --- etransitivity; [ | apply Permutation_Type_middle ].
                   apply Permutation_Type_cons; [ reflexivity | assumption ].
               --- intros ? [].
            ** assert (HC := sync_focus_F pi1').
               apply llFoc_foc_is_llFoc_foc in pi1'.
               apply llFoc_foc_is_llFoc_foc in pi2'.
               apply de_Fr in pi1'; [ apply de_Fr in pi2' | ].
               --- eapply (@incl_Foc _ (wn C :: l01) nil lw1') in pi1';
                     [ eapply (@incl_Foc _ (wn C :: l02) nil lw2') in pi2' | | | | ]; eauto.
                   +++ eapply ex_Fr; [ apply with_Fr; eapply ex_Fr | ].
                       *** apply pi1'.
                       *** symmetry. etransitivity; [ | apply Permutation_Type_middle ].
                           symmetry in HP11. symmetry. apply (@Permutation_Type_cons _ _ (wn C) eq_refl) in HP11.
                           etransitivity; [ apply HP11 | ].
                           rewrite app_comm_cons. symmetry. apply Permutation_Type_middle.
                       *** apply pi2'.
                       *** symmetry. etransitivity; [ | apply Permutation_Type_middle ].
                           symmetry in HP21. symmetry. apply (@Permutation_Type_cons _ _ (wn C) eq_refl) in HP21.
                           etransitivity; [ apply HP21 | ].
                           rewrite app_comm_cons. symmetry; apply Permutation_Type_middle.
                       *** rewrite (app_comm_cons _ (awith _ _ :: _) (wn C)). apply Permutation_Type_middle.
                   +++ etransitivity; [ | apply Permutation_Type_middle ].
                       apply Permutation_Type_cons; [ reflexivity | assumption ].
                   +++ intros ? [].
                   +++ etransitivity; [ | apply Permutation_Type_middle ].
                       apply Permutation_Type_cons; [ reflexivity | assumption ].
                   +++ intros ? [].
               --- pol_simpl. exact (wFoc_context pi2').
               --- pol_simpl. exact (wFoc_context pi1').
         ++ assert (notT (Forall_inf wFoc (l1 ++ C' :: l2))) as HF2
              by (intros HF0%Forall_inf_app_r; inversion_clear HF0; apply HnFC; assumption).
            eapply (snd Hs2') in HF2 as [pi2' pi2'']; split.
            ** eapply ex_Fr; [ apply with_Fr | ].
               --- apply foc_Fr in pi1'.
                   eapply (@incl_Foc _ (C :: l01) nil lw1') in pi1'.
                   +++ eapply ex_Fr; [ apply pi1' | ].
                       etransitivity; [ symmetry; apply Permutation_Type_middle | ].
                       symmetry in HP11. apply (@Permutation_Type_cons _ _ C eq_refl) in HP11.
                       etransitivity; [ apply HP11 | ].
                       rewrite app_comm_cons. symmetry. apply Permutation_Type_middle.
                   +++ etransitivity; [ | apply Permutation_Type_middle ].
                       apply Permutation_Type_cons; [ reflexivity | assumption ].
                   +++ apply Hi1.
                   +++ intros ? [].
                   +++ constructor.
               --- eapply ex_Fr; [ apply pi2' | ].
                   rewrite app_comm_cons. symmetry. apply Permutation_Type_middle.
               --- rewrite (app_comm_cons _ _ C). apply Permutation_Type_middle.
            ** eapply ex_Fr; [ apply with_Fr | ].
               --- assert (HC := sync_focus_F pi1').
                   apply llFoc_foc_is_llFoc_foc, de_Fr in pi1'.
                   +++ eapply (@incl_Foc _ (wn C :: l01) nil lw1') in pi1'.
                       *** eapply ex_Fr; [ apply pi1' | ].
                           etransitivity; [ symmetry; apply Permutation_Type_middle | ].
                           symmetry in HP11. apply (@Permutation_Type_cons _ _ (wn C) eq_refl) in HP11.
                           etransitivity; [ apply HP11 | ].
                           rewrite app_comm_cons. symmetry. apply Permutation_Type_middle.
                       *** etransitivity; [ | apply Permutation_Type_middle ].
                           apply Permutation_Type_cons; [ reflexivity | assumption ].
                       *** apply Hi1.
                       *** intros ? [].
                       *** constructor.
                   +++ pol_simpl. exact (wFoc_context pi1').
               --- eapply ex_Fr; [ apply pi2'' | ].
                   rewrite app_comm_cons. symmetry. apply Permutation_Type_middle.
               --- rewrite (app_comm_cons _ _ (wn C)). apply Permutation_Type_middle.
      -- assert (notT (Forall_inf wFoc (l1 ++ B' :: l2))) as HF1
           by (intros HF0%Forall_inf_app_r; inversion_clear HF0; apply HnFB; assumption).
         eapply (snd Hs1') in HF1 as [pi1' pi1'']; [ | reflexivity ].
         destruct (wFoc_dec C') as [HFC | HnFC].
         ++ assert (Forall_inf wFoc (l1 ++ C' :: l2)) as HF2
              by (apply Forall_inf_app; [ | constructor ]; assumption).
            eapply (snd (fst Hs2')) in HF2 as [(((l2',l02), lw2), lw2') [[HP21 HP22] Hi2] pi2']; split.
            ** apply foc_Fr in pi2'.
               eapply (@incl_Foc _ (C :: l02) nil lw2') in pi2'; [ | | eassumption | intros ? [] | constructor ].
               --- eapply ex_Fr; [ apply with_Fr; eapply ex_Fr | ].
                   +++ apply pi1'.
                   +++ rewrite app_comm_cons. symmetry. apply Permutation_Type_middle.
                   +++ apply pi2'.
                   +++ etransitivity; [ symmetry; apply Permutation_Type_middle | ].
                       symmetry in HP21. apply (@Permutation_Type_cons _ _ C eq_refl) in HP21.
                       etransitivity; [ apply HP21 | ].
                       rewrite app_comm_cons. symmetry. apply Permutation_Type_middle.
                   +++ rewrite (app_comm_cons _ (awith _ _ :: _) C).
                       apply Permutation_Type_middle.
               --- etransitivity; [ | apply Permutation_Type_middle ].
                   apply Permutation_Type_cons; [ reflexivity | assumption ].
            ** assert (HC := sync_focus_F pi2').
               apply llFoc_foc_is_llFoc_foc, de_Fr in pi2'.
               --- eapply (@incl_Foc _ (wn C :: l02) nil lw2') in pi2';
                     [ | | eassumption | intros ? [] | constructor ].
                   +++ eapply ex_Fr; [ apply with_Fr; eapply ex_Fr | ].
                       *** apply pi1''.
                       *** rewrite app_comm_cons. symmetry. apply Permutation_Type_middle.
                       *** apply pi2'.
                       *** etransitivity; [ symmetry; apply Permutation_Type_middle | ].
                           symmetry in HP21. apply (@Permutation_Type_cons _ _ (wn C) eq_refl) in HP21.
                           etransitivity; [ apply HP21 | ].
                           rewrite app_comm_cons. symmetry. apply Permutation_Type_middle.
                       *** rewrite (app_comm_cons _ (awith _ _ :: _) (wn C)). apply Permutation_Type_middle.
                   +++ etransitivity; [ | apply Permutation_Type_middle ].
                       apply Permutation_Type_cons; [ reflexivity | assumption ].
               --- pol_simpl. exact (wFoc_context pi2').
         ++ assert (notT (Forall_inf wFoc (l1 ++ C' :: l2))) as HF2
              by (intros HF0%Forall_inf_app_r; inversion_clear HF0; apply HnFC; assumption).
            eapply (snd Hs2') in HF2 as [pi2' pi2'']; split.
            ** eapply ex_Fr; [ apply with_Fr | ].
               --- eapply ex_Fr; [ apply pi1' | ].
                   rewrite app_comm_cons. symmetry. apply Permutation_Type_middle.
               --- eapply ex_Fr; [ apply pi2' | ].
                   rewrite app_comm_cons. symmetry. apply Permutation_Type_middle.
               --- rewrite (app_comm_cons _ _ C). apply Permutation_Type_middle.
            ** eapply ex_Fr; [ apply with_Fr | ].
               --- eapply ex_Fr; [ apply pi1'' | ].
                   rewrite app_comm_cons. symmetry. apply Permutation_Type_middle.
               --- eapply ex_Fr; [ apply pi2'' | ].
                   rewrite app_comm_cons. symmetry. apply Permutation_Type_middle.
               --- rewrite (app_comm_cons _ _ (wn C)). apply Permutation_Type_middle.
    * assert (notT (Forall_inf wFoc (l1 ++ B' :: l2))) as HF1.
      { intro HF0.
        assert (HF'1 := Forall_inf_app_l _ _ HF0).
        assert (HF'2 := Forall_inf_app_r _ _ HF0).
        inversion_clear HF'2.
        apply HnF. apply Forall_inf_app; assumption. }
      assert (notT (Forall_inf wFoc (l1 ++ C' :: l2))) as HF2.
      { intro HF0.
        assert (HF'1 := Forall_inf_app_l _ _ HF0).
        assert (HF'2 := Forall_inf_app_r _ _ HF0).
        inversion_clear HF'2.
        apply HnF. apply Forall_inf_app; assumption. }
      eapply (snd Hs1') in HF1 as [pi1' pi1'']; [ | reflexivity ].
      eapply (snd Hs2') in HF2 as [pi2' pi2'']; [ | reflexivity ].
      split; (eapply ex_Fr; [ apply with_Fr | ]).
      -- eapply ex_Fr; [ apply pi1' | ].
         rewrite app_comm_cons. symmetry. apply Permutation_Type_middle.
      -- eapply ex_Fr; [ apply pi2' | ].
         rewrite app_comm_cons. symmetry. apply Permutation_Type_middle.
      -- rewrite (app_comm_cons _ _ C). apply Permutation_Type_middle.
      -- eapply ex_Fr; [ apply pi1'' | ].
         rewrite app_comm_cons. symmetry. apply Permutation_Type_middle.
      -- eapply ex_Fr; [ apply pi2'' | ].
         rewrite app_comm_cons. symmetry. apply Permutation_Type_middle.
      -- rewrite (app_comm_cons _ _ (wn C)). apply Permutation_Type_middle.
Qed.


(** ** Unfocusing *)

Lemma llFoc_to_ll l Pi : llFoc l Pi ->
  ll_ll (match Pi with Some C => C :: nil | None => nil end ++ l).
Proof.
intro pi. induction pi; rewrite ? unfoc_sequent in *;
  try (now try destruct Pi; (constructor + (eapply ex_r; [ | apply Permutation_Type_swap ]; constructor))).
- eapply ex_r; [ eassumption | ].
  apply Permutation_Type_app; [ reflexivity | assumption ].
- assumption.
- eapply ex_r; [ apply tens_r; [ apply IHpi1 | apply IHpi2 ] | ].
  apply Permutation_Type_cons, Permutation_Type_app_comm. reflexivity.
Qed.


(** ** Direct wFocusing *)

Lemma unary_focusing A B l0 l1 l2 Pi : sformula A -> Forall_inf wFoc (B :: l0) ->
  (forall l, llFoc l (Some A) -> llFoc (B :: l0 ++ l) None) ->
  llFoc (l1 ++ A :: l2) Pi -> llFoc (l1 ++ B :: l0 ++ l2) Pi.
Proof.
intros Hs HF Hf pi.
remember (l1 ++ A :: l2) as l; revert A B l0 l1 l2 Hs HF Hf Heql.
induction pi; intros A0 B0 l0 l1' l2' Hs HF Hf Heql; subst.
- destruct l1'; destr_eq Heql; subst; [ exfalso; inversion Hs | ].
  destruct l1'; destr_eq H.
- destruct (Permutation_Type_vs_elt_inv _ _ _ p) as [(l1p, l2p) ->].
  apply Permutation_Type_app_inv,
       (Permutation_Type_app_middle l0), (Permutation_Type_elt B0) in p.
  refine (ex_Fr _ p).
  apply IHpi with A0; auto.
- destruct l1'; destr_eq Heql; subst.
  + cbn; apply Hf; assumption.
  + cbn; apply foc_Fr, (IHpi A0); auto.
- exfalso; destruct l1'; destr_eq Heql.
- destruct l1'; destr_eq Heql; subst; [ exfalso; inversion Hs | ].
  cbn; apply bot_Fr, (IHpi A0); auto.
- dichot_elt_app_inf_exec Heql; subst.
  + rewrite app_comm_cons, 2 app_assoc, <- (app_assoc _ _ l); apply tens_Fr; auto.
    * unfold polcont; destruct (polarity A); [ | rewrite app_comm_cons ]; apply (IHpi1 A0);
        auto; unfold polcont; destruct (polarity A); auto;
        exfalso; eapply disj_polarity; split; eassumption.
    * apply Forall_inf_app.
      -- apply (Forall_inf_app_l _ _ f).
      -- apply Forall_inf_app; auto.
         now apply Forall_inf_app_r in f; inversion f.
  + rewrite <- app_assoc; apply tens_Fr; auto.
    * unfold polcont; destruct (polarity B); [ | rewrite app_comm_cons ]; apply (IHpi2 A0);
      auto; unfold polcont; destruct (polarity B); auto;
      exfalso; eapply disj_polarity; split; eassumption.
    * apply Forall_inf_app.
      -- apply (Forall_inf_app_l _ _ f0).
      -- rewrite app_comm_cons; apply Forall_inf_app; auto.
         now apply Forall_inf_app_r in f0; inversion f0.
- destruct l1'; destr_eq Heql; subst; [ exfalso; inversion Hs | ].
  cbn; apply parr_Fr; rewrite 2 app_comm_cons; apply (IHpi A0); auto.
- destruct l1'; destr_eq Heql; subst; [ exfalso; inversion Hs | ].
  cbn; apply top_gen_Fr.
- apply plus_Fr1.
  + unfold polcont; destruct (polarity A); [ | rewrite app_comm_cons ]; apply (IHpi A0);
      auto; unfold polcont; destruct (polarity A); auto;
      exfalso; eapply disj_polarity; split; eassumption.
  + apply Forall_inf_app.
    * apply (Forall_inf_app_l _ _ f).
    * rewrite app_comm_cons; apply Forall_inf_app; auto.
      now apply Forall_inf_app_r in f; inversion f.
- apply plus_Fr2.
  + unfold polcont; destruct (polarity A); [ | rewrite app_comm_cons ]; apply (IHpi A0);
      auto; unfold polcont; destruct (polarity A); auto;
      exfalso; eapply disj_polarity; split; eassumption.
  + apply Forall_inf_app.
    * apply (Forall_inf_app_l _ _ f).
    * rewrite app_comm_cons; apply Forall_inf_app; auto.
      now apply Forall_inf_app_r in f; inversion f.
- destruct l1'; destr_eq Heql; subst; [ exfalso; inversion Hs | ].
  cbn. now apply with_Fr; rewrite app_comm_cons; [apply (IHpi1 A0) | apply (IHpi2 A0)].
- exfalso. decomp_map Heql. inversion Hs.
- destruct l1'; destr_eq Heql; subst; [ exfalso; inversion Hs | ].
  cbn. apply de_Fr.
  + unfold polcont. destruct (polarity A); [ | rewrite app_comm_cons ]; apply (IHpi A0);
      trivial; unfold polcont; destruct (polarity A); trivial;
      exfalso; eapply disj_polarity; split; eassumption.
  + apply Forall_inf_app; [ apply Forall_inf_app_l in f; apply f
                          | apply Forall_inf_app_r in f ].
    inversion f. inversion HF. constructor; [ | apply Forall_inf_app ]; assumption.
- destruct l1'; destr_eq Heql; subst; [ exfalso; inversion Hs | ].
  cbn. now apply wk_gen_Fr, (IHpi A0).
- destruct l1'; destr_eq Heql; subst; [ exfalso; inversion Hs | ].
  cbn. now apply co_gen_Fr; rewrite 2 app_comm_cons; apply (IHpi A0).
Qed.

Lemma focusing l : ll_ll l -> llFoc l None.
Proof.
intro pi. induction pi; (try discriminate f); (try now constructor).
- apply ex_Fr with (var X :: covar X :: nil); [ | apply Permutation_Type_swap ].
  apply foc_Fr, ax_Fr.
- now apply ex_Fr with l1.
- apply ex_Fr with (l1 ++ List.map wn lw ++ l2); auto.
  now apply Permutation_Type_app_head, Permutation_Type_app_tail, Permutation_Type_map.
- apply foc_Fr, one_Fr.
- clear pi1 pi2. destruct (polarity A).
  + apply ex_Fr with (tens A B :: l1 ++ l2);
      [ | apply Permutation_Type_cons, Permutation_Type_app_comm; reflexivity ].
    rewrite app_comm_cons; apply reversing with (B :: nil); auto.
    clear l2 IHpi2.
    intros l2 Hf pi; cbn in pi; cbn.
    apply ex_Fr with (tens A B :: l2 ++ l1);
      [ | apply Permutation_Type_cons, Permutation_Type_app_comm; reflexivity ].
    rewrite <- (app_nil_l _).
    eapply unary_focusing; [ eassumption | | | assumption ].
    * now constructor; [ left; left; constructor | ].
    * clear - Hf pi; intros l pi1.
      apply ex_Fr with (tens A B :: l ++ l2);
      [ | apply Permutation_Type_cons, Permutation_Type_app_comm; reflexivity ].
      destruct (polarity B).
      -- rewrite <- (app_nil_l _).
         eapply unary_focusing; [ eassumption | | | assumption ].
         ++ constructor; [ left; left; constructor | ].
            apply (wFoc_context pi1).
         ++ clear l2 Hf pi; intros l2 pi2.
            apply foc_Fr, tens_Fr.
            ** apply (llFoc_foc_is_llFoc_foc pi1).
            ** apply (llFoc_foc_is_llFoc_foc pi2).
            ** apply (wFoc_context pi1).
            ** apply (wFoc_context pi2).
      -- apply foc_Fr, tens_Fr; auto.
         ++ apply (llFoc_foc_is_llFoc_foc pi1).
         ++ pol_simpl. exact pi.
         ++ apply (wFoc_context pi1).
  + destruct (polarity B).
    * rewrite app_comm_cons; apply reversing with (A :: nil); auto.
      clear l1 IHpi1.
      intros l1 Hf pi; cbn in pi; cbn.
      apply ex_Fr with (nil ++ tens A B :: l1 ++ l2);
        [ | apply Permutation_Type_cons, Permutation_Type_app_comm; reflexivity ].
      eapply unary_focusing; [ eassumption | | | assumption ].
      -- now constructor; [ left; left; constructor | ].
      -- intros l pi'.
         apply foc_Fr, tens_Fr; auto.
         ++ pol_simpl. exact pi.
         ++ apply (llFoc_foc_is_llFoc_foc pi').
         ++ apply (wFoc_context pi').
    * rewrite app_comm_cons; apply (reversing (A :: nil)); auto.
      clear l1 IHpi1; intros l1 HF pi1; cbn in pi1.
      apply ex_Fr with (tens A B :: l1 ++ l2);
        [ | apply Permutation_Type_cons, Permutation_Type_app_comm; reflexivity ].
      rewrite app_comm_cons; apply (reversing (B :: nil)); auto.
      clear l2 IHpi2; intros l2 HF2 pi2; cbn in pi2; cbn.
      apply foc_Fr, tens_Fr; pol_simpl; assumption.
- apply top_gen_Fr.
- clear pi. destruct (polarity A).
  + rewrite <- (app_nil_l _), <- (app_nil_l l).
    eapply unary_focusing; [ eassumption | | | assumption ].
    * constructor; try left; try left; constructor.
    * clear; intros l pi.
      apply foc_Fr, plus_Fr1.
      -- apply (llFoc_foc_is_llFoc_foc pi).
      -- apply (wFoc_context pi).
  + change (aplus A B :: l) with ((aplus A B :: nil) ++ l).
    apply reversing with (A :: nil); auto.
    intros; apply foc_Fr, plus_Fr1; pol_simpl; assumption.
- clear pi. destruct (polarity A).
  + rewrite <- (app_nil_l _), <- (app_nil_l l).
    eapply unary_focusing; [ eassumption | | | assumption ].
    * constructor; try left; try left; constructor.
    * clear; intros l pi.
      apply foc_Fr, plus_Fr2.
      -- apply (llFoc_foc_is_llFoc_foc pi).
      -- apply (wFoc_context pi).
  + change (aplus B A :: l) with ((aplus B A :: nil) ++ l).
    apply reversing with (A :: nil); auto.
    intros; apply foc_Fr, plus_Fr2; pol_simpl; assumption.
- apply foc_Fr, oc_Fr. assumption.
- clear pi. destruct (polarity A).
  + rewrite <- (app_nil_l _), <- (app_nil_l l).
    eapply unary_focusing; [ eassumption | | | assumption ].
    * now repeat constructor.
    * clear; intros l pi.
      apply de_Fr; [ apply (llFoc_foc_is_llFoc_foc pi) | ].
      apply (wFoc_context pi).
  + change (wn A :: l) with ((wn A :: nil) ++ l).
    apply (reversing (A :: nil)); auto.
    clear l IHpi; intros l Hf pi.
    apply de_Fr; [ pol_simpl | ]; assumption.
- apply wk_gen_Fr. assumption.
- apply co_gen_Fr. assumption.
- destruct a.
Qed.

End Atoms.

Ltac pol_simpl :=
  match goal with
  | Hs : sformula _ |- _ => rewrite ? (fun l => polconts l Hs), ? (polfocs Hs) in *;
                            revert Hs; pol_simpl; intro Hs
  | Ha : aformula _ |- _ => rewrite ? (fun l => polconta l Ha), ? (polfoca Ha) in *;
                            revert Ha; pol_simpl; intro Ha
  | _ => idtac
  end.
