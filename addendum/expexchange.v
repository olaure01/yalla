From Stdlib Require Import List Permutation PeanoNat Lia.
From Yalla Require Import List_more Permutation_Type_more CPermutation_Type GPermutation_Type ll_fragments.
Import ListNotations.

Set Implicit Arguments.

Lemma list_sum_repeat k n : list_sum (repeat k n) = n * k.
Proof. induction n as [|n IHn]; [ | simpl repeat; simpl list_sum; rewrite IHn ]; reflexivity. Qed.

Lemma CPermutation_Type_flat_map A B (f : A -> list B) l1 l2:
  CPermutation_Type l1 l2 -> CPermutation_Type (flat_map f l1) (flat_map f l2).
Proof. intro HC. induction HC. rewrite ! flat_map_app. constructor. Qed.



Section ExponentialExchange.

Definition exwn := forall P l1 lw lw' l2, ll P (l1 ++ map wn lw ++ l2) ->
  Permutation_Type lw lw' -> ll P (l1 ++ map wn lw' ++ l2).
Check ex_wn_r : exwn.
Definition mco := forall P l0 l, ll P (map wn l0 ++ map wn l0 ++ l) -> ll P (map wn l0 ++ l).
Definition dcol := forall P A l0 l, ll P (wn A :: map wn l0 ++ wn A :: l) -> ll P (wn A :: map wn l0 ++ l).
Definition dcor := forall P A l0 l, ll P (wn A :: map wn l0 ++ wn A :: l) -> ll P (map wn l0 ++ wn A :: l).

Lemma exwn_dcol : dcol.
Proof.
intros P A l0. induction l0 as [|B l0 IH]; intros l pi.
- apply co_r. assumption.
- change (ll P ([wn A] ++ map wn (B :: l0) ++ l)).
  apply ex_wn_r with (l0 ++ [B]); [ | symmetry; apply Permutation_Type_cons_append ].
  list_simpl. apply IH.
  replace (wn A :: map wn l0 ++ wn A :: wn B :: l)
     with ([wn A] ++ map wn ((l0 ++ [A]) ++ [B]) ++ l) by now list_simpl.
  apply ex_wn_r with (B :: l0 ++ [A]); [ list_simpl; assumption | ].
  apply Permutation_Type_cons_append.
Qed.

Lemma dcol_exwn : dcol -> exwn.
Proof.
intros Hco P l1 lw lw' l2 pi HP. induction HP in l1, pi |- *.
- assumption.
- replace (l1 ++ map wn (x :: l') ++ l2)
     with ((l1 ++ [wn x]) ++ map wn l' ++ l2) by now list_simpl.
  apply IHHP. list_simpl. assumption.
- cbn.
  apply ex_r with ((wn x :: wn y :: map wn l ++ l2) ++ l1);
    [ | symmetry; apply PCPermutation_Type_app_comm ].
  replace ((wn x :: wn y :: map wn l ++ l2) ++ l1)
     with (wn x :: map wn [y] ++ map wn l ++ l2 ++ l1) by now list_simpl.
  apply Hco, wk_r.
  apply ex_r with (l1 ++ wn y :: wn x :: map wn l ++ l2); [ assumption | ].
  list_simpl. rewrite ? app_comm_cons, (app_assoc _ l2).
  apply PCPermutation_Type_app_comm.
- apply IHHP2, IHHP1, pi.
Qed.

Lemma mco_dcol : mco -> dcol.
Proof.
intros Hco P A l0 l pi.
change (ll P (map wn (A :: l0) ++ l)).
apply Hco.
change (ll P (map wn (A :: l0) ++ [wn A] ++ map wn l0 ++ l)).
rewrite app_assoc.
apply ex_r with ((map wn l0 ++ l) ++ (map wn (A :: l0) ++ [wn A]));
  [ | apply PCPermutation_Type_app_comm ].
rewrite <- app_assoc.
apply wk_list_r.
apply ex_r with ((map wn (A :: l0) ++ [wn A]) ++ l);
  [ | apply PCPermutation_Type_app_comm ].
list_simpl. assumption.
Qed.

Lemma dcol_mco : dcol -> mco.
Proof.
intros Hco P l0. induction l0 as [| A l0 IH]; intros l pi; [ assumption | ].
apply ex_r with (map wn l0 ++ l ++ [wn A]);
  [ | symmetry; list_simpl; rewrite app_assoc; apply PCPermutation_Type_cons_append ].
apply IH.
apply ex_r with (wn A :: map wn l0 ++ map wn l0 ++ l);
  [ | rewrite ? app_assoc; apply PCPermutation_Type_cons_append ].
apply Hco, pi.
Qed.

End ExponentialExchange.


Section StrongExponentialExchange.

Definition sexwnl := forall P A B l1 l2, ll P (l1 ++ B :: wn A :: l2) -> ll P (l1 ++ wn A :: B :: l2).
Definition sexwnr := forall P A B l1 l2, ll P (l1 ++ wn A :: B :: l2) -> ll P (l1 ++ B :: wn A :: l2).
Definition sdexwnl := forall P A l0 l1 l2, ll P (l1 ++ l0 ++ wn A :: l2) -> ll P (l1 ++ wn A :: l0 ++ l2).
Definition sdexwnr := forall P A l0 l1 l2, ll P (l1 ++ wn A :: l0 ++ l2) -> ll P (l1 ++ l0 ++ wn A :: l2).
Definition sdcol := forall P A l0 l, ll P (wn A :: l0 ++ wn A :: l) -> ll P (wn A :: l0 ++ l).
Definition sdcor := forall P A l0 l, ll P (wn A :: l0 ++ wn A :: l) -> ll P (l0 ++ wn A :: l).

Lemma sdexwnl_sdexwnr : sdexwnl -> sdexwnr.
Proof.
intros Hex P A l0 l1 l2 pi.
apply ex_r with ((l0 ++ wn A :: l2) ++ l1); [ | apply PCPermutation_Type_app_comm ].
list_simpl. rewrite <- (app_nil_r _), <- app_assoc, <- app_comm_cons. apply Hex.
list_simpl. rewrite app_assoc.
apply ex_r with ((l1 ++ [wn A]) ++ l0 ++ l2); [ | apply PCPermutation_Type_app_comm ].
list_simpl. exact pi.
Qed.

Lemma sdcol_sdcor : sdcol -> sdcor.
Proof.
intros Hco P A l0 l pi.
apply ex_r with ((wn A :: l) ++ l0); [ | apply PCPermutation_Type_app_comm ].
list_simpl. apply Hco.
rewrite app_comm_cons.
apply ex_r with ((wn A :: l0) ++ wn A :: l); [ | apply PCPermutation_Type_app_comm ].
exact pi.
Qed.

Lemma sexwnl_sdexwnl : sexwnl -> sdexwnl.
Proof.
intros Hex P A l0. induction l0 as [|B l0 IH]; intros l1 l2 pi.
- assumption.
- change (ll P (l1 ++ wn A :: [B] ++ l0 ++ l2)).
  apply Hex.
  change (ll P (l1 ++ [B] ++ wn A :: l0 ++ l2)). rewrite app_assoc.
  apply IH.
  rewrite <- app_assoc. assumption.
Qed.

Lemma sdexwnl_sdcol : sdexwnl -> sdcol.
Proof.
intros Hex P A l0 l pi.
apply co_r.
change (ll P ([wn A] ++ wn A :: l0 ++ l)).
apply Hex.
assumption.
Qed.

Lemma sdcol_sdexwnl : sdcol -> sdexwnl.
Proof.
intros Hco P A l0 l1 l2 pi.
apply ex_r with (wn A :: l0 ++ l2 ++ l1);
  [ | rewrite app_comm_cons, app_assoc; apply PCPermutation_Type_app_comm ].
apply Hco, wk_r.
rewrite app_comm_cons, app_assoc.
apply ex_r with (l1 ++ l0 ++ wn A :: l2); [ | apply PCPermutation_Type_app_comm ].
exact pi.
Qed.

End StrongExponentialExchange.



Notation birepeat X Y n := (concat (repeat [X; Y] n)).

Section Birepeat.

Variable T : Type.

Lemma cons_birepeat_odd (X Y : T) n : X :: birepeat Y X n = birepeat X Y n ++ [X].
Proof. induction n as [|n IHn]; [ | cbn; rewrite IHn ]; reflexivity. Qed.

Lemma birepeat_eq_app_odd (X Y : T) n l1 l2 :
  l1 ++ l2 = birepeat X Y n ++ [X] -> {'(p, q) &
  sum (prod (l1 = birepeat X Y p) (prod (l2 = [X] ++ birepeat Y X q) (n = p + q)))
      (prod (l1 = birepeat X Y p ++ [X]) (prod (l2 = birepeat Y X q) (n = p + q))) }.
Proof.
induction n in l1, l2 |- *; cbn; intros Heq.
- destruct l1; inversion Heq.
  + exists (0, 0). left. easy.
  + apply app_eq_nil in H1 as [-> ->].
    exists (0, 0). right. easy.
- destruct l1 as [|x [|y l1]].
  + exists (0, S n). left.
    cbn in Heq. subst. repeat split.
    rewrite cons_birepeat_odd. reflexivity.
  + exists (0, S n). right.
    inversion_clear Heq. repeat split.
    rewrite <- cons_birepeat_odd. reflexivity.
  + inversion Heq. subst.
    now destruct (IHn _ _ H2) as [(p, q) [[-> [-> ->]]|[-> [-> ->]]]]; exists (S p, q); [left|right].
Qed.

Variable X Y : T.

Lemma birepeat_app n m : birepeat X Y n ++ birepeat X Y m = birepeat X Y (n + m).
Proof. induction n as [|n IHn]; [ | cbn; rewrite IHn ]; reflexivity. Qed.

Lemma length_birepeat n : length (birepeat X Y n) = 2 * n.
Proof. rewrite length_concat, map_repeat, list_sum_repeat. cbn. lia. Qed.

Lemma birepeat_inj n m : birepeat X Y n = birepeat X Y m -> n = m.
Proof. intro Heq. apply (f_equal (@length _)) in Heq. rewrite ! length_birepeat in Heq. lia. Qed.

Lemma birepeat_twice n : birepeat X X n = repeat X (2 * n).
Proof. induction n; [ | cbn; rewrite IHn; replace (n + S (n + 0)) with (S (2 * n)) by lia ]; reflexivity. Qed.

Lemma birepeat_eq_app n l1 l2 :
  l1 ++ l2 = birepeat X Y n -> {'(p, q) &
  sum (prod (l1 = birepeat X Y p) (prod (l2 = birepeat X Y q) (n = p + q)))
      (prod (l1 = birepeat X Y p ++ [X]) (prod (l2 = [Y] ++ birepeat X Y q) (n = S (p + q)))) }.
Proof.
induction n in l1, l2 |- *; cbn; intros Heq.
- exists (0, 0). left.
  now apply app_eq_nil in Heq as [-> ->].
- destruct l1 as [|x [|y l1]].
  + exists (0, S n). left.
    now cbn in Heq; subst.
  + exists (0, n). right.
    now injection Heq as [].
  + injection Heq as [= -> -> Heq].
    destruct (IHn _ _ Heq) as [(p, q) [[-> [-> ->]]|[-> [-> ->]]]].
    * now exists (S p, q); left.
    * now exists (S p, q); right.
Qed.

Lemma cperm_birepeat n l : CPermutation_Type (X :: Y :: l) (birepeat X Y n) -> l = birepeat X Y (pred n).
Proof.
intros HC. inversion HC as [l1 l2 Heq1 Heq2].
apply birepeat_eq_app in Heq2 as [(p, q) [[-> [-> ->]]|[-> [-> ->]]]].
- destruct q as [|q].
  + destruct p as [|p]; inversion Heq1.
    now replace (S p + 0) with (S p) by lia.
  + injection Heq1 as [= <-].
    rewrite birepeat_app.
    now replace (p + S q) with (S (q + p)) by lia.
- rewrite <- cons_birepeat_odd in Heq1.
  change (X :: birepeat Y X p) with ([X] ++ birepeat Y X p) in Heq1.
  rewrite app_assoc, <- (app_assoc [Y]), <- cons_birepeat_odd in Heq1.
  replace (pred (S (p + q))) with (q + p) by lia; rewrite <- birepeat_app.
  injection Heq1 as [= -> _ <-]. reflexivity.
Qed.

Lemma cperm_birepeat_odd_1 n l : CPermutation_Type (X :: Y :: l) (birepeat X Y n ++ [X]) ->
  {'(p, q) | l = birepeat X Y p ++ [X] ++ birepeat X Y q & n = S (p + q) }.
Proof.
intros HC. inversion HC as [l1 l2 Heq1 Heq2].
apply birepeat_eq_app_odd in Heq2 as [(p, q) [[-> [-> ->]]|[-> [-> ->]]]];
  (destruct q as [|q]; [ destruct p as [|p] | ]; inversion Heq1).
- exists (p, 0); [ | lia ].
  rewrite cons_birepeat_odd. reflexivity.
- exists (q, p); [ | lia ].
  rewrite app_assoc, <- cons_birepeat_odd. reflexivity.
- exists (p, 0); [ | lia ].
  rewrite app_nil_r. reflexivity.
- exists (q, p); [ | lia ].
  cbn. rewrite cons_birepeat_odd, app_assoc. reflexivity.
Qed.

Lemma cperm_birepeat_odd_2 n l : CPermutation_Type (X :: Y :: l) (Y :: birepeat X Y n ) ->
  {'(p, q) | l = birepeat X Y p ++ [Y] ++ birepeat X Y q & n = S (p + q) }.
Proof.
intros HC. inversion HC as [l1 l2 Heq1 Heq2].
rewrite cons_birepeat_odd in Heq2.
apply birepeat_eq_app_odd in Heq2 as [(p, q) [[-> [-> ->]]|[-> [-> ->]]]];
  (destruct q as [|q]; [ destruct p as [|p] | ]; inversion Heq1).
- exists (p, 0); [ | lia ].
  rewrite cons_birepeat_odd. reflexivity.
- exists (q, p); [ | lia ].
  rewrite app_assoc, <- cons_birepeat_odd. reflexivity.
- exists (p, 0); [ | lia ].
  rewrite app_nil_r. reflexivity.
- exists (q, p); [ | lia ].
  cbn. rewrite cons_birepeat_odd, app_assoc. reflexivity.
Qed.

End Birepeat.


Section wnpermut.

Variable P : pfrag.
Variable Pnc : pperm P = false.
Variable Pmix0 : pmix0 P = false.
Variable Pmix2 : pmix2 P = false.
Variable Pcut : pcut P = false.
Variable Pgax : pgax P = NoAxioms.

Fixpoint vars A :=
match A with
| var X | covar X => [X]
| one | bot | top | zero => []
| tens A1 A2 | parr A1 A2 | aplus A1 A2 | awith A1 A2 => vars A1 ++ vars A2
| oc A1 | wn A1 => vars A1
end.

Lemma notpermut X Y l n :
  incl l [var X; var Y; covar X; covar Y; tens (covar X) (covar Y); wn (tens (covar X) (covar Y))] ->
   (CPermutation_Type (flat_map vars l) (birepeat X Y n)
  + CPermutation_Type (flat_map vars l) (birepeat Y X n ++ [Y])
  + CPermutation_Type (flat_map vars l) (birepeat X Y n ++ [X])) ->
  ll P l -> X = Y.
Proof.
intros Hincl HC pi. induction pi in n, Hincl, HC |- *; cbn in HC.
- destruct HC as [[HC|HC]|HC]; apply CPermutation_Type_length_2_inv in HC as [HC|HC];
    destruct n; inversion HC; reflexivity.
- rewrite Pnc in p. cbn in p.
  apply (IHpi n).
  + intros x Hin.
    apply Hincl.
    apply Permutation_Type_in with l1; [ | assumption ].
    apply CPermutation_Permutation_Type, p.
  + destruct HC as [[HC|HC]|HC]; [left;left|left;right|right];
      (transitivity (flat_map vars l2); [ apply CPermutation_Type_flat_map, p | assumption ]).
- assert (lw' = repeat (tens (covar X) (covar Y)) (length lw')) as Hlw'.
  { clear - Hincl.
    assert (forall x, In x lw' -> x = tens (covar X) (covar Y)) as Hin.
    { intros x Hx.
      apply (in_map wn) in Hx.
      apply or_introl with (B := In (wn x) l2) in Hx.
      apply in_or_app in Hx.
      apply or_intror with (A := In (wn x) l1) in Hx.
      apply in_or_app, Hincl in Hx.
      repeat (inversion Hx as [Hx1|Hx1]; [ inversion Hx1 | clear Hx; rename Hx1 into Hx ]).
      - reflexivity.
      - destruct Hx. }
    clear Hincl. induction lw' in Hin |- *; [ reflexivity | cbn ].
    rewrite IHlw'.
    - rewrite repeat_length. f_equal.
      apply Hin. left. reflexivity.
    - intros x Hx. apply Hin. right. exact Hx. }
  rewrite <- (Permutation_Type_length p) in Hlw'.
  rewrite Hlw' in p.
  apply Permutation_Type_Permutation, Permutation_repeat in p.
  rewrite <- p in Hlw'. subst lw'.
  apply (IHpi n); assumption.
- rewrite Pmix0 in f. discriminate f.
- rewrite Pmix2 in f. discriminate f.
- exfalso. specialize (Hincl one (or_introl eq_refl)).
  repeat destruct Hincl as [Hincl|Hincl]; inversion Hincl.
- exfalso. specialize (Hincl bot (or_introl eq_refl)).
  repeat destruct Hincl as [Hincl|Hincl]; inversion Hincl.
- assert (Hin := Hincl (tens A B) (or_introl eq_refl)).
  repeat destruct Hin as [Hin|Hin]; inversion Hin; subst.
  destruct HC as [[HC|HC]|HC];
    [ destruct n as [|n]; [ symmetry in HC; apply CPermutation_Type_nil in HC; inversion HC | ]
    | destruct n as [|n]; [ symmetry in HC; apply CPermutation_Type_length_1_inv in HC; inversion HC | ]
    | destruct n as [|n]; [ symmetry in HC; apply CPermutation_Type_length_1_inv in HC; inversion HC | ] ];
    simpl vars in HC; rewrite flat_map_app in HC.
  + apply cperm_birepeat in HC.
    apply birepeat_eq_app in HC as [(q, p) [[Heq2 [Heq1 Hn]]|[Heq2 [Heq1 Hn]]]].
    * apply (IHpi2 q).
      -- intros x [<-|Hx].
         ++ right. right. right. left. reflexivity.
         ++ apply Hincl. right. apply in_or_app. left. exact Hx.
      -- left. right.
         cbn. rewrite Heq2, cons_birepeat_odd. reflexivity.
    * apply (IHpi2 (S q)).
      -- intros x [<-|Hx].
         ++ right. right. right. left. reflexivity.
         ++ apply Hincl. right. apply in_or_app. left. exact Hx.
      -- left. left.
         cbn. rewrite Heq2.
         rewrite app_comm_cons. constructor.
  + change (([X] ++ [Y]) ++ flat_map vars l2 ++ flat_map vars l1)
      with (X :: Y :: flat_map vars l2 ++ flat_map vars l1) in HC.
    rewrite <- cons_birepeat_odd in HC.
    apply cperm_birepeat_odd_2 in HC as [(p, q) Heq].
    dichot_app_exec Heq; [ | dichot_app_exec Heq1 ].
    * apply birepeat_eq_app in Heq0 as [(q', p') [[Heq2' [Heq1' Hn]]|[Heq2' [Heq1' Hn]]]]; subst.
      -- apply (IHpi2 q').
         ++ intros x [<-|Hx].
            ** now right; right; right; left.
            ** now apply Hincl; right; apply in_or_app; left.
         ++ cbn; rewrite Heq2'; left; right.
            now rewrite cons_birepeat_odd.
      -- apply (IHpi2 (S q')).
         ++ intros x [<-|Hx].
            ** now right; right; right; left.
            ** now apply Hincl; right; apply in_or_app; left.
         ++ left. left.
            cbn. rewrite Heq2', app_comm_cons. constructor.
    * destruct l; inversion Heq2.
      -- list_simpl in Heq2. subst l0.
         apply (IHpi1 (S q)).
         ++ intros x [<-|Hx].
            ** now right; right; left.
            ** now apply Hincl; right; apply in_or_app; right.
         ++ cbn; rewrite Heq3; left; left.
            now rewrite app_comm_cons; etransitivity; [ constructor | ].
      -- subst.
         apply app_eq_nil in H1 as [-> ->].
         apply (IHpi1 q).
         ++ intros x [<-|Hx].
            ** now right; right; left.
            ** now apply Hincl; right; apply in_or_app; right.
         ++ cbn; rewrite Heq3; right.
            now rewrite app_comm_cons; etransitivity; [ constructor | ].
    * apply birepeat_eq_app in Heq3 as [(q', p') [[Heq2' [Heq1' Hn]]|[Heq2' [Heq1' Hn]]]]; subst.
      -- apply (IHpi1 p').
         ++ intros x [<-|Hx].
            ** now right; right; left.
            ** now apply Hincl; right; apply in_or_app; right.
         ++ cbn; rewrite Heq1'; right.
            apply CPermutation_Type_cons_append.
      -- apply (IHpi1 (S p')).
         ++ intros x [<-|Hx].
            ** now right; right; left.
            ** now apply Hincl; right; apply in_or_app; right.
         ++ cbn; rewrite Heq1'; left; left.
            now rewrite app_comm_cons; etransitivity; [ constructor | ].
  + change (([X] ++ [Y]) ++ flat_map vars l2 ++ flat_map vars l1)
      with (X :: Y :: flat_map vars l2 ++ flat_map vars l1) in HC.
    apply cperm_birepeat_odd_1 in HC as [(p, q) Heq].
    dichot_app_exec Heq; [ | destruct l; inversion Heq1; subst ].
    * apply birepeat_eq_app in Heq0 as [(q', p') [[Heq2' [Heq1' Hn]]|[Heq2' [Heq1' Hn]]]]; subst.
      -- apply (IHpi2 q').
         ++ intros x [<-|Hx].
            ** now right; right; right; left.
            ** now apply Hincl; right; apply in_or_app; left.
         ++ cbn; rewrite Heq2'; left; right.
            now rewrite cons_birepeat_odd.
      -- apply (IHpi2 (S q')).
         ++ intros x [<-|Hx].
            ** now right; right; right; left.
            ** now apply Hincl; right; apply in_or_app; left.
         ++ cbn; rewrite Heq2'; left; left.
            now rewrite app_comm_cons; etransitivity; [ constructor | ].
    * apply (IHpi2 p).
      -- intros x [<-|Hx].
         ++ now right; right; right; left.
         ++ now apply Hincl; right; apply in_or_app; left.
      -- cbn; rewrite Heq0; left; right.
         now rewrite app_nil_r, cons_birepeat_odd.
    * apply birepeat_eq_app in H1 as [(q', p') [[Heq2' [Heq1' Hn]]|[Heq2' [Heq1' Hn]]]]; subst.
      -- apply (IHpi1 p').
         ++ intros x [<-|Hx].
            ** now right; right; left.
            ** now apply Hincl; right; apply in_or_app; right.
         ++ cbn; rewrite Heq1'; right.
            apply CPermutation_Type_cons_append.
      -- apply (IHpi1 (S p')).
         ++ intros x [<-|Hx].
            ** now right; right; left.
            ** now apply Hincl; right; apply in_or_app; right.
         ++ cbn; rewrite Heq1'; left; left.
            now rewrite app_comm_cons; etransitivity; [ constructor | ].
- exfalso. specialize (Hincl (parr A B) (or_introl eq_refl)).
  repeat destruct Hincl as [Hincl|Hincl]; inversion Hincl.
- exfalso. specialize (Hincl top (or_introl eq_refl)).
  repeat destruct Hincl as [Hincl|Hincl]; inversion Hincl.
- exfalso. specialize (Hincl (aplus A B) (or_introl eq_refl)).
  repeat destruct Hincl as [Hincl|Hincl]; inversion Hincl.
- exfalso. specialize (Hincl (aplus B A) (or_introl eq_refl)).
  repeat destruct Hincl as [Hincl|Hincl]; inversion Hincl.
- exfalso. specialize (Hincl (awith A B) (or_introl eq_refl)).
  repeat destruct Hincl as [Hincl|Hincl]; inversion Hincl.
- exfalso. specialize (Hincl (oc A) (or_introl eq_refl)).
  repeat destruct Hincl as [Hincl|Hincl]; inversion Hincl.
- assert (Hin := Hincl (wn A) (or_introl eq_refl)).
  repeat destruct Hin as [Hin|Hin]; inversion Hin; subst.
  apply (IHpi n).
  + intros x [<-|Hx].
    * now right; right; right; right; left.
    * now apply Hincl; right.
  + exact HC.
- assert (Hin := Hincl (wn A) (or_introl eq_refl)).
  repeat destruct Hin as [Hin|Hin]; inversion Hin; subst.
  apply (IHpi (pred n)).
  + intros x Hx. apply Hincl. right. exact Hx.
  + destruct HC as [[HC|HC]|HC]; [left;left|left;right|right].
    * apply cperm_birepeat in HC as ->. reflexivity.
    * cbn in HC. rewrite <- cons_birepeat_odd in HC.
      apply cperm_birepeat_odd_2 in HC as [(p, q) -> ->].
      etransitivity; [ constructor | ]. list_simpl.
      rewrite birepeat_app, Nat.add_comm, cons_birepeat_odd. reflexivity.
    * cbn in HC. apply cperm_birepeat_odd_1 in HC as [(p, q) -> ->].
      etransitivity; [ constructor | ]; list_simpl.
      rewrite birepeat_app, Nat.add_comm.
      apply CPermutation_Type_cons_append.
- assert (Hin := Hincl (wn A) (or_introl eq_refl)).
  repeat destruct Hin as [Hin|Hin]; inversion Hin; subst.
  apply (IHpi (S n)).
  + intros x [<-|Hx].
    * now right; right; right; right; right; left.
    * apply Hincl, Hx.
  + assert (n > 0) as Hn.
    { clear - HC.
      destruct HC as [[HC|HC]|HC]; apply CPermutation_Permutation_Type, Permutation_Type_length in HC;
        unfold id in HC; cbn in HC.
      - rewrite length_birepeat in HC. lia.
      - rewrite length_app, length_birepeat in HC. cbn in HC. lia.
      - rewrite length_app, length_birepeat in HC. cbn in HC. lia. }
    destruct HC as [[HC|HC]|HC]; [left;left|left;right|right].
    * cbn. apply cperm_birepeat in HC as ->.
      change (X :: Y :: birepeat X Y (Nat.pred n)) with (birepeat X Y (S (pred n))).
      now replace (S (pred n)) with n by lia.
    * cbn. cbn in HC.
      rewrite <- cons_birepeat_odd in HC.
      apply cperm_birepeat_odd_2 in HC as [(p, q) -> ->].
      rewrite 4 app_comm_cons; etransitivity; [ constructor | ]; list_simpl.
      change (X :: Y :: X :: Y :: birepeat X Y p) with (birepeat X Y (S (S p))).
      now rewrite birepeat_app, Nat.add_comm, cons_birepeat_odd.
    * cbn. cbn in HC.
      apply cperm_birepeat_odd_1 in HC as [(p, q) -> ->].
      rewrite 4 app_comm_cons, app_assoc. etransitivity; [ constructor | ]. list_simpl.
      change (X :: Y :: X :: Y :: birepeat X Y p ++ [X]) with (birepeat X Y (S (S p)) ++ [X]).
      now rewrite app_assoc, birepeat_app, Nat.add_comm.
- rewrite Pcut in f; inversion f.
- clear - a Pgax. rewrite Pgax in a. destruct a.
Qed.

Lemma weakcommut X Y : ll P [var X; var Y; wn (tens (covar X) (covar Y))] -> X = Y.
Proof.
intro pi. eapply (notpermut 2) in pi; [ eassumption | | left; left; reflexivity ].
intros x [<-|[<-|[<-|[]]]].
- left. reflexivity.
- right. left. reflexivity.
- right. right. right. right. right. left. reflexivity.
Qed.

End wnpermut.

(* let us first show that commuting (wn _) with (var _) is enough *)
Lemma prestrongcommut P X Y : ll P [var X; wn (tens (covar X) (covar Y)); var Y].
Proof.
apply (ex_r _ (wn (tens (covar X) (covar Y)) :: [var Y] ++ [var X])).
2:{ cbn. symmetry. apply PCPermutation_Type_cons_append. }
apply de_r, tens_r; apply ax_r.
Qed.

Lemma strongcommut P X Y (Pc : pperm P = true) : ll P [var X; var Y; wn (tens (covar X) (covar Y))].
Proof.
apply (ex_r _ [var X; wn (tens (covar X) (covar Y)); var Y]).
apply prestrongcommut.
rewrite Pc. cbn. apply Permutation_Type_skip, Permutation_Type_swap.
Qed.
