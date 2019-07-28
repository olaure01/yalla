(* ll_fragments library for yalla *)


(** * Definitions of various Linear Logic fragments *)

Require Import PeanoNat.
Require Import Lia.

Require Import Bool_more.
Require Import List_more.
Require Import List_Type_more.
Require Import Permutation_Type_more.
Require Import Permutation_Type_solve.
Require Import genperm_Type.
Require Import Dependent_Forall_Type.

Require Export ll_prop.
Require Import subs.


(** ** Property on mix_n *)

Lemma mix_by_tens_n {P} : forall L,
  Forall_Type (ll P) L -> ll P (tens_n (length L) bot :: concat L).
Proof with try assumption.
  intros L FL; induction FL.
  - apply one_r.
  - destruct l.
    + apply bot_r.
      simpl; rewrite app_nil_r...
    + apply tens_r...
      apply bot_r...
Qed.

(** Provability in [P + mix_n] by adding [wn (tens_n n bot)], and provability in [P + cut + ax : parr_n n bot] are equivalent *)

Lemma ll_to_mix_cut {P} : forall n l, ll P (wn (tens_n n bot) :: l) ->
  ll (cutupd_pfrag (pmixupd_point_pfrag P n true) true) l.
Proof with try assumption; try reflexivity; try PCperm_Type_solve.
  intros n l pi.
  rewrite <- (app_nil_r _).
  apply cut_r with (wn (tens_n n bot))...
  + simpl; change nil with (map wn nil); apply oc_r.
    rewrite dual_tens_n; simpl.
    apply parr_n_r.
    rewrite app_nil_r.
    replace (const_list n one) with (concat (const_list n (one :: nil))).
    * apply mix_r.
      -- simpl; rewrite const_list_length.
         rewrite <- EqNat.beq_nat_refl with n...
      -- remember (cutupd_pfrag (pmixupd_point_pfrag P n true) true) as P'.
         clear.
         induction n.
         ++ apply Forall_Type_nil.
         ++ apply Forall_Type_cons...
            apply one_r.
    * clear; induction n...
      simpl; rewrite IHn...
  + apply stronger_pfrag with P...
    nsplit 4; simpl...
    * apply leb_true.
    * intros a.
      split with a...
    * intros n0.
      case_eq (n0 =? n); intros Heq...
      apply leb_true...
Qed.

Lemma mix_to_ll {P} : pperm P = true -> forall n bn l,
  ll (pmixupd_point_pfrag P n bn) l -> ll P (wn (tens_n n bot) :: l).
Proof with myeeasy ; try PCperm_Type_solve.
intros fp n bn l pi.
eapply (ext_wn_param _ P fp _ ((tens_n n bot) :: nil)) in pi.
- eapply ex_r...
- intros Hcut...
- simpl ; intros a.
  eapply ex_r ; [ | apply PCperm_Type_last ].
  apply wk_r.
  apply gax_r.
- intros.
  remember (length L) as nL.
  case_eq (nL =? n); intros Heq.
  + simpl in H; rewrite Heq in H.
    apply ex_r with (map wn (tens_n n bot :: nil) ++ concat L)...
    simpl.
    apply co_const_list_r with (S nL)...
    change (const_list (S nL) (wn (tens_n n bot)))
      with ((wn (tens_n n bot) :: nil) ++ const_list nL (wn (tens_n n bot))).
    rewrite HeqnL.
    refine (ex_concat_r _ _ ((wn (tens_n n bot)) :: nil) (wn (tens_n n bot)) L _)...
    replace n with nL by (apply EqNat.beq_nat_true; apply Heq).
    rewrite HeqnL.
    rewrite flat_map_concat_map.
    replace ((wn (tens_n (length L) bot)) :: nil )
       with (wn (tens_n (length (map (cons (wn (tens_n (length L) bot))) L)) bot) :: nil)
       by (rewrite map_length; reflexivity).
    apply de_r.
    apply tens_n_r.
    apply forall_Forall_Type.
    intros l' Hin.
    destruct (in_Type_map_inv _ _ _ Hin) as (l'' & (Heql'' & Hin'')); subst; clear Hin.
    apply bot_r.
    destruct (in_Type_map_inv _ _ _ Hin'') as (l' & (Heql' & Hin')); subst; clear Hin''.
    replace (length L) with n by (symmetry; apply EqNat.beq_nat_true; apply Heq).
    apply ex_r with (l' ++ map wn (tens_n n bot :: nil)).
    * apply Forall_Type_forall with (map (fun l => l ++ map wn (tens_n n bot :: nil)) L)...
      change (l' ++ map wn (tens_n n bot :: nil)) with ((fun l0 => l0 ++ map wn (tens_n n bot :: nil)) l').
      apply in_Type_map...
    * rewrite fp; simpl.
      perm_Type_solve.
  + exfalso.
    simpl in H; rewrite Heq in H; rewrite H0 in H; inversion H.
Qed.

Lemma parr_n_to_mix {P} : forall n l, pcut P = true ->
  ll (axupd_pfrag P (existT (fun x => x -> list formula) _
                            (fun a => match a with
                                      | inl x => projT2 (pgax P) x
                                      | inr tt => parr_n n one :: nil
                                      end))) l ->
  ll (pmixupd_point_pfrag P n true) l.
Proof with try assumption; try reflexivity.
  intros n l bcut pi.
  remember (axupd_pfrag P
               (existT (fun x : Type => x -> list formula)
                  (projT1 (pgax P) + unit)%type
                  (fun a : projT1 (pgax P) + unit =>
                   match a with
                   | inl x => projT2 (pgax P) x
                   | inr tt => parr_n n one :: nil
                   end))) as P'.
  induction pi using (ll_nested_ind _); try now constructor.
  - apply ex_r with l1...
    simpl; rewrite HeqP' in p; simpl in p...
  - apply ex_wn_r with lw...
  - apply mix_r.
    + simpl.
      rewrite HeqP' in eqpmix; simpl in eqpmix.
      case (length L =? n)...
    + apply forall_Forall_Type.
      intros l' Hin.
      apply In_Forall_Type_in with _ _ _ PL in Hin as (pi' & Hin).
      refine (Dependent_Forall_Type_forall_formula _ _ _ _ PL X Hin).
  - apply cut_r with A...
  - revert a.
    rewrite HeqP'; simpl.
    intro a.
    destruct a.
    + change (ll (pmixupd_point_pfrag P n true) (projT2 (pgax P) p))
        with (ll (pmixupd_point_pfrag P n true) (projT2 (pgax (pmixupd_point_pfrag P n true)) p)).
      apply gax_r.
    + destruct u.
      apply parr_n_r.
      rewrite app_nil_r.
      rewrite const_list_to_concat.
      apply mix_r.
      * simpl; rewrite const_list_length.
        rewrite <- EqNat.beq_nat_refl with n...
      * apply forall_Forall_Type.
        intros l' Hin.
        apply In_Type_const_list in Hin; subst.
        apply one_r.
Qed.

Lemma mix_to_parr_n {P} : forall n l, ll (pmixupd_point_pfrag P n true) l ->
  ll (cutupd_pfrag (axupd_pfrag P (existT (fun x => x -> list formula) _
                                          (fun a => match a with
                                                    | inl x => projT2 (pgax P) x
                                                    | inr tt => parr_n n one :: nil
                                                    end))) true) l.
Proof with try assumption; try reflexivity; try PCperm_Type_solve.
  intros n l pi.
  remember (cutupd_pfrag
          (axupd_pfrag P
          (existT (fun x : Type => x -> list formula) (projT1 (pgax P) + unit)%type
             (fun a : projT1 (pgax P) + unit =>
              match a with
              | inl x => projT2 (pgax P) x
              | inr tt => parr_n n one :: nil
              end))) true) as P'.
  induction pi using (ll_nested_ind _); try now constructor...
  - rewrite HeqP'; rewrite HeqP' in IHpi.
    apply ex_r with l1...
  - apply ex_wn_r with lw...
  - case_eq (length L =? n); intros Heq.
    + rewrite<- (app_nil_r _).
      apply cut_r with (tens_n (length L) bot).
      * rewrite HeqP'...
      * rewrite dual_tens_n; change (dual bot) with one.
        replace(parr_n (length L) one :: nil) with (projT2 (pgax (cutupd_pfrag
            (axupd_pfrag P
               (existT (fun x : Type => x -> list formula)
                  (projT1 (pgax P) + unit)%type
                  (fun a : projT1 (pgax P) + unit =>
                   match a with
                   | inl x => projT2 (pgax P) x
                   | inr tt => parr_n n one :: nil
                   end))) true)) (inr tt))...
        2:{ replace n with (length L) by (apply EqNat.beq_nat_true; apply Heq)... }
        rewrite HeqP'.
        apply gax_r.
      * apply mix_by_tens_n.
        apply forall_Forall_Type.
        intros l' Hin.
        apply In_Forall_Type_in with _ _ _ PL in Hin as (pi' & Hin).
        refine (Dependent_Forall_Type_forall_formula _ _ _ _ PL X Hin).
    + simpl in eqpmix.
      rewrite Heq in eqpmix.
      apply mix_r.
      * rewrite HeqP'...
      * apply forall_Forall_Type.
        intros l' Hin.
        apply In_Forall_Type_in with _ _ _ PL in Hin as (pi' & Hin).
        refine (Dependent_Forall_Type_forall_formula _ _ _ _ PL X Hin).
  - apply cut_r with A...
    rewrite HeqP'...
  - simpl.
    change (projT2 (pgax P) a) with (projT2 (pgax (cutupd_pfrag
            (axupd_pfrag P
               (existT (fun x : Type => x -> list formula)
                  (projT1 (pgax P) + unit)%type
                  (fun a : projT1 (pgax P) + unit =>
                   match a with
                   | inl x => projT2 (pgax P) x
                   | inr tt => parr_n n one :: nil
                   end))) true)) (inl a))...
    rewrite HeqP'.
    apply gax_r.
Qed.

Lemma ll_to_parr_n {P} : forall l n, ll P (wn (tens_n n bot) :: l) ->
  ll (cutupd_pfrag (axupd_pfrag P (existT (fun x => x -> list formula) _
                                          (fun a => match a with
                                                    | inl x => projT2 (pgax P) x
                                                    | inr tt => parr_n n one :: nil
                                                    end))) true) l.
Proof with try assumption; try reflexivity.
  intros l n pi.
  rewrite<- (app_nil_r l).
  apply cut_r with (wn (tens_n n bot))...
  + simpl.
    change nil with (map wn nil).
    apply oc_r; simpl.
    rewrite dual_tens_n.
    change (dual bot) with one.
    pattern (parr_n n one :: nil) at 2.
    replace (parr_n n one :: nil) with (projT2 (pgax (cutupd_pfrag
       (axupd_pfrag P
          (existT (fun x : Type => x -> list formula) (projT1 (pgax P) + unit)%type
             (fun a : projT1 (pgax P) + unit =>
              match a with
              | inl x => projT2 (pgax P) x
              | inr tt => parr_n n one :: nil
              end))) true)) (inr tt))...
    apply gax_r.
  + apply stronger_pfrag with P...
    nsplit 4...
    * apply leb_true.
    * intro a.
      split with (inl a)...
Qed.

Lemma parr_to_ll {P} : forall n l, pcut P = true -> pperm P = true ->
  ll (axupd_pfrag P (existT (fun x => x -> list formula) _
                            (fun a => match a with
                                      | inl x => projT2 (pgax P) x
                                      | inr tt => parr_n n one :: nil
                                      end))) l ->
  ll P (wn (tens_n n bot) :: l).
Proof with try assumption.
  intros n l Hcut Hperm pi.
  apply mix_to_ll with true...
  apply parr_n_to_mix...
Qed.

(** provability in [P + mix_n + mix_m] is equivalent to provability in [P + mix_n + mix_m + pmix_(n+m-1)] *)

Lemma mix_n_m_r {P} : forall n m, P.(pmix) n = true -> P.(pmix) m = true ->
  forall L, length L = n + m - 1 -> Forall_Type (ll P) L -> ll P (concat L).
Proof with try assumption; try reflexivity.
  intros n m Hpmixn Hpmixm L Heq FL.
  destruct n.
  { destruct m.
    - destruct L; inversion Heq.
      apply mix_r...
    - simpl in Heq; rewrite Nat.sub_0_r in Heq.
      change (concat L) with (concat (nil :: L)).
      apply mix_r...
      + simpl; rewrite Heq...
      + apply Forall_Type_cons...
        change nil with (concat (@nil (list formula))).
        apply mix_r...
        apply Forall_Type_nil. }
  simpl in Heq; rewrite Nat.sub_0_r in Heq.
  destruct (decomp_length_plus L n m Heq) as ((l1 & l2) & (Heql1 & (Heql2 & HeqL))).
  rewrite HeqL.
  rewrite concat_app.
  replace (concat l1 ++ concat l2) with (concat (l1 ++ ((concat l2) :: nil)))
    by (rewrite concat_app; simpl; rewrite app_nil_r; reflexivity).
  apply mix_r.
  - rewrite app_length.
    rewrite Nat.add_comm.
    rewrite Heql1...
  - rewrite HeqL in FL.
    apply Forall_Type_app_inv in FL as (FL1 & FL2).
    apply forall_Forall_Type.
    intros l' Hin.
    apply in_Type_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + apply Forall_Type_forall with l1...
    + inversion Hin ; [ | inversion X].
      rewrite <- H.
      apply mix_r...
      rewrite Heql2...
Qed.

Lemma mix_n_m_admissible {P} : forall n m, P.(pmix) n = true -> P.(pmix) m = true ->
  forall l, ll (pmixupd_point_pfrag P (n + m - 1) true) l -> ll P l.
Proof with try assumption; try reflexivity.
  intros n m Hpmixn Hpmixm l pi.
  remember (pmixupd_point_pfrag P (n + m -1) true) as P'.
  induction pi using (ll_nested_ind _); try now constructor.
  - apply ex_r with l1...
    rewrite HeqP' in p...
  - apply ex_wn_r with lw...
  - case_eq (length L =? (n + m - 1)); intro Heq.
    + apply mix_n_m_r with n m...
      * apply EqNat.beq_nat_true...
      * apply forall_Forall_Type.
        intros l' Hin.
        apply (In_Forall_Type_in _ _ _ PL) in Hin as (pi & Hin).
        refine (Dependent_Forall_Type_forall_formula _ _ _ _ PL X Hin).
    + rewrite HeqP' in eqpmix.
      simpl in eqpmix; rewrite Heq in eqpmix.
      apply mix_r...
      apply forall_Forall_Type.
      intros l' Hin.
      apply (In_Forall_Type_in _ _ _ PL) in Hin as (pi & Hin).
      refine (Dependent_Forall_Type_forall_formula _ _ _ _ PL X Hin).
  - apply cut_r with A...
    rewrite HeqP' in f...
  - revert a.
    replace (pgax P') with (pgax P).
    + intro a; apply gax_r.
    + rewrite HeqP'...
Qed.

(** provability in [P + mix_2] is equivalent to provability in [P + mix 2 + mix k] for all k > 2 *)

Lemma mix_2_to_mix_k_r {P} : P.(pmix) 2 = true ->
  forall L, 2 <= length L -> Forall_Type (ll P) L -> ll P (concat L).
Proof with try assumption.
  intro Hpmix; induction L; intros H FL.
  - exfalso.
    inversion H.
  - destruct L; [ | destruct L ].
    + exfalso.
      inversion H; inversion H1.
    + apply mix_r...
    + inversion FL; subst.
      clear FL; rename X into pi1; rename X0 into FL.
      replace (concat (a :: l :: l0 :: L)) with (concat (a :: (concat (l :: l0 :: L) :: nil)))
        by (simpl; rewrite<- ? app_assoc; rewrite app_nil_r; reflexivity).
      apply mix_r...
      apply Forall_Type_cons...
      apply Forall_Type_cons ; [ | apply Forall_Type_nil].
      apply IHL...
      simpl; simpl in H.
      do 2 apply le_n_S.
      apply le_0_n.
Qed.

Lemma mix_2_to_mix_k_admissible {P} : P.(pmix) 2 = true ->
  forall l, ll P l ->
  ll (pmixupd_pfrag P (fun k => if k =? 0 then P.(pmix) 0 else (if k =? 2 then true else false))) l.
Proof with try assumption.
  intros Hpmix l pi.
  remember (pmixupd_pfrag P (fun k => if k =? 0 then pmix P 0 else if k =? 2 then true else false))
    as P'.
  induction pi using (ll_nested_ind _); try now constructor.
  - apply ex_r with l1...
    rewrite HeqP'...
  - apply ex_wn_r with lw...
  - destruct L; [ | destruct L ].
    + apply mix_r.
      * rewrite HeqP'...
      * apply Forall_Type_nil.
    + simpl; rewrite app_nil_r.
      inversion X...
    + apply mix_2_to_mix_k_r.
      * rewrite HeqP'; reflexivity.
      * do 2 apply le_n_S.
        apply le_0_n.
      * apply forall_Forall_Type.
        intros l' Hin.
        apply (In_Forall_Type_in _ _ _ PL) in Hin as (pi' & Hin).
        refine (Dependent_Forall_Type_forall_formula _ _ _ _ PL X Hin).
  - apply cut_r with A...
    rewrite HeqP'...
  - revert a.
    replace (pgax P) with (pgax P').
    + intro a; apply gax_r.
    + rewrite HeqP'; reflexivity.
Qed.

(** provability in [P + mix_1] is equivalent to provability in [P] *)

Lemma mix1_rm {P} : forall l, ll P l -> ll (pmixupd_point_pfrag P 1 false) l.
Proof with try assumption; try reflexivity.
  intros l pi.
  remember (pmixupd_point_pfrag P 1 false) as P'.
  induction pi using (ll_nested_ind _); try now constructor.
  - apply ex_r with l1...
    rewrite HeqP'...
  - apply ex_wn_r with lw...
  - destruct L; [ | destruct L ].
    + apply mix_r.
      * rewrite HeqP'...
      * apply Forall_Type_nil.
    + simpl; rewrite app_nil_r.
      inversion X...
    + apply mix_r.
      * rewrite HeqP'; simpl in eqpmix; simpl; rewrite eqpmix...
      * apply forall_Forall_Type.
        intros l' Hin.
        apply (In_Forall_Type_in _ _ _ PL) in Hin as (pi' & Hin).
        refine (Dependent_Forall_Type_forall_formula _ _ _ _ PL X Hin).
  - apply cut_r with A...
    rewrite HeqP'...
  - revert a.
    replace (pgax P) with (pgax P').
    + intro a; apply gax_r.
    + rewrite HeqP'...
Qed.

(** provability in [P + mix_0 + mix_n] is equivalent to provability in [P + mix_0 + mix_n + pmix_k] for all k < n *)

Lemma mix_0_n_r {P} : forall n, P.(pmix) 0 = true -> P.(pmix) n = true ->
  forall L, length L <= n -> Forall_Type (ll P) L -> ll P (concat L).
Proof with try assumption; try reflexivity.
  intros n Hpmix0 Hpmixn L.
  remember (n - length L) as k.
  revert L Heqk.
  induction k; intros L Heqk H FL.
  - assert (length L = n).
    { apply Nat.le_antisymm...
      symmetry in Heqk.
      apply Nat.sub_0_le... }
    apply mix_r...
    rewrite H0...
  - change (concat L) with (concat (nil :: L)).
    apply IHk...
    + simpl; rewrite Nat.sub_succ_r.
      rewrite <- Heqk...
    + simpl; lia.
    + apply Forall_Type_cons...
      change nil with (concat (@nil (list formula))).
      apply mix_r...
      apply Forall_Type_nil.
Qed.

Lemma mix_0_n_admissible {P} : forall n, P.(pmix) 0 = true -> P.(pmix) n = true ->
  forall l, ll P l ->
  ll (pmixupd_pfrag P (fun k => if k =? 0 then P.(pmix) 0
                         else ( if n <=? k then P.(pmix) k else false))) l.
Proof with try assumption; try reflexivity.
  intros n Hpmix0 Hpmixn l pi.
  remember (pmixupd_pfrag P (fun k => if k =? 0 then P.(pmix) 0
                                                else (if n <=? k then P.(pmix) k else false))) as P'.
  induction pi using (ll_nested_ind _); try now constructor.
  - apply ex_r with l1...
    rewrite HeqP'...
  - apply ex_wn_r with lw...
  - destruct L.
    { apply mix_r.
      - rewrite HeqP'...
      - apply Forall_Type_nil. }
    case_eq (n <=? length (l0 :: L)); intros Heq.
    + apply mix_r...
      * rewrite HeqP'...
        simpl; simpl in Heq.
        rewrite Heq...
      * apply forall_Forall_Type.
        intros l' Hin.
        apply (In_Forall_Type_in _ _ _ PL) in Hin as (pi' & Hin).
        refine (Dependent_Forall_Type_forall_formula _ _ _ _ PL X Hin).
    + apply mix_0_n_r with n.
      * rewrite HeqP'...
      * rewrite HeqP'.
        destruct n...
        simpl.
        rewrite Nat.leb_refl...
      * apply Nat.le_trans with (S (S (length L))).
        -- apply Nat.le_succ_diag_r.
        -- apply Compare_dec.leb_iff_conv...
      * apply forall_Forall_Type.
        intros l' Hin.
        apply (In_Forall_Type_in _ _ _ PL) in Hin as (pi' & Hin).
        refine (Dependent_Forall_Type_forall_formula _ _ _ _ PL X Hin).
  - apply cut_r with A...
    rewrite HeqP'...
  - revert a.
    replace (pgax P) with (pgax P').
    + intro a; apply gax_r.
    + rewrite HeqP'...
Qed.

(** provability in [P + mix_0 + mix_2] is equivalent to provability in [P + mix_k] for all k *)

Lemma allmix_r {P} : P.(pmix) 0 = true -> P.(pmix) 2 = true ->
  forall L, Forall_Type (ll P) L -> ll P (concat L).
Proof with try assumption; try reflexivity.
  intros Hpmix0 Hpimx2 L FL.
  destruct L; [ | destruct L ].
  - apply mix_r...
  - simpl; rewrite app_nil_r.
    inversion FL...
  - apply mix_2_to_mix_k_r...
    simpl; lia.
Qed.

Lemma allmix_admissible {P} : P.(pmix) 0 = true -> P.(pmix) 2 = true ->
  forall l, ll P l -> ll (pmixupd_pfrag P pmix02) l.
Proof with try assumption; try reflexivity.
  intros Hpmix0 Hpmixn l pi.
  remember (pmixupd_pfrag P pmix02) as P'.
  induction pi using (ll_nested_ind _); try now constructor.
  - apply ex_r with l1...
    rewrite HeqP'...
  - apply ex_wn_r with lw...
  - apply allmix_r; try now rewrite HeqP'.
    apply forall_Forall_Type.
    intros l' Hin.
    apply (In_Forall_Type_in _ _ _ PL) in Hin as (pi' & Hin).
    refine (Dependent_Forall_Type_forall_formula _ _ _ _ PL X Hin).
  - apply cut_r with A...
    rewrite HeqP'...
  - revert a.
    replace (pgax P) with (pgax P').
    + intro a; apply gax_r.
    + rewrite HeqP'...
Qed.

(** ** Standard linear logic: [ll_ll] (no mix, no axiom, commutative) *)

(** cut / axioms / pmix / permutation *)
Definition pfrag_ll :=  mk_pfrag false NoAxioms pmix_none true.
(*                               cut   axioms    mix  perm  *)

Definition ll_ll := ll pfrag_ll.

Lemma cut_ll_r : forall A l1 l2,
  ll_ll (dual A :: l1) -> ll_ll (A :: l2) -> ll_ll (l2 ++ l1).
Proof with myeeasy.
intros A l1 l2 pi1 pi2.
eapply cut_r_axfree...
intros a ; destruct a.
Qed.

Lemma cut_ll_admissible :
  forall l, ll (cutupd_pfrag pfrag_ll true) l -> ll_ll l.
Proof with myeeasy.
intros l pi.
induction pi using (ll_nested_ind _); try (now econstructor).
- eapply ex_r...
- eapply ex_wn_r...
- eapply cut_ll_r...
Qed.



(** ** Linear logic with mix0: [ll_mix0] (no mix2, no axiom, commutative) *)

(** cut / axioms / pmix / permutation *)
Definition pfrag_mix0 := mk_pfrag false NoAxioms pmix0 true.
(*                                cut   axioms   mix   perm  *)

Definition ll_mix0 := ll pfrag_mix0.

Lemma cut_mix0_r : forall A l1 l2, 
  ll_mix0 (dual A :: l1) -> ll_mix0 (A :: l2) -> ll_mix0 (l2 ++ l1).
Proof with myeeasy.
intros A l1 l2 pi1 pi2.
eapply cut_r_axfree...
intros a ; destruct a.
Qed.

Lemma cut_mix0_admissible :
  forall l, ll (cutupd_pfrag pfrag_mix0 true) l -> ll_mix0 l.
Proof with myeeasy.
intros l pi.
induction pi using (ll_nested_ind _) ; try (now econstructor).
- eapply ex_r...
- eapply ex_wn_r...
- apply mix_r...
  apply forall_Forall_Type.
  intros l' Hin.
  destruct (In_Forall_Type_in _ _ _ PL Hin) as (pi' & HFin).
  refine (Dependent_Forall_Type_forall_formula _ _ _ _ PL X HFin).
- eapply cut_mix0_r...
Qed.

(** Provability in [ll_mix0] is equivalent to adding [wn one] in [ll] *)
Lemma mix0_to_ll {P} : pperm P = true -> forall b0 l,
  ll (pmixupd_point_pfrag P 0 b0) l -> ll P (wn one :: l).
Proof with myeeasy ; try PCperm_Type_solve.
  intros fp b0 l pi.
  change one with (tens_n 0 bot).
  apply mix_to_ll with b0...
Qed.

Lemma ll_to_mix0_cut {P} : forall l,
  ll P (wn one :: l) -> ll (cutupd_pfrag (pmixupd_point_pfrag P 0 true) true) l.
Proof.
  intros l pi.
  change one with (tens_n 0 bot) in pi.
  apply ll_to_mix_cut.
  apply pi.
Qed.

Lemma mix0_wn_one : forall l, ll_mix0 (wn one :: l) -> ll_mix0 l.
Proof with myeeasy; try reflexivity.
  intros l pi.
  (* an alternative proof is by introducing a cut with (oc bot) *)
  apply stronger_pfrag with (cutrm_pfrag (cutupd_pfrag (pmixupd_point_pfrag pfrag_mix0 0 true) true)).
  - nsplit 4...
    + intro a; split with a...
    + intro n; destruct n...
  - apply cut_admissible_axfree.
    + intros a; inversion a.
    + apply ll_to_mix_cut...
Qed.


(** Provability in [ll_mix0] is equivalent to provability of [ll]
extended with the provability of [bot :: bot :: nil] *)

Lemma mix0_to_ll_bot {P} : pcut P = true -> pperm P = true -> forall bc b0 bp l,
  ll (mk_pfrag bc P.(pgax) (fun k => if (k =? 0) then b0 else P.(pmix) k) bp) l ->
  ll (axupd_pfrag P (existT (fun x => x -> list formula) _
                            (fun a => match a with
                                      | inl x => projT2 (pgax P) x
                                      | inr tt => bot :: bot :: nil
                                      end))) l.
Proof with myeeasy ; try (unfold PCperm_Type ; PCperm_Type_solve).
remember (axupd_pfrag P (existT (fun x => x -> list formula) _
                                (fun a => match a with
                                          | inl x => projT2 (pgax P) x
                                          | inr tt => bot :: bot :: nil
                                          end))) as P'.
intros fc fp bc b0 bp l pi.
eapply stronger_pfrag in pi.
- eapply mix0_to_ll in pi...
  assert (pcut P' = true) as fc' by (rewrite HeqP' ; simpl ; assumption).
  apply (stronger_pfrag _ P') in pi.
  + assert (ll P' (bot :: map wn nil)) as pi'.
    { change (bot :: map wn nil) with ((bot :: nil) ++ nil).
      eapply (@cut_r _ fc' bot).
      - apply one_r.
      - assert ({ b | bot :: bot :: nil = projT2 (pgax P') b })
          as [b Hgax] by (rewrite HeqP' ; now (exists (inr tt))).
        rewrite Hgax.
        apply gax_r. }
    apply oc_r in pi'.
    rewrite <- (app_nil_l l).
    eapply (@cut_r _ fc' (oc bot)) ; [ simpl ; apply pi | apply pi' ].
  + nsplit 4 ; rewrite HeqP'...
    simpl ; intros a ; exists (inl a)...
- nsplit 4 ; intros ; simpl...
  + rewrite fc.
    destruct bc...
  + exists a...
  + rewrite fp; apply leb_true.
Qed.

Lemma ll_bot_to_mix0 {P} : forall l,
  ll (axupd_pfrag P (existT (fun x => x -> list formula) _
                              (fun a => match a with
                                        | inl x => projT2 (pgax P) x
                                        | inr tt => bot :: bot :: nil
                                        end))) l ->
  ll (pmixupd_point_pfrag P 0 true) l.
Proof with myeeasy.
intros l pi.
remember (pmixupd_point_pfrag P 0 true) as P'.
apply (stronger_pfrag _
  (axupd_pfrag P' (existT (fun x => x -> list formula) _
                          (fun a => match a with
                                    | inl x => projT2 (pgax P) x
                                    | inr tt => bot :: bot :: nil
                                    end)))) in pi.
- eapply ax_gen...
  clear - HeqP' ; simpl ; intros a.
  destruct a.
  + assert ({ b | projT2 (pgax P) p = projT2 (pgax P') b })
      as [b Hgax] by (rewrite HeqP' ; now exists p).
    rewrite Hgax.
    apply gax_r.
  + destruct u.
    apply bot_r.
    apply bot_r.
    change nil with (concat (@nil (list formula))).
    apply mix_r.
    * rewrite HeqP'...
    * apply Forall_Type_nil.
- rewrite HeqP' ; nsplit 4 ; simpl ; intros...
  + exists a...
  + destruct n.
    * apply leb_true.
    * apply leb_refl.
Qed.

(** [mix2] is not valid in [ll_mix0] *)

Lemma mix0_not_mix2 : ll_mix0 (one :: one :: nil) -> False.
Proof.
intros pi.
remember (one :: one :: nil) as l.
revert Heql ; induction pi ; intros Heql ; subst ; try inversion Heql.
- apply IHpi.
  simpl in p ; apply Permutation_Type_sym in p.
  apply Permutation_Type_length_2_inv in p.
  destruct p ; assumption.
- destruct l1 ; destruct lw' ; inversion Heql ; subst.
  + now symmetry in p ; apply Permutation_Type_nil in p ; subst.
  + now symmetry in p ; apply Permutation_Type_nil in p ; subst.
  + destruct l1 ; inversion H2.
    destruct l1 ; inversion H3.
- destruct L.
  + inversion H0.
  + inversion i.
- inversion f.
- destruct a.
Qed.


(** ** Linear logic with mix2: [ll_mix2] (no mix0, no axiom, commutative) *)

(** cut / axioms / pmix / permutation *)
Definition pfrag_mix2 := mk_pfrag false NoAxioms pmix2 true.
(*                                cut   axioms   mix   perm  *)

Definition ll_mix2 := ll pfrag_mix2.

Lemma cut_mix2_r : forall A l1 l2,
  ll_mix2 (dual A :: l1) -> ll_mix2 (A :: l2) -> ll_mix2 (l2 ++ l1).
Proof with myeeasy.
intros A l1 l2 pi1 pi2.
eapply cut_r_axfree...
intros a ; destruct a.
Qed.

Lemma cut_mix2_admissible :
  forall l, ll (cutupd_pfrag pfrag_mix2 true) l -> ll_mix2 l.
Proof with myeeasy.
intros l pi.
induction pi using (ll_nested_ind _) ; try (now econstructor).
- eapply ex_r...
- eapply ex_wn_r...
- apply mix_r...
  apply forall_Forall_Type.
  intros l' Hin.
  destruct (In_Forall_Type_in _ _ _ PL Hin) as (pi' & HFin).
  refine (Dependent_Forall_Type_forall_formula _ _ _ _ PL X HFin).
- eapply cut_mix2_r...
Qed.

(** Provability in [ll_mix2] is equivalent to adding [wn (tens bot bot)] in [ll] *)

Lemma mix2_to_ll {P} : pperm P = true -> forall b2 l,
  ll (pmixupd_point_pfrag P 2 b2) l -> ll P (wn (tens bot bot) :: l).
Proof with myeeasy ; try PCperm_Type_solve.
  intros fp b2 l pi.
  change (tens bot bot) with (tens_n 2 bot).
  apply mix_to_ll with b2...
Qed.

Lemma ll_to_mix2_cut {P} : forall l,
  ll P (wn (tens bot bot) :: l) -> ll (cutupd_pfrag (pmixupd_point_pfrag P 2 true) true) l.
Proof with myeasy.
  intros l pi.
  change (tens bot bot) with (tens_n 2 bot).
  apply ll_to_mix_cut...
Qed.

(** Provability in [ll_mix2] is equivalent to
provability of [ll] extended with the provability of [one :: one :: nil]
and to provability of [ll] extended with the provability of [parr (dual B) (dual A) :: tens A B :: nil]
for all [A] and [B] *)


Lemma mix2_to_ll_one_one {P} : pcut P = true -> pperm P = true -> forall bc b2 bp l,
  ll (mk_pfrag bc P.(pgax) (fun k => if (k =? 2) then b2 else P.(pmix) k) bp) l ->
  ll (axupd_pfrag P (existT (fun x => x -> list formula) _
                            (fun a => match a with
                                      | inl x => projT2 (pgax P) x
                                      | inr tt => one :: one :: nil
                                      end))) l.
Proof with myeeasy ; try (unfold PCperm_Type ; PCperm_Type_solve).
remember (axupd_pfrag P (existT (fun x => x -> list formula) _
                                (fun a => match a with
                                          | inl x => projT2 (pgax P) x
                                          | inr tt => one :: one :: nil
                                          end))) as P'.
intros fc fp bc b2 bp l pi.
eapply stronger_pfrag in pi.
- eapply mix2_to_ll in pi...
  assert (pcut P' = true) as fc' by (rewrite HeqP' ; simpl ; assumption).
  apply (stronger_pfrag _ P') in pi.
  + assert (ll P' (parr one one :: map wn nil)) as pi'.
    { change (parr one one :: map wn nil) with ((parr one one :: nil) ++ nil).
      eapply (@cut_r _ fc' bot).
      - apply one_r.
      - apply bot_r.
        apply parr_r.
        assert ({ b | one :: one :: nil = projT2 (pgax P') b })
          as [b Hgax] by (rewrite HeqP' ; now (exists (inr tt))).
        rewrite Hgax.
        apply gax_r. }
    apply oc_r in pi'.
    rewrite <- (app_nil_l l).
    eapply (@cut_r _ fc' (oc (parr one one))) ; [ simpl ; apply pi | apply pi' ].
  + nsplit 4 ; rewrite HeqP'...
    simpl ; intros a ; exists (inl a)...    
- nsplit 4 ; intros ; simpl...
  + rewrite fc.
    destruct bc...
  + exists a...
  + rewrite fp; apply leb_true.
Qed.

Lemma ll_one_one_to_ll_tens_parr_one_one_cut {P} : (pcut P = true) ->
  ll P (parr one one :: parr bot bot :: nil) -> ll P (one :: one :: nil).
Proof.
intros Hcut pi.
assert (ll P (dual (parr (parr one one) (parr bot bot)) :: one :: one :: nil)) as pi'.
{ simpl.
  rewrite <- (app_nil_r _) ; rewrite <- app_comm_cons.
  apply tens_r.
  - rewrite <- (app_nil_r _) ; rewrite <- app_comm_cons.
    apply tens_r ; apply one_r.
  - rewrite <- (app_nil_l (one :: nil)).
    rewrite (app_comm_cons _ _ one).
    apply tens_r ; apply ax_exp. }
rewrite <- (app_nil_l _).
eapply cut_r ; [ assumption | apply pi' | ].
apply parr_r ; apply pi.
Qed.

Lemma ll_tens_parr_one_one_to_ll_tens_parr {P} : forall l,
  ll (axupd_pfrag P (existT (fun x => x -> list formula) _
                              (fun a => match a with
                                        | inl x => projT2 (pgax P) x
                                        | inr tt => parr one one :: parr bot bot :: nil
                                        end))) l ->
  ll (axupd_pfrag P (existT (fun x => x -> list formula) _
                            (fun a => match a with
                                      | inl x => projT2 (pgax P) x
                                      | inr (A,B) => parr (dual B) (dual A) :: parr A B :: nil
                                      end))) l.
Proof with myeeasy.
intros l pi.
remember (axupd_pfrag P (existT (fun x => x -> list formula) _
                         (fun a => match a with
                                   | inl x => projT2 (pgax P) x
                                   | inr tt => parr one one :: parr bot bot :: nil
                                   end))) as P'.
apply (ax_gen P') ; (try now (rewrite HeqP' ; simpl ; reflexivity))...
clear - HeqP' ; simpl ; intros a.
revert a ; rewrite HeqP' ; intros a ; destruct a ; simpl.
- assert ({ b | projT2 (pgax P) p =
                projT2 (pgax (axupd_pfrag P (existT (fun x => x -> list formula) _
                       (fun a => match a with
                                 | inl x => projT2 (pgax P) x
                                 | inr (A,B) => parr (dual B) (dual A) :: parr A B :: nil
                                 end)))) b })
    as [b Hgax] by (now exists (inl p)).
  rewrite Hgax.
  apply gax_r.
- destruct u.
  assert ({ b | parr one one :: parr bot bot :: nil =
                projT2 (pgax (axupd_pfrag P (existT (fun x => x -> list formula) _
                       (fun a => match a with
                                 | inl x => projT2 (pgax P) x
                                 | inr (A,B) => parr (dual B) (dual A) :: parr A B :: nil
                                 end)))) b })
    as [b Hgax] by (exists (inr (bot,bot)) ; reflexivity).
  rewrite Hgax.
  apply gax_r.
Qed.

Lemma ll_tens_parr_to_mix2 {P} : forall l,
  ll (axupd_pfrag P (existT (fun x => x -> list formula) _
                              (fun a => match a with
                                        | inl x => projT2 (pgax P) x
                                        | inr (A,B) => parr (dual B) (dual A) :: parr A B :: nil
                                        end))) l ->
  ll (pmixupd_point_pfrag P 2 true) l.
Proof with myeeasy.
intros l pi.
remember (pmixupd_point_pfrag P 2 true) as P'.
apply (stronger_pfrag _
  (axupd_pfrag P' (existT (fun x => x -> list formula) _
                          (fun a => match a with
                                    | inl x => projT2 (pgax P) x
                                    | inr (A,B) => parr (dual B) (dual A) :: parr A B :: nil
                                    end)))) in pi.
- eapply ax_gen...
  clear - HeqP' ; simpl ; intros a.
  destruct a.
  + assert ({ b | projT2 (pgax P) p = projT2 (pgax P') b })
      as [b Hgax] by (rewrite HeqP' ; now exists p).
    rewrite Hgax.
    apply gax_r.
  + destruct p as [A B].
    apply parr_r.
    apply (ex_r _ (parr A B :: (dual B :: nil) ++ (dual A) :: nil)) ;
      [ |etransitivity ; [ apply PCperm_Type_last | reflexivity ] ].
    apply parr_r.
    eapply ex_r ;
      [ | symmetry ; apply PCperm_Type_last ].
    list_simpl.
    rewrite <- (app_nil_l (dual A :: _)).
    rewrite 2 app_comm_cons.
    change ((B :: dual B :: nil) ++ dual A :: A :: nil)
      with (concat ((B :: dual B :: nil) :: (dual A :: A :: nil) :: nil)).
    apply mix_r.
    * rewrite HeqP'...
    * apply Forall_Type_cons.
      -- apply ax_exp.
      -- apply Forall_Type_cons ; [ | apply Forall_Type_nil].
         apply ex_r with (A :: dual A :: nil) ; [apply ax_exp | PCperm_Type_solve].
- rewrite HeqP' ; nsplit 4 ; simpl ; intros...
  + exists a...
  + repeat (destruct n; try apply leb_refl; try apply leb_true).
Qed.

Lemma ll_one_one_to_mix2 {P} : forall l,
  ll (axupd_pfrag P (existT (fun x => x -> list formula) _
                            (fun a => match a with
                                      | inl x => projT2 (pgax P) x
                                      | inr tt => one :: one :: nil
                                      end))) l ->
  ll (pmixupd_point_pfrag P 2 true) l.
Proof with myeeasy.
intros l pi.
remember (pmixupd_point_pfrag P 2 true) as P'.
apply (stronger_pfrag _
  (axupd_pfrag P' (existT (fun x => x -> list formula) _
                          (fun a => match a with
                                    | inl x => projT2 (pgax P) x
                                    | inr tt => one :: one :: nil
                                    end)))) in pi.
- eapply ax_gen...
  clear - HeqP' ; simpl ; intros a.
  destruct a.
  + assert ({ b | projT2 (pgax P) p = projT2 (pgax P') b })
      as [b Hgax] by (rewrite HeqP' ; now exists p).
    rewrite Hgax.
    apply gax_r.
  + destruct u.
    change (one :: one :: nil) with ((one :: nil) ++ one :: nil).
    rewrite HeqP'.
    change ((one :: nil) ++ one :: nil) with (concat ((one :: nil) :: (one :: nil) :: nil)).
    apply mix_r...
    repeat (apply Forall_Type_cons; try apply one_r).
    apply Forall_Type_nil.
- rewrite HeqP' ; nsplit 4 ; simpl ; intros...
  + exists a...
  + repeat (destruct n; try apply leb_refl; try apply leb_true).
Qed.

(** [mix0] is not valid in [ll_mix2] *)

Lemma mix2_not_mix0 : ll_mix2 nil -> False.
Proof.
intros pi.
remember nil as l.
revert Heql ; induction pi using (ll_nested_ind _) ; intros Heql ; subst ; try inversion Heql.
- apply IHpi.
  simpl in p ; apply Permutation_Type_sym in p.
  apply Permutation_Type_nil in p.
  assumption.
- apply app_eq_nil in Heql ; destruct Heql as [Heql Heql2].
  apply app_eq_nil in Heql2 ; destruct Heql2 as [Heql2 _] ; subst.
  destruct lw' ; inversion Heql2.
  symmetry in p ; apply Permutation_Type_nil in p ; subst.
  intuition.
- destruct L; try (destruct L); try (destruct L); try (destruct L); inversion eqpmix.
  clear H0.
  simpl in Heql.
  destruct l0; inversion Heql; destruct l1; inversion Heql.
  destruct (In_Forall_Type_in _ _ nil PL) as (pi & Hin).
  + left; reflexivity.
  + refine (Dependent_Forall_Type_forall_formula _ _ _ _ PL X Hin eq_refl).
- inversion f.
- destruct a.
Qed.


(** ** Linear logic with both mix0 and mix2: [ll_mix02] (no axiom, commutative) *)

(** cut / axioms / mix0 / mix2 / permutation *)
Definition pfrag_mix02 := mk_pfrag false NoAxioms pmix02 true.
(*                                 cut   axioms   mix    perm  *)

Definition ll_mix02 := ll pfrag_mix02.

Lemma cut_mix02_r : forall A l1 l2,
  ll_mix02 (dual A :: l1) -> ll_mix02 (A :: l2) -> ll_mix02 (l2 ++ l1).
Proof with myeeasy.
intros A l1 l2 pi1 pi2.
eapply cut_r_axfree...
intros a ; destruct a.
Qed.

Lemma cut_mix02_admissible :
  forall l, ll (cutupd_pfrag pfrag_mix02 true) l -> ll_mix02 l.
Proof with myeeasy.
intros l pi.
induction pi using (ll_nested_ind _) ; try (now econstructor).
- eapply ex_r...
- eapply ex_wn_r...
- apply mix_r...
  apply forall_Forall_Type.
  intros l' Hin.
  apply (In_Forall_Type_in _ _ _ PL) in Hin as (pi & Hin).
  refine (Dependent_Forall_Type_forall_formula _ _ _ _ PL X Hin).
- eapply cut_mix02_r...
Qed.

(** Provability in [ll_mix02] is equivalent to adding [wn (tens (wn one) (wn one))] in [ll] *)

Lemma mix02_to_ll {P} : pperm P = true -> forall b1 b2 bp l,
  ll (mk_pfrag P.(pcut) P.(pgax) (fun k => if (k =? 0) then b1
                                     else (if (k =? 2) then b2 else P.(pmix) k)) bp) l ->
  ll P (wn (tens (wn one) (wn one)) :: l).
Proof with myeeasy ; try PCperm_Type_solve.
intros fp b1 b2 bp l pi.
eapply (ext_wn_param _ P fp _ (tens (wn one) (wn one) :: nil)) in pi.
- eapply ex_r...
- intros Hcut...
- simpl ; intros a.
  eapply ex_r ; [ | apply PCperm_Type_last ].
  apply wk_r.
  apply gax_r.
- intros L Hpmix eqpmix FL.
  destruct L.
  + apply de_r.
    change nil with (@nil formula ++ nil).
    apply tens_r; apply de_r; apply one_r.
  + destruct L.
    * simpl; rewrite app_nil_r.
      inversion FL...
    * destruct L.
      -- simpl.
         apply ex_r with (wn (tens (wn one) (wn one)) :: (l0 ++ l1))...
         inversion FL; subst; inversion X0; subst.
         clear FL X0 X2.
         apply co_r; apply co_r.
         apply ex_r with (wn (tens (wn one) (wn one)) :: ((l0 ++ wn (tens (wn one) (wn one)) :: nil)
                                                              ++ (l1 ++ wn (tens (wn one) (wn one)) :: nil))) ;
           [ | rewrite fp; simpl; perm_Type_solve].
         apply de_r.
         apply tens_r; apply wk_r...
      -- apply ex_r with (wn (tens (wn one) (wn one)) :: concat (l0 :: l1 :: l2 :: L));
           [ | rewrite fp; simpl; perm_Type_solve].
         apply co_const_list_r with (length (l0 :: l1 :: l2 :: L)).
         apply (ex_concat_r _ fp nil).
         rewrite app_nil_l; rewrite flat_map_concat_map.
         apply mix_r.
         ++ rewrite map_length...
         ++ apply forall_Forall_Type.
            intros l' Hin.
            apply in_Type_map_inv in Hin as (l'' & (Heq & Hin)).
            rewrite <- Heq.
            apply ex_r with ((fun l0 => l0 ++ (map wn (tens (wn one) (wn one) :: nil))) l'')...
            apply (in_Type_map (fun l : list formula => l ++ map wn (tens (wn one) (wn one) :: nil))) in Hin.
            apply Forall_Type_forall with (map
             (fun l : list formula => l ++ map wn (tens (wn one) (wn one) :: nil))
             (l0 :: l1 :: l2 :: L))...
Qed.

Lemma ll_to_mix02_cut {P} : forall l, ll P (wn (tens (wn one) (wn one)) :: l) ->
  ll (mk_pfrag true P.(pgax) (fun k => if (k =? 0) then true
                                 else (if (k =? 2) then true else P.(pmix) k)) P.(pperm)) l.
Proof with myeasy.
intros l pi.
eapply stronger_pfrag in pi.
- rewrite <- (app_nil_r l).
  eapply cut_r ; [ | | apply pi]...
  change nil with (map wn nil).
  apply oc_r.
  apply parr_r.
  change (oc bot :: oc bot :: map wn nil)
    with (concat ((oc bot :: map wn nil) :: (oc bot :: map wn nil) :: nil)).
  apply mix_r...
  apply forall_Forall_Type.
  intros l' Hin.
  destruct Hin.
  + subst.
    apply oc_r.
    apply bot_r.
    change (map wn nil) with (concat (@nil (list formula))).
    apply mix_r...
    apply Forall_Type_nil.
  + destruct i; [ | destruct i].
    subst.
    apply oc_r.
    apply bot_r.
    change (map wn nil) with (concat (@nil (list formula))).
    apply mix_r...
    apply Forall_Type_nil.
- nsplit 4...
  + destruct pcut...
  + intros a.
    exists a...
  + intros n.
    repeat (destruct n ; try (apply leb_refl); try (apply leb_true)).
Qed.

(** Provability in [ll_mix02] is equivalent to adding other stuff in [ll] *)

Lemma mix02_to_ll' {P} : pperm P = true -> forall b0 b2 l,
  ll (pmixupd_point_pfrag (pmixupd_point_pfrag P 0 b0) 2 b2) l -> ll P (wn one :: wn (tens bot bot) :: l).
Proof with myeasy.
intros Hperm b0 b2 l pi.
eapply mix0_to_ll...
eapply mix2_to_ll...
apply pi.
Qed.

Lemma mix02_to_ll'' {P} : pperm P = true -> forall b0 b2 bp l,
  ll (mk_pfrag P.(pcut) P.(pgax) (fun k => if (k =? 0) then b0
                                     else (if (k =? 2) then b2 else P.(pmix) k)) bp) l ->
  ll P (wn one :: wn (tens (wn one) bot) :: l).
Proof with myeeasy ; try PCperm_Type_solve.
intros Hperm b0 b2 bp l pi.
eapply (ext_wn_param _ _ _ _ (one :: tens (wn one) bot :: nil)) in pi.
- eapply ex_r...
- intros Hcut...
- simpl ; intros a.
  eapply ex_r ; [ | apply PCperm_Type_app_comm ] ; list_simpl.
  apply wk_r.
  apply wk_r.
  apply gax_r.
- destruct L.
  { intros Hpmix0 Hpmix0' pi'.
    simpl.
    apply de_r...
    eapply ex_r ; [ | apply PCperm_Type_swap ].
    apply wk_r.
    apply one_r. }
  destruct L.
  { intros Hpmix1 Hpmix1' FL.
    simpl in Hpmix1, Hpmix1'.
    rewrite Hpmix1 in Hpmix1'; inversion Hpmix1'. }
  destruct L.
  2:{ intros Hpmix Hpmix' FL.
      simpl in Hpmix, Hpmix'.
      rewrite Hpmix in Hpmix'; inversion Hpmix'. }
  intros _ _ FL.
  simpl.
  inversion FL; inversion X0; subst; clear FL X0 X2;
    rename X into pi1; rename X1 into pi2; rename l1 into l2; rename l0 into l1.
  apply (ex_r _ (wn (tens (wn one) bot) :: (wn one :: l2) ++ l1)) ; [ | rewrite Hperm ]...
  apply co_r.
  apply co_r.
  apply de_r.
  apply (ex_r _ (tens (wn one) bot :: (wn (tens (wn one) bot) :: wn one :: l2)
                                   ++ (wn (tens (wn one) bot) :: l1))) ;
    [ | rewrite Hperm ]...
  apply tens_r.
  + eapply ex_r ; [ apply pi1 | ]...
  + apply bot_r ; eapply ex_r ; [ apply pi2 | rewrite Hperm ]...
Unshelve. assumption.
Qed.

(** Provability in [ll_mix02] is equivalent to provability of [ll]
extended with the provability of both [bot :: bot :: nil] and [one :: one :: nil] *)

Lemma mix02_to_ll_one_eq_bot {P} : pcut P = true -> pperm P = true -> forall bc b0 b2 bp l,
  ll (mk_pfrag bc P.(pgax) (fun k => if (k =? 0) then b0 else (if (k =? 2) then b2 else P.(pmix) k)) bp) l ->
  ll (axupd_pfrag P (existT (fun x => x -> list formula) _
                            (fun a => match a with
                                      | inl x => projT2 (pgax P) x
                                      | inr true => one :: one :: nil
                                      | inr false => bot :: bot :: nil
                                      end))) l.
Proof with myeeasy ; try (unfold PCperm_Type ; PCperm_Type_solve).
remember (axupd_pfrag P (existT (fun x => x -> list formula) _
                                (fun a => match a with
                                          | inl x => projT2 (pgax P) x
                                          | inr true => one :: one :: nil
                                          | inr false => bot :: bot :: nil
                                          end))) as P'.
intros fc fp bc b0 b2 bp l pi.
eapply stronger_pfrag in pi.
- eapply mix02_to_ll in pi...
  assert (pcut P' = true) as fc' by (rewrite HeqP' ; simpl ; assumption).
  apply (stronger_pfrag _ P') in pi.
  + assert (ll P' (parr (oc bot) (oc bot) :: map wn nil)) as pi'.
    { apply parr_r.
      change (oc bot :: oc bot :: map wn nil)
        with ((oc bot :: nil) ++ oc bot :: map wn nil).
      eapply (@cut_r _ fc' one).
      - apply bot_r.
        apply oc_r.
        change (bot :: map wn nil) with ((bot :: nil) ++ nil).
        eapply (@cut_r _ fc' bot).
        + apply one_r.
        + assert ({ b | bot :: bot :: nil = projT2 (pgax P') b })
            as [b Hgax] by (rewrite HeqP' ; now (exists (inr false))).
          rewrite Hgax.
          apply gax_r.
      - change (one :: oc bot :: nil)
          with ((one :: nil) ++ oc bot :: map wn nil).
        eapply (@cut_r _ fc' one).
        + apply bot_r.
          apply oc_r.
          change (bot :: map wn nil) with ((bot :: nil) ++ nil).
          eapply (@cut_r _ fc' bot).
          * apply one_r.
          * assert ({ b | bot :: bot :: nil = projT2 (pgax P') b })
              as [b Hgax] by (rewrite HeqP' ; now (exists (inr false))).
            rewrite Hgax.
            apply gax_r.
        + assert ({ b | one :: one :: nil = projT2 (pgax P') b })
            as [b Hgax] by (rewrite HeqP' ; now (exists (inr true))).
          rewrite Hgax.
          apply gax_r. }
    apply oc_r in pi'.
    rewrite <- (app_nil_l l).
    eapply (@cut_r _ fc' (oc (parr (oc bot) (oc bot)))) ; [ simpl ; apply pi | apply pi' ].
  + nsplit 4 ; rewrite HeqP'...
    simpl ; intros a ; exists (inl a)...
- nsplit 4 ; intros ; simpl...
  + rewrite fc.
    destruct bc...
  + exists a...
Qed.

Lemma ll_one_eq_bot_to_mix02 {P} : forall l,
  ll (axupd_pfrag P (existT (fun x => x -> list formula) _
                            (fun a => match a with
                                      | inl x => projT2 (pgax P) x
                                      | inr true => one :: one :: nil
                                      | inr false => bot :: bot :: nil
                                      end))) l ->
  ll (mk_pfrag P.(pcut) P.(pgax) (fun k => if (k =? 0) then true
                                     else (if (k =? 2) then true else P.(pmix) k)) P.(pperm)) l.
Proof with myeeasy.
intros l pi.
remember (mk_pfrag P.(pcut) P.(pgax) (fun k => if (k =? 0) then true
                                         else (if (k =? 2) then true else P.(pmix) k)) P.(pperm)) as P'.
apply (stronger_pfrag _
  (axupd_pfrag P' (existT (fun x => x -> list formula) _
                          (fun a => match a with
                                    | inl x => projT2 (pgax P) x
                                    | inr true => one :: one :: nil
                                    | inr false => bot :: bot :: nil
                                    end)))) in pi.
- eapply ax_gen...
  clear - HeqP' ; simpl ; intros a.
  destruct a.
  + assert ({ b | projT2 (pgax P) p = projT2 (pgax P') b })
      as [b Hgax] by (rewrite HeqP' ; now exists p).
    rewrite Hgax.
    apply gax_r.
  + destruct b.
    * change (one :: one :: nil) with ((one :: nil) ++ one :: nil).
      rewrite HeqP'.
      change ((one :: nil) ++ one :: nil) with (concat ((one :: nil) :: (one :: nil) :: nil)).
      apply mix_r...
      repeat (apply Forall_Type_cons; try apply one_r).
      apply Forall_Type_nil.
    * apply bot_r.
      apply bot_r.
      rewrite HeqP'.
      change nil with (concat (@nil (list formula))).
      apply mix_r...
      apply Forall_Type_nil.
- rewrite HeqP' ; nsplit 4 ; simpl ; intros...
  + exists a...
  + repeat (destruct n; try apply leb_refl; try apply leb_true).
Qed.


(* Hgax_cut is here only to allow the use of cut_admissible
   the more general result without Hgax_cut should be provable by induction as for [ll_to_mix2] *)
Lemma ll_to_mix02''_axcut {P} :
    (forall a, Forall atomic (projT2 (pgax P) a)) ->
    (forall a b x l1 l2 l3 l4,
       projT2 (pgax P) a = (l1 ++ dual x :: l2) -> projT2 (pgax P) b = (l3 ++ x :: l4) ->
       { c | projT2 (pgax P) c = l3 ++ l2 ++ l1 ++ l4 }) ->
    pperm P = true ->
  forall l, ll P (wn one :: wn (tens (wn one) bot) :: l) ->
  ll (pmixupd_point_pfrag (pmixupd_point_pfrag P 0 true) 2 true) l.
Proof with myeasy.
intros Hgax_at Hgax_cut Hperm l pi.
apply (stronger_pfrag (cutrm_pfrag (cutupd_pfrag (pmixupd_point_pfrag
                                                 (pmixupd_point_pfrag P 0 true) 2 true) true))).
{ nsplit 4...
  intros a ; exists a... }
eapply cut_admissible...
eapply stronger_pfrag in pi.  
- rewrite <- (app_nil_r l).
  eapply (cut_r _ (wn (tens (wn one) bot))) ; simpl.
  + change nil with (map wn nil).
    apply oc_r.
    apply parr_r.
    change (one :: oc bot :: map wn nil) with (concat ((one :: nil) :: (oc bot :: map wn nil) :: nil)).
    apply mix_r...
    apply Forall_Type_cons.
    { apply one_r. }
    apply Forall_Type_cons.
    { apply oc_r.
      apply bot_r.
      change (map wn nil) with (concat (@nil (list formula))).
      apply mix_r...
      apply Forall_Type_nil. }
    apply Forall_Type_nil.
  + rewrite <- app_nil_r.
    eapply cut_r ; [ | | apply pi ] ; simpl...
    change nil with (map wn nil).
    apply oc_r.
    apply bot_r.
    change (map wn nil) with (concat (@nil (list formula))).
    apply mix_r...
    apply Forall_Type_nil.
- etransitivity ; [ apply cutupd_pfrag_true| ].
  nsplit 4...
  + intros a ; exists a...
  + intros n.
    repeat (destruct n; try apply leb_true; try apply leb_refl).
Unshelve. reflexivity.
Qed.


(* Hgax_cut is here only to allow the use of cut_admissible
   the more general result without Hgax_cut should be provable by induction as for [ll_to_mix2] *)
Lemma ll_to_mix02'''_axcut {P} : (forall a, Forall atomic (projT2 (pgax P) a)) ->
  (forall a b x l1 l2 l3 l4,
     projT2 (pgax P) a = (l1 ++ dual x :: l2) -> projT2 (pgax P) b = (l3 ++ x :: l4) ->
     { c | projT2 (pgax P) c = l3 ++ l2 ++ l1 ++ l4 }) ->
  pperm P = true -> forall l (l0 : list unit),
  ll P (wn one :: map (fun _ => wn (tens (wn one) bot)) l0 ++ l)  ->
  ll (pmixupd_point_pfrag (pmixupd_point_pfrag P 0 true) 2 true) l.
Proof with try assumption.
intros Hgax_at Hgax_cut Hperm l l0 pi.
apply ll_to_mix02''_axcut...
revert l pi ; induction l0 ; intros l pi.
- cons2app.
  eapply ex_r ; [ | rewrite Hperm ; apply Permutation_Type_app_comm ].
  simpl ; apply wk_r.
  eapply ex_r ; [ | rewrite Hperm ; apply Permutation_Type_app_comm ]...
- cons2app.
  eapply ex_r ; [ | rewrite Hperm ; apply Permutation_Type_app_comm ].
  simpl ; apply co_r.
  rewrite 2 app_comm_cons.
  eapply ex_r ; [ | rewrite Hperm ; apply Permutation_Type_app_comm ].
  list_simpl ; apply IHl0.
  list_simpl in pi.
  eapply ex_r ; [ apply pi | rewrite Hperm ; PCperm_Type_solve ].
Qed.

(* llR *)

(** ** Linear logic extended with [R] = [bot]: [llR] *)

(** cut / axioms / mpmix / permutation *)
Definition pfrag_llR R :=
  mk_pfrag true (existT (fun x => x -> list formula) _
                        (fun a => match a with
                                  | true => dual R :: nil
                                  | false => R :: one :: nil
                                  end))
             pmix_none true.
(*         cut  axioms  mix  perm  *)

Definition llR R := ll (pfrag_llR R).

Lemma llR1_R2 : forall R1 R2,
  llR R2 (dual R1 :: R2 :: nil) -> llR R2 (dual R2 :: R1 :: nil) ->
  forall l, llR R1 l-> llR R2 l.
Proof with myeeasy.
intros R1 R2 HR1 HR2 l Hll.
induction Hll ; try (now constructor).
- eapply ex_r...
- eapply ex_wn_r...
- eapply cut_r...
- destruct a.
  + rewrite <- (app_nil_l _).
    apply (@cut_r (pfrag_llR R2) eq_refl (dual R2)).
    * rewrite bidual.
      eapply ex_r.
      apply HR1.
      apply PCperm_Type_swap.
    * assert ({ b | dual R2 :: nil = projT2 (pgax (pfrag_llR R2)) b })
        as [b Hgax] by (now exists true).
      rewrite Hgax.
      apply gax_r.
  + eapply (@cut_r (pfrag_llR R2) eq_refl R2) in HR2.
    * eapply ex_r ; [ apply HR2 | ].
      unfold PCperm_Type.
      simpl.
      apply Permutation_Type_sym.
      apply Permutation_Type_cons_app.
      rewrite app_nil_r.
      apply Permutation_Type_refl.
    * assert ({ b | R2 :: one :: nil = projT2 (pgax (pfrag_llR R2)) b })
        as [b Hgax] by (now exists false).
      rewrite Hgax.
      apply gax_r.
Qed.

Lemma ll_to_llR : forall R l, ll_ll l -> llR R l.
Proof with myeeasy.
intros R l pi.
induction pi ; try (now econstructor).
- eapply ex_r...
- eapply ex_wn_r...
Qed.

Lemma subs_llR : forall R C x l, llR R l -> llR (subs C x R) (map (subs C x) l).
Proof with myeeasy.
intros R C x l pi.
apply (subs_ll C x) in pi.
eapply stronger_pfrag in pi...
nsplit 4...
simpl ; intros a.
destruct a ; simpl.
- exists true.
  rewrite subs_dual...
- exists false...
Qed.

Lemma llR_to_ll : forall R l, llR R l-> ll_ll (l ++ wn R :: wn (tens (dual R) bot) :: nil).
Proof with myeasy.
intros R l pi.
apply cut_ll_admissible.
replace (wn R :: wn (tens (dual R) bot) :: nil) with (map wn (map dual (dual R :: parr one R :: nil)))
  by (simpl ; rewrite bidual ; reflexivity).
apply deduction_list...
eapply ax_gen ; [ | | | | apply pi ]...
simpl ; intros a.
destruct a ; simpl.
- assert ({ b | dual R :: nil = projT2 (pgax (axupd_pfrag (cutupd_pfrag pfrag_ll true)
    (existT (fun x => x -> list formula) (sum _ {k : nat | k < 2})
            (fun a => match a with
                      | inl x => Empty_fun x
                      | inr x => match proj1_sig x with
                                 | 0 => dual R
                                 | 1 => parr one R
                                 | 2 => one
                                 | S (S (S _)) => one
                                 end :: nil
                      end)))) b })
    as [b Hgax] by (now exists (inr (exist _ 0 (le_n_S _ _ (le_S _ _ (le_n 0)))))).
  rewrite Hgax.
  apply gax_r.
- rewrite <- (app_nil_r nil).
  rewrite_all app_comm_cons.
  eapply (cut_r _ (dual (parr one R))).
  + rewrite bidual.
    assert ({ b | parr one R :: nil = projT2 (pgax (axupd_pfrag (cutupd_pfrag pfrag_ll true)
      (existT (fun x => x -> list formula) (sum _ {k : nat | k < 2})
              (fun a => match a with
                        | inl x => Empty_fun x
                        | inr x => match proj1_sig x with
                                   | 0 => dual R
                                   | 1 => parr one R
                                   | 2 => one
                                   | S (S (S _)) => one
                                   end :: nil
                        end)))) b })
      as [b Hgax] by (now exists (inr (exist _ 1 (le_n 2)))).
    erewrite Hgax.
    apply gax_r.
  + apply (ex_r _ (tens (dual R) bot :: (one :: nil) ++ R :: nil)) ; [ | PCperm_Type_solve ].
    apply tens_r.
    * eapply ex_r ; [ | apply PCperm_Type_swap ].
      eapply stronger_pfrag ; [ | apply ax_exp ].
      nsplit 4...
      simpl ; intros a.
      destruct a as [a | a].
      -- destruct a.
      -- destruct a as [n Hlt].
         destruct n ; simpl.
         ++ exists (inr (exist _ 0 Hlt))...
         ++ destruct n ; simpl.
            ** exists (inr (exist _ 1 Hlt))...
            ** exfalso.
               inversion Hlt ; subst.
               inversion H0 ; subst.
               inversion H1.
    * apply bot_r.
      apply one_r.
Unshelve. reflexivity.
Qed.

Lemma llwnR_to_ll : forall R l, llR (wn R) l -> ll_ll (l ++ wn R :: nil).
Proof with myeeasy.
intros R l pi.
apply llR_to_ll in pi.
eapply (ex_r _ _ (wn (tens (dual (wn R)) bot) :: l ++ wn (wn R) :: nil)) in pi ;
  [ | PCperm_Type_solve ].
eapply (cut_ll_r _ nil) in pi.
- eapply (cut_ll_r (wn (wn R))).
  + simpl.
    change (wn R :: nil) with (map wn (R :: nil)).
    apply oc_r ; simpl.
    replace (wn R) with (dual (oc (dual R))) by (simpl ; rewrite bidual ; reflexivity).
    apply ax_exp.
  + eapply ex_r ; [ apply pi | PCperm_Type_solve ].
- simpl ; rewrite bidual.
  change nil with (map wn nil).
  apply oc_r.
  apply parr_r.
  eapply ex_r ; [ apply wk_r ; apply one_r | PCperm_Type_solve ].
Qed.

Lemma ll_wn_wn_to_llR : forall R l, ll_ll (l ++ wn R :: wn (tens (dual R) bot) :: nil) -> llR R l.
Proof with myeasy.
intros R l pi.
apply (ll_to_llR R) in pi.
rewrite <- (app_nil_l l).
eapply (cut_r _ (oc (dual R))).
- rewrite <- (app_nil_l (dual _ :: l)).
  eapply (cut_r _ (oc (parr one R))).
  + simpl ; rewrite bidual ; eapply ex_r ; [apply pi | PCperm_Type_solve ].
  + change nil with (map wn nil).
    apply oc_r.
    apply parr_r.
    apply (ex_r _ (R :: one :: nil)).
    * assert ({ b | R :: one :: nil = projT2 (pgax (pfrag_llR R)) b })
        as [b Hgax] by (now exists false).
      rewrite Hgax.
      apply gax_r.
    * PCperm_Type_solve.
- change nil with (map wn nil).
  apply oc_r.
  assert ({ b | dual R :: map wn nil = projT2 (pgax (pfrag_llR R)) b })
    as [b Hgax] by (now exists true).
  rewrite Hgax.
  apply gax_r.
Unshelve. all : reflexivity.
Qed.

Lemma ll_wn_to_llwnR : forall R l, ll_ll (l ++ wn R :: nil) -> llR (wn R) l.
Proof with myeasy.
intros R l pi.
eapply ll_wn_wn_to_llR.
eapply (ex_r _ (wn (tens (dual (wn R)) bot) :: wn (wn R) :: l)) ;
  [ | PCperm_Type_solve ].
apply wk_r.
apply de_r.
eapply ex_r ; [ apply pi | PCperm_Type_solve ].
Qed.





