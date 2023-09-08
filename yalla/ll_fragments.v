(** * Definitions of various Linear Logic fragments *)

From Coq Require Import PeanoNat Lia.
From OLlibs Require Import infinite funtheory List_more Dependent_Forall_Type
                           Permutation_Type_more GPermutation_Type.
From Yalla Require Export ll_prop.
From Yalla Require Import subs.

Set Default Proof Using "Type".
Set Implicit Arguments.


Section Atoms.

Context {atom : InfDecType}.
Notation formula := (@formula atom).
Notation ll := (@ll atom).

(** ** Property on mix_n *)

Lemma mix_by_tens_n P L : Forall_inf (ll P) L -> ll P (tens_n (length L) bot :: concat L).
Proof.
intro FL. induction FL as [|l0 [|l L] pi FL IHFL]; cbn; repeat constructor; rewrite ? app_nil_r; assumption.
Qed.

(** Provability in [P + mix_n] by adding [wn (tens_n n bot)], and provability in [P + cut + ax : parr_n n bot] are equivalent *)

Lemma ll_to_mix_cut P n l : ll P (wn (tens_n n bot) :: l) ->
  ll (cutupd_pfrag (pmixupd_point_pfrag P n true) pcut_all) l.
Proof.
intro pi. rewrite <- (app_nil_r _). apply cut_r with (wn (tens_n n bot)); [ reflexivity | | ].
- cbn. change nil with (map (@wn atom) nil). apply oc_r.
  rewrite dual_tens_n. cbn. apply parr_n_r.
  replace (repeat one n ++ nil) with (concat (repeat (@one atom :: nil) n))
    by (symmetry; rewrite app_nil_r; apply repeat_to_concat).
  apply mix_r.
  + cbn. rewrite repeat_length, Nat.eqb_refl. reflexivity.
  + remember (cutupd_pfrag (pmixupd_point_pfrag P n true) pcut_all) as P'. clear.
    induction n; constructor; [ | assumption ].
    apply one_r.
- apply stronger_pfrag with P; [ | assumption ].
  repeat split; cbn.
  + intro. apply BoolOrder.le_true.
  + intro a. exists a. reflexivity.
  + intro n0. destruct (n0 =? n); [ apply BoolOrder.le_true | reflexivity ].
  + reflexivity.
Qed.

Lemma mix_to_ll P (fp : pperm P = true) n bn l :
  ll (pmixupd_point_pfrag P n bn) l -> ll P (wn (tens_n n bot) :: l).
Proof.
intro pi.
eapply ex_r; [ | symmetry; rewrite fp; apply Permutation_Type_cons_append ].
refine (ext_wn_param fp _ ((tens_n n bot) :: nil) _ _ pi).
- reflexivity.
- cbn. intro.
  eapply ex_r; [ | rewrite fp; apply Permutation_Type_cons_append ].
  apply wk_r, gax_r.
- intros L Hmix Hmix' FL. remember (length L) as nL eqn:HeqL. destruct (nL =? n) eqn:Heq.
  + cbn in Hmix. rewrite Heq in Hmix.
    apply ex_r with (map wn (tens_n n bot :: nil) ++ concat L);
      [ cbn | rewrite fp; apply Permutation_Type_app_comm ].
    apply co_const_list_r with (S nL).
    change (repeat (wn (tens_n n bot)) (S nL))
      with ((@wn atom (tens_n n bot) :: nil) ++ repeat (wn (tens_n n bot)) nL).
    rewrite HeqL.
    apply (ex_concat_r fp ((wn (tens_n n bot)) :: nil) (wn (tens_n n bot)) L).
    replace n with nL by (apply Nat.eqb_eq, Heq).
    rewrite HeqL, flat_map_concat_map.
    replace ((wn (tens_n (length L) bot)) :: nil )
       with (@wn atom (tens_n (length (map (cons (wn (tens_n (length L) bot))) L)) bot) :: nil)
       by (rewrite map_length; reflexivity).
    apply de_r, tens_n_r.
    apply forall_Forall_inf.
    intros l' Hin.
    destruct (in_inf_map_inv _ _ _ Hin) as [l'' <- Hin'']. clear Hin.
    apply bot_r.
    destruct (in_inf_map_inv _ _ _ Hin'') as [l' <- Hin']. clear Hin''.
    subst. replace (length L) with n by (symmetry; apply Nat.eqb_eq, Heq).
    apply ex_r with (l' ++ map wn (tens_n n bot :: nil)).
    * apply Forall_inf_forall with (map (fun l => l ++ map wn (tens_n n bot :: nil)) L); [ assumption | ].
      change (l' ++ map wn (tens_n n bot :: nil))
        with ((fun l0 => l0 ++ map wn (tens_n n bot :: nil)) l').
      apply in_inf_map. assumption.
    * symmetry. rewrite fp. apply Permutation_Type_cons_append.
  + exfalso. cbn in Hmix. rewrite Heq, Hmix' in Hmix. discriminate Hmix.
Qed.

Lemma parr_n_to_mix P n l : full_cut P ->
  ll (axupd_pfrag P (existT (fun x => x -> _) _
                            (fun a => match a with
                                      | inl x => projT2 (pgax P) x
                                      | inr tt => parr_n n one :: nil
                                      end))) l ->
  ll (pmixupd_point_pfrag P n true) l.
Proof.
intros bcut pi.
remember (axupd_pfrag P (existT (fun x => x -> _) _
                                (fun a => match a with
                                          | inl x => projT2 (pgax P) x
                                          | inr tt => parr_n n one :: nil
                                          end))) as P'.
induction pi using ll_nested_ind; try now constructor.
- apply ex_r with l1; [ assumption | ].
  cbn. rewrite HeqP' in p. cbn in p. assumption.
- apply ex_wn_r with lw; assumption.
- apply mix_r.
  + cbn. rewrite HeqP' in eqpmix. cbn in eqpmix.
    destruct (length L =? n); [ reflexivity | assumption ].
  + apply forall_Forall_inf.
    intros l' Hin.
    apply In_Forall_inf_in with _ _ _ _ PL in Hin as [pi' Hin].
    apply (Dependent_Forall_inf_forall_formula _ _ X Hin).
- rewrite HeqP' in f. apply cut_r with A; assumption.
- revert a. rewrite HeqP'. cbn. intros [a|[]].
  + change (ll (pmixupd_point_pfrag P n true) (projT2 (pgax P) a))
      with (ll (pmixupd_point_pfrag P n true) (projT2 (pgax (pmixupd_point_pfrag P n true)) a)).
    apply gax_r.
  + apply parr_n_r.
    rewrite app_nil_r, repeat_to_concat. apply mix_r.
    * cbn. rewrite repeat_length, Nat.eqb_refl. reflexivity.
    * apply forall_Forall_inf.
      intros l' Hin.
      apply in_inf_in, repeat_spec in Hin as ->.
      apply one_r.
Qed.

Lemma mix_to_parr_n P n l : ll (pmixupd_point_pfrag P n true) l ->
  ll (cutupd_pfrag (axupd_pfrag P (existT (fun x => x -> _) _
                                          (fun a => match a with
                                                    | inl x => projT2 (pgax P) x
                                                    | inr tt => parr_n n one :: nil
                                                    end))) pcut_all) l.
Proof.
intro pi.
remember (cutupd_pfrag (axupd_pfrag P (existT (fun x => x -> _) _
                                              (fun a => match a with
                                                        | inl x => projT2 (pgax P) x
                                                        | inr tt => parr_n n one :: nil
                                                        end))) pcut_all) as P'.
induction pi using ll_nested_ind; try now constructor.
- rewrite HeqP'. rewrite HeqP' in IHpi.
  apply ex_r with l1; assumption.
- apply ex_wn_r with lw; assumption.
- destruct (length L =? n) eqn:Heq.
  + rewrite <- (app_nil_r _).
    apply cut_r with (tens_n (length L) bot).
    * rewrite HeqP'. reflexivity.
    * rewrite dual_tens_n; change (dual bot) with (@one atom).
      replace (parr_n (length L) one :: nil)
         with (projT2 (pgax (cutupd_pfrag (axupd_pfrag P
                 (existT (fun x => x -> _) _
                         (fun a => match a with
                                   | inl x => projT2 (pgax P) x
                                   | inr tt => parr_n n one :: nil
                                   end))) pcut_all)) (inr tt))
        by (replace n with (length L) by (apply Nat.eqb_eq, Heq); reflexivity).
      rewrite HeqP'.
      apply gax_r.
    * apply mix_by_tens_n.
      apply forall_Forall_inf.
      intros l' Hin.
      apply In_Forall_inf_in with _ _ _ _ PL in Hin as [pi' Hin].
      apply (Dependent_Forall_inf_forall_formula _ _ X Hin).
  + cbn in eqpmix. rewrite Heq in eqpmix.
    apply mix_r.
    * rewrite HeqP'. assumption.
    * apply forall_Forall_inf.
      intros l' Hin.
      apply In_Forall_inf_in with _ _ _ _ PL in Hin as [pi' Hin].
      apply (Dependent_Forall_inf_forall_formula _ _ X Hin).
- apply cut_r with A; [ rewrite HeqP'; reflexivity | assumption | assumption ].
- cbn.
  change (projT2 (pgax P) a)
    with (projT2 (pgax (cutupd_pfrag (axupd_pfrag P
                     (existT (fun x => x -> _) _
                             (fun a => match a with
                                       | inl x => projT2 (pgax P) x
                                       | inr tt => parr_n n one :: nil
                                       end))) pcut_all)) (inl a)).
  rewrite HeqP'.
  apply gax_r.
Qed.

Lemma ll_to_parr_n P l n : ll P (wn (tens_n n bot) :: l) ->
  ll (cutupd_pfrag (axupd_pfrag P (existT (fun x => x -> _) _
                                          (fun a => match a with
                                                    | inl x => projT2 (pgax P) x
                                                    | inr tt => parr_n n one :: nil
                                                    end))) pcut_all) l.
Proof.
intros pi.
rewrite <- (app_nil_r l).
apply cut_r with (wn (tens_n n bot)); [ reflexivity | | ].
- cbn. change nil with (map (@wn atom) nil).
  apply oc_r. cbn.
  rewrite dual_tens_n.
  change (dual bot) with (@one atom).
  pattern (@parr_n atom n one :: nil) at 2.
  change (parr_n n one :: nil)
    with (projT2 (pgax (cutupd_pfrag (axupd_pfrag P
                     (existT (fun x => x -> list formula) _
                             (fun a => match a with
                                       | inl x => projT2 (pgax P) x
                                       | inr tt => parr_n n one :: nil
                                       end))) pcut_all)) (inr tt)).
  apply gax_r.
- apply stronger_pfrag with P; [ | assumption ].
  repeat split; [ | | reflexivity .. ].
  + intro. apply BoolOrder.le_true.
  + intro a. exists (inl a). reflexivity.
Qed.

Lemma parr_to_ll P n l : full_cut P -> pperm P = true ->
  ll (axupd_pfrag P (existT (fun x => x -> _) _
                            (fun a => match a with
                                      | inl x => projT2 (pgax P) x
                                      | inr tt => parr_n n one :: nil
                                      end))) l ->
  ll P (wn (tens_n n bot) :: l).
Proof. intros Hcut Hperm pi. apply mix_to_ll with true, parr_n_to_mix; assumption. Qed.

(** provability in [P + mix_n + mix_m] is equivalent to provability in [P + mix_n + mix_m + pmix_(n+m-1)] *)

Lemma mix_n_m_r P n m : P.(pmix) n = true -> P.(pmix) m = true ->
  forall L, length L = n + m - 1 -> Forall_inf (ll P) L -> ll P (concat L).
Proof.
intros Hpmixn Hpmixm L Heq FL. destruct n as [|n]; [ destruct m as [|m] | ].
- destruct L; inversion Heq.
  apply mix_r; assumption.
- cbn in Heq. rewrite Nat.sub_0_r in Heq.
  change (concat L) with (concat (nil :: L)).
  apply mix_r.
  + cbn. rewrite Heq. assumption.
  + apply Forall_inf_cons; [ | assumption ].
    change nil with (concat (@nil (list formula))).
    apply mix_r; [ assumption | constructor ].
- cbn in Heq. rewrite Nat.sub_0_r in Heq.
  destruct (decomp_length_add L n m Heq) as [(l1, l2) [<- <-] ->].
  replace (concat (l1 ++ l2)) with (concat (l1 ++ ((concat l2) :: nil)))
    by (rewrite ! concat_app; cbn; rewrite app_nil_r; reflexivity).
  apply mix_r.
  + rewrite app_length, Nat.add_comm. assumption.
  + assert (FL1 := Forall_inf_app_l _ _ FL).
    assert (FL2 := Forall_inf_app_r _ _ FL).
    apply forall_Forall_inf.
    intros l' [Hin | Hin]%in_inf_app_or.
    * apply Forall_inf_forall with l1; assumption.
    * inversion Hin; [ | inversion X ]. subst.
      apply mix_r; assumption.
Qed.

Lemma mix_conservativity P Q : (forall C, Bool.le (pcut P C) (pcut Q C)) -> Bool.le (pperm P) (pperm Q) ->
  (forall a, { b | projT2 (pgax P) a = projT2 (pgax Q) b }) ->
  (forall n, pmix P n = true ->
    forall L, length L = n -> Forall_inf (ll Q) L -> ll Q (concat L)) ->
forall l, ll P l -> ll Q l.
Proof.
intros Hcut Hperm Hgax Hpmix l pi.
induction pi using ll_nested_ind; try now constructor.
- apply ex_r with l1; [ assumption | ].
  apply PCPermutation_Type_monot with (pperm P); assumption.
- apply ex_wn_r with lw; assumption.
- apply (Hpmix (length L)); [ assumption | reflexivity | ].
  apply forall_Forall_inf.
  intros l' Hin.
  apply (In_Forall_inf_in _ PL) in Hin as [pi' Hin].
  apply (Dependent_Forall_inf_forall_formula _ _ X Hin).
- specialize (Hcut A). rewrite f in Hcut.
  apply cut_r with A; assumption.
- destruct (Hgax a) as [b ->]; apply gax_r.
Qed.

Lemma mix_conservativity_updl P fmix : let Q := (pmixupd_pfrag P fmix) in
  (forall n, pmix Q n = true ->
    forall L, length L = n -> Forall_inf (ll P) L -> ll P (concat L)) ->
  forall l, ll Q l -> ll P l.
Proof.
intros Q Hpmix l pi; apply mix_conservativity with Q;
  [ | | intro a; exists a | assumption .. ]; reflexivity.
Qed.

Lemma mix_conservativity_updr P fmix : let Q := (pmixupd_pfrag P fmix) in
  (forall n, pmix P n = true ->
    forall L, length L = n -> Forall_inf (ll Q) L -> ll Q (concat L)) ->
  forall l, ll P l -> ll Q l.
Proof.
intros Q Hpmix l pi; apply mix_conservativity with P;
  [ | | intro a; exists a | assumption .. ]; reflexivity.
Qed.

Lemma mix_n_m_admissible P n m : P.(pmix) n = true -> P.(pmix) m = true ->
  forall l, ll (pmixupd_point_pfrag P (n + m - 1) true) l -> ll P l.
Proof.
intros Hpmixn Hpmixm l pi.
eapply mix_conservativity_updl, pi.
cbn. intros k Hpmixk L <- HF.
destruct (length L =? n + m - 1) eqn:Heq.
- apply (mix_n_m_r n m); [ | | apply Nat.eqb_eq | ]; assumption.
- apply mix_r; assumption.
Qed.

(** provability in [P + mix_2] is equivalent to provability in [P + mix k] for all k >= 2 *)

Lemma mix_2_to_mix_k_r P : P.(pmix) 2 = true ->
  forall L, 2 <= length L -> Forall_inf (ll P) L -> ll P (concat L).
Proof.
intro Hpmix. induction L as [|A [|B [|C L]] IHL]; intros Hl FL; [ cbn in Hl; lia .. | | ].
- apply mix_r; assumption.
- inversion_clear FL as [|? ? pi1 FL'].
  replace (concat (A :: B :: C :: L))
     with (concat (A :: (concat (B :: C :: L) :: nil)))
    by (cbn; rewrite <- ? app_assoc, app_nil_r; reflexivity).
  apply mix_r, Forall_inf_cons, Forall_inf_cons, Forall_inf_nil; [ assumption .. | ].
  apply IHL; [ cbn; lia | assumption ].
Qed.

Lemma mix_2_to_mix_k_admissible P : P.(pmix) 2 = true ->
  forall l, ll P l ->
  ll (pmixupd_pfrag P (fun k => if k =? 0 then P.(pmix) 0
                          else (if k =? 2 then true else false))) l.
Proof.
intros Hpmix l pi.
eapply mix_conservativity_updr, pi.
cbn. intros k Hpmixk [|l1 [|l2 L]] Hl HF; cbn in Hl; subst.
- apply mix_r; assumption.
- list_simpl. inversion_clear HF. assumption.
- apply mix_2_to_mix_k_r; [ reflexivity | cbn; lia | assumption ].
Qed.

(** provability in [P + mix_1] is equivalent to provability in [P] *)

Lemma mix1_rm P l : ll P l -> ll (pmixupd_point_pfrag P 1 false) l.
Proof.
intros pi.
eapply mix_conservativity_updr; [ | apply pi].
cbn. intros k Hpmixk [|l1 [|l2 L]] Hl HF; cbn in Hl; subst.
- apply mix_r; assumption.
- list_simpl. inversion_clear HF. assumption.
- apply mix_r; assumption.
Qed.

(** provability in [P + mix_0 + mix_n] is equivalent to provability in [P + mix_k] for all k <= n *)

Lemma mix_0_n_r P n : P.(pmix) 0 = true -> P.(pmix) n = true ->
  forall L, length L <= n -> Forall_inf (ll P) L -> ll P (concat L).
Proof.
intros Hpmix0 Hpmixn L.
remember (n - length L) as k eqn:Heqk.
induction k in L, Heqk |- *; intros Hlen FL.
- assert (length L = n) as <- by lia.
  apply mix_r; assumption.
- change (concat L) with (concat (nil :: L)).
  apply IHk; cbn; [ lia .. | ].
  apply Forall_inf_cons; [ | assumption ].
  change nil with (concat (@nil (list formula))).
  apply mix_r, Forall_inf_nil. assumption.
Qed.

Lemma mix_0_n_admissible P n : P.(pmix) 0 = true -> P.(pmix) n = true ->
  forall l, ll P l ->
  ll (pmixupd_pfrag P (fun k => if k =? 0  then P.(pmix) 0
                          else (if n <=? k then P.(pmix) k else false))) l.
Proof.
intros Hpmix0 Hpmixn l pi.
eapply mix_conservativity_updr; [ | apply pi].
cbn. intros k Hpmixk [|l1 L] <- HF; [ apply mix_r; assumption | ].
destruct (n <=? length (l1 :: L)) eqn:Heq.
- apply mix_r; [ | assumption ].
  cbn. cbn in Heq. rewrite Heq. assumption.
- apply mix_0_n_r with n; cbn; [ assumption | | | assumption ].
  + destruct n as [|n]; [ assumption | ].
    cbn. rewrite Nat.leb_refl. assumption.
  + transitivity (S (S (length L))); try lia.
    case (Nat.compare_spec n (S (length L))); intros Ho; [ | | lia ]; exfalso.
    -- subst. rewrite Nat.leb_refl in Heq. discriminate Heq.
    -- eapply or_introl, Nat.le_lteq, Nat.leb_le in Ho.
       cbn in Heq. rewrite Ho in Heq. discriminate Heq.
Qed.

(** provability in [P + mix_0 + mix_2] is equivalent to provability in [P + mix_k] for all k *)

Lemma allmix_r P : P.(pmix) 0 = true -> P.(pmix) 2 = true ->
  forall L, Forall_inf (ll P) L -> ll P (concat L).
Proof.
intros Hpmix0 Hpimx2 [|l1 [|l2 L]] FL.
- apply mix_r; assumption.
- cbn. rewrite app_nil_r. inversion_clear FL. assumption.
- apply mix_2_to_mix_k_r; [ | cbn; lia | ]; assumption.
Qed.

Lemma allmix_admissible P : P.(pmix) 0 = true -> P.(pmix) 2 = true ->
  forall l, ll P l -> ll (pmixupd_pfrag P pmix02) l.
Proof.
intros Hpmix0 Hpmix2 l pi.
eapply mix_conservativity_updr, pi.
intros k Hpmixk L Hl HF.
now apply allmix_r.
Qed.


(** ** Standard linear logic: [ll_ll] (no mix, no axiom, commutative) *)

(** cut / axioms / pmix / permutation *)
Definition pfrag_ll :=  @mk_pfrag atom  pcut_none NoAxioms pmix_none true.
(*                                atoms cut       axioms   mix       perm  *)

Definition ll_ll := ll pfrag_ll.

Lemma cut_ll_r A l1 l2 : ll_ll (dual A :: l1) -> ll_ll (A :: l2) -> ll_ll (l2 ++ l1).
Proof. intros pi1 pi2. refine (cut_r_axfree _ pi1 pi2). intros []. Qed.

Lemma cut_ll_admissible l : ll (cutupd_pfrag pfrag_ll pcut_all) l -> ll_ll l.
Proof.
intros pi. induction pi using ll_nested_ind; (try now constructor); try (econstructor; eassumption).
- eapply cut_ll_r; eassumption.
- refine (gax_r _).
Qed.



(** ** Linear logic with mix0: [ll_mix0] (no mix2, no axiom, commutative) *)

(** cut / axioms / pmix / permutation *)
Definition pfrag_mix0 := @mk_pfrag atom  pcut_none NoAxioms pmix0 true.
(*                                 atoms cut       axioms   mix   perm  *)

Definition ll_mix0 := ll pfrag_mix0.

Lemma cut_mix0_r A l1 l2 : ll_mix0 (dual A :: l1) -> ll_mix0 (A :: l2) -> ll_mix0 (l2 ++ l1).
Proof. apply cut_r_axfree. intros []. Qed.

Lemma cut_mix0_admissible l : ll (cutupd_pfrag pfrag_mix0 pcut_all) l -> ll_mix0 l.
Proof.
intro pi. induction pi using ll_nested_ind; (try now constructor); try (econstructor; eassumption).
- apply mix_r; [ assumption | ].
  apply forall_Forall_inf.
  intros l' Hin. destruct (In_Forall_inf_in _ PL Hin) as [pi' HFin].
  apply (Dependent_Forall_inf_forall_formula _ _ X HFin).
- eapply cut_mix0_r; eassumption.
- destruct a.
Qed.

(** Provability in [ll_mix0] is equivalent to adding [wn one] in [ll] *)
Lemma mix0_to_ll P (fp : pperm P = true) b0 l : ll (pmixupd_point_pfrag P 0 b0) l -> ll P (wn one :: l).
Proof. intro. change one with (@tens_n atom 0 bot). apply mix_to_ll with b0; assumption. Qed.

Lemma ll_to_mix0_cut P l : ll P (wn one :: l) -> ll (cutupd_pfrag (pmixupd_point_pfrag P 0 true) pcut_all) l.
Proof. intro pi. change one with (@tens_n atom 0 bot) in pi. apply ll_to_mix_cut; assumption. Qed.

Lemma mix0_wn_one l : ll_mix0 (wn one :: l) -> ll_mix0 l.
Proof.
intro pi.
(* an alternative proof is by introducing a cut with (oc bot) *)
apply stronger_pfrag with (cutrm_pfrag (cutupd_pfrag (pmixupd_point_pfrag pfrag_mix0 0 true) pcut_all)).
- repeat split.
  + intro a. exists a. reflexivity.
  + intros [|n]; reflexivity.
- apply cut_admissible_axfree.
  + intros [].
  + apply ll_to_mix_cut. assumption.
Qed.


(** Provability in [ll_mix0] is equivalent to provability of [ll]
extended with the provability of [bot :: bot :: nil] *)

Lemma mix0_to_ll_bot P : full_cut P -> pperm P = true -> forall bc b0 bp l,
  ll (mk_pfrag bc P.(pgax) (fun k => if (k =? 0) then b0 else P.(pmix) k) bp) l ->
  ll (axupd_pfrag P (existT (fun x => x -> _) _
                            (fun a => match a with
                                      | inl x => projT2 (pgax P) x
                                      | inr tt => bot :: bot :: nil
                                      end))) l.
Proof.
remember (axupd_pfrag P (existT (fun x => x -> _) _
                                (fun a => match a with
                                          | inl x => projT2 (pgax P) x
                                          | inr tt => bot :: bot :: nil
                                          end))) as P'.
intros fc fp bc b0 bp l pi.
eapply stronger_pfrag in pi.
- eapply mix0_to_ll in pi; [ | eassumption ].
  assert (full_cut P') as fc' by (rewrite HeqP'; cbn; intro; apply fc).
  eapply stronger_pfrag in pi.
  + assert (ll P' (bot :: map wn nil)) as pi'.
    { change (bot :: map wn nil) with ((@bot atom :: nil) ++ nil).
      apply (cut_r bot (fc' _)).
      - apply one_r.
      - assert ({ b | bot :: bot :: nil = projT2 (pgax P') b }) as [b ->]
          by (rewrite HeqP'; now exists (inr tt)).
        apply gax_r. }
    apply oc_r in pi'.
    rewrite <- (app_nil_l l).
    apply (cut_r (oc bot) (fc' _)); [ cbn; apply pi | apply pi' ].
  + repeat split; rewrite HeqP'; try reflexivity.
    cbn. intros a. exists (inl a). reflexivity.
- repeat split; intros; cbn.
  + rewrite fc. apply BoolOrder.le_true.
  + exists a. reflexivity.
  + reflexivity.
  + rewrite fp. apply BoolOrder.le_true.
Qed.

Lemma ll_bot_to_mix0 P l :
  ll (axupd_pfrag P (existT (fun x => x -> list _) _
                              (fun a => match a with
                                        | inl x => projT2 (pgax P) x
                                        | inr tt => bot :: bot :: nil
                                        end))) l ->
  ll (pmixupd_point_pfrag P 0 true) l.
Proof.
intros pi.
remember (pmixupd_point_pfrag P 0 true) as P' eqn:HeqP'.
apply (stronger_pfrag _ (axupd_pfrag P' (existT (fun x => x -> _) _
                                                (fun a => match a with
                                                          | inl x => projT2 (pgax P) x
                                                          | inr tt => bot :: bot :: nil
                                                          end)))) in pi.
- eapply ax_gen; try eassumption; try reflexivity.
  clear - HeqP'. cbn. intros [p | []].
  + assert ({ b | projT2 (pgax P) p = projT2 (pgax P') b }) as [b ->]
        by (rewrite HeqP'; exists p; reflexivity).
    apply gax_r.
  + apply bot_r, bot_r.
    change nil with (concat (@nil (list formula))).
    apply mix_r.
    * rewrite HeqP'. reflexivity.
    * apply Forall_inf_nil.
- rewrite HeqP'. repeat split; cbn; intros; [ | exists a | | ]; try reflexivity.
  destruct n.
  + apply BoolOrder.le_true.
  + reflexivity.
Qed.

(** [mix2] is not valid in [ll_mix0] *)

Lemma mix0_not_mix2 : notT (ll_mix0 (one :: one :: nil)).
Proof.
intro pi.
remember (one :: one :: nil) as l eqn:Heql.
induction pi in Heql |- *; subst; try now inversion Heql.
- apply IHpi.
  apply Permutation_Type_sym, Permutation_Type_length_2_inv in p as []; assumption.
- destruct l1, lw'; inversion Heql; subst.
  + symmetry in p. now apply Permutation_Type_nil in p as ->.
  + symmetry in p. now apply Permutation_Type_nil in p as ->.
  + destruct l1 as [|A [|B l1]]; inversion H1.
- destruct L; discriminate.
Qed.


(** ** Linear logic with mix2: [ll_mix2] (no mix0, no axiom, commutative) *)

(** cut / axioms / pmix / permutation *)
Definition pfrag_mix2 := @mk_pfrag atom  pcut_none NoAxioms pmix2 true.
(*                                 atoms cut       axioms   mix   perm  *)

Definition ll_mix2 := ll pfrag_mix2.

Lemma cut_mix2_r A l1 l2 : ll_mix2 (dual A :: l1) -> ll_mix2 (A :: l2) -> ll_mix2 (l2 ++ l1).
Proof. intros pi1 pi2. eapply cut_r_axfree; try eassumption. intros []. Qed.

Lemma cut_mix2_admissible l : ll (cutupd_pfrag pfrag_mix2 pcut_all) l -> ll_mix2 l.
Proof.
intro pi. induction pi using ll_nested_ind; try (now constructor); try (econstructor; eassumption).
- apply mix_r; [ assumption | ].
  apply forall_Forall_inf.
  intros l' [pi' HFin]%(In_Forall_inf_in _ PL).
  apply (Dependent_Forall_inf_forall_formula _ _ X HFin).
- eapply cut_mix2_r; eassumption.
- destruct a.
Qed.

(** Provability in [ll_mix2] is equivalent to adding [wn (tens bot bot)] in [ll] *)

Lemma mix2_to_ll P (fp : pperm P = true) b2 l : ll (pmixupd_point_pfrag P 2 b2) l ->
  ll P (wn (tens bot bot) :: l).
Proof. intro. change (tens bot bot) with (@tens_n atom 2 bot). apply mix_to_ll with b2; assumption. Qed.

Lemma ll_to_mix2_cut P l : ll P (wn (tens bot bot) :: l) ->
  ll (cutupd_pfrag (pmixupd_point_pfrag P 2 true) pcut_all) l.
Proof. intro. change (tens bot bot) with (tens_n 2 bot). apply ll_to_mix_cut. assumption. Qed.

(** Provability in [ll_mix2] is equivalent to
provability of [ll] extended with the provability of [one :: one :: nil]
and to provability of [ll] extended with the provability of [parr (dual B) (dual A) :: parr A B :: nil]
for all [A] and [B] *)

Lemma mix2_to_ll_one_one P : full_cut P -> pperm P = true -> forall bc b2 bp l,
  ll (mk_pfrag bc P.(pgax) (fun k => if (k =? 2) then b2 else P.(pmix) k) bp) l ->
  ll (axupd_pfrag P (existT (fun x => x -> _) _
                            (fun a => match a with
                                      | inl x => projT2 (pgax P) x
                                      | inr tt => one :: one :: nil
                                      end))) l.
Proof.
remember (axupd_pfrag P (existT (fun x => x -> _) _
                                (fun a => match a with
                                          | inl x => projT2 (pgax P) x
                                          | inr tt => one :: one :: nil
                                          end))) as P' eqn:HeqP'.
intros fc fp bc b2 bp l pi.
eapply stronger_pfrag in pi.
- eapply mix2_to_ll in pi; [ | eassumption ].
  assert (full_cut P') as fc' by (rewrite HeqP'; cbn; intro; apply fc).
  eapply stronger_pfrag in pi.
  + rewrite <- (app_nil_l l). apply (cut_r (oc (parr one one)) (fc' _) pi).
    change nil with (map (@wn atom) nil). apply oc_r. cbn.
    apply parr_r.
    assert ({ b | one :: one :: nil = projT2 (pgax P') b }) as [b ->]
      by (now rewrite HeqP'; exists (inr tt)).
    apply gax_r.
  + repeat split; rewrite HeqP'; try reflexivity.
    cbn. intros a. exists (inl a). reflexivity.
- repeat split; intros; cbn.
  + rewrite fc. apply BoolOrder.le_true.
  + exists a. reflexivity.
  + reflexivity.
  + rewrite fp. apply BoolOrder.le_true.
Qed.

Lemma ll_one_one_to_ll_tens_parr_one_one_cut P : full_cut P ->
  ll P (parr one one :: parr bot bot :: nil) -> ll P (one :: one :: nil).
Proof.
intros Hcut pi.
assert (ll P (dual (parr (parr one one) (parr bot bot)) :: one :: one :: nil)) as pi'.
{ cbn. rewrite <- (app_nil_r _), <- app_comm_cons.
  apply tens_r.
  - rewrite <- (app_nil_r _), <- app_comm_cons.
    apply tens_r; apply one_r.
  - rewrite <- (app_nil_l (one :: nil)), (app_comm_cons _ _ one).
    change one with (dual (@bot atom)).
    apply tens_r; apply ax_exp. }
rewrite <- (app_nil_l _).
eapply cut_r; [ apply Hcut | apply pi' | apply parr_r, pi ].
Qed.

Lemma ll_tens_parr_one_one_to_ll_tens_parr P l :
  ll (axupd_pfrag P (existT (fun x => x -> _) _
                              (fun a => match a with
                                        | inl x => projT2 (pgax P) x
                                        | inr tt => parr one one :: parr bot bot :: nil
                                        end))) l ->
  ll (axupd_pfrag P (existT (fun x => x -> _) _
                            (fun a => match a with
                                      | inl x => projT2 (pgax P) x
                                      | inr (A,B) => parr (dual B) (dual A) :: parr A B :: nil
                                      end))) l.
Proof.
intros pi.
remember (axupd_pfrag P (existT (fun x => x -> _) _
                         (fun a => match a with
                                   | inl x => projT2 (pgax P) x
                                   | inr tt => parr one one :: parr bot bot :: nil
                                   end))) as P'.
apply (@ax_gen _ P'); (try now (rewrite HeqP'; cbn)); [ | assumption ].
clear - HeqP'. cbn. rewrite HeqP'. intros []; cbn.
- assert ({ b | projT2 (pgax P) p =
                projT2 (pgax (axupd_pfrag P (existT (fun x => x -> _) _
                       (fun a => match a with
                                 | inl x => projT2 (pgax P) x
                                 | inr (A,B) => parr (dual B) (dual A) :: parr A B :: nil
                                 end)))) b })
    as [b ->] by now exists (inl p).
  apply gax_r.
- destruct u.
  assert ({ b | parr one one :: parr bot bot :: nil =
                projT2 (pgax (axupd_pfrag P (existT (fun x => x -> _) _
                       (fun a => match a with
                                 | inl x => projT2 (pgax P) x
                                 | inr (A,B) => parr (dual B) (dual A) :: parr A B :: nil
                                 end)))) b })
    as [b ->] by now exists (inr (bot,bot)).
  apply gax_r.
Qed.

Lemma ll_tens_parr_to_mix2 P l :
  ll (axupd_pfrag P (existT (fun x => x -> list _) _
                              (fun a => match a with
                                        | inl x => projT2 (pgax P) x
                                        | inr (A,B) => parr (dual B) (dual A) :: parr A B :: nil
                                        end))) l ->
  ll (pmixupd_point_pfrag P 2 true) l.
Proof.
intros pi.
remember (pmixupd_point_pfrag P 2 true) as P'.
apply (stronger_pfrag _
  (axupd_pfrag P' (existT (fun x => x -> list _) _
                          (fun a => match a with
                                    | inl x => projT2 (pgax P) x
                                    | inr (A,B) => parr (dual B) (dual A) :: parr A B :: nil
                                    end)))) in pi.
- eapply ax_gen; try eassumption; try reflexivity.
  clear - HeqP'. cbn. intros [].
  + assert ({ b | projT2 (pgax P) p = projT2 (pgax P') b })
      as [b ->] by (now rewrite HeqP'; exists p).
    apply gax_r.
  + destruct p as [A B].
    apply parr_r.
    apply (ex_r (parr A B :: (dual B :: nil) ++ (dual A) :: nil));
      [ |etransitivity; [ apply PCPermutation_Type_cons_append | reflexivity ] ].
    apply parr_r.
    eapply ex_r; [ | symmetry; apply PCPermutation_Type_cons_append ].
    list_simpl; rewrite <- (app_nil_l (dual A :: _)), 2 app_comm_cons.
    change ((B :: dual B :: nil) ++ dual A :: A :: nil)
      with (concat ((B :: dual B :: nil) :: (dual A :: A :: nil) :: nil)).
    apply mix_r.
    * rewrite HeqP'. reflexivity.
    * apply Forall_inf_cons.
      -- apply ax_exp.
      -- apply Forall_inf_cons; [ | apply Forall_inf_nil].
         apply ex_r with (A :: dual A :: nil); [ apply ax_exp | apply PCPermutation_Type_swap ].
- rewrite HeqP'. repeat split; cbn; intros; try reflexivity.
  + exists a. reflexivity.
  + repeat (destruct n; try apply BoolOrder.le_refl; try apply BoolOrder.le_true).
Qed.

Lemma ll_one_one_to_mix2 P l :
  ll (axupd_pfrag P (existT (fun x => x -> list _) _
                            (fun a => match a with
                                      | inl x => projT2 (pgax P) x
                                      | inr tt => one :: one :: nil
                                      end))) l ->
  ll (pmixupd_point_pfrag P 2 true) l.
Proof.
intros pi.
remember (pmixupd_point_pfrag P 2 true) as P'.
apply (stronger_pfrag _
  (axupd_pfrag P' (existT (fun x => x -> _) _
                          (fun a => match a with
                                    | inl x => projT2 (pgax P) x
                                    | inr tt => one :: one :: nil
                                    end)))) in pi.
- eapply ax_gen; try eassumption; try reflexivity.
  clear - HeqP'; cbn; intros [p|[]].
  + assert ({ b | projT2 (pgax P) p = projT2 (pgax P') b })
      as [b ->] by (now rewrite HeqP'; exists p).
    apply gax_r.
  + change (one :: one :: nil) with ((@one atom :: nil) ++ one :: nil).
    rewrite HeqP'.
    change ((one :: nil) ++ one :: nil) with (concat ((@one atom :: nil) :: (one :: nil) :: nil)).
    apply mix_r; [ reflexivity | ].
    repeat (apply Forall_inf_cons; try apply one_r).
    apply Forall_inf_nil.
- rewrite HeqP'. repeat split; cbn; intros; try reflexivity.
  + exists a. reflexivity.
  + repeat (destruct n; try apply BoolOrder.le_refl; try apply BoolOrder.le_true).
Qed.

(** [mix0] is not valid in [ll_mix2] *)

Lemma mix2_not_mix0 : notT (ll_mix2 nil).
Proof.
intros pi. remember nil as l eqn:Heql.
induction pi in Heql using ll_nested_ind; subst; try now inversion Heql.
- apply IHpi.
  cbn in p. apply Permutation_Type_sym, Permutation_Type_nil in p as ->. reflexivity.
- apply app_eq_nil in Heql as [-> [->%map_eq_nil ->]%app_eq_nil].
  symmetry in p. now apply Permutation_Type_nil in p as ->.
- destruct L as [|? [|? [|? L]]]; try discriminate eqpmix.
  cbn in Heql. rewrite app_nil_r in Heql. apply app_eq_nil in Heql as [-> ->].
  destruct (In_Forall_inf_in nil PL) as [pi Hin].
  + apply in_inf_eq.
  + apply (Dependent_Forall_inf_forall_formula _ _ X Hin eq_refl).
Qed.


(** ** Linear logic with both mix0 and mix2: [ll_mix02] (no axiom, commutative) *)

(** cut / axioms / mix0 / mix2 / permutation *)
Definition pfrag_mix02 := @mk_pfrag atom  pcut_none NoAxioms pmix02 true.
(*                                  atoms cut       axioms   mix    perm  *)

Definition ll_mix02 := ll pfrag_mix02.

Lemma cut_mix02_r A l1 l2 : ll_mix02 (dual A :: l1) -> ll_mix02 (A :: l2) -> ll_mix02 (l2 ++ l1).
Proof. apply cut_r_axfree. intros []. Qed.

Lemma cut_mix02_admissible l : ll (cutupd_pfrag pfrag_mix02 pcut_all) l -> ll_mix02 l.
Proof.
intro pi. induction pi using ll_nested_ind; try (now constructor); try (econstructor; eassumption).
- apply mix_r; [ assumption | ].
  apply forall_Forall_inf.
  intros l' [pi Hin]%(In_Forall_inf_in _ PL).
  apply (Dependent_Forall_inf_forall_formula _ _ X Hin).
- eapply cut_mix02_r; eassumption.
- destruct a.
Qed.

(** Provability in [ll_mix02] is equivalent to adding [wn (tens (wn one) (wn one))] in [ll] *)

Lemma mix02_to_ll P (fp : pperm P = true) b1 b2 bp l :
  ll (mk_pfrag P.(pcut) P.(pgax) (fun k => if (k =? 0) then b1
                                     else (if (k =? 2) then b2 else P.(pmix) k)) bp) l ->
  ll P (wn (tens (wn one) (wn one)) :: l).
Proof.
intros pi.
eapply ex_r; [ | symmetry; apply PCPermutation_Type_cons_append ].
refine (ext_wn_param fp _ (tens (wn one) (wn one) :: nil) _ _ pi).
- reflexivity.
- cbn. intros a.
  eapply ex_r; [ | apply PCPermutation_Type_cons_append ].
  apply wk_r, gax_r.
- intros L Hpmix eqpmix FL. destruct L.
  + apply de_r.
    change nil with (@nil formula ++ nil).
    apply tens_r; apply de_r, one_r.
  + destruct L.
    * cbn; rewrite app_nil_r.
      inversion FL; assumption.
    * destruct L.
      -- cbn.
         apply ex_r with (wn (tens (wn one) (wn one)) :: (l0 ++ l1));
           [ | list_simpl; rewrite app_assoc; apply PCPermutation_Type_cons_append ].
         inversion FL; subst; inversion X0; subst.
         clear FL X0 X2.
         apply co_r, co_r.
         apply ex_r with (wn (tens (wn one) (wn one)) :: ((l0 ++ wn (tens (wn one) (wn one)) :: nil)
                                                              ++ (l1 ++ wn (tens (wn one) (wn one)) :: nil)));
           [ apply de_r, tens_r; apply wk_r; assumption | rewrite fp; cbn ].
         apply Permutation_Type_cons; [ reflexivity | ].
         symmetry; etransitivity; [ apply Permutation_Type_cons_append | ].
         rewrite ? app_assoc; apply Permutation_Type_app_tail.
         list_simpl; apply Permutation_Type_middle.
      -- apply ex_r with (wn (tens (wn one) (wn one)) :: concat (l0 :: l1 :: l2 :: L));
           [ | rewrite fp; cbn; apply Permutation_Type_cons_append ].
         apply co_const_list_r with (length (l0 :: l1 :: l2 :: L)).
         apply (ex_concat_r fp nil).
         rewrite app_nil_l, flat_map_concat_map.
         apply mix_r.
         ++ rewrite map_length; assumption.
         ++ apply forall_Forall_inf.
            intros l' Hin.
            apply in_inf_map_inv in Hin as [l'' <- Hin].
            apply ex_r with ((fun l0 => l0 ++ (map wn (tens (wn one) (wn one) :: nil))) l'');
              [ | symmetry; apply PCPermutation_Type_cons_append ].
            apply (in_inf_map (fun l => l ++ map wn (tens (wn one) (wn one) :: nil))) in Hin.
            apply Forall_inf_forall
             with (map (fun l => l ++ map wn (tens (wn one) (wn one) :: nil)) (l0 :: l1 :: l2 :: L)); assumption.
Qed.

Lemma ll_to_mix02_cut P l : ll P (wn (tens (wn one) (wn one)) :: l) ->
  ll (mk_pfrag pcut_all P.(pgax) (fun k => if (k =? 0) then true
                                 else (if (k =? 2) then true else P.(pmix) k)) P.(pperm)) l.
Proof.
intros pi.
eapply stronger_pfrag in pi.
- rewrite <- (app_nil_r l).
  eapply cut_r; [ reflexivity | | apply pi].
  change nil with (map (@wn atom) nil).
  apply oc_r, parr_r.
  change (oc bot :: oc bot :: map wn nil)
    with (concat ((@oc atom bot :: map wn nil) :: (oc bot :: map wn nil) :: nil)).
  apply mix_r; [ reflexivity | ].
  apply forall_Forall_inf.
  intros l' Hin.
  destruct Hin.
  + subst.
    apply oc_r, bot_r.
    change (map wn nil) with (concat (@nil (list formula))).
    apply mix_r; [ reflexivity | ].
    apply Forall_inf_nil.
  + destruct i; [ | destruct i ]; subst.
    apply oc_r, bot_r.
    change (map wn nil) with (concat (@nil (list formula))).
    apply mix_r; [ reflexivity | ].
    apply Forall_inf_nil.
- repeat split.
  + intro A. destruct (pcut P A); reflexivity.
  + intro a. exists a. reflexivity.
  + intro n. repeat (destruct n; try apply BoolOrder.le_refl; try apply BoolOrder.le_true).
  + reflexivity.
Qed.

(** Provability in [ll_mix02] is equivalent to adding other stuff in [ll] *)

Lemma mix02_to_ll' P (fp : pperm P = true) b0 b2 l :
  ll (pmixupd_point_pfrag (pmixupd_point_pfrag P 0 b0) 2 b2) l -> ll P (wn one :: wn (tens bot bot) :: l).
Proof. intro pi. eapply mix0_to_ll, mix2_to_ll; eassumption. Qed.

Lemma mix02_to_ll'' P (fp : pperm P = true) b0 b2 bp l :
  ll (mk_pfrag P.(pcut) P.(pgax) (fun k => if (k =? 0) then b0
                                     else (if (k =? 2) then b2 else P.(pmix) k)) bp) l ->
  ll P (wn one :: wn (tens (wn one) bot) :: l).
Proof.
intros pi.
apply (ex_r (l ++ map wn (one :: tens (wn one) bot :: nil))).
2:{ rewrite fp. cbn.
    symmetry. etransitivity; [ apply Permutation_Type_swap | ].
    etransitivity; [ apply Permutation_Type_cons_append | ].
    cons2app; rewrite ? app_assoc; apply Permutation_Type_app_tail; list_simpl.
    apply Permutation_Type_cons_append. }
refine (ext_wn_param fp _ (one :: tens (wn one) bot :: nil) _ _ pi).
- reflexivity.
- cbn. intros a.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ]; list_simpl.
  apply wk_r, wk_r, gax_r.
- destruct L.
  { intros Hpmix0 Hpmix0' pi'. cbn.
    apply de_r.
    eapply ex_r; [ | apply PCPermutation_Type_swap ].
    apply wk_r, one_r. }
  destruct L.
  { intros Hpmix1 Hpmix1' FL. cbn in Hpmix1, Hpmix1'. rewrite Hpmix1 in Hpmix1'; inversion Hpmix1'. }
  destruct L.
  2:{ intros Hpmix Hpmix' FL. cbn in Hpmix, Hpmix'. rewrite Hpmix in Hpmix'. inversion Hpmix'. }
  intros _ _ FL. cbn.
  inversion FL; inversion X0; subst; clear FL X0 X2;
    rename X into pi1; rename X1 into pi2; rename l1 into l2; rename l0 into l1.
  apply (ex_r (wn (tens (wn one) bot) :: (wn one :: l2) ++ l1)); [ | rewrite fp; cbn ].
  2:{ etransitivity; [ apply Permutation_Type_cons_append | ].
      cons2app; rewrite ? app_assoc; apply Permutation_Type_app_tail; list_simpl.
      etransitivity; [ | rewrite app_assoc; apply Permutation_Type_cons_append ].
      apply Permutation_Type_cons, Permutation_Type_app_comm; reflexivity. }
  apply co_r, co_r, de_r.
  apply (ex_r (tens (wn one) bot :: (wn (tens (wn one) bot) :: wn one :: l2)
                                   ++ (wn (tens (wn one) bot) :: l1))).
  2:{ rewrite fp; cbn; apply Permutation_Type_cons, Permutation_Type_cons; try reflexivity.
      symmetry; rewrite ? (app_comm_cons _ _ (wn one)); apply Permutation_Type_middle. }
  apply tens_r.
  + eapply ex_r; [ apply pi1 | rewrite fp; cbn ].
    symmetry. etransitivity; [ apply Permutation_Type_swap | ].
    etransitivity; [ apply Permutation_Type_cons_append | ].
    cons2app. rewrite ? app_assoc. apply Permutation_Type_app_tail, Permutation_Type_cons_append.
  + apply bot_r; eapply ex_r; [ apply pi2 | rewrite fp; cbn ].
    symmetry. etransitivity; [ apply Permutation_Type_cons_append | ].
    cons2app. rewrite ? app_assoc. apply Permutation_Type_app_tail, Permutation_Type_cons_append.
Qed.

(** Provability in [ll_mix02] is equivalent to provability of [ll]
extended with the provability of both [bot :: bot :: nil] and [one :: one :: nil] *)

Lemma mix02_to_ll_one_eq_bot P (fc : full_cut P) (fp : pperm P = true) bc b0 b2 bp l :
  ll (mk_pfrag bc P.(pgax) (fun k => if (k =? 0) then b0 else (if (k =? 2) then b2 else P.(pmix) k)) bp) l ->
  ll (axupd_pfrag P (existT (fun x => x -> _) _
                            (fun a => match a with
                                      | inl x => projT2 (pgax P) x
                                      | inr true => one :: one :: nil
                                      | inr false => bot :: bot :: nil
                                      end))) l.
Proof.
remember (axupd_pfrag P (existT (fun x => x -> _) _
                                (fun a => match a with
                                          | inl x => projT2 (pgax P) x
                                          | inr true => one :: one :: nil
                                          | inr false => bot :: bot :: nil
                                          end))) as P' eqn:HeqP'.
intros pi. eapply stronger_pfrag in pi.
- eapply mix02_to_ll in pi; [ | eassumption ].
  assert (full_cut P') as fc' by (rewrite HeqP'; cbn; apply fc).
  apply (stronger_pfrag _ P') in pi.
  + rewrite <- (app_nil_l l). apply (cut_r (oc (parr (oc bot) (oc bot))) (fc' _) pi).
    change nil with (map (@wn atom) nil). apply oc_r.
    apply parr_r.
    change (oc bot :: oc bot :: map wn nil)
      with ((@oc atom bot :: nil) ++ oc bot :: map wn nil).
    apply (cut_r one (fc' _)).
    * apply bot_r, oc_r.
      change (bot :: map wn nil) with ((@bot atom :: nil) ++ nil).
      apply (cut_r bot (fc' _)).
      -- apply one_r.
      -- assert ({ b | bot :: bot :: nil = projT2 (pgax P') b }) as [b ->]
           by (now rewrite HeqP'; exists (inr false)).
         apply gax_r.
    * change (one :: oc bot :: nil)
        with ((@one atom :: nil) ++ oc bot :: map wn nil).
      apply (cut_r one (fc' _)).
      -- apply bot_r, oc_r.
         change (bot :: map wn nil) with ((@bot atom :: nil) ++ nil).
         apply (cut_r bot (fc' _)).
         ++ apply one_r.
         ++ assert ({ b | bot :: bot :: nil = projT2 (pgax P') b }) as [b ->]
              by (now rewrite HeqP'; exists (inr false)).
            apply gax_r.
      -- assert ({ b | one :: one :: nil = projT2 (pgax P') b }) as [b ->]
           by (now rewrite HeqP'; exists (inr true)).
          apply gax_r.
  + repeat split; rewrite HeqP'; try reflexivity.
    cbn. intros a. exists (inl a). reflexivity.
- repeat split; intros; cbn; try reflexivity.
  + rewrite fc. apply BoolOrder.le_true.
  + exists a. reflexivity.
Qed.

Lemma ll_one_eq_bot_to_mix02 P l :
  ll (axupd_pfrag P (existT (fun x => x -> _) _
                            (fun a => match a with
                                      | inl x => projT2 (pgax P) x
                                      | inr true => one :: one :: nil
                                      | inr false => bot :: bot :: nil
                                      end))) l ->
  ll (mk_pfrag P.(pcut) P.(pgax) (fun k => if (k =? 0) then true
                                     else (if (k =? 2) then true else P.(pmix) k)) P.(pperm)) l.
Proof.
intros pi.
remember (mk_pfrag P.(pcut) P.(pgax) (fun k => if (k =? 0) then true
                                         else (if (k =? 2) then true else P.(pmix) k)) P.(pperm)) as P' eqn:HeqP'.
apply (stronger_pfrag _
  (axupd_pfrag P' (existT (fun x => x -> _) _
                          (fun a => match a with
                                    | inl x => projT2 (pgax P) x
                                    | inr true => one :: one :: nil
                                    | inr false => bot :: bot :: nil
                                    end)))) in pi.
- eapply ax_gen; try eassumption; try reflexivity.
  clear - HeqP'. cbn. intros [p|[|]].
  + assert ({ b | projT2 (pgax P) p = projT2 (pgax P') b }) as [b ->]
      by (now rewrite HeqP'; exists p).
    apply gax_r.
  + change (one :: one :: nil) with (concat ((@one atom :: nil) :: (one :: nil) :: nil)).
    rewrite HeqP'.
    apply mix_r; [ reflexivity | ].
    repeat (constructor; try apply one_r).
  + apply bot_r, bot_r.
    change nil with (concat (@nil (list formula))).
    rewrite HeqP'.
    apply mix_r; [ reflexivity | apply Forall_inf_nil ].
- rewrite HeqP'. repeat split; cbn; try reflexivity.
  + intros a. exists a. reflexivity.
  + intros n. repeat (destruct n; try apply BoolOrder.le_refl; try apply BoolOrder.le_true).
Qed.

(* Hcut is here only to allow the use of cut_admissible
   the more general result without Hcut should be provable by induction *)
Lemma ll_to_mix02'_axcut P (Hgax_at : atomic_ax P) (Hcut : cut_closed P) (Hperm : pperm P = true) l :
  ll P (wn one :: wn (tens bot bot) :: l) ->
  ll (mk_pfrag pcut_all P.(pgax) (fun k => if (k =? 0) then true
                                     else (if (k =? 2) then true else P.(pmix) k)) P.(pperm)) l.
Proof.
intros pi.
apply (stronger_pfrag (cutrm_pfrag (cutupd_pfrag (pmixupd_point_pfrag
                                                 (pmixupd_point_pfrag P 0 true) 2 true) pcut_all))).
{ repeat split.
  - intros a. exists a. reflexivity.
  - intros n. repeat (destruct n; try apply BoolOrder.le_refl; try apply BoolOrder.le_true).
  - reflexivity. }
eapply cut_admissible; try eassumption.
eapply stronger_pfrag in pi.
- rewrite <- (app_nil_r l).
  refine (cut_r (wn (tens bot bot)) _ _ _); [ reflexivity | | ]; cbn.
  + change nil with (map (@wn atom) nil).
    apply oc_r, parr_r.
    change (one :: one :: map wn nil) with (concat ((@one atom :: nil) :: (one :: nil) :: nil)).
    apply mix_r; [ reflexivity | ].
    apply Forall_inf_cons; [ apply one_r | ].
    apply Forall_inf_cons; [ apply one_r | ].
    apply Forall_inf_nil.
  + rewrite <- app_nil_r.
    eapply cut_r; [ reflexivity | | apply pi ].
    change nil with (map (@wn atom) nil).
    apply oc_r, bot_r.
    change (map wn nil) with (concat (@nil (list formula))).
    apply mix_r; [ reflexivity | ].
    apply Forall_inf_nil.
- eapply le_pfrag_po; [ apply cutupd_pfrag_true| ].
  repeat split.
  + intros a. exists a. reflexivity.
  + intros n. repeat (destruct n; try apply BoolOrder.le_refl; try apply BoolOrder.le_true).
  + reflexivity.
Qed.

(* Hcut is here only to allow the use of cut_admissible
   the more general result without Hcut should be provable by induction *)
Lemma ll_to_mix02''_axcut P (Hgax_at : atomic_ax P) (Hcut : cut_closed P) (Hperm : pperm P = true) l :
  ll P (wn one :: wn (tens (wn one) bot) :: l) ->
  ll (pmixupd_point_pfrag (pmixupd_point_pfrag P 0 true) 2 true) l.
Proof.
intros pi.
apply (stronger_pfrag (cutrm_pfrag (cutupd_pfrag (pmixupd_point_pfrag
                                                 (pmixupd_point_pfrag P 0 true) 2 true) pcut_all)));
  [ repeat split; try (intros a; exists a); reflexivity | ].
eapply cut_admissible; try eassumption.
eapply stronger_pfrag in pi.
- rewrite <- (app_nil_r l).
  refine (cut_r (wn (tens (wn one) bot)) _ _ _); [ reflexivity | | ]; cbn.
  + change nil with (map (@wn atom) nil).
    apply oc_r, parr_r.
    change (one :: oc bot :: map wn nil)
      with (concat ((@one atom :: nil) :: (oc bot :: map wn nil) :: nil)).
    apply mix_r; [ reflexivity | ].
    apply Forall_inf_cons; [ apply one_r | ].
    apply Forall_inf_cons.
    { apply oc_r, bot_r.
      change (map wn nil) with (concat (@nil (list formula))).
      apply mix_r; [ reflexivity | ].
      apply Forall_inf_nil. }
    apply Forall_inf_nil.
  + rewrite <- app_nil_r.
    eapply cut_r; [ reflexivity | | apply pi ].
    change nil with (map (@wn atom) nil).
    apply oc_r, bot_r.
    change (map wn nil) with (concat (@nil (list formula))).
    apply mix_r; [ reflexivity | ].
    apply Forall_inf_nil.
- eapply le_pfrag_po; [ apply cutupd_pfrag_true| ].
  repeat split.
  + intros a. exists a. reflexivity.
  + intros n. repeat (destruct n; try apply BoolOrder.le_refl; try apply BoolOrder.le_true).
  + reflexivity.
Qed.


(* Hcut is here only to allow the use of cut_admissible
   the more general result without Hcut should be provable by induction *)
Lemma ll_to_mix02'''_axcut P (Hgax_at : atomic_ax P) (Hcut : cut_closed P) (Hperm : pperm P = true) l n :
  ll P (wn one :: repeat (wn (tens (wn one) bot)) n ++ l)  ->
  ll (pmixupd_point_pfrag (pmixupd_point_pfrag P 0 true) 2 true) l.
Proof.
intros pi.
apply ll_to_mix02''_axcut; try assumption.
induction n as [|n IHn ] in l, pi |- *; cons2app.
- eapply ex_r; [ | rewrite Hperm; apply Permutation_Type_app_comm ].
  cbn. apply wk_r.
  eapply ex_r; [ | rewrite Hperm; apply Permutation_Type_app_comm ]; assumption.
- eapply ex_r; [ | rewrite Hperm; apply Permutation_Type_app_comm ].
  cbn. apply co_r. rewrite 2 app_comm_cons.
  eapply ex_r; [ | rewrite Hperm; apply Permutation_Type_app_comm ].
  list_simpl. apply IHn.
  list_simpl in pi. eapply ex_r; [ apply pi | rewrite Hperm; cbn ].
  apply Permutation_Type_cons, Permutation_Type_middle. reflexivity.
Qed.

(* llR *)

(** ** Linear logic extended with [R] = [bot]: [llR] *)

(** cut / axioms / mix / permutation *)
Definition pfrag_llR R :=
  mk_pfrag pcut_all (existT (fun x => x -> list formula) _
                            (fun a => match a with
                                      | true => dual R :: nil
                                      | false => R :: one :: nil
                                      end))
             pmix_none true.
(*         cut  axioms  mix  perm  *)

Definition llR R := ll (pfrag_llR R).

Lemma llR1_R2 R1 R2 : llR R2 (dual R1 :: R2 :: nil) -> llR R2 (dual R2 :: R1 :: nil) ->
  forall l, llR R1 l-> llR R2 l.
Proof.
intros HR1 HR2 l Hll. induction Hll; try (now constructor); try (econstructor; eassumption).
destruct a; cbn.
- rewrite <- (app_nil_l _). apply (@cut_r _ (pfrag_llR R2) (dual R2) eq_refl).
  + rewrite bidual. eapply ex_r, PCPermutation_Type_swap.
    apply HR1.
  + assert ({ b | dual R2 :: nil = projT2 (pgax (pfrag_llR R2)) b }) as [b ->] by now exists true.
    apply gax_r.
- eapply (@cut_r _ (pfrag_llR R2) R2 eq_refl) in HR2.
  + eapply ex_r; [ apply HR2 | ].
    symmetry. apply Permutation_Type_cons_app. rewrite app_nil_r. reflexivity.
  + assert ({ b | R2 :: one :: nil = projT2 (pgax (pfrag_llR R2)) b }) as [b ->] by now exists false.
    apply gax_r.
Qed.

Lemma ll_to_llR R l : ll_ll l -> llR R l.
Proof.
intro pi. induction pi; try (now constructor); try (econstructor; eassumption).
- eapply cut_r; [ reflexivity | eassumption .. ].
- destruct a.
Qed.

Lemma subs_llR R C x l : llR R l -> llR (subs C x R) (map (subs C x) l).
Proof.
intros pi%(subs_ll C x).
eapply stronger_pfrag in pi; [ eassumption | ].
repeat split. intros [|]; cbn.
- rewrite subs_dual. exists true. reflexivity.
- exists false. reflexivity.
- reflexivity.
Qed.

Lemma llR_to_ll R l : llR R l-> ll_ll (l ++ wn R :: wn (tens (dual R) bot) :: nil).
Proof.
intro pi. apply cut_ll_admissible.
replace (wn R :: wn (tens (dual R) bot) :: nil)
   with (map wn (map dual (dual R :: parr one R :: nil)))
  by (cbn; rewrite bidual; reflexivity).
apply deduction_list; [ reflexivity | ].
eapply ax_gen, pi; [ reflexivity .. | ].
intros [|]; cbn.
- assert ({ b | dual R :: nil = projT2 (pgax (axupd_pfrag (cutupd_pfrag pfrag_ll pcut_all)
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
    as [b ->] by (now exists (inr (exist _ 0 (le_n_S _ _ (le_S _ _ (le_n 0)))))).
  apply gax_r.
- rewrite <- (app_nil_r nil), ! app_comm_cons.
  refine (cut_r (dual (parr one R)) _ _ _); [ reflexivity | | ].
  + rewrite bidual.
    assert ({ b | parr one R :: nil = projT2 (pgax (axupd_pfrag (cutupd_pfrag pfrag_ll pcut_all)
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
      as [b ->] by (now exists (inr (exist _ 1 (le_n 2)))).
    apply gax_r.
  + apply (ex_r (tens (dual R) bot :: (one :: nil) ++ R :: nil));
      [ | apply Permutation_Type_cons, Permutation_Type_swap; reflexivity ].
    apply tens_r.
    * eapply ex_r; [ | apply PCPermutation_Type_swap ].
      eapply stronger_pfrag; [ | apply ax_exp ].
      repeat split; try reflexivity.
      intros [[] | [[|[|n]] Hlt]]; cbn.
      -- exists (inr (exist _ 0 Hlt)). reflexivity.
      -- exists (inr (exist _ 1 Hlt)). reflexivity.
      -- exfalso. lia.
    * apply bot_r, one_r.
Qed.

Lemma llwnR_to_ll R l : llR (wn R) l -> ll_ll (l ++ wn R :: nil).
Proof.
intros pi%llR_to_ll.
eapply (ex_r _ (wn (tens (dual (wn R)) bot) :: l ++ wn (wn R) :: nil)) in pi;
  [ | symmetry; cons2app; rewrite ? app_assoc; apply Permutation_Type_cons_append ].
eapply (@cut_ll_r _ nil) in pi.
- eapply cut_ll_r with (wn (wn R)).
  + cbn. change (wn R :: nil) with (map wn (R :: nil)). apply oc_r. cbn.
    replace (wn R) with (dual (oc (dual R))) by (cbn; rewrite bidual; reflexivity).
    apply ax_exp.
  + eapply ex_r; [ apply pi | symmetry; list_simpl; apply Permutation_Type_cons_append ].
- cbn. rewrite bidual. change nil with (map (@wn atom) nil).
  apply oc_r, parr_r.
  eapply ex_r; [ apply wk_r, one_r | apply Permutation_Type_swap ].
Qed.

Lemma ll_wn_wn_to_llR R l : ll_ll (l ++ wn R :: wn (tens (dual R) bot) :: nil) -> llR R l.
Proof.
intros pi%(ll_to_llR R).
rewrite <- (app_nil_l l).
refine (cut_r (oc (dual R)) _ _ _); [ reflexivity | | ].
- rewrite <- (app_nil_l (dual _ :: l)).
  refine (cut_r (oc (parr one R)) _ _ _); [ reflexivity | | ].
  + cbn. rewrite bidual. eapply ex_r; [apply pi | ].
    symmetry. etransitivity; [ apply Permutation_Type_cons_append | ].
    cons2app. rewrite ? app_assoc. apply Permutation_Type_app_tail.
    list_simpl. apply Permutation_Type_cons_append.
  + change nil with (map (@wn atom) nil).
    apply oc_r, parr_r.
    apply (ex_r (R :: one :: nil)).
    * assert ({ b | R :: one :: nil = projT2 (pgax (pfrag_llR R)) b }) as [b ->] by now exists false.
      apply gax_r.
    * apply Permutation_Type_swap.
- change nil with (map (@wn atom) nil). apply oc_r.
  assert ({ b | dual R :: map wn nil = projT2 (pgax (pfrag_llR R)) b }) as [b ->] by now exists true.
  apply gax_r.
Qed.

Lemma ll_wn_to_llwnR R l : ll_ll (l ++ wn R :: nil) -> llR (wn R) l.
Proof.
intro pi. eapply ll_wn_wn_to_llR.
eapply (ex_r (wn (tens (dual (wn R)) bot) :: wn (wn R) :: l)).
2:{ cons2app. etransitivity; [ rewrite ! app_assoc; apply Permutation_Type_cons_append | ].
    rewrite ! app_assoc. apply Permutation_Type_app_tail, Permutation_Type_cons_append. }
apply wk_r, de_r.
eapply ex_r; [ apply pi | symmetry; apply Permutation_Type_cons_append ].
Qed.

End Atoms.
