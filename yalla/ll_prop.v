(* ll_prop library for yalla *)

(** * Properties relying on cut admissibility *)

Require Import Bool_more.
Require Import List_more.
Require Import Permutation_Type_more.
Require Import CyclicPerm_Type.
Require Import genperm_Type.

Require Export ll_cut.


(** Some additional reversibility statements *)
Lemma with_rev1_noax {P} : (projT1 (pgax P) -> False) ->
  forall l, ll P l -> forall A B l1 l2, l = l1 ++ awith A B :: l2 ->
  ll P (l1 ++ A :: l2).
Proof with myeeasy.
intros Hgax l pi A B l1 l2 Heq ; subst.
assert (Hax := @ax_exp P (dual A)).
rewrite bidual in Hax.
eapply (ex_r _ _ (awith A B :: l2 ++ l1)) in pi ; [ | PCperm_Type_solve ].
eapply (cut_r_axfree _ _ (A :: nil)) in pi...
- eapply ex_r ; [ apply pi | PCperm_Type_solve ].
- apply plus_r1...
Unshelve. assumption.
Qed.

Lemma with_rev2_noax {P} : (projT1 (pgax P) -> False) ->
  forall l, ll P l -> forall A B l1 l2, l = l1 ++ awith B A :: l2 ->
  ll P (l1 ++ A :: l2).
Proof with myeeasy.
intros Hgax l pi A B l1 l2 Heq ; subst.
assert (Hax := @ax_exp P (dual A)).
rewrite bidual in Hax.
eapply (ex_r _ _ (awith B A :: l2 ++ l1)) in pi ; [ | PCperm_Type_solve ].
eapply (cut_r_axfree _ _ (A :: nil)) in pi...
- eapply ex_r ; [ apply pi | PCperm_Type_solve ].
- apply plus_r2...
Unshelve. assumption.
Qed.

Lemma oc_rev_noax {P} : (projT1 (pgax P) -> False) ->
  forall l, ll P l -> forall A l1 l2, l = l1 ++ oc A :: l2 ->
  ll P (l1 ++ A :: l2).
Proof with myeeasy.
intros Hgax l pi A l1 l2 Heq ; subst.
assert (Hax := @ax_exp P (dual A)).
rewrite bidual in Hax.
eapply (ex_r _ _ (oc A :: l2 ++ l1)) in pi ; [ | PCperm_Type_solve ].
eapply (cut_r_axfree _ _ (A :: nil)) in pi...
- eapply ex_r ; [ apply pi | PCperm_Type_solve ].
- apply de_r...
Unshelve. assumption.
Qed.


(** ** Subformula Property *)

(** version of ll with predicate parameter for constraining sequents *)
Inductive ll_ps P PS : list formula -> Type :=
| ax_ps_r : forall X, is_true (PS (covar X :: var X :: nil)) -> ll_ps P PS (covar X :: var X :: nil)
| ex_ps_r : forall l1 l2, is_true (PS l2) -> ll_ps P PS l1 -> PCperm_Type (pperm P) l1 l2 -> ll_ps P PS l2
| ex_wn_ps_r : forall l1 lw lw' l2, is_true (PS (l1 ++ map wn lw' ++ l2)) ->
                 ll_ps P PS (l1 ++ map wn lw ++ l2) ->
                 Permutation_Type lw lw' -> ll_ps P PS (l1 ++ map wn lw' ++ l2)
| mix0_ps_r {f : pmix0 P = true} : is_true (PS nil) -> ll_ps P PS nil
| mix2_ps_r {f : pmix2 P = true} : forall l1 l2, is_true (PS (l2 ++ l1)) -> 
                                     ll_ps P PS l1 -> ll_ps P PS l2 -> ll_ps P PS (l2 ++ l1)
| one_ps_r : is_true (PS (one :: nil)) -> ll_ps P PS (one :: nil)
| bot_ps_r : forall l, is_true (PS (bot :: l)) -> ll_ps P PS l -> ll_ps P PS (bot :: l)
| tens_ps_r : forall A B l1 l2, is_true (PS (tens A B :: l2 ++ l1)) ->
                               ll_ps P PS (A :: l1) -> ll_ps P PS (B :: l2) ->
                               ll_ps P PS (tens A B :: l2 ++ l1)
| parr_ps_r : forall A B l, is_true (PS (parr A B :: l)) -> 
                               ll_ps P PS (A :: B :: l) -> ll_ps P PS (parr A B :: l)
| top_ps_r : forall l, is_true (PS (top :: l)) -> ll_ps P PS (top :: l)
| plus_ps_r1 : forall A B l, is_true (PS (aplus A B :: l)) ->
                               ll_ps P PS (A :: l)-> ll_ps P PS (aplus A B :: l)
| plus_ps_r2 : forall A B l, is_true (PS (aplus B A :: l)) ->
                               ll_ps P PS (A :: l) -> ll_ps P PS (aplus B A :: l)
| with_ps_r : forall A B l, is_true (PS (awith A B :: l)) ->
                               ll_ps P PS (A :: l) -> ll_ps P PS (B :: l) ->
                               ll_ps P PS (awith A B :: l)
| oc_ps_r : forall A l, is_true (PS (oc A :: map wn l)) ->
                                ll_ps P PS (A :: map wn l) -> ll_ps P PS (oc A :: map wn l)
| de_ps_r : forall A l, is_true (PS (wn A :: l)) -> ll_ps P PS (A :: l) -> ll_ps P PS (wn A :: l)
| wk_ps_r : forall A l, is_true (PS (wn A :: l)) -> ll_ps P PS l -> ll_ps P PS (wn A :: l)
| co_ps_r : forall A l, is_true (PS (wn A :: l)) ->
                            ll_ps P PS (wn A :: wn A :: l) -> ll_ps P PS (wn A :: l)
| cut_ps_r {f : pcut P = true} : forall A l1 l2, is_true (PS (l2 ++ l1)) ->
                               ll_ps P PS (dual A :: l1) -> ll_ps P PS (A :: l2) ->
                               ll_ps P PS (l2 ++ l1)
| gax_ps_r : forall a, is_true (PS (projT2 (pgax P) a)) -> ll_ps P PS (projT2 (pgax P) a).

Lemma stronger_ps_pfrag P Q : le_pfrag P Q -> forall PS l,
  ll_ps P PS l -> ll_ps Q PS l.
Proof with myeeasy.
intros Hle PS l H.
induction H ; try (econstructor ; myeeasy ; fail).
- apply (ex_ps_r _ _ l1)...
  destruct Hle as (_ & _ & _ & _ & Hp).
  unfold PCperm_Type in p.
  unfold PCperm_Type.
  destruct (pperm P) ; destruct (pperm Q) ;
    simpl in Hp ; try inversion Hp...
  apply cperm_perm_Type...
- unfold le_pfrag in Hle.
  rewrite f in Hle.
  destruct Hle as (_ & _ & Hmix0 & _).
  simpl in Hmix0...
  apply (@mix0_ps_r _ _ Hmix0)...
- unfold le_pfrag in Hle.
  rewrite f in Hle.
  destruct Hle as (_ & _ & _ & Hmix2 & _).
  simpl in Hmix2...
  apply (@mix2_ps_r _ _ Hmix2)...
- destruct Hle as [Hle _].
  rewrite f in Hle.
  simpl in Hle.
  eapply (@cut_ps_r _ _ Hle)...
- destruct Hle as (_ & Hgax & _).
  destruct (Hgax a) as [b Heq].
  rewrite Heq in i ; rewrite Heq.
  apply gax_ps_r...
Qed.

Lemma ll_ps_stronger {P} : forall PS QS l,
  ll_ps P PS l -> (forall x, is_true (PS x) -> is_true (QS x)) -> ll_ps P QS l.
Proof with try eassumption.
intros PS QS l pi Hs.
induction pi ; try (econstructor ; try apply Hs ; eassumption ; fail).
Qed.

Lemma ll_ps_is_ps {P} : forall l PS, ll_ps P PS l -> is_true (PS l).
Proof.
intros l PS Hll.
inversion Hll ; assumption.
Qed.

Lemma ll_ps_is_ll {P} : forall l PS, ll_ps P PS l -> ll P l.
Proof with try eassumption.
intros l PS pi.
induction pi ; try (econstructor ; eassumption ; fail).
Qed.

Lemma ll_is_ll_ps {P} : forall l, ll P l -> ll_ps P (fun _ => true) l.
Proof with myeeasy.
intros l pi.
induction pi ; try (econstructor ; myeeasy ; fail).
Qed.

(** A fragment is a subset of formulas closed under subformula. *)
Definition fragment FS :=
  forall A, is_true (FS A) -> forall B, subform B A -> is_true (FS B).

(** Linear logic is conservative over its fragments (in the absence of cut). *)
Lemma conservativity {P} : pcut P = false -> forall FS, fragment FS ->
  forall l, ll_ps P (fun _ => true) l -> is_true (Forallb FS l) -> ll_ps P (Forallb FS) l.
Proof with try eassumption ; try reflexivity.
intros P_cutfree FS HFS l pi.
induction pi ; intros HFrag.
- apply ax_ps_r...
- apply (ex_ps_r _ _ l1)...
  apply IHpi.
  apply PCperm_Type_sym in p.
  apply Forallb_Forall in HFrag.
  apply Forallb_Forall.
  eapply PCperm_Type_Forall...
- eapply ex_wn_ps_r...
  apply IHpi.
  apply Forallb_Forall in HFrag.
  apply Forallb_Forall.
  apply (Permutation_Type_map wn) in p.
  eapply Permutation_Type_Forall...
  PCperm_Type_solve.
- apply (@mix0_ps_r _ _ f)...
- apply Forallb_Forall in HFrag.
  assert (HFrag2 := Forall_app_inv _ _ _ HFrag).
  destruct HFrag2 as [HFragl HFragr].
  apply Forallb_Forall in HFragl.
  apply Forallb_Forall in HFragr.
  apply (@mix2_ps_r _ _ f)...
  + apply Forallb_Forall...
  + apply IHpi1...
  + apply IHpi2...
- apply one_ps_r...
- apply bot_ps_r...
  inversion HFrag.
  apply andb_true_iff in H0.
  destruct H0.
  apply IHpi...
- assert (HFrag2 := HFrag).
  simpl in HFrag.
  apply andb_true_iff in HFrag.
  destruct HFrag as [HFragt HFrag].
  apply Forallb_Forall in HFrag.
  apply Forall_app_inv in HFrag.
  destruct HFrag as [HFragl HFragr].
  apply Forallb_Forall in HFragl.
  apply Forallb_Forall in HFragr.
  apply tens_ps_r...
  + apply IHpi1...
    simpl ; apply andb_true_iff ; split...
    eapply HFS...
    apply sub_tens_l...
  + apply IHpi2...
    simpl ; apply andb_true_iff ; split...
    eapply HFS...
    apply sub_tens_r...
- inversion HFrag ; subst.
  apply andb_true_iff in H0 ; destruct H0.
  apply parr_ps_r...
  apply IHpi.
  simpl ; apply andb_true_iff ; split ;
    [ | simpl ; apply andb_true_iff ; split ]...
  + eapply HFS...
    apply sub_parr_l...
  + eapply HFS...
    apply sub_parr_r...
- apply top_ps_r...
- inversion HFrag ; subst.
  apply andb_true_iff in H0 ; destruct H0.
  apply plus_ps_r1...
  apply IHpi.
  simpl ; apply andb_true_iff ; split...
  eapply HFS...
  apply sub_plus_l...
- inversion HFrag ; subst.
  apply andb_true_iff in H0 ; destruct H0.
  apply plus_ps_r2...
  apply IHpi.
  simpl ; apply andb_true_iff ; split...
  eapply HFS...
  apply sub_plus_r...
- inversion HFrag ; subst.
  apply andb_true_iff in H0 ; destruct H0.
  apply with_ps_r...
  + apply IHpi1...
    simpl ; apply andb_true_iff ; split...
    eapply HFS...
    apply sub_with_l...
  + apply IHpi2...
    simpl ; apply andb_true_iff ; split...
    eapply HFS...
    apply sub_with_r...
- inversion HFrag ; subst.
  apply andb_true_iff in H0 ; destruct H0.
  apply oc_ps_r...
  apply IHpi.
  simpl ; apply andb_true_iff ; split...
  eapply HFS...
  apply sub_oc...
- inversion HFrag ; subst.
  apply andb_true_iff in H0 ; destruct H0.
  apply de_ps_r...
  apply IHpi.
  simpl ; apply andb_true_iff ; split...
  eapply HFS...
  apply sub_wn...
- inversion HFrag ; subst.
  apply andb_true_iff in H0 ; destruct H0.
  apply wk_ps_r...
  apply IHpi...
- inversion HFrag ; subst.
  apply andb_true_iff in H0 ; destruct H0.
  apply co_ps_r...
  apply IHpi.
  simpl ; apply andb_true_iff ; split...
- rewrite P_cutfree in f.
  inversion f.
- apply gax_ps_r...
Qed.

(** Subformula property:
any provable sequent is provable by a proof containing only subformulas of this sequent. *)
Proposition subformula {P} : pcut P = false -> forall l,
  ll P l -> ll_ps P (fun x => subformb_list x l) l.
Proof with try eassumption ; try reflexivity.
intros P_cutfree l pi.
apply ll_is_ll_ps in pi.
apply conservativity...
- intros A Hf B Hs.
  revert Hf ; clear - Hs ; induction l ; intro Hf ; inversion Hf ; subst.
  simpl ; apply orb_true_iff.
  apply orb_true_iff in H0.
  destruct H0.
  + left.
    eapply subb_trans...
    apply subb_sub...
  + right.
    apply IHl...
- apply (subb_id_list l nil).
Qed.

(* Cut is admissible in any fragment with no axioms. *)
Lemma cut_admissible_fragment {P} : (projT1 (pgax P) -> False) ->
 forall FS, fragment FS -> forall l,
   ll_ps P (Forallb FS) l -> ll_ps (cutrm_pfrag P) (Forallb FS) l.
Proof with myeeasy.
intros P_axfree FS HFS l pi.
apply conservativity...
- apply ll_is_ll_ps.
  apply cut_admissible_axfree...
  eapply ll_ps_is_ll...
- destruct pi...
Qed.

(** Linear logic (with no axioms) is conservative over its fragments. *)
Lemma conservativity_cut_axfree {P} : (projT1 (pgax P) -> False) ->
  forall FS, fragment FS -> forall l,
    ll P l -> is_true (Forallb FS l) -> ll_ps P (Forallb FS) l.
Proof with try eassumption ; try reflexivity.
intros P_axfree FS Hf l pi HFS.
apply cut_admissible_axfree in pi...
apply ll_is_ll_ps in pi.
eapply conservativity in pi...
clear - pi ; induction pi ;
  try (econstructor ; eassumption ; fail).
- eapply @cut_ps_r...
  destruct P.
  inversion f.
- revert a i.
  assert (pgax (cutrm_pfrag P) = pgax P) as Hcut by reflexivity.
  rewrite Hcut.
  apply gax_ps_r.
Qed.


(** ** Deduction Theorem *)

(** Deduction lemma for linear logic. *)
Lemma deduction_list {P} : pperm P = true -> pcut P = true -> forall lax l, 
  ll (axupd_pfrag P (existT (fun x => x -> list formula) (sum _ { k | k < length lax })
                                (fun a => match a with
                                          | inl x => projT2 (pgax P) x
                                          | inr x => nth (proj1_sig x) lax one :: nil
                                          end))) l
  -> ll P (l ++ map wn (map dual lax)).
Proof with myeeasy.
intros P_perm P_cut lax.
induction lax ; intros l pi.
- list_simpl.
  eapply stronger_pfrag...
  nsplit 5...
  simpl ; intros a.
  destruct a.
  + exists p...
  + destruct s...
- remember (axupd_pfrag P (existT (fun x => x -> list formula) (sum _ { k | k < length lax })
                                (fun a => match a with
                                          | inl x => projT2 (pgax P) x
                                          | inr x => nth (proj1_sig x) lax one :: nil
                                          end)))
    as Q.
  simpl.
  cons2app.
  rewrite app_assoc.
  apply IHlax.
  eapply (@ext_wn _ _ _ (dual a :: nil)) in pi.
  eapply ax_gen ; [ | | | | | apply pi ] ; try (now rewrite HeqQ).
  simpl in pi ; simpl ; intros a0.
  destruct a0.
  + eapply ex_r ; [ | apply PCperm_Type_last ].
    apply wk_r.
    assert ({ b | projT2 (pgax P) p = projT2 (pgax Q) b}) as [b Hgax]
      by (subst ; simpl ; exists (inl p) ; reflexivity).
    rewrite Hgax.
    apply gax_r.
  + destruct s as [k Hlen].
    destruct k ; simpl.
    * eapply ex_r ; [ | apply PCperm_Type_swap ].
      apply de_r.
      eapply ex_r ; [ | apply PCperm_Type_swap ].
      apply ax_exp.
    * eapply ex_r ; [ | apply PCperm_Type_swap ].
      apply wk_r.
      assert ({ b | nth k lax one :: nil = projT2 (pgax Q) b}) as [b Hgax].
      { subst ; simpl ; clear - Hlen.
        apply Lt.lt_S_n in Hlen.
        exists (inr (exist _ k Hlen))... }
      rewrite Hgax.
      apply gax_r.
Unshelve. assumption.
Qed.

Lemma deduction_list_inv {P} : pperm P = true -> pcut P = true -> forall lax l, 
  ll P (l ++ map wn (map dual lax)) ->
  ll (axupd_pfrag P (existT (fun x => x -> list formula) (sum _ { k | k < length lax })
                                (fun a => match a with
                                          | inl x => projT2 (pgax P) x
                                          | inr x => nth (proj1_sig x) lax one :: nil
                                          end))) l.
Proof with myeeasy.
intros P_perm P_cut lax.
induction lax ; intros l pi.
- list_simpl in pi.
  eapply stronger_pfrag...
  nsplit 5...
  simpl ; intros a.
  exists (inl a)...
- list_simpl in pi.
  cons2app in pi.
  rewrite app_assoc in pi.
  apply IHlax in pi.
  rewrite <- (app_nil_r l).
  eapply (cut_r _ (wn (dual a)))...
  + simpl ; rewrite bidual.
    change nil with (map wn nil).
    apply oc_r ; simpl.
    assert ({ b | a :: nil = projT2 (pgax (axupd_pfrag P
     (existT (fun x => x -> list formula) (sum _ {k | k < S (length lax)})
        (fun a0 => match a0 with
                   | inl x => projT2 (pgax P) x
                   | inr x => match proj1_sig x with
                              | 0 => a
                              | S m => nth m lax one
                              end :: nil
                   end)))) b}) as [b Hgax]
      by (clear ; simpl ; exists (inr (exist _ 0 (le_n_S _ _ (le_0_n _)))) ; reflexivity).
    rewrite Hgax.
    apply gax_r.
  + eapply ex_r ; [ | apply PCperm_Type_sym ; apply PCperm_Type_last ].
    eapply stronger_pfrag...
    nsplit 5...
    simpl ; intros a'.
    destruct a'.
    * exists (inl p)...
    * destruct s as [k Hlen] ; simpl.
      apply Lt.lt_n_S in Hlen.
      exists (inr (exist _ (S k) Hlen))...
Unshelve. assumption.
Qed.

Lemma deduction {P} : pperm P = true -> (projT1 (pgax P) -> False) -> pcut P = true -> forall lax l,
  ll (axupd_pfrag P (existT (fun x => x -> list formula) { k | k < length lax }
                            (fun a => nth (proj1_sig a) lax one :: nil))) l
    -> ll (cutrm_pfrag P) (l ++ (map wn (map dual lax))).
Proof with myeeasy.
intros P_perm P_axfree P_cut lax l ; intros pi.
apply cut_admissible_axfree...
apply deduction_list...
eapply stronger_pfrag...
nsplit 5...
simpl ; intros a.
exists (inr a)...
Qed.

Lemma deduction_inv {P} : pperm P = true -> (projT1 (pgax P) -> False) -> pcut P = true -> forall lax l,
  ll (cutrm_pfrag P) (l ++ (map wn (map dual lax))) ->
  ll (axupd_pfrag P (existT (fun x => x -> list formula) { k | k < length lax }
                            (fun a => nth (proj1_sig a) lax one :: nil))) l.
Proof with myeeasy.
intros P_perm P_axfree P_cut lax l ; intros pi.
assert (ll P (l ++ (map wn (map dual lax)))) as pi'.
{ eapply stronger_pfrag...
  nsplit 5...
  simpl ; intros a.
  exists a... }
apply deduction_list_inv in pi'...
eapply stronger_pfrag...
nsplit 5...
simpl ; intros a.
destruct a.
- contradiction P_axfree.
- exists s...
Qed.



