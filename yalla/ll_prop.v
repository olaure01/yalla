(* ll_prop library for yalla *)

(** * Properties relying on cut admissibility *)

From Coq Require Import Bool.
From OLlibs Require Import dectype List_more
                           Permutation_Type_more CPermutation_Type GPermutation_Type
                           Dependent_Forall_Type flat_map_more.
From Yalla Require Export ll_cut.

Set Implicit Arguments.


Section Atoms.

Context {atom : DecType}.
Notation formula := (@formula atom).
Notation ll := (@ll atom).

(** Consistency statements *)

Lemma weak_consistency_axfree P : notT (projT1 (pgax P)) -> pmix P 0 = false -> notT (ll P nil).
Proof.
intros Hgax Hmix0 pi.
apply cut_admissible_axfree in pi; [ | assumption ].
remember nil as l. induction pi using ll_nested_ind in Heql |- *; inversion Heql; subst.
- symmetry in p.
  apply IHpi, (PCPermutation_Type_nil _ _ p).
- apply IHpi.
  destruct l1, lw', l2; try discriminate Heql.
  symmetry in p. apply Permutation_Type_nil in p as ->. reflexivity.
- destruct L; [ | inversion Heql as [ HeqL ] ].
  + cbn in eqpmix. rewrite Hmix0 in eqpmix. discriminate eqpmix.
  + inversion_clear X as [ | ? ? ? ? Hnil ].
    apply Hnil. destruct l; [ reflexivity | discriminate HeqL ].
- discriminate f.
- exact (Hgax a).
Qed.

Lemma strong_consistency_axfree P : notT (projT1 (pgax P)) -> notT (ll P (zero :: nil)).
Proof.
intros Hgax pi.
apply cut_admissible_axfree in pi; [ | assumption ].
remember (zero :: nil) as l. induction pi using ll_nested_ind in Heql |- *; inversion Heql; subst.
- symmetry in p.
  apply IHpi, (PCPermutation_Type_length_1_inv _ _ _ p).
- apply IHpi.
  destruct l1; inversion Heql.
  + destruct lw'; inversion Heql.
    symmetry in p. apply Permutation_Type_nil in p as ->.
    destruct l2; inversion_clear H. reflexivity.
  + apply app_eq_nil in H2 as [-> H2].
    apply app_eq_nil in H2 as [H2 ->].
    destruct lw'; inversion H2.
    symmetry in p. apply Permutation_Type_nil in p as ->. reflexivity.
- rename X into HPL. clear - PL HPL Heql. induction L in PL, HPL, Heql |- *; [ discriminate Heql | ].
  inversion HPL as [ | ? ? ? ? Heq ]. destruct a; subst.
  + apply IHL with Fl; assumption.
  + injection Heql as [= -> Heq'].
    destruct a; [ | discriminate Heq' ].
    apply Heq. reflexivity.
- discriminate f.
- exact (Hgax a).
Qed.


(** Some additional reversibility statements *)
(* TODO atomic gax should be enough, induction on cut-free proof, see ll_def *)

Lemma with_rev1_noax P (Hgax : notT (projT1 (pgax P))) A B l1 l2 :
  ll P (l1 ++ awith A B :: l2) -> ll P (l1 ++ A :: l2).
Proof.
intros pi.
assert (ll P (dual (awith A B) :: A :: nil)) as pi'
  by (eapply plus_r1, ex_r; [ apply ax_exp | apply PCPermutation_Type_swap ]).
eapply (ex_r ((l2 ++ l1) ++ A :: nil)).
- eapply cut_r_axfree; [ assumption | eassumption | ].
  eapply ex_r; [ apply pi | ].
  rewrite app_comm_cons. apply PCPermutation_Type_app_comm.
- list_simpl. cons2app. rewrite (app_assoc l1). apply PCPermutation_Type_app_comm.
Qed.

Lemma with_rev2_noax P (Hgax : notT (projT1 (pgax P))) A B l1 l2 :
  ll P (l1 ++ awith B A :: l2) -> ll P (l1 ++ A :: l2).
Proof.
intros pi.
assert (ll P (dual (awith B A) :: A :: nil)) as pi'
  by (eapply plus_r2, ex_r; [ apply ax_exp | apply PCPermutation_Type_swap ]).
eapply (ex_r ((l2 ++ l1) ++ A :: nil)).
- eapply cut_r_axfree; [ assumption | eassumption | ].
  eapply ex_r; [ apply pi | ].
  rewrite app_comm_cons. apply PCPermutation_Type_app_comm.
- list_simpl. cons2app. rewrite (app_assoc l1). apply PCPermutation_Type_app_comm.
Qed.

Lemma oc_rev_noax P (Hgax : notT (projT1 (pgax P))) A l1 l2 :
  ll P (l1 ++ oc A :: l2) -> ll P (l1 ++ A :: l2).
Proof.
intros pi.
assert (ll P (dual (oc A) :: A :: nil)) as pi'
  by (eapply de_r, ex_r; [ apply ax_exp | apply PCPermutation_Type_swap ]).
eapply (ex_r ((l2 ++ l1) ++ A :: nil)).
- eapply cut_r_axfree; try eassumption.
  eapply ex_r; [ apply pi | ].
  rewrite app_comm_cons. apply PCPermutation_Type_app_comm.
- list_simpl. cons2app. rewrite (app_assoc l1). apply PCPermutation_Type_app_comm.
Qed.



(** ** Subformula Property *)

(** version of ll with predicate parameter for constraining sequents *)
Inductive ll_ps P PS : list formula -> Type :=
| ax_ps_r : forall X, is_true (PS (covar X :: var X :: nil)) -> ll_ps P PS (covar X :: var X :: nil)
| ex_ps_r : forall l1 l2, is_true (PS l2) -> ll_ps P PS l1 -> PCPermutation_Type (pperm P) l1 l2 -> ll_ps P PS l2
| ex_wn_ps_r : forall l1 lw lw' l2, is_true (PS (l1 ++ map wn lw' ++ l2)) ->
                 ll_ps P PS (l1 ++ map wn lw ++ l2) ->
                 Permutation_Type lw lw' -> ll_ps P PS (l1 ++ map wn lw' ++ l2)
| mix_ps_r : forall L, pmix P (length L) = true -> is_true (PS (concat L)) ->
                       Forall_inf (ll_ps P PS) L ->
                       ll_ps P PS (concat L)
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

Section ll_ps_ind.
  Variable P : @pfrag atom.
  Variable PS : list formula -> bool.

  Definition Forall_Proofs_ps (Pred : forall l, ll_ps P PS l -> Type) {L} (piL : Forall_inf (ll_ps P PS) L) :=
    Dependent_Forall_inf Pred piL.

  Fixpoint ll_ps_nested_ind l (pi : ll_ps P PS l): forall (Pred : forall l, ll_ps P PS l -> Type),
    (forall X Hps, Pred (covar X :: var X :: nil) (ax_ps_r P PS X Hps)) ->
    (forall l1 l2 Hps pi p, Pred l1 pi -> Pred l2 (ex_ps_r l2 Hps pi p)) ->
    (forall l1 lw lw' l2 Hps pi p, Pred (l1 ++ map wn lw ++ l2) pi ->
      Pred (l1 ++ map wn lw' ++ l2) (ex_wn_ps_r l1 l2 Hps pi p)) ->
    (forall L eqpmix Hps PL, Forall_Proofs_ps Pred PL ->
      Pred (concat L) (mix_ps_r eqpmix Hps PL)) ->
    (forall Hps, Pred (one :: nil) (one_ps_r P PS Hps)) ->
    (forall l Hps pi, Pred l pi -> Pred (bot :: l) (bot_ps_r Hps pi)) ->
    (forall A B l1 l2 Hps pi1 pi2, Pred (A :: l1) pi1 -> Pred (B :: l2) pi2 ->
      Pred (tens A B :: l2 ++ l1) (tens_ps_r Hps pi1 pi2)) ->
    (forall A B l Hps pi, Pred (A :: B :: l) pi -> Pred (parr A B :: l) (parr_ps_r Hps pi)) ->
    (forall l Hps, Pred (top :: l) (top_ps_r P PS l Hps)) ->
    (forall A B l Hps pi, Pred (A :: l) pi -> Pred (aplus A B :: l) (plus_ps_r1 B Hps pi)) ->
    (forall A B l Hps pi, Pred (A :: l) pi -> Pred (aplus B A :: l) (plus_ps_r2 B Hps pi)) ->
    (forall A B l Hps pi1 pi2, Pred (A :: l) pi1 -> Pred (B :: l) pi2 ->
      Pred (awith A B :: l) (with_ps_r Hps pi1 pi2)) ->
    (forall A l Hps pi, Pred (A :: map wn l) pi -> Pred (oc A :: map wn l) (oc_ps_r l Hps pi)) ->
    (forall A l Hps pi, Pred (A :: l) pi -> Pred (wn A :: l) (de_ps_r Hps pi)) ->
    (forall A l Hps pi, Pred l pi -> Pred (wn A :: l) (wk_ps_r A Hps pi)) ->
    (forall A l Hps pi, Pred (wn A :: wn A :: l) pi -> Pred (wn A :: l) (co_ps_r Hps pi)) ->
    (forall f A l1 l2 Hps pi1 pi2, Pred (dual A :: l1) pi1 -> Pred (A :: l2) pi2 ->
      Pred (l2 ++ l1) (@cut_ps_r P PS f A l1 l2 Hps pi1 pi2)) ->
    (forall a Hps, Pred (projT2 (pgax P) a) (gax_ps_r P PS a Hps)) ->
    Pred l pi :=
      fun Pred ax_case ex_case ex_wn_case mix_case one_case bot_case tens_case parr_case
               top_case plus_case1 plus_case2 with_case oc_case de_case wk_case co_case cut_case gax_case =>
    let rec_call {l} (pi : ll_ps P PS l) :=
       (ll_ps_nested_ind pi ax_case ex_case ex_wn_case mix_case one_case bot_case tens_case parr_case
                            top_case plus_case1 plus_case2 with_case
                            oc_case de_case wk_case co_case cut_case gax_case) in
    match pi with
    | ax_ps_r _ _ X Hps => ax_case X Hps
    | @ex_ps_r _ _ l1 l2 Hps pi p => ex_case l1 l2 Hps pi p (rec_call pi)
    | @ex_wn_ps_r _ _ l1 lw lw' l2 Hps pi p => ex_wn_case l1 lw lw' l2 Hps pi p (rec_call pi)
    | @mix_ps_r _ _ L eqpmix Hps PL => mix_case L eqpmix Hps PL (
        (fix ll_ps_nested_ind_aux L (PL : Forall_inf (ll_ps P PS) L) : Forall_Proofs_ps Pred PL :=
          match PL with
          | Forall_inf_nil _ => Dependent_Forall_inf_nil _ Pred
          | @Forall_inf_cons _ _ l L Pil PiL => Dependent_Forall_inf_cons _ Pil (rec_call Pil)
                                                                            (ll_ps_nested_ind_aux L PiL)
          end) L PL)
    | @one_ps_r _ _ Hps => one_case Hps
    | @bot_ps_r _ _ l Hps pi => bot_case l Hps pi (rec_call pi)
    | @tens_ps_r _ _ A B l1 l2 Hps pi1 pi2 => tens_case A B l1 l2 Hps pi1 pi2 (rec_call pi1) (rec_call pi2)
    | @parr_ps_r _ _ A B l Hps pi => parr_case A B l Hps pi (rec_call pi)
    | @top_ps_r _ _ l Hps => top_case l Hps
    | @plus_ps_r1 _ _ A B l Hps pi => plus_case1 A B l Hps pi (rec_call pi)
    | @plus_ps_r2 _ _ A B l Hps pi => plus_case2 A B l Hps pi (rec_call pi)
    | @with_ps_r _ _ A B l Hps pi1 pi2 => with_case A B l Hps pi1 pi2 (rec_call pi1) (rec_call pi2)
    | @oc_ps_r _ _ A l Hps pi => oc_case A l Hps pi (rec_call pi)
    | @de_ps_r _ _ A l Hps pi => de_case A l Hps pi (rec_call pi)
    | @wk_ps_r _ _ A l Hps pi => wk_case A l Hps pi (rec_call pi)
    | @co_ps_r _ _ A l Hps pi => co_case A l Hps pi (rec_call pi)
    | @cut_ps_r _ _ f A l1 l2 Hps pi1 pi2 => cut_case f A l1 l2 Hps pi1 pi2 (rec_call pi1) (rec_call pi2)
    | gax_ps_r _ _ a Hps => gax_case a Hps
    end.

End ll_ps_ind.

Arguments ll_ps_nested_ind P PS {l}.


Lemma stronger_ps_pfrag P Q : le_pfrag P Q -> forall PS l,
  ll_ps P PS l -> ll_ps Q PS l.
Proof.
intros Hle PS l pi.
induction pi using (ll_ps_nested_ind P PS); try (now constructor).
- apply (@ex_ps_r _ _ l1); try assumption.
  destruct Hle as (_ & _ & _  & Hp).
  unfold PCPermutation_Type in *.
  destruct (pperm P); destruct (pperm Q); cbn in Hp; try (inversion Hp; assumption).
  apply CPermutation_Permutation_Type; assumption.
- eapply ex_wn_ps_r; eassumption.
- unfold le_pfrag in Hle.
  destruct Hle as (_ & _ & Hmix & _).
  specialize (Hmix (length L)).
  rewrite eqpmix in Hmix; cbn in Hmix.
  apply mix_ps_r; try assumption.
  apply forall_Forall_inf.
  intros l' Hin.
  apply(In_Forall_inf_in _ PL) in Hin as [pi Hin].
  refine (Dependent_Forall_inf_forall_formula _ _ X Hin).
- destruct Hle as [Hle _].
  rewrite f in Hle; cbn in Hle.
  apply (@cut_ps_r _ _ Hle A); assumption.
- destruct Hle as (_ & Hgax & _).
  destruct (Hgax a) as [b Heq].
  rewrite Heq in Hps; rewrite Heq.
  apply gax_ps_r; assumption.
Qed.

Lemma ll_ps_stronger P PS QS l :
  ll_ps P PS l -> (forall x, is_true (PS x) -> is_true (QS x)) -> ll_ps P QS l.
Proof.
intros pi Hs.
induction pi using (ll_ps_nested_ind P PS); try now (econstructor; try apply Hs; eassumption).
apply mix_ps_r ; [ | apply Hs | ]; try assumption.
apply forall_Forall_inf.
intros l' Hin.
apply(In_Forall_inf_in _ PL) in Hin as [pi Hin].
apply (Dependent_Forall_inf_forall_formula _ _ X Hin).
Qed.

Lemma ll_ps_is_ps P PS l : ll_ps P PS l -> is_true (PS l).
Proof. intros Hll. destruct Hll; assumption. Qed.

Lemma ll_ps_is_ll P PS l : ll_ps P PS l -> ll P l.
Proof.
intros pi; induction pi using (ll_ps_nested_ind P PS); try now (econstructor; eassumption).
apply mix_r; [ assumption | ].
apply forall_Forall_inf; intros l' Hin.
apply(In_Forall_inf_in _ PL) in Hin as [pi Hin].
apply (Dependent_Forall_inf_forall_formula _ _ X Hin).
Qed.

Lemma ll_is_ll_ps P l : ll P l -> ll_ps P (fun _ => true) l.
Proof.
intros pi. induction pi using ll_nested_ind; try now (econstructor; try eassumption; reflexivity).
apply mix_ps_r; [ assumption | reflexivity | ].
apply forall_Forall_inf. intros l' Hin.
apply(In_Forall_inf_in _ PL) in Hin as [pi Hin].
apply (Dependent_Forall_inf_forall_formula _ _ X Hin).
Qed.

(** A fragment is a subset of formulas closed under subformula. *)
Definition fragment FS := forall A : formula, FS A -> forall B, subform B A -> FS B.

Definition fragmentb FS := fragment (fun A => is_true (FS A)).

(** Linear logic is conservative over its fragments (in the absence of cut). *)
Lemma conservativity P : pcut P = false -> forall FS, fragmentb FS ->
  forall l, ll_ps P (fun _ => true) l -> is_true (forallb FS l) -> ll_ps P (forallb FS) l.
Proof.
intros P_cutfree FS HFS l pi.
induction pi using (ll_ps_nested_ind P (fun _ => true)); intros HFrag.
- apply ax_ps_r; assumption.
- apply (@ex_ps_r _ _ l1); try assumption.
  apply IHpi.
  apply PCPermutation_Type_sym in p.
  unfold is_true in HFrag; rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  apply forallb_forall, Forall_forall.
  eapply PCPermutation_Type_Forall; eassumption.
- eapply ex_wn_ps_r; try eassumption.
  apply IHpi.
  unfold is_true in HFrag; rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  apply forallb_forall, Forall_forall.
  apply (Permutation_Type_map wn) in p.
  eapply Permutation_Type_Forall; [ | eassumption ].
  symmetry; apply Permutation_Type_app_head, Permutation_Type_app_tail; assumption.
- unfold is_true in HFrag; rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  apply mix_ps_r; [ assumption | | ].
  + apply forallb_forall, Forall_forall; assumption.
  + apply forall_Forall_inf; intros l' Hin.
    apply(In_Forall_inf_in _ PL) in Hin as [pi Hin].
    refine (Dependent_Forall_inf_forall_formula _ _ X Hin _).
    clear - Hin HFrag.
    apply forallb_forall; intros A Hin'.
    apply (Forall_forall (fun x => is_true (FS x)) (concat L)); [ assumption | ].
    apply in_concat; exists l'.
    apply In_Forall_inf_to_In_inf in Hin.
    apply in_inf_in in Hin; split; assumption.
- apply one_ps_r; assumption.
- apply bot_ps_r; [ assumption | ].
  inversion HFrag.
  apply andb_true_iff in H0.
  destruct H0.
  apply IHpi; assumption.
- assert (HFrag2 := HFrag).
  cbn in HFrag.
  apply andb_true_iff in HFrag.
  destruct HFrag as [HFragt HFrag].
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  apply Forall_app in HFrag as [HFragl HFragr].
  rewrite Forall_forall, <- forallb_forall in HFragl.
  rewrite Forall_forall, <- forallb_forall in HFragr.
  apply tens_ps_r; [ assumption | | ].
  + apply IHpi1.
    cbn; apply andb_true_iff; split; [ | assumption ].
    eapply HFS; [ eassumption | ].
    apply sub_tens_l; reflexivity.
  + apply IHpi2.
    cbn; apply andb_true_iff; split; [ | assumption ].
    eapply HFS; [ eassumption | ].
    apply sub_tens_r; reflexivity.
- inversion HFrag ; subst.
  apply andb_true_iff in H0 ; destruct H0.
  apply parr_ps_r; [ assumption | ].
  apply IHpi.
  cbn ; apply andb_true_iff ; split ;
    [ | cbn ; apply andb_true_iff ; split ]; [ | | assumption ].
  + eapply HFS; [ eassumption | ].
    apply sub_parr_l; reflexivity.
  + eapply HFS; [ eassumption | ].
    apply sub_parr_r; reflexivity.
- apply top_ps_r; assumption.
- inversion HFrag; subst.
  apply andb_true_iff in H0; destruct H0.
  apply plus_ps_r1; [ assumption | ];
  apply IHpi.
  cbn; apply andb_true_iff; split; [ | assumption ].
  eapply HFS; [ eassumption | ].
  apply sub_plus_l; reflexivity.
- inversion HFrag; subst.
  apply andb_true_iff in H0; destruct H0.
  apply plus_ps_r2; [ assumption | ].
  apply IHpi.
  cbn; apply andb_true_iff; split; [ | assumption ].
  eapply HFS; [ eassumption | ].
  apply sub_plus_r; reflexivity.
- inversion HFrag; subst.
  apply andb_true_iff in H0; destruct H0.
  apply with_ps_r; [ assumption | | ].
  + apply IHpi1.
    cbn; apply andb_true_iff; split; [ | assumption ].
    eapply HFS; [ eassumption | ].
    apply sub_with_l; reflexivity.
  + apply IHpi2.
    cbn; apply andb_true_iff; split; [ | assumption ].
    eapply HFS; [ eassumption | ].
    apply sub_with_r; reflexivity.
- inversion HFrag; subst.
  apply andb_true_iff in H0; destruct H0.
  apply oc_ps_r; [ assumption | ].
  apply IHpi.
  cbn; apply andb_true_iff; split; [ | assumption ].
  eapply HFS; [ eassumption | ].
  apply sub_oc; reflexivity.
- inversion HFrag; subst.
  apply andb_true_iff in H0; destruct H0.
  apply de_ps_r; [ assumption | ].
  apply IHpi.
  cbn ; apply andb_true_iff ; split; [ | assumption ].
  eapply HFS; [ eassumption | ].
  apply sub_wn; reflexivity.
- inversion HFrag; subst.
  apply andb_true_iff in H0; destruct H0.
  apply wk_ps_r; [ assumption | ].
  apply IHpi; assumption.
- inversion HFrag; subst.
  apply andb_true_iff in H0; destruct H0.
  apply co_ps_r; [ assumption | ].
  apply IHpi.
  cbn; apply andb_true_iff; split; assumption.
- rewrite P_cutfree in f; inversion f.
- apply gax_ps_r; assumption.
Qed.

(** Subformula property:
any provable sequent is provable by a proof containing only subformulas of this sequent. *)
Proposition subformula P : pcut P = false -> forall l,
  ll P l -> ll_ps P (fun x => subformb_list x l) l.
Proof.
intros P_cutfree l pi.
apply ll_is_ll_ps in pi.
apply conservativity; try assumption.
- intros A Hf B Hs.
  revert Hf; clear - Hs; induction l; intro Hf; inversion Hf; subst.
  cbn; apply orb_true_iff.
  apply orb_true_iff in H0.
  destruct H0.
  + left; eapply subb_trans; [ | eassumption ].
    apply subb_sub; assumption.
  + right; apply IHl; assumption.
- apply (subb_id_list l nil).
Qed.

Variable P : @pfrag atom.
Variable P_axfree : notT (projT1 (pgax P)).

(* Cut is admissible in any fragment with no axioms. *)
Lemma cut_admissible_fragment_axfree FS (Hfrag : fragmentb FS) l :
  ll_ps P (forallb FS) l -> ll_ps (cutrm_pfrag P) (forallb FS) l.
Proof using P_axfree.
intros pi.
apply conservativity; [ reflexivity | exact Hfrag | | ].
- apply ll_is_ll_ps, (cut_admissible_axfree P_axfree), (ll_ps_is_ll pi).
- exact (ll_ps_is_ps pi).
Qed.

(** Linear logic (with no axioms) is conservative over its fragments. *)
Lemma conservativity_axfree FS (Hfrag : fragmentb FS) l :
   ll P l -> is_true (forallb FS l) -> ll_ps P (forallb FS) l.
Proof using P_axfree.
intros pi HFS.
apply cut_admissible_axfree in pi; [ | assumption ].
apply ll_is_ll_ps in pi.
eapply conservativity in pi; try eassumption; [ | reflexivity ].
clear - pi. induction pi using (ll_ps_nested_ind (cutrm_pfrag P) (forallb FS));
  try now (econstructor; eassumption).
- cbn in eqpmix.
  apply mix_ps_r; [ assumption | assumption | ].
  apply forall_Forall_inf. intros l' Hin.
  apply (In_Forall_inf_in _ PL) in Hin as [pi Hin].
  apply (Dependent_Forall_inf_forall_formula _ _ X Hin).
- refine (cut_ps_r Hps IHpi1 IHpi2).
  discriminate f.
- assert (pgax (cutrm_pfrag P) = pgax P) as Hcut by reflexivity.
  revert a Hps. rewrite Hcut. apply gax_ps_r.
Qed.
*)

(** ** Deduction Theorem *)

Variable P_perm : pperm P = true.
Variable P_cut : pcut P = true.

(** Deduction lemma for linear logic. *)
Lemma deduction_list lax l :
  ll (axupd_pfrag P (existT (fun x => x -> _) (sum _ { k | k < length lax })
                            (fun a => match a with
                                      | inl x => projT2 (pgax P) x
                                      | inr x => nth (proj1_sig x) lax one :: nil
                                      end))) l ->
  ll P (l ++ map wn (map dual lax)).
Proof using P_perm.
induction lax as [ | A lax IHlax ] in l |- *; intros pi.
- list_simpl.
  eapply stronger_pfrag, pi.
  repeat split; try reflexivity.
  cbn. intros [a | [k Hlt]].
  + exists a. reflexivity.
  + exfalso. exact (PeanoNat.Nat.nlt_0_r _ Hlt).
- remember (axupd_pfrag P (existT (fun x => x -> _) (sum _ { k | k < length lax })
                                  (fun a => match a with
                                            | inl x => projT2 (pgax P) x
                                            | inr x => nth (proj1_sig x) lax one :: nil
                                            end)))
    as Q eqn:HeqQ.
  cbn. cons2app. rewrite app_assoc.
  apply IHlax.
  eapply ax_gen; [ | | | | refine (ext_wn _ (dual A :: nil) pi); assumption ]; try (now rewrite ! HeqQ).
  cbn in pi. cbn. intros [p | [[|k] Hlen]]; cbn.
  + eapply ex_r; [ | apply PCPermutation_Type_cons_append ].
    apply wk_r.
    assert ({ b | projT2 (pgax P) p = projT2 (pgax Q) b}) as [b Hgax]
      by (subst; cbn; exists (inl p); reflexivity).
    rewrite Hgax. apply gax_r.
  + eapply ex_r; [ | apply PCPermutation_Type_swap ].
    apply de_r.
    eapply ex_r; [ apply ax_exp | apply PCPermutation_Type_swap ].
  + eapply ex_r; [ | apply PCPermutation_Type_swap ].
    apply wk_r.
    assert ({ b | nth k lax one :: nil = projT2 (pgax Q) b}) as [b Hgax].
    { subst. clear - Hlen. cbn.
      apply PeanoNat.Nat.succ_lt_mono in Hlen.
      exists (inr (exist _ k Hlen)). reflexivity. }
      rewrite Hgax. apply gax_r.
Qed.

Lemma deduction_list_inv lax l :
  ll P (l ++ map wn (map dual lax)) ->
  ll (axupd_pfrag P (existT (fun x => x -> _) (sum _ { k | k < length lax })
                            (fun a => match a with
                                      | inl x => projT2 (pgax P) x
                                      | inr x => nth (proj1_sig x) lax one :: nil
                                      end))) l.
Proof using P_perm P_cut.
induction lax as [|A lax IHlax] in l |- *; intros pi.
- list_simpl in pi.
  eapply stronger_pfrag, pi.
  repeat split; try reflexivity.
  cbn. intros a. exists (inl a). reflexivity.
- list_simpl in pi. cons2app in pi. rewrite app_assoc in pi.
  apply IHlax in pi.
  rewrite <- (app_nil_r l). refine (cut_r (wn (dual A)) _ _); [ assumption | | ].
  + cbn. rewrite bidual.
    change nil with (map (@wn atom) nil).
    apply oc_r. cbn.
    assert ({ b | A :: nil = projT2 (pgax (axupd_pfrag P
     (existT (fun x => x -> _) (sum _ {k | k < S (length lax)})
        (fun a0 => match a0 with
                   | inl x => projT2 (pgax P) x
                   | inr x => match proj1_sig x with
                              | 0 => A
                              | S m => nth m lax one
                              end :: nil
                   end)))) b}) as [b Hgax]
      by (clear; cbn; exists (inr (exist _ 0 (le_n_S _ _ (le_0_n _)))); reflexivity).
    rewrite Hgax. apply gax_r.
  + eapply ex_r; [ | apply PCPermutation_Type_sym, PCPermutation_Type_cons_append ].
    eapply stronger_pfrag, pi.
    repeat split; try reflexivity.
    cbn. intros [p | [k Hlen]].
    * exists (inl p). reflexivity.
    * cbn. apply -> PeanoNat.Nat.succ_lt_mono in Hlen.
      exists (inr (exist _ (S k) Hlen)). reflexivity.
Qed.

Lemma deduction lax l :
  ll (axupd_pfrag P (existT (fun x => x -> _) { k | k < length lax }
                            (fun a => nth (proj1_sig a) lax one :: nil))) l ->
  ll (cutrm_pfrag P) (l ++ (map wn (map dual lax))).
Proof using P_perm P_cut P_axfree.
intros pi.
apply (cut_admissible_axfree P_axfree).
apply deduction_list.
eapply stronger_pfrag, pi.
repeat split; try reflexivity.
intros a. exists (inr a). reflexivity.
Qed.

Lemma deduction_inv lax l :
  ll (cutrm_pfrag P) (l ++ (map wn (map dual lax))) ->
  ll (axupd_pfrag P (existT (fun x => x -> _) { k | k < length lax }
                            (fun a => nth (proj1_sig a) lax one :: nil))) l.
Proof using P_perm P_cut P_axfree.
intros pi.
assert (ll P (l ++ (map wn (map dual lax)))) as pi'.
{ eapply stronger_pfrag, pi.
  repeat split; try reflexivity.
  intros a. exists a. reflexivity. }
apply deduction_list_inv in pi'.
eapply stronger_pfrag, pi'.
repeat split; try reflexivity.
cbn. intros [? | s].
- contradiction P_axfree.
- exists s. reflexivity.
Qed.

End Atoms.
