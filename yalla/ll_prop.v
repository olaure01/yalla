(** * Properties relying on cut admissibility *)

From Coq Require Import Bool.
From OLlibs Require Import dectype List_more Dependent_Forall_Type flat_map_more
                           Permutation_Type_more GPermutation_Type.
From Yalla Require Export ll_cut.

Set Implicit Arguments.


Section Atoms.

Context {atom : DecType}.
Notation formula := (@formula atom).
Notation ll := (@ll atom).

(** Consistency statements *)

Lemma weak_consistency_axfree P (Hgax : no_ax P) (Hmix0 : pmix P 0 = false) : notT (ll P nil).
Proof.
intros pi.
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

Lemma strong_consistency_axfree P (Hgax : no_ax P) : notT (ll P (zero :: nil)).
Proof.
intros pi.
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


(** ** Subformula Property *)

(** A fragment is a subset of formulas closed under subformula. *)
Definition fragment FS := forall A : formula, FS A -> forall B, subform B A -> FS B.

(** Linear logic is conservative over its fragments (in the absence of cut). *)
Lemma conservativity P (P_cutfree : no_cut P) FS (Hfrag : fragment FS) l (pi : ll P l) :
  Forall_inf FS l -> Forall_formula FS pi.
Proof.
induction pi using ll_nested_ind; cbn; intros HFS; try split; try now (inversion HFS; auto);
  try (inversion_clear HFS; try split; try apply IHpi; try apply IHpi1; try apply IHpi2;
       repeat constructor; try assumption; (eapply Hfrag; [ eassumption | ]); repeat constructor).
- symmetry in p.
  eapply IHpi, PCPermutation_Type_Forall_inf; eassumption.
- symmetry in p.
  eapply IHpi, (PCPermutation_Type_Forall_inf true), HFS.
  apply Permutation_Type_app_head, Permutation_Type_app_tail, Permutation_Type_map, p.
- apply Forall_Proofs_to_Forall_inf in X. clear - X HFS.
  induction PL in X, HFS |- *; [ constructor | split; inversion X; subst ].
  + apply X0. cbn. exact (Forall_inf_app_l _ _ HFS).
  + apply IHPL; [ apply X1 | exact (Forall_inf_app_r _ _ HFS) ].
- inversion_clear HFS. split.
  + apply IHpi1.
    constructor; [ | exact (Forall_inf_app_r _ _ X0) ].
    apply (Hfrag _ X).
    constructor; constructor.
  + apply IHpi2.
    constructor; [ | exact (Forall_inf_app_l _ _ X0) ].
    apply (Hfrag _ X).
    constructor; constructor.
- rewrite P_cutfree in f. discriminate f.
Qed.

(** Cut-free subformula property:
cut-free proofs only use subformulas of the conclusion. *)
Proposition subformula_cutfree P (P_cutfree : no_cut P) l (pi : ll P l) :
  Forall_formula (fun x => Exists (subform x) l) pi.
Proof.
apply (conservativity P_cutfree).
- intros A Hf B Hs.
  eapply Exists_impl, Hf.
  intros C HAC.
  transitivity A; assumption.
- clear. induction l as [|A l IHl]; constructor.
  + constructor; constructor.
  + eapply Forall_inf_arrow, IHl.
    intros B Hl. right. exact Hl.
Qed.

(** Linear logic (with no axioms) is conservative over its fragments. *)
Lemma conservativity_axfree P (P_axfree : no_ax P) FS (Hfrag : fragment FS) l (pi : ll P l) :
  Forall_inf FS l -> { pi' : ll P l & Forall_formula FS pi' }.
Proof.
intros HFS.
apply cut_admissible_axfree in pi; [ | assumption ].
exists (stronger_pfrag _ _ (cutrm_pfrag_le P) _ pi).
apply Forall_sequent_stronger_pfrag.
apply conservativity; [ apply nocut_cutrm | | ]; assumption.
Qed.

Variable P : @pfrag atom.
Variable P_axfree : no_ax P.

(** Cut is admissible in any fragment with no axioms. *)
Lemma cut_admissible_fragment_axfree FS (Hfrag : fragment FS) l (pi : ll P l) : Forall_formula FS pi ->
  { pi' : ll (cutrm_pfrag P) l & Forall_formula FS pi'}.
Proof using P_axfree.
intros HFS.
apply conservativity_axfree; [ assumption | assumption | | ].
- apply cut_admissible_axfree; assumption.
- apply (Forall_sequent_is _ _ HFS).
Qed.

(** Subformula property:
any provable sequent is provable by a proof containing only subformulas of this sequent. *)
Proposition subformula l (pi : ll P l) : { pi': ll P l & Forall_formula (fun x => Exists (subform x) l) pi' }.
Proof using P_axfree.
refine (conservativity_axfree P_axfree _ pi _).
- intros A Hf B Hs.
  eapply Exists_impl, Hf.
  intros C HAC.
  transitivity A; assumption.
- clear. induction l; constructor.
  + constructor; constructor.
  + eapply Forall_inf_arrow, IHl. clear. cbn.
    intros A Hl. right. exact Hl.
Qed.


(** ** Deduction Theorem *)

Variable P_perm : pperm P = true.
Variable P_cut : full_cut P.

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
  rewrite <- (app_nil_r l). refine (cut_r (wn (dual A)) _ _ _); [ cbn; apply P_cut | | ].
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
