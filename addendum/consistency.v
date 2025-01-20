From Stdlib Require Import List.
From Yalla Require Import Permutation_Type_more GPermutation_Type ll_fragments ll_cut.
Import ListNotations.

Set Implicit Arguments.


Lemma empty_double_bot P : ll P nil -> ll P [bot; bot].
Proof. intro. do 2 apply bot_r. assumption. Qed.

Lemma double_bot_empty P (Hcut : pcut P = true) : ll P [bot; bot] -> ll P [].
Proof. intro. do 2 refine (@cut_r _ Hcut _ _ _ _ (one_r _)). assumption. Qed.

Lemma empty_contradiction P : ll P [] -> { A & ll P [A] & ll P [dual A] }.
Proof. intro pi. exists bot; [ apply bot_r, pi | apply one_r ]. Qed.

Lemma contradiction_empty P (Hcut : pcut P = true) : { A & ll P [A] & ll P [dual A] } -> ll P [].
Proof. intros [A pi1 pi2]. apply (@cut_r _ Hcut _ _ _ pi2 pi1). Qed.


Lemma zero_any P (Hcut : pcut P = true) : ll P [zero] -> forall l, ll P l.
Proof. intros pi l. rewrite <- app_nil_r. refine (@cut_r _ Hcut top _ _ pi (top_r _ l)). Qed.

Lemma any_zero P : (forall l, ll P l) -> ll P [zero].
Proof. intro H. apply H. Qed.


Lemma not_empty_provable P (P_gax : notT (projT1 (pgax P))) (P_mix0 : pmix0 P = false) : notT (ll P nil).
Proof.
remember nil as l eqn:Heql.
intros pi%(cut_admissible_axfree P_gax). induction pi in Heql |- *; (discriminate Heql + subst).
- symmetry in p. apply IHpi, (PCPermutation_Type_nil _ _ p).
- symmetry in p. apply IHpi.
  apply app_eq_nil in Heql as [-> [->%map_eq_nil ->]%app_eq_nil].
  apply Permutation_Type_nil in p as ->. reflexivity.
- cbn in f. rewrite P_mix0 in f. discriminate f.
- apply app_eq_nil in Heql as [_ ->].
  exact (IHpi1 eq_refl).
- discriminate f.
- exact (P_gax a).
Qed.

Lemma not_zero_provable P (P_gax : notT (projT1 (pgax P))) : notT (ll P [zero]).
Proof.
remember [zero] as l eqn:Heql.
intros pi%(cut_admissible_axfree P_gax). induction pi in Heql |- *; (discriminate Heql + subst).
- symmetry in p. apply PCPermutation_Type_length_1_inv in p.
  exact (IHpi p).
- enough (lw' = nil) as ->
    by (symmetry in p; apply Permutation_Type_nil in p as ->; exact (IHpi Heql)).
  destruct l1.
  + destruct lw'; (discriminate Heql + reflexivity).
  + injection Heql as [= _ [-> [->%map_eq_nil ->]%app_eq_nil]%app_eq_nil]. reflexivity.
- apply app_eq_unit in Heql as [[-> ->]|[-> ->]]; [ apply IHpi1 | apply IHpi2 ]; reflexivity.
- discriminate f.
- exact (P_gax a).
Qed.

Lemma not_var_provable P (P_cut : pcut P = false) X (P_gax : forall a, projT2 (pgax P) a <> [var X]) :
  notT (ll P [var X]).
Proof.
remember [var X] as l eqn:Heql.
intro pi. induction pi in P_gax, Heql |- *; (discriminate Heql + subst).
- symmetry in p. apply PCPermutation_Type_length_1_inv in p.
  rewrite <- p in P_gax. exact (IHpi p P_gax).
- enough (lw' = nil) as ->
    by (symmetry in p; apply Permutation_Type_nil in p as ->; exact (IHpi Heql P_gax)).
  destruct l1.
  + destruct lw'; (discriminate Heql + reflexivity).
  + injection Heql as [= _ [-> [->%map_eq_nil ->]%app_eq_nil]%app_eq_nil]. reflexivity.
- now apply app_eq_unit in Heql as [[-> ->]|[-> ->]]; [ apply IHpi1 | apply IHpi2 ].
- rewrite P_cut in f. discriminate f.
- exact (P_gax a eq_refl).
Qed.

Lemma not_gax_cut_admissible X p b0 b2:
  let P := {| pcut := true; pperm := p; pmix0 := b0; pmix2:= b2;
              pgax := existT (fun x => x -> _) unit (fun _ => [awith (var X) (var X)]) |} in
  ll P [var X] * notT (ll (cutrm_pfrag P) [var X]).
Proof.
intro P. split.
- apply (@cut_r P eq_refl (awith (var X) (var X)) _ []).
  + apply plus_r1, ax_r.
  + apply (gax_r P tt).
- apply not_var_provable.
  + reflexivity.
  + intros _ [=].
Qed.
