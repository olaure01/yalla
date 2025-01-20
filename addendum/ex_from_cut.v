From Yalla Require Import List_more CPermutation_Type GPermutation_Type ll_def.
Import ListNotations.

Set Implicit Arguments.

Lemma exc_rule P (Pcut : pcut P = true) l A : ll P (A :: l) -> ll P (l ++ [A]).
Proof.
intro pi.
apply (@cut_r _ Pcut A); [ | assumption ].
replace [dual A; A] with [dual A; dual (dual A)] by now rewrite bidual.
apply ax_exp.
Qed.

Lemma exc_r_cut P (Pcut : pcut P = true) l1 l2 : ll P l1 -> CPermutation_Type l1 l2 -> ll P l2.
Proof.
intros pi HC. inversion HC; subst; clear HC.
induction l0 as [|A l IHl] in l3, pi |- *.
- rewrite app_nil_r. assumption.
- cons2app. rewrite app_assoc. apply IHl.
  rewrite app_assoc. apply exc_rule; assumption.
Qed.

Lemma comm_wn P (Pcut : pcut P = true) l A B :
  ll P (wn A :: wn B :: l) -> ll P (wn B :: wn A :: l).
Proof.
intros pi%parr_r.
assert (ll P (wn (aplus B A) :: l)) as pi'; [ | clear pi ].
{ cons2app.
  apply (@cut_r P Pcut (tens (oc (dual B)) (oc (dual A)))).
  { cbn. rewrite ! bidual. assumption. }
  eapply ex_r; [ | apply PCPermutation_Type_swap ].
  apply co_r.
  eapply ex_r; [ |cons2app; rewrite app_assoc; apply PCPermutation_Type_app_comm ].
  cbn. cons2app. rewrite <- app_comm_cons, app_nil_l.
  apply tens_r; change [wn (aplus B A)] with (map wn [aplus B A]); apply oc_r;
    (eapply ex_r; [ | apply PCPermutation_Type_swap ]); apply de_r.
  - apply plus_r1, ax_exp.
  - apply plus_r2, ax_exp. }
cons2app. rewrite app_assoc.
apply (@cut_r P Pcut (oc (awith (dual B) (dual A)))).
{ cbn. rewrite ! bidual. assumption. }
change ([wn B] ++ [wn A]) with (map wn [B; A]); apply oc_r; apply with_r; cbn;
  (eapply ex_r; [ |cons2app; rewrite app_assoc; apply PCPermutation_Type_app_comm ]; cbn);
  (eapply ex_r; [ |cons2app; rewrite app_assoc; apply PCPermutation_Type_app_comm ]; cbn).
- apply de_r.
  eapply ex_r; [ |cons2app; rewrite app_assoc; apply PCPermutation_Type_app_comm ]. cbn.
  eapply ex_r; [ |cons2app; rewrite app_assoc; apply PCPermutation_Type_app_comm ]. cbn.
  apply wk_r.
  eapply ex_r; [ | apply PCPermutation_Type_swap ].
  apply ax_exp.
- apply wk_r, de_r, ax_exp.
Qed.
