From Stdlib Require Import CMorphisms.
From OLlibs Require Import funtheory List_more PermutationT_more.
From Yalla Require Import ll_fragments.
From NanoYalla Require Export macroll. (* order matters *)

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Proof Using Clear Unused.
Set Implicit Arguments.


Instance ex_PermutationT : Proper ((@PermutationT _) ==> arrow) ll.
Proof.
intros ? ?. unfold arrow.
apply (PermutationT_rect_transp (fun l1 l2 => ll l1 -> ll l2)); auto using ex_t_r.
Qed.

Fixpoint nll2ll A :=
match A with
| var x     => @formulas.var nat_infdectype x
| covar x   => @formulas.covar nat_infdectype x
| one       => formulas.one
| bot       => formulas.bot
| tens A B  => formulas.tens (nll2ll B) (nll2ll A)
| parr A B  => formulas.parr (nll2ll A) (nll2ll B)
| zero      => formulas.zero
| top       => formulas.top
| awith A B => formulas.awith (nll2ll A) (nll2ll B)
| aplus A B => formulas.aplus (nll2ll A) (nll2ll B)
| oc A      => formulas.oc (nll2ll A)
| wn A      => formulas.wn (nll2ll A)
end.

Lemma nll2ll_inj : injective nll2ll.
Proof.
intros A B Heq.
induction A as [ | | | | ? IHA1 ? IHA2 | ? IHA1 ? IHA2 |
                       | | ? IHA1 ? IHA2 | ? IHA1 ? IHA2 | ? IHA1 | ? IHA1 ] in B, Heq |- *;
  destruct B;
  try discriminate Heq; try (injection Heq as [= Heq1 Heq2]); try (injection Heq as [= Heq1]);
  try apply IHA1 in Heq1;
  try apply IHA2 in Heq2;
  try apply IHA1 in Heq2;
  try apply IHA2 in Heq1;
  subst; reflexivity.
Qed.

Lemma nll2ll_dual A : formulas.dual (nll2ll A) = nll2ll (dual A).
Proof.
induction A as [ | | | | ? IHA1 ? IHA2 | ? IHA1 ? IHA2 |
                       | | ? IHA1 ? IHA2 | ? IHA1 ? IHA2 | ? IHA1 | ? IHA1 ]; cbn in *;
  rewrite ?IHA1, ?IHA2; reflexivity.
Qed.

Lemma nll2ll_map_wn l : map nll2ll (map wn l) = map formulas.wn (map nll2ll l).
Proof. induction l as [|? ? IHl]; [ | cbn in *; rewrite IHl ]; reflexivity. Qed.

Lemma nll2ll_map_wn_inv l1 l2 : map formulas.wn l1 = map nll2ll l2 ->
  { l2' | l2 = map wn l2' & l1 = map nll2ll l2' }.
Proof.
induction l1 as [|a l1 IHl1] in l2 |- *; intros Heq; destruct l2 as [|b l2];
  inversion Heq as [[Heqf Heq']].
- exists nil; reflexivity.
- apply IHl1 in Heq' as [l2' -> ->].
  destruct b as [ | | | | | | | | | | | b ]; inversion_clear Heqf.
  exists (b :: l2'); reflexivity.
Qed.

Lemma nll2llfrag l : ll l -> ll_fragments.ll_ll (map nll2ll l).
Proof.
intro pi. induction pi as [ | l1 l2 A B ? IH | | | A B l1 l2 ? IH1 ? IH2 | | | | | | | | | ];
  try (now constructor); cbn in *; rewrite ? map_app.
- apply (ll_def.ex_r _ _ IH).
  rewrite map_app. apply PermutationT_app_head, PermutationT_swap.
- apply (ll_def.tens_r IH2 IH1).
- rewrite nll2ll_map_wn. apply ll_def.oc_r.
  rewrite <- nll2ll_map_wn. assumption.
Qed.

Lemma llfrag2nll l : ll_fragments.ll_ll (map nll2ll l) -> ll l.
Proof.
intro pi. remember (map nll2ll l) as l0 eqn:Heql0.
induction pi as [ | l1 l2 pi1 IH1 HP | l1 lw lw' l2 pi1 IH1 HP | ? Hf | | l1 pi1 IH1
                | A B l1 l2 pi1 IH1 pi2 IH2 | A B l1 pi1 IH1 |
                | A B l1 pi1 IH1 | A B l1 pi1 IH1 | A B l1 pi1 IH1 pi2 IH2
                | A l1 pi1 IH1 | A l1 pi1 IH1 | A l1 pi1 IH1 | A l1 pi1 IH1 | ? Hf | Ha ]  in l, Heql0 |- *;
  subst;
  try discriminate Hf;
  try (destruct l as [|f l]; destr_eq Heql0; destruct f; destr_eq Heql0; subst;
       constructor; apply IH1; reflexivity).
- destruct l as [ | C [ | D [] ] ]; try discriminate Heql0. injection Heql0 as [= Heq1 Heq2].
  destruct C; destr_eq Heq1. destruct D; destr_eq Heq2. subst.
  apply ax_r.
- apply PermutationT_map_inv in HP as [l' Heq HP%PermutationT_sym]. rewrite <-HP.
  apply IH1, Heq.
- change map with List.map in Heql0.
  symmetry in Heql0. decomp_list_eq Heql0. subst. symmetry in Heq.
  apply nll2ll_map_wn_inv in Heq as [l -> ->].
  apply PermutationT_map_inv in HP as [l' -> HP].
  refine (@ex_PermutationT (l1 ++ map wn l' ++ l2) _ _ _).
  + symmetry. apply PermutationT_app_head, PermutationT_app_tail, PermutationT_map, HP.
  + apply IH1. rewrite <-nll2ll_map_wn, <-?map_app. reflexivity.
- destruct l as [ | C [] ]; destr_eq Heql0. destruct C; destr_eq Heql0.
  apply one_r.
- destruct l as [ | C l ]; inversion Heql0 as [[H1 H2]]. destruct C; inversion H1.
  change map with List.map in H2. symmetry in H2. decomp_list_eq H2. subst.
  apply tens_r; [ apply IH2 | apply IH1 ]; reflexivity.
- destruct l as [ | C l ]; inversion Heql0 as [[H1 ->]]. destruct C; inversion H1. subst.
  apply with_r; [ apply IH1 | apply IH2 ]; reflexivity.
- destruct l as [ | C l ]; inversion Heql0 as [[H1 H2]]. destruct C; inversion H1. subst.
  apply nll2ll_map_wn_inv in H2 as [l'' -> ->].
  apply oc_r, IH1.
  cbn. rewrite nll2ll_map_wn. reflexivity.
- destruct Ha.
Qed.

Lemma cut_r : cut_admissibility.
Proof.
intros A l1 l2 pi1%nll2llfrag pi2%nll2llfrag. apply llfrag2nll.
cbn in pi2. rewrite <-nll2ll_dual in pi2. rewrite map_app.
refine (ll_cut.cut_r_axfree _ pi2 pi1). intros [].
Qed.

Lemma cut_r_ext l1 A l2 : ll (l1 ++ A :: nil) -> ll (dual A :: l2) -> ll (l1 ++ l2).
Proof.
intros pi1%(ex_transp_middle2 nil) pi2.
replace (app l1 nil) with l1 in pi1 by apply app_nil_r_sym_inf.
apply (@cut_r A); assumption.
Qed.
