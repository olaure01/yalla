(* ll library for yalla *)


(** * Linear Logic with explicit permutations *)
(* not cuts here, see ll_cut.v for cut admissibility and ll_prop.v for other properties *)

Require Import CMorphisms.

Require Import Bool_more.
Require Import List_more.
Require Import List_Type_more.
Require Import Permutation_Type_more.
Require Import CyclicPerm_Type.
Require Import Permutation_Type_solve.
Require Import CPermutation_Type_solve.
Require Import genperm_Type.

Require Export basic_misc.
Require Export formulas.


(** ** Fragments for proofs *)

Definition NoAxioms := (existT (fun x => x -> list formula) _ Empty_fun).

(** Parameters for [ll] provability:
 - [pcut], [pmix0] and [pmix2] determine whether the corresponding rule is in the system or not;
 - [pperm] is [false] for exchange rule modulo cyclic permutations and [true] for exchange rule modulo arbitrary permutations;
 - [pgax] determines the sequents which are valid as axioms in proofs.
*)
Record pfrag := mk_pfrag {
  pcut : bool ;
  pgax : { ptypgax : Type & ptypgax -> list formula } ;
  pmix0 : bool ;
  pmix2 : bool ;
  pperm : bool }.

(** Order relation on proof fragments: [P] is more restrictive than [Q]. *)
Definition le_pfrag P Q :=
  prod
    (Bool.leb (pcut P) (pcut Q))
  (prod
    (forall a, { b | projT2 (pgax P) a = projT2 (pgax Q) b })
  (prod
    (Bool.leb (pmix0 P) (pmix0 Q))
  (prod
    (Bool.leb (pmix2 P) (pmix2 Q))
    (Bool.leb (pperm P) (pperm Q))))).

Lemma le_pfrag_trans : forall P Q R,
  le_pfrag P Q -> le_pfrag Q R -> le_pfrag P R.
Proof with myeeasy.
intros P Q R H1 H2.
unfold le_pfrag in H1.
destruct H1 as (Hc1 & Ha1 & H01 & H21 & Hp1).
unfold le_pfrag in H2.
destruct H2 as (Hc2 & Ha2 & H02 & H22 & Hp2).
nsplit 5 ; try (eapply leb_trans ; myeeasy).
intros a.
destruct (Ha1 a) as [b Heq].
destruct (Ha2 b) as [c Heq2].
exists c ; etransitivity...
Qed.

Instance le_pfrag_po : PreOrder le_pfrag.
Proof.
split.
- nsplit 5 ; try reflexivity.
  simpl ; intros a.
  exists a ; reflexivity.
- intros P Q R.
  apply le_pfrag_trans.
Qed.

(** Same proof fragment as [P] but with value [b] for [pcut]. *)
Definition cutupd_pfrag P b :=
  mk_pfrag b (pgax P) (pmix0 P) (pmix2 P) (pperm P).

Lemma cutupd_pfrag_true : forall P, le_pfrag P (cutupd_pfrag P true).
Proof.
intros P.
nsplit 5 ; try reflexivity.
- apply leb_true.
- intros a ; exists a ; reflexivity.
Qed.

(** Same proof fragment as [P] but with value [G] for [pgax]. *)
Definition axupd_pfrag P G :=
  mk_pfrag (pcut P) G (pmix0 P) (pmix2 P) (pperm P).

(** Same proof fragment as [P] but without the [cut] rule. *)
Definition cutrm_pfrag P := cutupd_pfrag P false.

Lemma cutrm_cutrm : forall P,
  cutrm_pfrag (cutrm_pfrag P) = cutrm_pfrag P.
Proof.
intros P.
unfold cutrm_pfrag ; unfold cutupd_pfrag.
reflexivity.
Qed.


(** ** Rules *)

(** The main predicate: [ll] proofs.

The [nat] parameter is a size of proofs.
Choices between [plus] and [max] in binary cases are determined by the behaviour in cut admissibility.

All rules have their main formula at first position in the conclusion.
 - [ax_r]: identity rule restricted to propositional variables (general case proved later)
 - [ex_r]: exchange rule (parametrized by [pperm P] to determine allowed permutations)
 - [ex_wn_r]: exchange rule between [wn] formulas
 - [mix0_r]: nullary linear mix rule (available only if [pmix0 P = true])
 - [mix2_r]: binary linear mix rule (the order of lists is matched with the [tens_r] case) (available only if [pmix2 P = true])
 - [one_r]: one rule
 - [bot_r]: bot rule
 - [tens_r]: tensor rule (the order of lists is imposed by the cyclic permutation case)
 - [parr_r]: par rule
 - [top_r]: par rule
 - [plus_r1]: plus left rule
 - [plus_r2]: plus right rule
 - [with_r]: with rule
 - [oc_r]: promotion rule (standard shape)
 - [de_r]: dereliction rule
 - [wk_r]: weakening rule
 - [co_r]: contraction rule with [wn] context inserted between principal formulas to be general enough in the cyclic permutation case
 - [cut_r]: cut rule (the order of lists is matched with the [tens_r] case) (available only if [pcut P = true])
 - [gax_r]: generic axiom rule (parametrized by the predicate [pgax P] over sequents)
*)
Inductive ll P : list formula -> Type :=
| ax_r : forall X, ll P (covar X :: var X :: nil)
| ex_r : forall l1 l2, ll P l1 -> PCperm_Type (pperm P) l1 l2 -> ll P l2
| ex_wn_r : forall l1 lw lw' l2, ll P (l1 ++ map wn lw ++ l2) ->
               Permutation_Type lw lw' -> ll P (l1 ++ map wn lw' ++ l2)
| mix0_r {f : pmix0 P = true} : ll P nil
| mix2_r {f : pmix2 P = true} : forall l1 l2, ll P l1 -> ll P l2 ->
                         ll P (l2 ++ l1)
| one_r : ll P (one :: nil)
| bot_r : forall l, ll P l -> ll P (bot :: l)
| tens_r : forall A B l1 l2, ll P (A :: l1) -> ll P (B :: l2) ->
                                   ll P (tens A B :: l2 ++ l1)
| parr_r : forall A B l, ll P (A :: B :: l) -> ll P (parr A B :: l)
| top_r : forall l, ll P (top :: l)
| plus_r1 : forall A B l, ll P (A :: l) -> ll P (aplus A B :: l)
| plus_r2 : forall A B l, ll P (A :: l) -> ll P (aplus B A :: l)
| with_r : forall A B l, ll P (A :: l) -> ll P (B :: l) ->
                               ll P (awith A B :: l)
| oc_r : forall A l, ll P (A :: map wn l) -> ll P (oc A :: map wn l)
| de_r : forall A l, ll P (A :: l) -> ll P (wn A :: l)
| wk_r : forall A l, ll P l -> ll P (wn A :: l)
| co_r : forall A l, ll P (wn A :: wn A :: l) -> ll P (wn A :: l)
| cut_r {f : pcut P = true} : forall A l1 l2,
    ll P (dual A :: l1) -> ll P (A :: l2) -> ll P (l2 ++ l1)
| gax_r : forall a, ll P (projT2 (pgax P) a).

Instance ll_perm {P} : Proper ((@PCperm_Type _ (pperm P)) ==> Basics.arrow) (ll P).
Proof.
intros l1 l2 HP pi ; eapply ex_r ; eassumption.
Qed.

Fixpoint psize {P l} (pi : ll P l) :=
match pi with
| ax_r _ _ => 1
| ex_r _ _ _ pi0 _ => S (psize pi0)
| ex_wn_r _ _ _ _ _ pi0 _ => S (psize pi0)
| mix0_r _ => 1
| mix2_r _ _ _ pi1 pi2 => S (psize pi1 + psize pi2)
| one_r _ => 1
| bot_r _ _ pi0 => S (psize pi0)
| tens_r _ _ _ _ _ pi1 pi2 => S (psize pi1 + psize pi2)
| parr_r _ _ _ _ pi0 => S (psize pi0)
| top_r _ _ => 1
| plus_r1 _ _ _ _ pi0 => S (psize pi0)
| plus_r2 _ _ _ _ pi0 => S (psize pi0)
| with_r _ _ _ _ pi1 pi2 => S (max (psize pi1) (psize pi2))
| oc_r _ _ _ pi0 => S (psize pi0)
| de_r _ _ _ pi0 => S (psize pi0)
| wk_r _ _ _ pi0 => S (psize pi0)
| co_r _ _ _ pi0 => S (psize pi0)
| cut_r _ _ _ _ pi1 pi2 => S (psize pi1 + psize pi2)
| gax_r _ _ => 1
end.

Lemma psize_pos P : forall l (pi : @ll P l), 0 < psize pi.
Proof.
intros l pi ; induction pi ; simpl ; myeasy.
Qed.

(** List of the elements of [pgax P] used in [pi] *)
Fixpoint gax_elts {P l} (pi : ll P l) :=
match pi with
| ax_r _ _ => nil
| ex_r _ _ _ pi0 _ => gax_elts pi0
| ex_wn_r _ _ _ _ _ pi0 _ => gax_elts pi0
| mix0_r _ => nil
| mix2_r _ _ _ pi1 pi2 => (gax_elts pi1) ++ (gax_elts pi2)
| one_r _ => nil
| bot_r _ _ pi0 => gax_elts pi0
| tens_r _ _ _ _ _ pi1 pi2 => (gax_elts pi1) ++ (gax_elts pi2)
| parr_r _ _ _ _ pi0 => gax_elts pi0
| top_r _ _ => nil
| plus_r1 _ _ _ _ pi0 => gax_elts pi0
| plus_r2 _ _ _ _ pi0 => gax_elts pi0
| with_r _ _ _ _ pi1 pi2 => (gax_elts pi1) ++ (gax_elts pi2)
| oc_r _ _ _ pi0 => gax_elts pi0
| de_r _ _ _ pi0 => gax_elts pi0
| wk_r _ _ _ pi0 => gax_elts pi0
| co_r _ _ _ pi0 => gax_elts pi0
| cut_r _ _ _ _ pi1 pi2 => (gax_elts pi1) ++ (gax_elts pi2)
| gax_r _ a => a :: nil
end.

Lemma stronger_pfrag P Q : le_pfrag P Q -> forall l, ll P l -> ll Q l.
Proof with myeeasy.
intros Hle l H.
induction H ; try (constructor ; myeasy ; fail).
- apply (ex_r _ l1)...
  destruct Hle as (_ & _ & _ & _ & Hp).
  unfold PCperm_Type in p.
  unfold PCperm_Type.
  destruct (pperm P) ; destruct (pperm Q) ;
    simpl in Hp ; try inversion Hp...
  apply cperm_perm_Type...
- apply (ex_wn_r _ l1 lw)...
- unfold le_pfrag in Hle.
  rewrite f in Hle.
  destruct Hle as (_ & _ & Hmix0 & _).
  simpl in Hmix0...
  apply (@mix0_r _ Hmix0).
- unfold le_pfrag in Hle.
  rewrite f in Hle.
  destruct Hle as (_ & _ & _ & Hmix2 & _).
  simpl in Hmix2...
  apply (@mix2_r _ Hmix2)...
- unfold le_pfrag in Hle.
  destruct Hle as [Hcut _].
  rewrite f in Hcut.
  simpl in Hcut...
  eapply (@cut_r _ Hcut)...
- destruct Hle as (_ & Hgax & _).
  destruct (Hgax a) as [b Heq].
  rewrite Heq.
  apply gax_r.
Qed.

(** *** Variants of rules *)

(** Weakening on a list of formulas *)
Lemma wk_list_r {P} : forall l l', ll P l' -> ll P (map wn l ++ l').
Proof with myeeasy.
induction l ; intros l' H...
apply IHl in H.
apply wk_r...
Qed.

(** Contraction on a list of formulas *)
Lemma co_list_r {P} : forall l l',
  ll P (map wn l ++ map wn l ++ l') -> ll P (map wn l ++ l').
Proof with myeeasy.
induction l ; intros l' pi...
rewrite <- app_nil_l.
apply (ex_wn_r _ _ (l ++ a :: nil)) ; [ | perm_Type_solve ].
list_simpl ; apply IHl.
cons2app ; rewrite 2 app_assoc.
replace ((map wn l ++ map wn l) ++ wn a :: nil)
  with (nil ++ map wn (l ++ l ++ a :: nil))
  by (list_simpl ; reflexivity).
rewrite <- app_assoc.
apply (ex_wn_r _ _ (a :: l ++ l)) ; [ | perm_Type_solve ].
list_simpl.
apply co_r.
rewrite 2 app_comm_cons ; rewrite app_assoc.
replace ((wn a :: wn a :: map wn l) ++ map wn l)
   with (map wn (a :: a :: l ++ l))
   by (list_simpl ; reflexivity).
rewrite <- app_nil_l.
rewrite app_assoc in pi.
replace (map wn (a :: l) ++ (map wn (a :: l)))
  with (map wn (a :: l ++ a :: l))
  in pi by (list_simpl ; reflexivity).
rewrite <- app_nil_l in pi.
eapply ex_wn_r ; [ eassumption | perm_Type_solve ].
Qed.


(** *** Some tactics for manipulating rules *)

Ltac destruct_ll H f X l Hl Hr HP a :=
  match type of H with
  | ll _ _ => destruct H as [ X
                            | l ? Hl HP
                            | l ? ? ? Hl HP
                            | f
                            | f ? ? Hl Hr
                            | 
                            | ? Hl
                            | ? ? ? ? Hl Hr
                            | ? ? ? Hl
                            | l
                            | ? ? ? Hl
                            | ? ? ? Hl
                            | ? ? ? Hl Hr
                            | ? ? Hl
                            | ? ? Hl
                            | ? ? Hl
                            | ? ? Hl
                            | f ? ? ? Hl Hr
                            | a ] ; subst
  end.

Ltac ll_swap :=
  match goal with
  | |- ll ?P (?a1 :: ?a2 :: nil) => eapply ex_r ; [ | apply PCperm_Type_swap ]
  end.
Ltac ll_swap_hyp H :=
  match goal with
  | H : ll ?P (?a1 :: ?a2 :: nil) |- _ =>
        eapply ex_r in H ;[ | apply PCperm_Type_swap ]
  end.
Tactic Notation "ll_swap" "in" hyp(H) := ll_swap_hyp H.


(** ** Some reversibility statements *)

Lemma bot_rev {P} : (forall a, In bot (projT2 (pgax P) a) -> False) ->
  forall l1 l2, ll P (l1 ++ bot :: l2) -> ll P (l1 ++ l2).
Proof with myeeasy.
intros Hgax l1 l2 pi.
remember (l1 ++ bot :: l2) as l ; revert l1 l2 Heql.
induction pi ; intros l1' l2' Heq ; subst.
- exfalso.
  destruct l1' ; inversion Heq.
  destruct l1' ; inversion H1.
  destruct l1' ; inversion H3.
- apply PCperm_Type_vs_elt_inv in p.
  destruct p as [(l3 & l4) Heq HP'].
  simpl in HP' ; simpl in Heq.
  apply IHpi in Heq...
  eapply ex_r...
  apply PEperm_PCperm_Type in HP' ; unfold id in HP'.
  apply PCperm_Type_sym.
  eapply PCperm_Type_trans ; [ apply PCperm_Type_app_comm | ].
  eapply PCperm_Type_trans ; [ apply HP' | ].
  apply PCperm_Type_app_comm.
- dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_assoc.
    eapply ex_wn_r...
    list_simpl ; apply IHpi ; list_simpl...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * exfalso.
      decomp_map Heq0 ; inversion Heq0.
    * list_simpl ; eapply ex_wn_r...
      rewrite 2 app_assoc.
      apply IHpi ; list_simpl...
- destruct l1' ; inversion Heq.
- dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_assoc ; apply mix2_r...
    apply IHpi2...
  + rewrite <- app_assoc ; apply mix2_r...
    apply IHpi1...
- exfalso.
  destruct l1' ; inversion Heq.
  destruct l1' ; inversion H1.
- destruct l1' ; inversion Heq ; subst...
  list_simpl ; eapply bot_r.
  apply IHpi...
- rewrite app_comm_cons in Heq ; dichot_Type_elt_app_exec Heq ; subst.
  + destruct l1' ; inversion Heq0 ; subst.
    list_simpl.
    rewrite app_assoc ; apply tens_r...
    rewrite app_comm_cons.
    apply IHpi2...
  + list_simpl.
    apply tens_r...
    rewrite app_comm_cons.
    apply IHpi1...
- destruct l1' ; inversion Heq ; subst.
  rewrite 2 app_comm_cons in IHpi.
  list_simpl ; eapply parr_r...
  rewrite 2 app_comm_cons.
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; apply top_r...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply plus_r1...
  rewrite app_comm_cons.
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply plus_r2...
  rewrite app_comm_cons.
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply with_r...
  + rewrite app_comm_cons.
    apply IHpi1...
  + rewrite app_comm_cons.
    apply IHpi2...
- exfalso.
  destruct l1' ; inversion Heq.
  symmetry in H1.
  decomp_map H1.
  inversion H1.
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply de_r...
  rewrite app_comm_cons.
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply wk_r...
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; apply co_r.
  rewrite 2 app_comm_cons.
  apply IHpi...
- dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_assoc ; eapply cut_r...
    rewrite app_comm_cons.
    eapply IHpi2...
  + rewrite <- app_assoc ; eapply cut_r...
    rewrite app_comm_cons.
    eapply IHpi1...
- exfalso.
  apply (Hgax a) ; rewrite Heq.
  apply in_elt.
Qed.

Lemma parr_rev {P} : (forall a A B, In (parr A B) (projT2 (pgax P) a) -> False) ->
  forall A B l1 l2, ll P (l1 ++ parr A B :: l2) -> ll P (l1 ++ A :: B :: l2).
Proof with myeeasy.
intros Hgax A B l1 l2 pi.
remember (l1 ++ parr A B :: l2) as l.
revert A B l1 l2 Heql.
induction pi ; intros A' B' l1' l2' Heq ; subst.
- exfalso.
  destruct l1' ; inversion Heq.
  destruct l1' ; inversion H1.
  destruct l1' ; inversion H3.
- apply PCperm_Type_vs_elt_inv in p.
  destruct p as [(l3 & l4) Heq HP'].
  simpl in HP'.
  apply IHpi in Heq...
  eapply ex_r...
  destruct (pperm P) ; simpl in HP' ; simpl.
  + apply Permutation_Type_sym.
    eapply Permutation_Type_trans ; [ apply Permutation_Type_app_comm | ].
    eapply Permutation_Type_trans ; [ | apply Permutation_Type_app_comm ].
    perm_Type_solve.
  + eapply cperm_Type_trans ; [ apply cperm_Type | ].
    list_simpl ; rewrite <- HP' ; cperm_Type_solve.
- dichot_Type_elt_app_exec Heq ; subst.
  + rewrite 2 app_comm_cons ; rewrite app_assoc.
    eapply ex_wn_r...
    list_simpl ; apply IHpi ; list_simpl...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * exfalso.
      decomp_map Heq0 ; inversion Heq0.
    * list_simpl ; eapply ex_wn_r...
      rewrite 2 app_assoc.
      apply IHpi ; list_simpl...
- destruct l1' ; inversion Heq.
- dichot_Type_elt_app_exec Heq ; subst.
  + rewrite 2 app_comm_cons ; rewrite app_assoc ; apply mix2_r...
    apply IHpi2...
  + rewrite <- app_assoc ; apply mix2_r...
    apply IHpi1...
- exfalso.
  destruct l1' ; inversion Heq.
  destruct l1' ; inversion H1.
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply bot_r...
  apply IHpi...
- rewrite app_comm_cons in Heq ; dichot_Type_elt_app_exec Heq ; subst.
  + destruct l1' ; inversion Heq0 ; subst.
    rewrite 2 app_comm_cons ; rewrite app_assoc ; apply tens_r...
    rewrite app_comm_cons.
    apply IHpi2...
  + rewrite <- app_assoc ; apply tens_r...
    rewrite app_comm_cons ; apply IHpi1...
- destruct l1' ; inversion Heq ; subst...
  list_simpl ; eapply parr_r...
  rewrite 2 app_comm_cons.
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; apply top_r...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply plus_r1...
  rewrite app_comm_cons.
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply plus_r2...
  rewrite app_comm_cons.
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply with_r...
  + rewrite app_comm_cons.
    apply IHpi1...
  + rewrite app_comm_cons.
    apply IHpi2...
- exfalso.
  destruct l1' ; inversion Heq.
  symmetry in H1.
  decomp_map H1.
  inversion H1.
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply de_r...
  rewrite app_comm_cons.
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply wk_r...
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply co_r...
    rewrite 2 app_comm_cons ; apply IHpi ; list_simpl...
- dichot_Type_elt_app_exec Heq ; subst.
  + rewrite 2 app_comm_cons ; rewrite app_assoc ; eapply cut_r...
    rewrite app_comm_cons ; apply IHpi2...
  + rewrite <- app_assoc ; eapply cut_r...
    rewrite app_comm_cons ; apply IHpi1...
- exfalso.
  apply (Hgax a A' B') ; rewrite Heq.
  apply in_elt.
Qed.

Lemma one_rev {P} : (forall a, In one (projT2 (pgax P) a) -> False) ->
  forall l0, ll P l0 -> forall l1 l2, ll P (l1 ++ one :: l2) ->
  ll P (l1 ++ l0 ++ l2).
Proof with myeeasy.
intros Hgax l0 pi0 l1 l2 pi.
remember (l1 ++ one :: l2) as l.
revert l1 l2 Heql.
induction pi ; intros l1' l2' Heq ; subst.
- exfalso.
  destruct l1' ; inversion Heq.
  destruct l1' ; inversion H1.
  destruct l1' ; inversion H3.
- apply PCperm_Type_vs_elt_inv in p.
  destruct p as [(l3 & l4) Heq HP'].
  simpl in HP' ; apply IHpi in Heq...
  eapply ex_r...
  destruct (pperm P) ; simpl in HP' ; simpl.
  + apply Permutation_Type_sym.
    eapply Permutation_Type_trans ; [ apply Permutation_Type_app_comm | ].
    eapply Permutation_Type_trans ; [ | apply Permutation_Type_app_comm ].
    perm_Type_solve.
  + eapply cperm_Type_trans ; [ apply cperm_Type | ].
    list_simpl ; rewrite <- HP' ; cperm_Type_solve.
- dichot_Type_elt_app_exec Heq ; subst.
  + rewrite 2 app_assoc.
    eapply ex_wn_r...
    list_simpl ; apply IHpi ; list_simpl...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * exfalso.
      decomp_map Heq0 ; inversion Heq0.
    * list_simpl ; eapply ex_wn_r...
      rewrite 2 app_assoc.
      apply IHpi ; list_simpl...
- destruct l1' ; inversion Heq.
- dichot_Type_elt_app_exec Heq ; subst.
  + rewrite 2 app_assoc ; apply mix2_r...
    list_simpl ; apply IHpi2...
  + rewrite <- app_assoc ; apply mix2_r...
    apply IHpi1...
- destruct l1' ; inversion Heq ; subst.
  + list_simpl...
  + destruct l1' ; inversion H1.
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply bot_r...
  apply IHpi...
- rewrite app_comm_cons in Heq ; dichot_Type_elt_app_exec Heq ; subst.
  + destruct l1' ; inversion Heq0 ; subst.
    rewrite <- app_comm_cons ; rewrite 2 app_assoc ; apply tens_r...
    list_simpl ; rewrite app_comm_cons ; apply IHpi2...
  + rewrite <- app_assoc ; apply tens_r...
    rewrite app_comm_cons ; apply IHpi1...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply parr_r...
  rewrite 2 app_comm_cons ; apply IHpi...
- destruct l1' ; inversion Heq ; subst.
   list_simpl ; apply top_r...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply plus_r1...
  rewrite app_comm_cons.
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply plus_r2...
  rewrite app_comm_cons.
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply with_r...
  + rewrite app_comm_cons.
    apply IHpi1...
  + rewrite app_comm_cons.
    apply IHpi2...
- exfalso.
  destruct l1' ; inversion Heq.
  symmetry in H1.
  decomp_map H1.
  inversion H1.
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply de_r...
  rewrite app_comm_cons.
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply wk_r...
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply co_r...
  rewrite 2 app_comm_cons ; apply IHpi ; list_simpl...
- dichot_Type_elt_app_exec Heq ; subst.
  + rewrite 2 app_assoc ; eapply cut_r...
    list_simpl ; rewrite app_comm_cons ; apply IHpi2...
  + rewrite <- app_assoc ; eapply cut_r...
    rewrite app_comm_cons ; apply IHpi1...
- exfalso.
  apply (Hgax a) ; rewrite Heq.
  apply in_elt.
Qed.

Lemma tens_one_rev {P} :
(forall a, In one (projT2 (pgax P) a) -> False) ->
(forall a A, In (tens one A) (projT2 (pgax P) a) -> False) ->
  forall A l1 l2, ll P (l1 ++ tens one A :: l2) -> ll P (l1 ++ A :: l2).
Proof with myeeasy.
intros Hgax1 Hgaxt A l1 l2 pi.
remember (l1 ++ tens one A :: l2) as l.
revert A l1 l2 Heql.
induction pi ; intros A' l1' l2' Heq ; subst.
- exfalso.
  destruct l1' ; inversion Heq.
  destruct l1' ; inversion H1.
  destruct l1' ; inversion H3.
- apply PCperm_Type_vs_elt_inv in p.
  destruct p as [(l3 & l4) Heq HP'].
  simpl in HP' ; apply IHpi in Heq...
  simpl in Heq ; eapply ex_r...
  destruct (pperm P) ; simpl in HP' ; simpl.
  + apply Permutation_Type_sym.
    eapply Permutation_Type_trans ; [ apply Permutation_Type_app_comm | ].
    eapply Permutation_Type_trans ; [ | apply Permutation_Type_app_comm ].
    perm_Type_solve.
  + eapply cperm_Type_trans ; [ apply cperm_Type | ].
    list_simpl ; rewrite <- HP' ; cperm_Type_solve.
- dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_comm_cons ; rewrite app_assoc.
    eapply ex_wn_r...
    list_simpl ; apply IHpi ; list_simpl...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * exfalso.
      decomp_map Heq0 ; inversion Heq0.
    * list_simpl ; eapply ex_wn_r...
      rewrite 2 app_assoc.
      apply IHpi ; list_simpl...
- destruct l1' ; inversion Heq.
- dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_comm_cons ; rewrite app_assoc ; apply mix2_r...
    list_simpl ; apply IHpi2...
  + rewrite <- app_assoc ; apply mix2_r...
    apply IHpi1...
- destruct l1' ; inversion Heq ; subst.
  destruct l1' ; inversion H1.
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply bot_r...
  apply IHpi...
- rewrite app_comm_cons in Heq ; dichot_Type_elt_app_exec Heq ; subst.
  + destruct l1' ; inversion Heq0 ; subst.
    * rewrite <- (app_nil_l _) in pi1 ; eapply (one_rev Hgax1 _ pi2) in pi1...
    * rewrite <- app_comm_cons ; rewrite (app_comm_cons l) ; rewrite app_assoc ; apply tens_r...
      rewrite app_comm_cons ; apply IHpi2...
  + rewrite <- app_assoc ; apply tens_r...
    rewrite app_comm_cons ; apply IHpi1...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply parr_r...
  rewrite 2 app_comm_cons ; apply IHpi...
- destruct l1' ; inversion Heq ; subst.
   list_simpl ; apply top_r...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply plus_r1...
  rewrite app_comm_cons.
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply plus_r2...
  rewrite app_comm_cons.
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply with_r...
  + rewrite app_comm_cons.
    apply IHpi1...
  + rewrite app_comm_cons.
    apply IHpi2...
- exfalso.
  destruct l1' ; inversion Heq.
  symmetry in H1.
  decomp_map H1.
  inversion H1.
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply de_r...
  rewrite app_comm_cons.
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply wk_r...
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply co_r...
  rewrite 2 app_comm_cons ; apply IHpi ; list_simpl...
- dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_comm_cons ; rewrite app_assoc ; eapply cut_r...
    list_simpl ; rewrite app_comm_cons ; apply IHpi2...
  + rewrite <- app_assoc ; eapply cut_r...
    rewrite app_comm_cons ; apply IHpi1...
- exfalso.
  apply (Hgaxt a A') ; rewrite Heq.
  apply in_elt.
Qed.

Lemma tens_rev {P} : (forall a A B, projT2 (pgax P) a = tens A B :: nil -> False) ->
  pcut P = false -> forall A B,
  ll P (tens A B :: nil) -> prod (ll P (A :: nil)) (ll P (B :: nil)).
Proof with myeeasy.
intros Hgax Hcut A B pi.
remember (tens A B :: nil) as l ; revert A B Heql ;
  induction pi ; intros A' B' Heq ; subst ;
  try (now inversion Heq).
- apply PCperm_Type_sym in p.
  apply PCperm_Type_length_1_inv in p ; subst.
  apply IHpi...
- destruct l1 ; inversion Heq.
  + destruct lw' ; inversion H0 ; list_simpl in H0.
    symmetry in p ; apply Permutation_Type_nil in p ; subst.
    apply IHpi...
  + apply app_eq_nil in H1 ; destruct H1 ; subst.
    apply app_eq_nil in H1 ; destruct H1 ; subst.
    destruct lw' ; inversion H.
    symmetry in p ; apply Permutation_Type_nil in p ; subst.
    apply IHpi...
- destruct l2 ; inversion Heq.
  + destruct l1 ; inversion Heq ; subst.
    apply IHpi1...
  + apply app_eq_nil in H1 ; destruct H1 ; subst.
    apply IHpi2...
- inversion Heq.
  apply app_eq_nil in H2 ; destruct H2 ; subst.
  constructor...
- rewrite Hcut in f ; inversion f.
- exfalso.
  apply (Hgax a A' B')...
Qed.

Lemma plus_rev {P} : (forall a A B, projT2 (pgax P) a = aplus A B :: nil -> False) ->
  pcut P = false -> forall A B,
  ll P (aplus A B :: nil) -> sum (ll P (A :: nil)) (ll P (B :: nil)).
Proof with myeeasy.
intros Hgax Hcut A B pi.
remember (aplus A B :: nil) as l ; revert A B Heql ;
  induction pi ; intros A' B' Heq ; subst ;
  try (now inversion Heq).
- apply PCperm_Type_sym in p.
  apply PCperm_Type_length_1_inv in p ; subst.
  apply IHpi...
- destruct l1 ; inversion Heq.
  + destruct lw' ; inversion H0 ; list_simpl in H0.
    symmetry in p ; apply Permutation_Type_nil in p ; subst.
    apply IHpi...
  + apply app_eq_nil in H1 ; destruct H1 ; subst.
    apply app_eq_nil in H1 ; destruct H1 ; subst.
    destruct lw' ; inversion H.
    symmetry in p ; apply Permutation_Type_nil in p ; subst.
    apply IHpi...
- destruct l2 ; inversion Heq.
  + destruct l1 ; inversion Heq ; subst.
    apply IHpi1...
  + apply app_eq_nil in H1 ; destruct H1 ; subst.
    apply IHpi2...
- inversion Heq ; subst.
  left...
- inversion Heq ; subst.
  right...
- rewrite Hcut in f ; inversion f.
- exfalso.
  apply (Hgax a A' B')...
Qed.


(** *** Tensor-One Par-Bottom simplifications *)

Inductive munit_smp : formula -> formula -> Type :=
| musmp_var : forall X, munit_smp (var X) (var X)
| musmp_covar : forall X, munit_smp (covar X) (covar X)
| musmp_one : munit_smp one one
| musmp_bot : munit_smp bot bot
| musmp_tens : forall A1 A2 B1 B2, munit_smp A1 B1 -> munit_smp A2 B2 ->
                 munit_smp (tens A1 A2) (tens B1 B2)
| musmp_parr : forall A1 A2 B1 B2, munit_smp A1 B1 -> munit_smp A2 B2 ->
                 munit_smp (parr A1 A2) (parr B1 B2)
| musmp_zero : munit_smp zero zero
| musmp_top : munit_smp top top
| musmp_plus : forall A1 A2 B1 B2, munit_smp A1 B1 -> munit_smp A2 B2 ->
                 munit_smp (aplus A1 A2) (aplus B1 B2)
| musmp_with : forall A1 A2 B1 B2, munit_smp A1 B1 -> munit_smp A2 B2 ->
                 munit_smp (awith A1 A2) (awith B1 B2)
| musmp_oc : forall A B, munit_smp A B -> munit_smp (oc A) (oc B)
| musmp_wn : forall A B, munit_smp A B -> munit_smp (wn A) (wn B)
| musmp_to : forall A B, munit_smp A B -> munit_smp (tens one A) B
| musmp_pb : forall A B, munit_smp A B -> munit_smp (parr A bot) B.

Lemma munit_smp_id : forall A, munit_smp A A.
Proof.
induction A ; constructor ; assumption.
Qed.

Lemma munit_smp_map_wn : forall l1 l2, Forall2_Type munit_smp (map wn l1) l2 ->
  { l : _ & l2 = map wn l & Forall2_Type munit_smp l1 l }.
Proof.
induction l1 ; intros l2 HF ; inversion HF ; subst.
- exists nil ; constructor.
- inversion H1 ; subst.
  apply IHl1 in H3.
  destruct H3 as [ l'' Heq HF' ] ; subst.
  exists (B :: l'') ; constructor ; assumption.
Qed.

Lemma munit_elim {P} : (forall a, Forall atomic (projT2 (pgax P) a)) ->
  forall l1, ll P l1 -> forall l2, Forall2_Type munit_smp l1 l2 -> ll P l2.
Proof with try eassumption.
intros Hgax l1 pi ; induction pi ; intros l2' HF ;
  try now (inversion HF ; subst ;
           inversion H1 ; subst ;
           constructor ; apply IHpi ; try eassumption ;
           constructor ; eassumption).
- inversion HF as [ | C D lc ld Hc' HF'] ; subst.
  inversion HF' as [ | C' D' lc' ld' Hc'' HF''] ; subst.
  inversion HF'' ; subst.
  inversion Hc' ; subst.
  inversion Hc'' ; subst.
  apply ax_r.
- symmetry in p.
  eapply PCperm_Type_Forall2 in p as [la HP] ; [ | eassumption ].
  symmetry in HP.
  eapply ex_r ; [ | apply HP ].
  apply IHpi ; assumption.
- apply Forall2_Type_app_inv_l in HF as ([ l' HF1 HF2 ] & Heq) ;
    simpl in Heq ; subst.
  apply Forall2_Type_app_inv_l in HF2 as ([ l'' HF2 HF3 ] & Heq) ;
    simpl in Heq ; rewrite Heq ; clear Heq.
  assert (HF4 := HF2).
  apply munit_smp_map_wn in HF2 as [ l''' Heq HF2 ] ; rewrite_all Heq ; clear Heq.
  symmetry in p.
  apply (Permutation_Type_map wn) in p.
  eapply Permutation_Type_Forall2 in p as [la HP] ; [ | eassumption ].
  symmetry in HP.
  apply Permutation_Type_map_inv in HP ; destruct HP as [lb Heq HP] ; subst.
  symmetry in HP.
  eapply ex_wn_r ; [ | apply HP ].
  apply IHpi.
  repeat apply Forall2_Type_app...
- inversion HF ; subst.
  constructor...
- apply Forall2_Type_app_inv_l in HF as ([ l' HF2 HF1 ] & Heq) ;
    simpl in Heq ; subst.
  constructor ; [ | apply IHpi1 | apply IHpi2 ]...
- inversion HF ; subst.
  inversion H1 ; inversion H3 ; subst.
  constructor.
- inversion HF ; subst.
  apply Forall2_Type_app_inv_l in H3 as ([ (l2' & l1') HF2 HF1 ] & Heq) ;
    simpl in Heq ; subst ; simpl in HF1 ; simpl in HF2.
  inversion H1 ; subst.
  + constructor ; [ apply IHpi1 | apply IHpi2 ] ; constructor...
  + apply (Forall2_Type_cons one one) in HF1 ; [ | constructor ].
    apply IHpi1 in HF1.
    apply (Forall2_Type_cons B y) in HF2...
    apply IHpi2 in HF2.
    assert (forall a, In one (projT2 (pgax P) a) -> False) as Hgax1.
    { intros a Hone.
      apply (Forall_In _ _ _ (Hgax a)) in Hone.
      inversion Hone. }
    rewrite <- (app_nil_l _) in HF1 ; eapply (one_rev Hgax1 _ HF2) in HF1...
- inversion HF ; subst.
  inversion H1 ; subst.
  + constructor ; apply IHpi ; constructor ; try constructor...
  + apply (Forall2_Type_cons bot bot) in H3 ; [ | constructor ].
    apply (Forall2_Type_cons A y) in H3...
    apply IHpi in H3.
    rewrite <- (app_nil_l l') ; rewrite app_comm_cons.
    eapply bot_rev...
    intros a Hbot.
    apply (Forall_In _ _ _ (Hgax a)) in Hbot.
    inversion Hbot.
- inversion HF ; subst.
  inversion H1 ; subst.
  constructor ; [ apply IHpi1 | apply IHpi2 ] ; constructor...
- inversion HF ; subst.
  inversion H1 ; subst.
  assert (HF' := H3).
  apply munit_smp_map_wn in H3 as [ l'' Heq HF'' ] ; subst.
  constructor ; apply IHpi ; constructor...
- apply Forall2_Type_app_inv_l in HF as ([ l' HF2 HF1 ] & Heq) ;
    simpl in Heq ; subst.
  eapply cut_r ; [ assumption | apply IHpi1 | apply IHpi2 ] ;
    (apply Forall2_Type_cons ; [ apply munit_smp_id | ])...
- specialize Hgax with a.
  assert (projT2 (pgax P) a = l2') as Heq ; subst.
  { remember (projT2 (pgax P) a) as l.
    revert l2' Hgax HF ; clear.
    induction l ; intros l2 Hgax HF ; inversion HF ; subst ; f_equal.
    - inversion Hgax ; subst.
      destruct a ; inversion H2 ; inversion H1 ; subst ; reflexivity.
    - inversion Hgax ; subst.
      apply IHl... }
  constructor.
Qed.


(** ** Properties on axioms *)

(** Axiom expansion *)
Lemma ax_exp {P} : forall A, ll P (A :: dual A :: nil).
Proof with myeeasy.
induction A ; simpl.
- ll_swap.
  apply ax_r.
- apply ax_r.
- ll_swap.
  apply bot_r.
  apply one_r.
- apply bot_r.
  apply one_r.
- ll_swap.
  apply parr_r.
  cons2app ; eapply ex_r ; [ | apply PCperm_Type_app_rot ].
  rewrite app_assoc.
  apply tens_r...
- apply parr_r.
  ll_swap in IHA1.
  ll_swap in IHA2.
  cons2app ; eapply ex_r ; [ | apply PCperm_Type_app_rot ].
  rewrite app_assoc.
  apply tens_r...
- ll_swap.
  apply top_r.
- apply top_r.
- eapply plus_r1 in IHA1.
  ll_swap in IHA1.
  eapply plus_r2 in IHA2.
  ll_swap in IHA2.
  ll_swap.
  apply with_r...
- apply with_r ; ll_swap.
  + apply plus_r1 ; ll_swap...
  + apply plus_r2 ; ll_swap...
- change (oc A :: wn (dual A) :: nil)
    with (oc A :: map wn (dual A :: nil)).
  apply oc_r.
  ll_swap in IHA.
  list_simpl ; ll_swap.
  apply de_r...
- apply de_r in IHA.
  ll_swap in IHA.
  ll_swap.
  change (oc (dual A) :: wn A :: nil)
    with (oc (dual A) :: map wn (A :: nil)).
  apply oc_r...
Qed.

Lemma ax_gen_loc : forall P Q l, Bool.leb (pperm P) (pperm Q) ->
  Bool.leb (pmix0 P) (pmix0 Q) ->
  Bool.leb (pmix2 P) (pmix2 Q) ->
  Bool.leb (pcut P) (pcut Q) ->
  forall pi : ll P l,
  Forall_Type (fun a => ll Q (projT2 (pgax P) a)) (gax_elts pi) ->
  ll Q l.
Proof with myeeasy.
intros P Q l Hperm Hmix0 Hmix2 Hcut pi.
induction pi ; simpl ; intros Hgax ;
  try (destruct (Forall_Type_app_inv _ _ _ Hgax) as [Hgax1 Hgax2]) ;
  try (apply IHpi1 in Hgax1) ;
  try (apply IHpi2 in Hgax2) ;
  try (constructor ; intuition ; fail).
- apply IHpi in Hgax.
  eapply ex_r...
  destruct (pperm P) ; destruct (pperm Q) ; inversion Hperm ; simpl ; simpl in p...
  apply cperm_perm_Type...
- apply IHpi in Hgax.
  eapply ex_wn_r...
- apply mix0_r.
  rewrite f in Hmix0 ; destruct (pmix0 Q) ; inversion Hmix0 ; simpl...
- apply mix2_r...
  rewrite f in Hmix2 ; destruct (pmix2 Q) ; inversion Hmix2 ; simpl...
- eapply cut_r...
  rewrite f in Hcut ; destruct (pcut Q) ; inversion Hcut ; simpl...
- inversion Hgax ; subst...
Qed.

Lemma ax_gen : forall P Q l, Bool.leb (pperm P) (pperm Q) ->
  Bool.leb (pmix0 P) (pmix0 Q) ->
  Bool.leb (pmix2 P) (pmix2 Q) ->
  Bool.leb (pcut P) (pcut Q) ->
  (forall a, ll Q (projT2 (pgax P) a)) ->
  ll P l -> ll Q l.
Proof.
intros P Q l Hperm Hmix0 Hmix2 Hcut Hgax pi.
apply (ax_gen_loc _ _ _ Hperm Hmix0 Hmix2 Hcut pi).
remember (gax_elts pi) as lax.
clear - Hgax ; induction lax ; intuition.
Qed.

Lemma ax_exp_frag {P} : forall l P', ll P' l ->
  le_pfrag P' (axupd_pfrag P (existT (fun x => x -> list formula) _
                                (fun a => match a with
                                          | inl x => projT2 (pgax P) x
                                          | inr x => x :: dual x :: nil
                                          end)))
    -> ll P l.
Proof with  try eassumption ; try reflexivity.
intros l P' pi Hlf.
eapply (ax_gen (axupd_pfrag P (existT (fun x => x -> list formula) _
                                (fun a => match a with
                                          | inl x => projT2 (pgax P) x
                                          | inr x => x :: dual x :: nil
                                          end))))...
- simpl ; intros a.
  destruct a.
  + apply gax_r.
  + apply ax_exp.
- eapply stronger_pfrag...
Qed.

Lemma ax_loc : forall P l (pi : ll P l),
  ll (axupd_pfrag P (existT (fun x => x -> list formula) (Fin.t (length (gax_elts pi)))
                       (fun n => projT2 (pgax P) (Vector.nth (Vector.of_list (gax_elts pi)) n)))) l.
Proof with myeasy.
intros P l pi.
refine (ax_gen_loc _ _ _ _ _ _ _ pi _)...
remember (gax_elts pi) as l0 ; clear.
remember l0 as l1.
enough (Forall_Type
  (fun a : projT1 (pgax P) =>
   ll
     (axupd_pfrag P
        (existT (fun x : Type => x -> list formula) (Fin.t (length l1))
           (fun n : Fin.t (length l1) => projT2 (pgax P) (Vector.nth (Vector.of_list l1) n)))) 
     (projT2 (pgax P) a)) l0).
{ subst ; assumption. }
rewrite <- app_nil_l in Heql1 ; subst.
remember nil as l ; clear ; revert l.
induction l0 ; intros l ; constructor...
- clear ; induction l.
  + rewrite app_nil_l.
    change (length (a :: l0)) with (S (length l0)).
    pose (Q := axupd_pfrag P
           (existT (fun x => x -> list formula) (Fin.t (length (a :: l0)))
                   (fun n => projT2 (pgax P) (Vector.nth (Vector.of_list (a :: l0)) n)))).
    replace (projT2 (pgax P) a) with (projT2 (pgax Q) Fin.F1) by reflexivity.
    apply gax_r.
  + eapply stronger_pfrag ; [ | apply IHl ].
    nsplit 5 ; simpl...
    intros a1 ; exists (Fin.FS a1)...
- cons2app ; rewrite app_assoc.
  apply IHl0.
Qed.


(** ** Extending sequents with a [wn] context *)

Lemma ext_wn_param P Q (Q_perm : pperm Q = true) : forall l l0,
  ll P l ->
  (pcut P = true -> pcut Q = true) ->
  (forall a, ll Q (projT2 (pgax P) a ++ map wn l0)) ->
  (pmix0 P = true -> pmix0 Q = false -> ll Q (map wn l0)) ->
  (pmix2 P = true -> pmix2 Q = false ->
     forall l1 l2, ll Q (l1 ++ map wn l0) -> ll Q (l2 ++ map wn l0) ->
       ll Q (l2 ++ l1 ++ map wn l0)) ->
  ll Q (l ++ map wn l0).
Proof with myeeasy.
intros l l0 pi Hpcut Hpgax Hpmix0 Hpmix2.
induction pi ; try (now constructor).
- eapply ex_r ; [ | apply PCperm_Type_app_comm ]...
  apply wk_list_r.
  apply ax_r.
- eapply ex_r...
  apply PCperm_perm_Type in p.
  rewrite Q_perm.
  apply Permutation_Type_app_tail...
- list_simpl.
  eapply ex_wn_r...
  rewrite app_assoc in IHpi ; rewrite 2 app_assoc...
- case_eq (pmix0 Q) ; intros Q_mix0.
  + list_simpl.
    rewrite <- app_nil_r.
    apply wk_list_r.
    apply mix0_r...
  + apply Hpmix0 in Q_mix0...
- case_eq (pmix2 Q) ; intros Q_mix2.
  + eapply ex_r ; [ | apply PCperm_Type_app_comm ]...
    apply co_list_r.
    eapply ex_r ; [ | apply PCperm_Type_app_comm ]...
    list_simpl ; rewrite app_assoc ; apply mix2_r...
    eapply ex_r ; [ | apply PCperm_Type_app_comm ]...
  + list_simpl ; eapply Hpmix2 in Q_mix2...
- eapply ex_r ; [ | apply PCperm_Type_app_comm ]...
  apply wk_list_r.
  apply one_r.
- eapply ex_r ; [ | apply PCperm_Type_app_comm ]...
  apply co_list_r.
  apply (ex_r _ (tens A B :: (l2 ++ map wn l0) ++ l1 ++ map wn l0)) ;
    [ | rewrite Q_perm ; PCperm_Type_solve ].
  apply tens_r...
- rewrite <- app_comm_cons in IHpi.
  rewrite <- map_app in IHpi.
  rewrite <- app_comm_cons.
  rewrite <- map_app.
  apply oc_r...
- eapply ex_r ; [ | apply PCperm_Type_app_comm ]...
  apply co_list_r.
  apply (ex_r _ ((l2 ++ map wn l0) ++ l1 ++ map wn l0)) ;
    [ | rewrite Q_perm ; PCperm_Type_solve ].
  eapply cut_r...
  intuition.
- apply Hpgax...
Qed.

(** By extending axioms of [P] with [map wn l0],
one can turn any proof of [l] in [P] into a proof of [l ++ map wn l0]. *)
Lemma ext_wn {P} {P_perm : pperm P = true} : forall l l0,
  ll P l ->
    ll (axupd_pfrag P ((existT (fun x => x -> list formula) _ (fun a => projT2 (pgax P) a ++ map wn l0))))
       (l ++ map wn l0).
Proof with myeeasy.
intros l l0 pi.
remember
  (axupd_pfrag P ((existT (fun x => x -> list formula) _ (fun a => projT2 (pgax P) a ++ map wn l0))))
  as Q.
eapply (ext_wn_param P Q) in pi...
- rewrite HeqQ...
- intros P_cut.
  rewrite HeqQ ; simpl...
- intros a.
  assert ({ b | projT2 (pgax P) a ++ map wn l0 = projT2 (pgax Q) b}) as [b Hgax]
    by (subst ; simpl ; exists a ; reflexivity).
  rewrite Hgax.
  apply gax_r.
- intros P_mix0 Q_mix0.
  rewrite HeqQ in Q_mix0 ; simpl in Q_mix0.
  rewrite P_mix0 in Q_mix0.
  inversion Q_mix0.
- intros P_mix2 Q_mix2.
  rewrite HeqQ in Q_mix2 ; simpl in Q_mix2.
  rewrite P_mix2 in Q_mix2.
  inversion Q_mix2.
Qed.


(** ** Consistency properties *)

Lemma weak_contradiction_contradiction {P} :
  ll P nil -> { A : _ & ll P (A :: nil) & ll P (dual A :: nil) }.
Proof.
intros pi.
split with bot.
- apply bot_r ; assumption.
- apply one_r.
Qed.

Lemma contradiction_weak_contradiction {P} : pcut P = true ->
  forall A, ll P (A :: nil) -> ll P (dual A :: nil) -> ll P nil.
Proof.
intros Hcut A pi1 pi2.
rewrite <- (app_nil_l).
apply (@cut_r _ Hcut A) ; assumption.
Qed.

Lemma bot_contradiction_weak_contradiction {P} :
  (forall a, In bot (projT2 (pgax P) a) -> False) ->
  ll P (bot :: nil) -> ll P nil.
Proof.
intros Hgax pi.
rewrite <- (app_nil_l).
apply bot_rev ; assumption.
Qed.

Lemma strong_contradition_general_contradiction {P} : pcut P = true ->
  ll P (zero :: nil) -> forall l, ll P l.
Proof.
intros Hcut pi l.
rewrite <- (app_nil_l _).
eapply (@cut_r _ Hcut) ; try eassumption.
apply top_r.
Qed.

