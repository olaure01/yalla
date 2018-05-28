(* ll_fragments library for yalla *)
(* Coq 8.6 *)
(* v 1.0   Olivier Laurent *)


(** * Definitions of various Linear Logic fragments *)

Require Import List.

Require Import Permutation_more.
Require Import genperm.

Require Export ll.
Require Import subs.


(** ** Standard linear logic: [ll_ll] (no mix, no axiom) *)

(** cut / axioms / mix0 / mix2 / permutation *)
Definition pfrag_ll :=  mk_pfrag false (fun _ => False) false false true.
(*                               cut   axioms           mix0  mix2  perm  *)

Definition ll_ll := ll pfrag_ll.

Lemma cut_ll_r : forall A l1 l2 s1 s2,
  ll_ll (dual A :: l1) s1 -> ll_ll (A :: l2) s2 -> exists s, ll_ll (l2 ++ l1) s.
Proof with myeeasy.
intros A l1 l2 s1 s2 pi1 pi2.
rewrite <- (app_nil_l (_ ++ _)).
eapply cut_elim ; try (intros ; inversion H ; fail)...
rewrite bidual...
Qed.


(** ** Linear logic with mix0: [ll_mix0] (no mix2, no axiom) *)

(** cut / axioms / mix0 / mix2 / permutation *)
Definition pfrag_mix0 := mk_pfrag false (fun _ => False) true false true.
(*                                cut   axioms           mix0 mix2  perm  *)

Definition ll_mix0 := ll pfrag_mix0.

Lemma cut_mix0_r : forall A l1 l2 s1 s2, 
  ll_mix0 (dual A :: l1) s1 -> ll_mix0 (A :: l2) s2 -> exists s,
    ll_mix0 (l2 ++ l1) s.
Proof with myeeasy.
intros A l1 l2 s1 s2 pi1 pi2.
rewrite <- (app_nil_l (_ ++ _)).
eapply cut_elim ; try (intros ; inversion H ; fail)... 
rewrite bidual...
Qed.

(** Provability in [ll_mix0] is equivalent to adding [wn one] in [ll] *)

Lemma mix0_to_ll {P} : pperm P = true -> forall b0 bp l s,
  ll (mk_pfrag P.(pcut) P.(pgax) b0 P.(pmix2) bp) l s -> exists s', ll P (wn one :: l) s'.
Proof with myeeasy ; try PCperm_solve.
intros fp b0 bp l s pi.
eapply (ext_wn_param _ P fp _ (one :: nil)) in pi.
- clear s ; destruct pi as [s pi].
  eexists.
  eapply ex_r...
- intros Hcut...
- intros l' Hgax.
  simpl in Hgax.
  apply gax_r in Hgax.
  apply (wk_list_r (one :: nil)) in Hgax.
  destruct Hgax as [s0 pi']. 
  eexists.
  eapply ex_r...
- intros.
  eexists.
  eapply de_r.
  eapply one_r.
- intros Hpmix2 Hpmix2'.
  exfalso.
  simpl in Hpmix2.
  rewrite Hpmix2 in Hpmix2'.
  inversion Hpmix2'.
Qed.

Lemma ll_to_mix0 {P} : forall l s,
  ll P (wn one :: l) s -> exists s',
    ll (mk_pfrag true P.(pgax) true P.(pmix2) P.(pperm)) l s'.
Proof with myeasy.
intros l s pi.
eapply stronger_pfrag in pi.
- eexists.
  rewrite <- (app_nil_r l).
  eapply cut_r ; [ | | apply pi]...
  change nil with (map wn nil).
  apply oc_r.
  apply bot_r.
  eapply mix0_r...
- nsplit 5...
  + destruct pcut...
  + intros f Hax...
  + destruct pmix0...
Qed.

(** Provability in [ll_mix0] is equivalent to provability of [ll]
extended with the provability of [bot :: bot :: nil] *)

Lemma mix0_to_ll_bot {P} : pcut P = true -> pperm P = true -> forall bc b0 bp l s,
  ll (mk_pfrag bc P.(pgax) b0 P.(pmix2) bp) l s -> exists s',
    ll (axupd_pfrag P (fun l => P.(pgax) l \/ l = bot :: bot :: nil)) l s'.
Proof with myeeasy ; try (unfold PCperm ; rewrite fp ; PCperm_solve).
remember (axupd_pfrag P (fun l => pgax P l \/ l = bot :: bot :: nil)) as P'.
intros fc fp bc b0 bp l s pi.
eapply stronger_pfrag in pi.
- eapply mix0_to_ll in pi...
  assert (pcut P' = true) as fc' by (rewrite HeqP' ; simpl ; assumption).
  clear s ; destruct pi as [s pi].
  apply (stronger_pfrag _ P') in pi.
  + assert (exists s', ll P' (bot :: map wn nil) s') as pi'.
    { eexists.
      change (bot :: map wn nil) with ((bot :: nil) ++ nil).
      eapply (@cut_r _ fc' bot).
      - apply one_r.
      - apply gax_r.
        rewrite HeqP'.
        right... }
    destruct pi' as [s' pi'].
    eexists.
    apply oc_r in pi'.
    rewrite <- (app_nil_l l).
    eapply (@cut_r _ fc' (oc bot)) ; [ simpl ; apply pi | apply pi' ].
  + nsplit 5 ; rewrite HeqP'...
    intros l0 Hpgax ; left...
- nsplit 5 ; intros ; simpl...
  rewrite fc.
  destruct bc...
Qed.

Lemma ll_bot_to_mix0 {P} : forall l s,
  ll (axupd_pfrag P (fun l => P.(pgax) l \/ l = bot :: bot :: nil)) l s -> exists s',
    ll (mk_pfrag P.(pcut) P.(pgax) true P.(pmix2) P.(pperm)) l s'.
Proof with myeeasy.
intros l s pi.
remember (mk_pfrag P.(pcut) P.(pgax) true P.(pmix2) P.(pperm)) as P'.
apply (stronger_pfrag _
  (axupd_pfrag P' (fun l => P.(pgax) l \/ l = bot :: bot :: nil)))
  in pi.
- eapply subs_ll_axioms...
  clear - HeqP' ; intros l Hgax.
  destruct Hgax ; subst ; eexists.
  + apply gax_r...
  + apply bot_r.
    apply bot_r.
    apply mix0_r...
- rewrite HeqP' ; nsplit 5 ; intros ; simpl...
  destruct (pmix0 P)...
Qed.

(** [mix2] is not valid in [ll_mix0] *)

Lemma mix0_not_mix2 : forall s, ~ ll_mix0 (one :: one :: nil) s.
Proof.
intros s pi.
remember (one :: one :: nil) as l.
revert Heql ; induction pi ; intros Heql ; subst ; try inversion Heql.
- apply IHpi.
  simpl in H.
  symmetry in H.
  apply Permutation_length_2_inv in H.
  destruct H ; assumption.
- inversion f.
- inversion f.
- inversion H.
Qed.


(** ** Linear logic with mix2: [ll_mix2] (no mix0, no axiom) *)

(** cut / axioms / mix0 / mix2 / permutation *)
Definition pfrag_mix2 := mk_pfrag false (fun _ => False) false true true.
(*                                cut   axioms           mix0  mix2 perm  *)

Definition ll_mix2 := ll pfrag_mix2.

Lemma cut_mix2_r : forall A l1 l2 s1 s2,
  ll_mix2 (dual A :: l1) s1 -> ll_mix2 (A :: l2) s2 -> exists s,
    ll_mix2 (l2 ++ l1) s.
Proof with myeeasy.
intros A l1 l2 s1 s2 pi1 pi2.
rewrite <- (app_nil_l (_ ++ _)).
eapply cut_elim ; try (intros ; inversion H ; fail)...
rewrite bidual...
Qed.

(** Provability in [ll_mix2] is equivalent to adding [wn (tens bot bot)] in [ll] *)

Lemma mix2_to_ll {P} : pperm P = true -> forall b2 bp l s,
  ll (mk_pfrag P.(pcut) P.(pgax) P.(pmix0) b2 bp) l s -> exists s',
    ll P (wn (tens bot bot) :: l) s'.
Proof with myeeasy ; try PCperm_solve.
intros fp b0 bp l s pi.
eapply (ext_wn_param _ P fp _ (tens bot bot :: nil)) in pi.
- clear s ; destruct pi as [s pi].
  eexists.
  eapply ex_r...
- intros Hcut...
- intros l' Hgax.
  simpl in Hgax.
  apply gax_r in Hgax.
  apply (wk_list_r (tens bot bot :: nil)) in Hgax.
  destruct Hgax as [s0 pi']. 
  eexists.
  eapply ex_r...
- intros Hpmix0 Hpmix0'.
  exfalso.
  simpl in Hpmix0.
  rewrite Hpmix0 in Hpmix0'.
  inversion Hpmix0'.
- intros _ _ l1 l2 s1 s2 pi1 pi2.
  eexists.
  apply (ex_r _ (wn (tens bot bot) :: l2 ++ l1))...
  apply co_std_r.
  apply co_std_r.
  apply de_r.
  eapply ex_r.
  + apply tens_r ; apply bot_r ; [ apply pi1 | apply pi2 ].
  + rewrite fp...
Qed.

Lemma ll_to_mix2 {P} : forall l s,
  ll P (wn (tens bot bot) :: l) s -> exists s',
    ll (mk_pfrag true P.(pgax) P.(pmix0) true P.(pperm)) l s'.
Proof with myeasy.
intros l s pi.
eapply stronger_pfrag in pi.
- eexists.
  rewrite <- (app_nil_r l).
  eapply cut_r ; [ | | apply pi]...
  change nil with (map wn nil).
  apply oc_r.
  apply parr_r.
  change (one :: one :: map wn nil) with ((one :: nil) ++ one :: nil).
  eapply mix2_r...
  + apply one_r.
  + apply one_r.
- nsplit 5...
  + destruct pcut...
  + intros f Hax...
  + destruct pmix2...
Qed.

(** Provability in [ll_mix2] is equivalent to provability of [ll]
extended with the provability of [one :: one :: nil] *)

Lemma mix2_to_ll_one_one {P} : pcut P = true -> pperm P = true -> forall bc b2 bp l s,
  ll (mk_pfrag bc P.(pgax) P.(pmix0) b2 bp) l s -> exists s',
    ll (axupd_pfrag P (fun l => P.(pgax) l \/ l = one :: one :: nil)) l s'.
Proof with myeeasy ; try (unfold PCperm ; rewrite fp ; PCperm_solve).
remember (axupd_pfrag P (fun l => pgax P l \/ l = one :: one :: nil)) as P'.
intros fc fp bc b0 bp l s pi.
eapply stronger_pfrag in pi.
- eapply mix2_to_ll in pi...
  assert (pcut P' = true) as fc' by (rewrite HeqP' ; simpl ; assumption).
  clear s ; destruct pi as [s pi].
  apply (stronger_pfrag _ P') in pi.
  + assert (exists s', ll P' (oc (parr one one) :: map wn nil) s') as pi'.
    { eexists.
      apply oc_r.
      apply parr_r.
      apply gax_r.
      rewrite HeqP'.
      right... }
    destruct pi' as [s' pi'].
    eexists.
    rewrite <- (app_nil_l l).
    eapply (@cut_r _ fc' (oc (parr one one))) ; [ simpl ; apply pi | apply pi' ].
  + nsplit 5 ; rewrite HeqP'...
    intros l0 Hpgax ; left...
- nsplit 5 ; intros ; simpl...
  rewrite fc.
  destruct bc...
Qed.

Lemma ll_one_one_to_mix2 {P} : forall l s,
  ll (axupd_pfrag P (fun l => P.(pgax) l \/ l = one :: one :: nil)) l s -> exists s',
    ll (mk_pfrag P.(pcut) P.(pgax) P.(pmix0) true P.(pperm)) l s'.
Proof with myeeasy.
intros l s pi.
remember (mk_pfrag P.(pcut) P.(pgax) P.(pmix0) true P.(pperm)) as P'.
apply (stronger_pfrag _
  (axupd_pfrag P' (fun l => P.(pgax) l \/ l = one :: one :: nil)))
  in pi.
- eapply subs_ll_axioms...
  clear - HeqP' ; intros l Hgax.
  destruct Hgax ; subst ; eexists.
  + apply gax_r...
  + change (one :: one :: nil) with ((one :: nil) ++ one :: nil).
    apply mix2_r...
    * apply one_r.
    * apply one_r.
- rewrite HeqP' ; nsplit 5 ; intros ; simpl...
  destruct (pmix2 P)...
Qed.

(** [mix0] is not valid in [ll_mix2] *)

Lemma mix2_not_mix0 : forall s, ~ ll_mix2 nil s.
Proof.
intros s pi.
remember (nil) as l.
revert Heql ; induction pi ; intros Heql ; subst ; try inversion Heql.
- apply IHpi.
  simpl in H.
  symmetry in H.
  apply Permutation_nil in H.
  assumption.
- inversion f.
- apply IHpi2.
  apply app_eq_nil in Heql.
  apply Heql.
- inversion f.
- inversion H.
Qed.


(** ** Linear logic with both mix0 and mix2: [ll_mix02] (no axiom) *)

(** cut / axioms / mix0 / mix2 / permutation *)
Definition pfrag_mix02 := mk_pfrag false (fun _ => False) true true true.
(*                                 cut   axioms           mix0 mix2 perm  *)

Definition ll_mix02 := ll pfrag_mix02.

Lemma cut_mix02_r : forall A l1 l2 s1 s2,
  ll_mix02 (dual A :: l1) s1 -> ll_mix02 (A :: l2) s2 -> exists s,
    ll_mix02 (l2 ++ l1) s.
Proof with myeeasy.
intros A l1 l2 s1 s2 pi1 pi2.
rewrite <- (app_nil_l (_ ++ _)).
eapply cut_elim ; try (intros ; inversion H ; fail)...
rewrite bidual...
Qed.


(* llR *)

(** ** Linear logic extended with [R] = [bot]: [llR] *)

(** cut / axioms / mix0 / mix2 / permutation *)
Definition pfrag_llR R :=
  mk_pfrag true (fun l => l = dual R :: nil \/ l = R :: one :: nil)
             false false true.
(*         cut  axioms
             mix0  mix2  perm  *)

Definition llR R := ll (pfrag_llR R).

Lemma llR1_R2 : forall R1 R2 s1 s2,
  llR R2 (dual R1 :: R2 :: nil) s1 -> llR R2 (dual R2 :: R1 :: nil) s2 ->
    forall l s, llR R1 l s -> exists s', llR R2 l s'.
Proof with myeeasy.
intros R1 R2 s1 s2 HR1 HR2 l s Hll.
induction Hll ;
  try (destruct IHHll as [s' IHHll]) ;
  try (destruct IHHll1 as [s1' IHHll1]) ;
  try (destruct IHHll2 as [s2' IHHll2]) ;
  try (eexists ; constructor ; myeeasy ; fail).
- eexists ; eapply ex_r...
- eexists ; eapply cut_r...
- inversion H ; subst.
  + eexists.
    rewrite <- (app_nil_l _).
    apply (@cut_r (pfrag_llR R2) eq_refl (dual R2)).
    * rewrite bidual.
      eapply ex_r.
      apply HR1.
      apply PCperm_swap.
    * apply gax_r.
      left...
  + eapply (@cut_r (pfrag_llR R2) eq_refl R2) in HR2.
    * eexists.
      eapply ex_r ; [ apply HR2 | ].
      unfold PCperm.
      simpl.
      symmetry.
      apply Permutation_cons_app.
      rewrite app_nil_r.
      reflexivity.
    * apply gax_r.
      right...
Qed.

Lemma ll_to_llR : forall R l s, ll_ll l s -> exists s', llR R l s'.
Proof with myeeasy.
intros R l s pi.
induction pi ;
  try (inversion f ; fail) ;
  try (inversion H ; fail) ;
  try (destruct IHpi as [s' pi']) ;
  try (destruct IHpi1 as [s1' pi1']) ;
  try (destruct IHpi2 as [s2' pi2']) ;
  eexists ;
  try (constructor ; myeeasy ; fail).
- eapply ex_r...
Qed.

Lemma subs_llR : forall R C x l s, llR R l s -> exists s',
  llR (subs C x R) (map (subs C x) l) s'.
Proof with myeasy.
intros.
apply (subs_ll C x) in H.
destruct H as [s' H].
eapply stronger_pfrag in H ; [ eexists ; eassumption | ].
nsplit 5...
intros f (l' & Hax & Heq) ; subst.
destruct Hax ; [ left | right ] ; subst ;
  simpl ; try rewrite subs_dual...
Qed.


