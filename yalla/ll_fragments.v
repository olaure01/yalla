(* ll_fragments library for yalla *)
(* v 1.1   Olivier Laurent *)


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

Lemma cut_ll_admissible :
  forall l s, ll (cutupd_pfrag pfrag_ll true) l s -> exists s', ll_ll l s'.
Proof with myeeasy.
intros l s pi.
induction pi ;
  try (eexists ; constructor ; myeeasy ; fail) ;
  try (destruct IHpi as [s' IHpi] ; eexists ; constructor ; myeeasy ; fail) ;
  try (destruct IHpi1 as [s'1 IHpi1] ;
       destruct IHpi2 as [s'2 IHpi2] ; eexists ; constructor ; myeeasy ; fail).
- destruct IHpi as [s' IHpi].
  eexists.
  apply (ex_r _ l1)...
- destruct IHpi1 as [s'1 IHpi1].
  destruct IHpi2 as [s'2 IHpi2].
  eapply cut_ll_r...
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

Lemma cut_mix0_admissible :
  forall l s, ll (cutupd_pfrag pfrag_mix0 true) l s -> exists s', ll_mix0 l s'.
Proof with myeeasy.
intros l s pi.
induction pi ;
  try (eexists ; constructor ; myeeasy ; fail) ;
  try (destruct IHpi as [s' IHpi] ; eexists ; constructor ; myeeasy ; fail) ;
  try (destruct IHpi1 as [s'1 IHpi1] ;
       destruct IHpi2 as [s'2 IHpi2] ; eexists ; constructor ; myeeasy ; fail).
- destruct IHpi as [s' IHpi].
  eexists.
  apply (ex_r _ l1)...
- destruct IHpi1 as [s'1 IHpi1].
  destruct IHpi2 as [s'2 IHpi2].
  eapply cut_mix0_r...
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

Lemma mix0_wn_one : forall l,
  (exists s, ll_mix0 l s) <-> (exists s, ll_mix0 (wn one :: l) s).
Proof with myeeasy.
intros l ; split ; intros [s pi].
- eexists.
  apply wk_r...
- (* an alternative proof is by introducing a cut with (oc bot) *)
  assert (pfrag_mix0 = mk_pfrag pfrag_mix0.(pcut) pfrag_mix0.(pgax)
                                true pfrag_mix0.(pmix2) true)
    as Heqfrag by reflexivity.
  unfold ll_mix0 in pi.
  rewrite Heqfrag in pi.
  apply mix0_to_ll in pi...
  clear s ; destruct pi as [s pi].
  apply co_std_r in pi.
  apply ll_to_mix0 in pi.
  clear s ; destruct pi as [s pi].
  eapply cut_mix0_admissible...
Qed.


(** Provability in [ll_mix0] is equivalent to provability of [ll]
extended with the provability of [bot :: bot :: nil] *)

Lemma mix0_to_ll_bot {P} : pcut P = true -> pperm P = true -> forall bc b0 bp l s,
  ll (mk_pfrag bc P.(pgax) b0 P.(pmix2) bp) l s -> exists s',
    ll (axupd_pfrag P (fun l => P.(pgax) l \/ l = bot :: bot :: nil)) l s'.
Proof with myeeasy ; try (unfold PCperm ; PCperm_solve).
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

Lemma cut_mix2_admissible :
  forall l s, ll (cutupd_pfrag pfrag_mix2 true) l s -> exists s', ll_mix2 l s'.
Proof with myeeasy.
intros l s pi.
induction pi ;
  try (eexists ; constructor ; myeeasy ; fail) ;
  try (destruct IHpi as [s' IHpi] ; eexists ; constructor ; myeeasy ; fail) ;
  try (destruct IHpi1 as [s'1 IHpi1] ;
       destruct IHpi2 as [s'2 IHpi2] ; eexists ; constructor ; myeeasy ; fail).
- destruct IHpi as [s' IHpi].
  eexists.
  apply (ex_r _ l1)...
- destruct IHpi1 as [s'1 IHpi1].
  destruct IHpi2 as [s'2 IHpi2].
  eapply cut_mix2_r...
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
Proof with myeeasy ; try (unfold PCperm ; PCperm_solve).
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

Lemma cut_mix02_admissible :
  forall l s, ll (cutupd_pfrag pfrag_mix02 true) l s -> exists s', ll_mix02 l s'.
Proof with myeeasy.
intros l s pi.
induction pi ;
  try (eexists ; constructor ; myeeasy ; fail) ;
  try (destruct IHpi as [s' IHpi] ; eexists ; constructor ; myeeasy ; fail) ;
  try (destruct IHpi1 as [s'1 IHpi1] ;
       destruct IHpi2 as [s'2 IHpi2] ; eexists ; constructor ; myeeasy ; fail).
- destruct IHpi as [s' IHpi].
  eexists.
  apply (ex_r _ l1)...
- destruct IHpi1 as [s'1 IHpi1].
  destruct IHpi2 as [s'2 IHpi2].
  eapply cut_mix02_r...
Qed.

(** Provability in [ll_mix02] is equivalent to adding [wn (tens (wn one) (wn one))] in [ll] *)

Lemma mix02_to_ll {P} : pperm P = true -> forall b1 b2 bp l s,
  ll (mk_pfrag P.(pcut) P.(pgax) b1 b2 bp) l s -> exists s',
    ll P (wn (tens (wn one) (wn one)) :: l) s'.
Proof with myeeasy ; try PCperm_solve.
intros fp b1 b2 bp l s pi.
eapply (ext_wn_param _ P fp _ (tens (wn one) (wn one) :: nil)) in pi.
- clear s ; destruct pi as [s pi].
  eexists.
  eapply ex_r...
- intros Hcut...
- intros l' Hgax.
  simpl in Hgax.
  apply gax_r in Hgax.
  apply (wk_list_r (tens (wn one) (wn one) :: nil)) in Hgax.
  destruct Hgax as [s0 pi']. 
  eexists.
  eapply ex_r...
- intros Hpmix0 Hpmix0'.
  eexists.
  apply de_r...
  rewrite <- (app_nil_l nil).
  apply tens_r ; apply de_r ; apply one_r.
- intros _ _ l1 l2 s1 s2 pi1 pi2.
  eexists.
  apply (ex_r _ (wn (tens (wn one) (wn one)) :: l2 ++ l1))...
  apply co_std_r.
  apply co_std_r.
  apply de_r.
  eapply ex_r.
  + apply tens_r ; apply wk_r ; [ apply pi1 | apply pi2 ].
  + rewrite fp...
Qed.

Lemma ll_to_mix02 {P} : forall l s,
  ll P (wn (tens (wn one) (wn one)) :: l) s -> exists s',
    ll (mk_pfrag true P.(pgax) true true P.(pperm)) l s'.
Proof with myeasy.
intros l s pi.
eapply stronger_pfrag in pi.
- eexists.
  rewrite <- (app_nil_r l).
  eapply cut_r ; [ | | apply pi]...
  change nil with (map wn nil).
  apply oc_r.
  apply parr_r.
  change (oc bot :: oc bot :: map wn nil) with ((oc bot :: map wn nil)
                                              ++ oc bot :: map wn nil).
  eapply mix2_r...
  + apply oc_r.
    apply bot_r.
    apply mix0_r...
  + apply oc_r.
    apply bot_r.
    apply mix0_r...
- nsplit 5...
  + destruct pcut...
  + intros f Hax...
  + destruct pmix0...
  + destruct pmix2...
Qed.

(** Provability in [ll_mix02] is equivalent to provability of [ll]
extended with the provability of both [bot :: bot :: nil] and [one :: one :: nil] *)

Lemma mix02_to_ll_one_eq_bot {P} : pcut P = true -> pperm P = true -> forall bc b0 b2 bp l s,
  ll (mk_pfrag bc P.(pgax) b0 b2 bp) l s -> exists s',
    ll (axupd_pfrag P
         (fun l => P.(pgax) l \/ l = one :: one :: nil \/ l = bot :: bot :: nil)) l s'.
Proof with myeeasy ; try (unfold PCperm ; PCperm_solve).
remember (axupd_pfrag P
           (fun l => pgax P l \/ l = one :: one :: nil \/ l = bot :: bot :: nil)) as P'.
intros fc fp bc b0 b2 bp l s pi.
eapply stronger_pfrag in pi.
- eapply mix02_to_ll in pi...
  assert (pcut P' = true) as fc' by (rewrite HeqP' ; simpl ; assumption).
  clear s ; destruct pi as [s pi].
  apply (stronger_pfrag _ P') in pi.
  + assert (exists s', ll P' (oc (parr (oc bot) (oc bot)) :: map wn nil) s') as pi'.
    { eexists.
      apply oc_r.
      apply parr_r.
      change (oc bot :: oc bot :: map wn nil)
        with ((oc bot :: nil) ++ oc bot :: map wn nil).
      eapply (@cut_r _ fc' one).
      - apply bot_r.
        apply oc_r.
        change (bot :: map wn nil) with ((bot :: nil) ++ nil).
        eapply (@cut_r _ fc' bot).
        + apply one_r.
        + apply gax_r.
          rewrite HeqP'.
          right ; right...
      - change (one :: oc bot :: nil)
          with ((one :: nil) ++ oc bot :: map wn nil).
        eapply (@cut_r _ fc' one).
        + apply bot_r.
          apply oc_r.
          change (bot :: map wn nil) with ((bot :: nil) ++ nil).
          eapply (@cut_r _ fc' bot).
          * apply one_r.
          * apply gax_r.
            rewrite HeqP'.
            right ; right...
        + apply gax_r.
          rewrite HeqP'.
          right ; left... }
    destruct pi' as [s' pi'].
    eexists.
    rewrite <- (app_nil_l l).
    eapply (@cut_r _ fc' (oc (parr (oc bot) (oc bot)))) ; [ simpl ; apply pi | apply pi' ].
  + nsplit 5 ; rewrite HeqP'...
    intros l0 Hpgax ; left...
- nsplit 5 ; intros ; simpl...
  rewrite fc.
  destruct bc...
Qed.

Lemma ll_one_eq_bot_to_mix02 {P} : forall l s,
  ll (axupd_pfrag P
     (fun l => P.(pgax) l \/ l = one :: one :: nil \/ l = bot :: bot :: nil)) l s
    -> exists s', ll (mk_pfrag P.(pcut) P.(pgax) true true P.(pperm)) l s'.
Proof with myeeasy.
intros l s pi.
remember (mk_pfrag P.(pcut) P.(pgax) true true P.(pperm)) as P'.
apply (stronger_pfrag _
  (axupd_pfrag P' (fun l => P.(pgax) l \/ l = one :: one :: nil \/ l = bot :: bot :: nil)))
  in pi.
- eapply subs_ll_axioms...
  clear - HeqP' ; intros l Hgax.
  destruct Hgax as [Hgax | [Hgax | Hgax]] ; subst ; eexists.
  + apply gax_r...
  + change (one :: one :: nil) with ((one :: nil) ++ one :: nil).
    apply mix2_r...
    * apply one_r.
    * apply one_r.
  + change (bot :: bot :: nil) with ((bot :: nil) ++ bot :: nil).
    apply bot_r...
    apply bot_r...
    apply mix0_r...
- rewrite HeqP' ; nsplit 5 ; intros ; simpl...
  + destruct (pmix0 P)...
  + destruct (pmix2 P)...
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

Lemma llR_to_ll : forall R l s,
  llR R l s -> exists s', ll_ll (l ++ wn R :: wn (tens (dual R) bot) :: nil) s'.
Proof with myeasy.
intros R l s pi.
destruct (@ax_exp pfrag_ll (dual R)) as [sR HaxR].
rewrite bidual in HaxR.
cut (exists s', ll (cutupd_pfrag pfrag_ll true) (l ++ wn R :: wn (tens (dual R) bot) :: nil) s').
{ intros [s' pi'].
  apply cut_ll_admissible in pi'... }
replace (wn R :: wn (tens (dual R) bot) :: nil) with (map wn (map dual (dual R :: parr one R :: nil)))
  by (simpl ; rewrite bidual ; reflexivity).
apply deduction_list...
eapply ax_gen ; [ | | | | | apply pi ]...
intros lax Hgax.
simpl in Hgax.
destruct Hgax ; eexists ; subst ; simpl.
- apply gax_r.
  right.
  constructor...
- rewrite <- (app_nil_r nil).
  rewrite_all app_comm_cons.
  eapply cut_r...
  + apply gax_r.
    right.
    right.
    constructor.
    rewrite <- (bidual (parr _ _)).
    reflexivity.
  + apply (ex_r _ (tens (dual R) bot :: (one :: nil) ++ R :: nil)) ; [ | PCperm_solve ].
    apply tens_r.
    * eapply stronger_pfrag ; [ | apply HaxR ].
      nsplit 5...
      intros lax Hgax ; destruct Hgax.
    * apply bot_r.
      apply one_r.
Qed.

Lemma llwnR_to_ll : forall R l s,
  llR (wn R) l s -> exists s', ll_ll (l ++ wn R :: nil) s'.
Proof with myeasy.
intros R l s pi.
apply llR_to_ll in pi.
destruct pi as [s' pi].
eapply (ex_r _ _ (wn (tens (dual (wn R)) bot) :: l ++ wn (wn R) :: nil)) in pi ;
  [ | PCperm_solve ].
eapply (cut_ll_r _ nil) in pi.
- destruct pi as [s'' pi].
  destruct (@ax_exp pfrag_ll (dual (wn R))) as [sR HaxR].
  rewrite bidual in HaxR.
  eapply (cut_ll_r (wn (wn R))).
  + simpl.
    change (wn R :: nil) with (map wn (R :: nil)).
    apply oc_r.
    apply HaxR.
  + eapply ex_r ; [ apply pi | PCperm_solve ].
- simpl ; rewrite bidual.
  change nil with (map wn nil).
  apply oc_r.
  apply parr_r.
  eapply ex_r ; [ apply wk_r ; apply one_r | PCperm_solve ].
Qed.

Lemma ll_wn_wn_to_llR : forall R l s,
  ll_ll (l ++ wn R :: wn (tens (dual R) bot) :: nil) s -> exists s', llR R l s'.
Proof with myeasy.
intros R l s pi.
apply (ll_to_llR R) in pi.
clear s ; destruct pi as [s pi].
eexists.
rewrite <- (app_nil_l l).
eapply (cut_r _ (oc (dual R))).
- rewrite <- (app_nil_l (dual _ :: l)).
  eapply (cut_r _ (oc (parr one R))).
  + simpl ; rewrite bidual ; eapply ex_r ; [apply pi | PCperm_solve ].
  + change nil with (map wn nil).
    apply oc_r.
    apply parr_r.
    eapply ex_r ; [ apply gax_r ; right ; reflexivity | PCperm_solve ].
- change nil with (map wn nil).
  apply oc_r.
  apply gax_r.
  left...
Unshelve. all : reflexivity.
Qed.

Lemma ll_wn_to_llwnR : forall R l s,
  ll_ll (l ++ wn R :: nil) s -> exists s', llR (wn R) l s'.
Proof with myeasy.
intros R l s pi.
eapply ll_wn_wn_to_llR.
eapply (ex_r _ (wn (tens (dual (wn R)) bot) :: wn (wn R) :: l)) ;
  [ | PCperm_solve ].
apply wk_r.
apply de_r.
eapply ex_r ; [ apply pi | PCperm_solve ].
Qed.





