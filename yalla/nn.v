(* nn library for yalla *)
(* Coq 8.6 *)
(* v 1.0   Olivier Laurent *)


(** * Parametric double-negation translation from [ll] into [ill]. *)

Require Import Arith.

Require Import Injective.
Require Import Bool_more.
Require Import List_more.
Require Import Permutation_more.
Require Import genperm.

Require Import subs.
Require Import ll_fragments.
Require Import ill.

Require Import bbb.

(** ** Basic ingredients for links with [ill] *)

Axiom fz : ifzer = false.
Axiom ft : iftop = true.

Parameter i2a : IAtom -> Atom.
Parameter a2i : Atom -> IAtom.
Axiom a2a : forall x, i2a (a2i x) = x.
Axiom i2a_inj : injective i2a.

Definition ipfrag_ill := mk_ipfrag false (fun _ _ => False) true.
Definition ill_ll := ill ipfrag_ill.

Lemma pfrag_i2a_le : le_pfrag (i2pfrag i2a ipfrag_ill) pfrag_ll.
Proof.
nsplit 5 ; myeasy.
intros f Hax.
destruct Hax as (l & C & _ & Hax).
inversion Hax.
Qed.

Definition unill := ill2ll i2a.


(** ** The translation *)

(** Definition of the translation of formulas ([R] is the parameter) *)
Fixpoint trans R A :=
match A with
| var X     => ilmap (ivar (a2i X)) R
| covar X   => ivar (a2i X)
| one       => ilmap ione R
| bot       => ione
| tens A B  => ilmap (itens (ilmap (trans R A) R) (ilmap (trans R B) R)) R
| parr A B  => itens (trans R A) (trans R B)
| zero      => @itop ft
| top       => ilmap (@itop ft) R
| aplus A B => iwith (trans R A) (trans R B)
| awith A B => ilmap (iwith (ilmap (trans R A) R) (ilmap (trans R B) R)) R
| oc A      => ilmap (ioc (ilmap (trans R A) R)) R
| wn A      => ioc (trans R A)
end.

(** A provability statement [ll l] is translated as [ill (map (trans R) l) R]. *)

(** The translation maps [ll] proofs into [ill] proofs
(under some conditions for [mix0] and [mix2]). **)

Lemma ll_to_ill_trans_gen {P} : (forall l, ~ pgax P l) -> pperm P = true ->
  forall R l l0 s,
  (pmix0 P = true -> exists s0, ill_ll (map ioc l0) R s0) ->
  (pmix2 P = true -> forall l1 l2 s1 s2,
    ill_ll (map ioc l0 ++ l1) R s1 -> ill_ll (map ioc l0 ++ l2) R s2 ->
      exists s0, ill_ll (map ioc l0 ++ l2 ++ l1) R s0) ->
  ll P l s -> exists s', ill_ll (map ioc l0 ++ map (trans R) l) R s'.
Proof with myeeasy ; try PEperm_solve.
intros P_axfree P_perm R l l0 s Hmix0 Hmix2 Hll.
apply cut_admissible_axfree in Hll...
clear s ; destruct Hll as [s Hll].
assert (Hax := @ax_exp_ill fz i2a i2a_inj ipfrag_ill R).
destruct Hax as [sax Hax].
rewrite <- (app_nil_l (R :: _)) in Hax.
assert (Hax' := wk_list_ilr l0 _ _ _ _ Hax).
destruct Hax' as [sax' Hax'].
rewrite <- (app_nil_r (map _ _)) in Hmix0.
induction Hll ; 
  try (destruct IHHll as [s' pi']) ;
  try (destruct IHHll1 as [s1' pi1']) ;
  try (destruct IHHll2 as [s2' pi2']) ;
  try (apply Hmix0 ; myeasy ; fail) ;
  try (rewrite map_app ; eapply Hmix2 ; myeeasy ; fail) ;
  try (apply P_axfree in H ; inversion H ; fail) ;
  try (inversion f ; fail) ;
  simpl.
- eexists.
  eapply ex_ir.
  + eapply lmap_ilr ; [ | apply Hax' ].
    eapply (ax_ir _ (a2i X)).
  + PEperm_solve.
- eexists.
  simpl in H.
  rewrite P_perm in H.
  eapply ex_ir...
  apply PEperm_app_head...
  apply Permutation_map...
- eexists.
  rewrite <- (app_nil_r nil).
  rewrite <- (app_nil_l (map _ _)).
  apply lmap_ilr...
  apply one_irr.
- eexists.
  apply one_ilr...
- apply (ex_ir _ _ ((map ioc l0 ++ map (trans R) l1) ++ trans R A :: nil))
    in pi1'...
  apply lmap_irr in pi1'.
  apply (ex_ir _ _ ((map ioc l0 ++ map (trans R) l2) ++ trans R B :: nil))
    in pi2'...
  apply lmap_irr in pi2'.
  apply (tens_irr _ _ _ _ _ _ _ pi1') in pi2'.
  apply (lmap_ilr _ _ _ _ _ _ _ _ _ pi2') in Hax.
  rewrite <- (app_nil_l (map _ _ ++ _)).
  change nil with (map ioc nil).
  rewrite <- (app_nil_l (map _ _)).
  rewrite <- app_assoc.
  eapply co_list_ilr.
  apply (ex_ir _ _ _ _ _ Hax)...
- eexists.
  apply tens_ilr...
- eexists.
  rewrite <- (app_nil_r (map (trans _) _)).
  apply lmap_ilr...
  apply top_irr.
- eexists.
  apply with_ilr1...
- eexists.
  apply with_ilr2...
- eexists.
  apply (ex_ir _ _ ((map ioc l0 ++ map (trans R) l) ++ trans R A :: nil))
    in pi1'...
  apply lmap_irr in pi1'.
  apply (ex_ir _ _ ((map ioc l0 ++ map (trans R) l) ++ trans R B :: nil))
    in pi2'...
  apply lmap_irr in pi2'.
  apply (with_irr _ _ _ _ _ _ pi1') in pi2'.
  apply (lmap_ilr _ _ _ _ _ _ _ _ _ pi2') in Hax.
  apply (ex_ir _ _ _ _ _ Hax)...
- eexists.
  simpl in pi' ; rewrite map_map in pi'.
  simpl in pi' ; rewrite <- map_map in pi'.
  apply (ex_ir _ _ ((map ioc (l0 ++ map (trans R) l)) ++ trans R A :: nil))
    in pi'...
  + apply lmap_irr in pi'.
    apply oc_irr in pi'.
    eapply ex_ir ; [ | symmetry  ; apply Permutation_app_comm ].
    rewrite <- (app_nil_r (map ioc _)).
    rewrite <- (app_nil_l (ilmap _ _ :: _)).
    rewrite <- app_assoc.
    rewrite <- app_comm_cons.
    rewrite app_assoc.
    apply lmap_ilr...
    eapply ex_ir...
    list_simpl...
    rewrite ? map_map...
  + list_simpl...
    rewrite ? map_map...
- eexists.
  apply de_ilr...
- eexists.
  apply wk_ilr...
- eexists.
  rewrite <- (app_nil_l (map _ _ ++ _)).
  apply co_ilr.
  eapply ex_ir...
Qed.

Theorem ll_to_ill_trans {P} : (forall l, ~ pgax P l) -> pperm P = true ->
  forall R l s, 
  (pmix0 P = true -> exists s0, ill_ll nil R s0) ->
  (pmix2 P = true -> forall l1 l2 s1 s2,
    ill_ll l1 R s1 -> ill_ll l2 R s2 -> exists s0, ill_ll (l2 ++ l1) R s0) ->
  ll P l s -> exists s', ill_ll (map (trans R) l) R s'.
Proof with myeeasy.
intros Hgax Hperm R l s Hmix0 Hmix2 Hll.
rewrite <- (app_nil_l (map _ _)).
change nil with (map ioc nil).
eapply ll_to_ill_trans_gen...
Qed.

(** In [llR] (where [bot] is equivalent to [R]),
  [A] is implied by the dual of its translation. *)
Lemma back_to_llR : forall R A, exists s,
  llR (unill R) (unill (trans R A) :: A :: nil) s.
Proof with myeeasy ; try ((try rewrite a2a) ; PCperm_solve).
induction A ; simpl ; 
  try (destruct IHA as [s IHA]) ;
  try (destruct IHA1 as [s1 IHA1]) ;
  try (destruct IHA2 as [s2 IHA2]) ;
  rewrite ? bidual.
- eexists.
  apply parr_r.
  apply (ex_r _ ((covar a :: var a :: nil) ++ unill R :: nil))...
  eapply (@cut_r (pfrag_llR (unill R)) eq_refl (dual one)).
  + apply (ex_r _ (unill R :: one :: nil))...
    apply gax_r.
    right...
  + apply bot_r.
    apply ax_r.
- eexists.
  apply (ex_r _ (covar a :: var a :: nil))...
  apply ax_r...
- eexists.
  eapply parr_r.
  eapply ex_r ; [ | apply perm_swap ].
  eapply (bot_r (pfrag_llR (unill R))).
  apply gax_r.
  right...
- eexists.
  apply (ex_r _ (bot :: one :: nil))...
  apply bot_r.
  apply one_r.
- assert (Hax := @ax_exp (pfrag_llR (unill R)) (unill R)).
  destruct Hax as [sax Hax].
  eexists.
  apply parr_r.
  eapply ex_r ; [ | apply perm_swap ].
  apply parr_r.
  change (tens (unill (trans _ A2)) (dual (unill R)) ::
  tens (unill (trans _ A1)) (dual (unill R)) :: unill R :: tens A1 A2 :: nil)
    with (tens (unill (trans R A2)) (dual (unill R)) :: nil ++ 
    tens (unill (trans R A1)) (dual (unill R)) :: unill R :: tens A1 A2 :: nil).
  apply tens_r.
  + apply (ex_r _ (tens (unill (trans R A1)) (dual (unill R))
             :: (unill R :: nil) ++ (unill (trans R A2) :: tens A1 A2 :: nil)))...
    apply tens_r.
    -- apply (ex_r _ (tens A1 A2 ::
             (unill (trans R A2) :: nil) ++ unill (trans R A1) :: nil))...
       apply tens_r.
       ++ eapply ex_r ; [ apply IHA1 | ]...
       ++ eapply ex_r ; [ apply IHA2 | ]...
    -- eapply ex_r ; [ | apply perm_swap ].
       apply Hax.
  + apply gax_r.
    left...
- eexists.
  apply (ex_r _ (parr A1 A2 ::
                 tens (unill (trans R A1)) (unill (trans R A2)) :: nil))...
  apply parr_r.
  apply (ex_r _ (tens (unill (trans R A1)) (unill (trans R A2))
                  :: (A2 :: nil) ++ (A1 :: nil)))...
  apply tens_r...
- eexists.
  apply top_r.
- eexists.
  apply parr_r.
  apply (ex_r _ (top :: zero :: unill R :: nil))...
  eapply top_r.
- eexists.
  apply with_r.
  + eapply ex_r ; [ | apply perm_swap ].
    apply plus_r1.
    eapply ex_r ; [ | apply perm_swap ]...
  + eapply ex_r ; [ | apply perm_swap ].
    apply plus_r2.
    eapply ex_r ; [ | apply perm_swap ]...
- assert (Hax := @ax_exp (pfrag_llR (unill R)) (unill R)).
  destruct Hax as [sax Hax].
  eexists.
  eapply ex_r ; [ | apply perm_swap ].
  apply with_r.
  + eapply ex_r ; [ | apply perm_swap ].
    apply parr_r.
    eapply ex_r ; [ | apply perm_swap ].
    apply plus_r1.
    rewrite <- (app_nil_l (A1 :: _)).
    rewrite app_comm_cons.
    apply tens_r...
    eapply ex_r ; [ | apply perm_swap ]...
  + eapply ex_r ; [ | apply perm_swap ].
    apply parr_r.
    eapply ex_r ; [ | apply perm_swap ].
    apply plus_r2.
    rewrite <- (app_nil_l (A2 :: _)).
    rewrite app_comm_cons.
    apply tens_r...
    eapply ex_r ; [ | apply perm_swap ]...
- eexists.
  apply parr_r.
  apply (ex_r _ ((oc A ::
                  map wn (tens (unill (trans R A)) (dual (unill R)) :: nil))
                  ++ unill R :: nil)) ; [idtac | simpl]...
  apply (@cut_r (pfrag_llR (unill R)) eq_refl (dual one)).
  + apply (ex_r _ (unill R :: one :: nil))...
    apply gax_r.
    right...
  + apply bot_r.
    apply oc_r ; simpl.
    apply (ex_r _ ((wn (tens (unill (trans R A)) (dual (unill R))) :: nil)
                     ++ nil ++ (A :: nil)))...
    apply de_r.
    apply tens_r...
    apply gax_r.
    left...
- eexists.
  change (wn A :: nil) with (map wn (A :: nil)).
  apply oc_r ; simpl.
  apply (ex_r _ (wn A :: unill (trans R A) :: nil))...
  apply de_r...
  eapply ex_r ; [ | apply perm_swap ]...
Qed.

(** The previous lemma comes with the following result from the [ll_fragments] library:
<<
Lemma ll_to_llR : forall R l s, ll_ll l s -> exists s', llR R l s'.
>> to deduce: *)

(** A sequent whose translation is provable in [ill] was provable in [llR]. *)
Lemma ill_trans_to_llR : forall R l s,
  ill_ll (map (trans R) l) R s -> exists s', llR (unill R) l s'.
Proof with myeeasy ; try PCperm_solve.
intros R l s Hill.
apply (ill_to_ll i2a) in Hill.
clear s ; destruct Hill as [s Hill].
eapply stronger_pfrag in Hill ; [ | apply pfrag_i2a_le ].
apply (ll_to_llR (unill R)) in Hill.
clear s ; destruct Hill as [s Hill].
assert (forall l' s',
 llR (unill R) (l' ++ map dual (map unill (map (trans R) (rev l)))) s'
  -> exists s'', llR (unill R) (l' ++ rev l) s'') as Hll.
{ clear.
  induction l using rev_ind ; intros...
  - eexists...
  - assert (Hb := back_to_llR R x).
    destruct Hb as [sb Hb].
    rewrite rev_unit in H.
    apply (ex_r _ _ (dual (unill (trans R x))
             :: l' ++ map dual (map unill (map (trans R) (rev l))))) in H...
    apply (@cut_r _ (eq_refl (pcut (pfrag_llR (unill R)))) _ _ _ _ _ H) in Hb.
    rewrite rev_unit.
    change (x :: rev l) with ((x :: nil) ++ rev l).
    rewrite app_assoc.
    eapply IHl.
    eapply ex_r... }
assert (exists s, llR (unill R) (dual (unill R) :: nil) s) as [sR HR].
{ eexists.
  apply gax_r.
  left... }
apply (@cut_r _ (eq_refl (pcut (pfrag_llR (unill R)))) _ _ _ _ _ HR) in Hill.
rewrite app_nil_r in Hill.
rewrite <- (app_nil_l (rev _)) in Hill.
rewrite <- ? map_rev in Hill.
apply Hll in Hill.
destruct Hill as [s' Hill].
eexists.
eapply ex_r ; [ apply Hill | ].
symmetry.
apply Permutation_rev.
Qed.


(** Ingredients for generating fresh variables *)
Parameter a2n : Atom -> nat.
Parameter n2a : nat -> Atom.
Axiom n2n : forall n, a2n (n2a n) = n.


(** ** Study of the case [R = bot] *)

(** Given a sequent, the following 3 statements are equivalent:
 - the translation of the sequent is provable in [ill] for any [R];
 - the sequent is provable in [llR bot];
 - the sequent is provable in [ll].
*)

Theorem ill_trans_to_llR_bot : forall l s,
  (forall R, ill_ll (map (trans R) l) R s) -> exists s', llR bot l s'.
Proof with myeeasy ; try PCperm_solve.
intros l s Hill.
remember (fresh_of_list a2n n2a l) as z.
specialize Hill with (ivar (a2i z)).
apply ill_trans_to_llR in Hill.
destruct Hill as [s' Hill].
apply (subs_llR _ bot z) in Hill ; subst.
clear s' ; destruct Hill as [s' Hill].
eexists.
simpl in Hill.
rewrite repl_at_eq in Hill ; [ | rewrite a2a ]...
rewrite ? (subs_fresh_list _ _ n2n) in Hill...
Qed.

Theorem llR_bot_to_ll : forall l s, llR bot l s -> exists s', ll_ll l s'.
Proof with myeeasy.
intros l s HR.
induction HR ;
  try (inversion f ; fail) ;
  try (destruct IHHR as [s' IHHR]) ;
  try (destruct IHHR1 as [s1' IHHR1]) ;
  try (destruct IHHR2 as [s2' IHHR2]) ;
  try (eexists ; constructor ; myeeasy ; fail).
- eexists.
  eapply ex_r...
- eapply cut_ll_r...
- inversion H ; subst.
  + eexists.
    apply one_r.
  + eexists.
    apply bot_r.
    apply one_r.
Qed.

Theorem ll_ll_to_ill_trans : forall R l s,
  ll_ll l s -> exists s', ill_ll (map (trans R) l) R s'.
Proof with myeeasy.
intros R l s Hll.
eapply ll_to_ill_trans ; myeeasy ; myeeasy.
- intros l' Hax ; inversion Hax.
- intros f ; inversion f.
- intros f ; inversion f.
Qed.


(** ** Study of the case [R = one] *)

(** Given a sequent, the following 3 statements are equivalent:
 - the translation of the sequent is provable in [ill] for parameter [ione];
 - the sequent is provable in [llR one];
 - the sequent is provable in [ll_mix02].
*)

Lemma ill_trans_to_llR_one : forall l s,
  ill_ll (map (trans ione) l) ione s -> exists s', llR one l s'.
Proof.
apply ill_trans_to_llR.
Qed.

Theorem llR_one_to_ll_mix02 : forall l s,
  llR one l s -> exists s', ll_mix02 l s'.
Proof with myeeasy.
intros l s pi.
induction pi ;
  try (destruct IHpi as [s' pi']) ;
  try (destruct IHpi1 as [s1' pi1']) ;
  try (destruct IHpi2 as [s2' pi2']) ;
  try (eexists ; constructor ; myeeasy ; fail).
- eexists.
  eapply ex_r...
- eapply cut_mix02_r...
- destruct H ; subst.
  + eexists.
    apply bot_r.
    apply (@mix0_r _ (eq_refl (pmix0 pfrag_mix02))).
  + eexists.
    change (one :: one :: nil) with ((one :: nil) ++ (one :: nil)).
    apply (@mix2_r _ (eq_refl (pmix2 pfrag_mix02))) ;
    apply one_r.
Qed.

Theorem ll_mix02_to_ill_trans : forall l s,
  ll_mix02 l s -> exists s', ill_ll (map (trans ione) l) ione s'.
Proof with myeeasy.
intros l s Hll.
eapply ll_to_ill_trans ; myeeasy ; myeeasy.
- intros l' Hax ; inversion Hax.
- intros f.
  eexists.
  apply one_irr.
- intros f l1 l2 s1 s2 pi1 pi2.
  rewrite <- (app_nil_l (l2 ++ l1)).
  rewrite <- (app_nil_r (l2 ++ l1)).
  assert (forall l C, ~ ipgax ipfrag_ill l C)
     as I_axfree by (intros ? ? Hgax ; inversion Hgax).
  eapply (@cut_ir_axfree fz i2a i2a_inj _ I_axfree
                         (itens ione ione)).
  + apply tens_irr...
  + apply tens_ilr.
    apply one_ilr.
    apply one_ilr.
    apply one_irr.
Qed.


(** ** Study of the case [R = wn one] *)

(** Given a sequent, the following 3 statements are equivalent:
 - the translation of the sequent is provable in [ill] for any parameter [R] such that [R] is provable in [ill];
 - the sequent is provable in [llR (wn one)];
 - the sequent is provable in [ll_mix0].
*)

Theorem ill_trans_to_llR_wn_one : forall l,
  (forall R s, ill_ll nil R s -> exists s', ill_ll (map (trans R) l) R s') ->
    exists s'', llR (wn one) l s''.
Proof with myeeasy ; try PCperm_solve.
intros l Hill.
remember (fresh_of_list a2n n2a l) as z.
assert (exists s, ill_ll nil (ilmap (ioc (ivar (a2i z))) (ivar (a2i z))) s)
  as [s Hz].
{ eexists.
  apply lmap_irr.
  apply de_ilr.
  apply ax_ir. }
specialize Hill with (ilmap (ioc (ivar (a2i z))) (ivar (a2i z))) s.
assert (Hz2 := Hz).
apply Hill in Hz2 ; clear Hill.
destruct Hz2 as [s' Hill].
apply ill_trans_to_llR in Hill...
clear s' ; destruct Hill as [s' Hill].
apply (subs_llR _ bot z) in Hill ; subst.
simpl in Hill.
rewrite repl_at_eq in Hill ; try rewrite a2a...
clear s' ; destruct Hill as [s' Hill].
assert (Hax := @ax_exp (pfrag_llR (wn one)) (wn one)).
destruct Hax as [sax Hax].
eapply (llR1_R2 _ (wn one)) in Hill.
- clear s' ; destruct Hill as [s' Hill].
  eexists.
  rewrite ? (subs_fresh_list _ _ n2n) in Hill...
- simpl.
  rewrite <- (app_nil_l (wn _ :: _)).
  apply tens_r.
  + change (wn one :: nil) with (map wn (one :: nil)).
    apply oc_r ; simpl.
    apply bot_r.
    apply de_r.
    apply one_r.
  + apply one_r.
- simpl.
  apply (ex_r _ (parr bot (wn one) :: oc bot :: nil))...
  apply parr_r.
  apply bot_r.
  change (wn one) with (dual (oc bot))...
Qed.

Theorem llR_wn_one_to_ll_mix0 : forall l s,
  llR (wn one) l s -> exists s', ll_mix0 l s'.
Proof with myeeasy.
intros l s pi.
induction pi ;
  try (destruct IHpi as [s' pi']) ;
  try (destruct IHpi1 as [s1' pi1']) ;
  try (destruct IHpi2 as [s2' pi2']) ;
  try (eexists ; constructor ; myeeasy ; fail).
- eexists.
  eapply ex_r...
- eapply cut_mix0_r...
- destruct H ; subst.
  + eexists.
    change nil with (map wn nil).
    apply oc_r.
    apply bot_r.
    apply (@mix0_r _ (eq_refl (pmix0 pfrag_mix0))).
  + eexists.
    apply wk_r.
    apply one_r.
Qed.

Theorem ll_mix0_to_ill_trans : forall R l s0 s,
  ill_ll nil R s0 -> ll_mix0 l s -> exists s', ill_ll (map (trans R) l) R s'.
Proof with myeeasy.
intros R l s0 s HR Hll.
eapply ll_to_ill_trans ; myeeasy ; myeeasy.
- intros l' Hax ; inversion Hax.
- intros f ; eexists...
- intros f ; inversion f.
Qed.


(** ** Study of the case [R = oc bot] *)

(** Given a sequent, the following 3 statements are equivalent:
 - the translation of the sequent is provable in [ill] for any parameter [ioc R];
 - the sequent is provable in [llR (oc bot)];
 - the sequent is provable in [ll_bbb].
*)

Theorem ill_trans_to_llR_oc_bot : forall l,
  (forall R, exists s, ill_ll (map (trans (ioc R)) l) (ioc R) s) ->
    exists s', llR (oc bot) l s'.
Proof with myeeasy ; try PCperm_solve.
intros l Hill.
remember (fresh_of_list a2n n2a l) as z.
specialize Hill with (ivar (a2i z)).
destruct Hill as [s Hill].
apply ill_trans_to_llR in Hill...
clear s ; destruct Hill as [s Hill].
apply (subs_llR _ bot z) in Hill ; subst.
clear s ; destruct Hill as [s Hill].
eexists.
simpl in Hill.
rewrite repl_at_eq in Hill ; [ | rewrite a2a ]...
rewrite ? (subs_fresh_list _ _ n2n) in Hill...
Qed.

Theorem llR_oc_bot_to_ll_bbb : forall l s,
  llR (oc bot) l s -> exists s', ll_bbb l s'.
Proof.
apply bb_to_bbb.
Qed.

Lemma ll_mix02_to_ill_trans_gen : forall R l s,
 ll_mix02 l s -> exists s',
   ill_ll (ioc R :: map (trans (ioc R)) l) (ioc R) s'.
Proof with myeeasy.
intros R l s Hll.
assert (Hax := @ax_exp_ill fz i2a i2a_inj ipfrag_ill (ioc R)).
destruct Hax as [sax Hax].
change (ioc R :: map (trans _) l)
  with (map ioc (R :: nil) ++ map (trans (ioc R)) l).
eapply ll_to_ill_trans_gen ; intros ; simpl...
- intro Hgax ; inversion Hgax.
- simpl...
- eexists...
- rewrite <- (app_nil_l (ioc R :: _)).
  rewrite <- (app_nil_r l1).
  rewrite app_comm_cons.
  rewrite (app_assoc _ l1).
  assert (forall l C, ~ ipgax ipfrag_ill l C)
     as I_axfree by (intros ? ? Hgax ; inversion Hgax).
  eapply (@cut_ir_axfree fz i2a i2a_inj _ I_axfree
                         (itens (ioc R) (ioc R))).
  + rewrite <- 2 (app_nil_l (ioc R :: _)).
    rewrite <- ? app_assoc.
    change nil with (map ioc nil) at 2.
    apply co_ilr.
    eapply ex_ir.
    * apply tens_irr ; [ apply H0 | apply H1 ].
    * PEperm_solve.
  + apply tens_ilr.
    apply wk_ilr...
Qed.

Theorem ll_bbb_to_ill_trans : forall R l s,
  ll_bbb l s -> exists s', ill_ll (map (trans (ioc R)) l) (ioc R) s'.
Proof with myeeasy ; try PEperm_solve.
intros R l s Hll.
assert (Hax := @ax_exp_ill fz i2a i2a_inj ipfrag_ill (ioc R)).
destruct Hax as [sax Hax].
rewrite <- (app_nil_l (ioc R :: _)) in Hax.
induction Hll ; 
  try (inversion f ; fail) ;
  try (inversion H ; fail) ;
  try (destruct IHHll as [s' pi']) ;
  try (destruct IHHll1 as [s1' pi1']) ;
  try (destruct IHHll2 as [s2' pi2']) ;
  simpl.
- eexists.
  eapply ex_ir.
  + eapply lmap_ilr ; [ | apply Hax ].
    eapply (ax_ir _ (a2i X)).
  + PEperm_solve.
- eexists.
  eapply ex_ir...
  apply Permutation_map...
- apply (ll_mix02_to_ill_trans_gen R) in H.
  destruct H as [s'' H].
  rewrite <- (app_nil_l (ioc _ :: _)) in H.
  rewrite map_app.
  eapply @cut_ir_axfree in H.
  + destruct H as [s0 H].
    eexists.
    eapply ex_ir ; [ | apply Permutation_app_comm ]...
  + apply fz.
  + apply i2a_inj.
  + intros l C Hgax ; inversion Hgax.
  + eassumption.
- eexists.
  rewrite <- (app_nil_r nil).
  rewrite <- (app_nil_l (ilmap _ _ :: _)).
  apply lmap_ilr...
  apply one_irr.
- eexists.
  rewrite <- (app_nil_l (ione :: _)).
  apply one_ilr...
- eexists.
  rewrite <- (app_nil_r (map _ _)).
  rewrite <- (app_nil_l (ilmap _ _ :: _)).
  apply lmap_ilr...
  rewrite map_app.
  eapply ex_ir ; [ | apply Permutation_app_comm ].
  apply tens_irr ; apply lmap_irr ; eapply ex_ir.
  + apply pi1'.
  + PEperm_solve.
  + apply pi2'.
  + PEperm_solve.
- eexists.
  rewrite <- (app_nil_l (itens _ _ :: _)).
  apply tens_ilr...
- eexists.
  rewrite <- (app_nil_r (map _ _)).
  rewrite <- (app_nil_l (ilmap _ _ :: _)).
  apply lmap_ilr...
  apply top_irr.
- eexists.
  rewrite <- (app_nil_r (map _ _)).
  rewrite <- (app_nil_l (iwith _ _ :: _)).
  apply with_ilr1.
  eapply ex_ir...
- eexists.
  rewrite <- (app_nil_r (map _ _)).
  rewrite <- (app_nil_l (iwith _ _ :: _)).
  apply with_ilr2.
  eapply ex_ir...
- eexists.
  rewrite <- (app_nil_r (map _ _)).
  rewrite <- (app_nil_l (ilmap _ _ :: _)).
  apply lmap_ilr...
  apply with_irr ; apply lmap_irr ; eapply ex_ir.
  + apply pi1'.
  + PEperm_solve.
  + apply pi2'.
  + PEperm_solve.
- eexists.
  rewrite <- (app_nil_r (map _ _)).
  rewrite <- (app_nil_l (ilmap _ _ :: _)).
  apply lmap_ilr...
  rewrite map_map ; simpl.
  rewrite <- map_map.
  simpl in pi' ; rewrite map_map in pi'.
  simpl in pi' ; rewrite <- map_map in pi'.
  apply oc_irr.
  apply lmap_irr.
  eapply ex_ir...
- eexists.
  rewrite <- (app_nil_l (ioc _ :: _)).
  apply de_ilr...
- eexists.
  rewrite <- (app_nil_l (ioc _ :: _)).
  apply wk_ilr...
- eexists.
  rewrite <- 2 (app_nil_l (ioc _ :: _)).
  change nil with (map ioc nil).
  apply co_ilr.
  eapply ex_ir...
Qed.

(** The following result is the converse of [bb_to_bbb] proved in the [bbb] library *)
Theorem bbb_to_bb : forall l s, ll_bbb l s -> exists s', llR (oc bot) l s'.
Proof with myeeasy.
intros l s pi.
assert (forall R, exists s', ill_ll (map (trans (ioc R)) l) (ioc R) s')
  as pi' by (intro R ; eapply ll_bbb_to_ill_trans ; myeeasy).
apply ill_trans_to_llR_oc_bot in pi'.
destruct pi' as [s' pi'].
eexists...
Qed.


