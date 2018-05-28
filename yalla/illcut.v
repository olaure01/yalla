(* ill library for yalla *)
(* v 1.1   Olivier Laurent *)


(* TODO clean file *)

(** * Intuitionistic Linear Logic *)

Require Import Omega.

Require Import Injective.
Require Import Bool_more.
Require Import List_more.
Require Import Permutation_more.
Require Import CyclicPerm.
Require Import Permutation_solve.
Require Import CPermutation_solve.
Require Import genperm.

Require Import ll.
Require Export iformulas.


(** ** Intuitionistic fragments for proofs *)

Record ipfrag := mk_ipfrag {
  ipcut : bool ;
  ipgax : list iformula -> iformula -> Prop ;
  ipperm : bool }.

Definition le_ipfrag P Q :=
     Bool.leb (ipcut P) (ipcut Q)
  /\ (forall f a, ipgax P f a -> ipgax Q f a)
  /\ Bool.leb (ipperm P) (ipperm Q).

Lemma le_ipfrag_trans : forall P Q R,
  le_ipfrag P Q -> le_ipfrag Q R -> le_ipfrag P R.
Proof with myeeasy.
intros P Q R H1 H2.
destruct H1 as (Hc1 & Ha1 & Hp1).
destruct H2 as (Hc2 & Ha2 & Hp2).
nsplit 3 ; try (eapply leb_trans ; myeeasy).
intros f a Hax.
apply Ha2.
apply Ha1...
Qed.

Definition cutupd_ipfrag P b := mk_ipfrag b (ipgax P) (ipperm P).

Definition axupd_ipfrag P G := mk_ipfrag (ipcut P) G (ipperm P).

Definition cutrm_ipfrag P := cutupd_ipfrag P false.


(** ** Rules *)

Inductive ill P : list iformula -> iformula -> nat -> Prop :=
| ax_ir : forall X, ill P (ivar X :: nil) (ivar X) 1
| ex_ir : forall l1 l2 A s, ill P l1 A s -> PEperm (ipperm P) l1 l2 ->
                            ill P l2 A (S s)
| one_irr : ill P nil ione 1
| one_ilr : forall l1 l2 A s, ill P (l1 ++ l2) A s ->
                              ill P (l1 ++ ione :: l2) A (S s)
| tens_irr : forall A B l1 l2 s1 s2,
                    ill P l1 A s1 -> ill P l2 B s2 ->
                    ill P (l1 ++ l2) (itens A B) (S (s1 + s2))
| tens_ilr : forall A B l1 l2 C s,
                    ill P (l1 ++ A :: B :: l2) C s ->
                    ill P (l1 ++ itens A B :: l2) C (S s)
| lpam_irr : forall A B l s,
                    ill P (l ++ A :: nil) B s ->
                    ill P l (ilpam A B) (S s)
| lpam_ilr : forall A B l0 l1 l2 C s1 s2,
                           ill P l0 A s1 -> ill P (l1 ++ B :: l2) C s2 ->
                           ill P (l1 ++ ilpam A B :: l0 ++ l2) C (S (s1 + s2))
| lmap_irr : forall A B l s,
                           ill P (A :: l) B s ->
                           ill P l (ilmap A B) (S s)
| lmap_ilr : forall A B l0 l1 l2 C s1 s2,
                           ill P l0 A s1 -> ill P (l1 ++ B :: l2) C s2 ->
                           ill P (l1 ++ l0 ++ ilmap A B :: l2) C (S (s1 + s2))
| neg_irr : forall A l s, ill P (A :: l) N s ->
                          ill P l (ineg A) (S s)
| neg_ilr : forall A l s, ill P l A s ->
                          ill P (l ++ ineg A :: nil) N (S s)
| top_irr : forall l, ill P l itop 1
| with_irr : forall A B l s1 s2,
                           ill P l A s1 -> ill P l B s2 ->
                           ill P l (iwith A B) (S (max s1 s2))
| with_ilr1 : forall A B l1 l2 C s, ill P (l1 ++ A :: l2) C s ->
                           ill P (l1 ++ iwith A B :: l2) C (S s)
| with_ilr2 : forall A B l1 l2 C s, ill P (l1 ++ A :: l2) C s ->
                           ill P (l1 ++ iwith B A :: l2) C (S s)
| zero_ilr : forall l1 l2 C, ill P (l1 ++ izero :: l2) C 1
| plus_irr1 : forall A B l s, ill P l A s ->
                              ill P l (iplus A B) (S s)
| plus_irr2 : forall A B l s, ill P l A s ->
                              ill P l (iplus B A) (S s)
| plus_ilr : forall A B l1 l2 C s1 s2,
                        ill P (l1 ++ A :: l2) C s1 ->
                        ill P (l1 ++ B :: l2) C s2 ->
                        ill P (l1 ++ iplus A B :: l2) C (S (max s1 s2))
| oc_irr : forall A l s,
                        ill P (map ioc l) A s ->
                        ill P (map ioc l) (ioc A) (S s)
| de_ilr : forall A l1 l2 C s,
                        ill P (l1 ++ A :: l2) C s ->
                        ill P (l1 ++ ioc A :: l2) C (S s)
| wk_ilr : forall A l1 l2 C s,
                        ill P (l1 ++ l2) C s ->
                        ill P (l1 ++ ioc A :: l2) C (S s)
| co_ilr : forall A lw l1 l2 C s,
                        ill P (l1 ++ ioc A :: map ioc lw
                                  ++ ioc A :: l2) C s ->
                        ill P (l1 ++ map ioc lw ++ ioc A :: l2) C (S s)
| cut_ir {f : ipcut P = true} : forall A l0 l1 l2 C s1 s2,
                               ill P l0 A s1 -> ill P (l1 ++ A :: l2) C s2 ->
                               ill P (l1 ++ l0 ++ l2) C (S (s1 + s2))
| gax_ir : forall l A, ipgax P l A -> ill P l A 1.

Lemma stronger_ipfrag P Q : le_ipfrag P Q -> forall l A s, ill P l A s -> ill Q l A s.
Proof with myeeasy.
intros Hle l A s H.
induction H ; try (constructor ; myeasy ; fail).
- apply (ex_ir _ l1)...
  destruct Hle as (_ & _ & Hp).
  hyps_PEperm_unfold ; unfold PEperm.
  destruct (ipperm P) ; destruct (ipperm Q) ;
    simpl in Hp ; try inversion Hp ; subst...
- destruct Hle as [Hcut _].
  rewrite f in Hcut.
  eapply (@cut_ir _ Hcut)...
- apply gax_ir.
  apply Hle...
Qed.

(** Generalized weakening for lists *)
Lemma wk_list_ilr {P} : forall l l1 l2 C s,
  ill P (l1 ++ l2) C s -> exists s', ill P (l1 ++ map ioc l ++ l2) C s'.
Proof with myeeasy.
induction l ; intros.
- eexists...
- apply IHl in H.
  destruct H as [s' H].
  eexists.
  apply wk_ilr...
Qed.

(** Generalized contraction for lists *)
Lemma co_list_ilr {P} : forall l lw l1 l2 C s,
  ill P (l1 ++ map ioc l ++ map ioc lw ++ map ioc l ++ l2) C s ->
    exists s', ill P (l1 ++ map ioc lw ++ map ioc l ++ l2) C s'.
Proof with myeeasy ; try PEperm_solve.
induction l ; intros.
- eexists...
- simpl in H.
  rewrite app_assoc in H.
  rewrite <- map_app in H.
  apply co_ilr in H.
  eapply (ex_ir _ _
    (l1 ++ map ioc l ++ map ioc (lw ++ a :: nil) ++ map ioc l ++ l2))
    in H.
  + apply IHl in H.
    destruct H as [s' H].
    eexists.
    eapply ex_ir...
    list_simpl...
  + list_simpl...
Qed.

(** Tactic for manipulating rules *)

Ltac inversion_ill H f X l Hl Hr HP Hax :=
  match type of H with
  | ill _ _ _ _ => inversion H as [ X
                                  | l ? ? ? Hl HP
                                  |
                                  | ? ? ? ? Hl Hr
                                  | ? ? ? ? ? ? Hl Hr
                                  | ? ? ? ? ? ? Hl
                                  | ? ? ? ? Hl
                                  | ? ? ? ? ? ? ? Hl Hr
                                  | ? ? ? ? Hl
                                  | ? ? ? ? ? ? ? Hl Hr
                                  | ? ? ? Hl
                                  | ? ? ? Hl
                                  | l
                                  | ? ? ? ? ? Hl Hr
                                  | ? ? ? ? ? ? Hl
                                  | ? ? ? ? ? ? Hl
                                  | ? ? ?
                                  | ? ? ? ? Hl
                                  | ? ? ? ? Hl
                                  | ? ? ? ? Hl Hr
                                  | ? ? ? Hl
                                  | ? ? ? ? ? Hl
                                  | ? ? ? ? ? Hl
                                  | ? ? ? ? ? ? Hl
                                  | f ? ? ? ? ? ? ? Hl Hr
                                  | l ? Hax] ; subst
  end.


(** Axiom expansion *)
Lemma ax_exp_ill {P} : forall A, exists s, ill P (A :: nil) A s.
Proof with myeeasy.
induction A ;
  try (destruct IHA as [s' IHA]) ;
  try (destruct IHA1 as [s1' IHA1]) ;
  try (destruct IHA2 as [s2' IHA2]) ;
  eexists.
- apply ax_ir.
- rewrite <- (app_nil_l (ione :: _)).
  apply one_ilr.
  apply one_irr.
- rewrite <- (app_nil_l (itens _ _ :: _)).
  apply tens_ilr.
  list_simpl ; cons2app.
  apply tens_irr...
- apply lpam_irr.
  list_simpl.
  rewrite <- (app_nil_l (ilpam _ _ :: _)).
  rewrite <- (app_nil_l nil).
  rewrite (app_comm_cons _ _ A1).
  apply lpam_ilr ; list_simpl...
- apply lmap_irr.
  list_simpl.
  cons2app.
  rewrite <- (app_nil_l ((A1 :: _) ++ _)).
  apply lmap_ilr ; list_simpl...
- apply neg_irr.
  cons2app.
  apply neg_ilr...
- apply top_irr.
- apply with_irr.
  + rewrite <- (app_nil_l (iwith _ _ :: _)).
    apply with_ilr1...
  + rewrite <- (app_nil_l (iwith _ _ :: _)).
    apply with_ilr2...
- rewrite <- (app_nil_l (izero :: _)).
  apply zero_ilr.
- rewrite <- (app_nil_l (iplus _ _ :: _)).
  apply plus_ilr.
  + apply plus_irr1...
  + apply plus_irr2...
- change (ioc A :: nil) with (map ioc (A :: nil)).
  apply oc_irr.
  simpl ; rewrite <- (app_nil_l (ioc A :: _)).
  apply de_ilr...
Qed.

(* TODO more general ipgax *)

Theorem cut_ir_axfree : forall P, (forall l C, ~ ipgax P l C) ->
  forall c s A l0 l1 l2 C s1 s2,
  ill P l0 A s1 -> ill P (l1 ++ A :: l2) C s2 ->
  s = s1 + s2 -> ifsize A <= c -> exists s,
    ill P (l1 ++ l0 ++ l2) C s.
Proof with myeasy_perm ; try ifsize_auto.
intros P Hgax.
case_eq (ipcut P) ; intros P_cutfree.
{ intros A l1 l2 l3 C s1 s2 Hl Hr.
  eexists.
  eapply cut_ir... }
induction c using (well_founded_induction lt_wf).
assert (
  forall A l0 l1 l2 C s1 s2,
  ill P l0 A s1 -> ill P (l1 ++ A :: l2) C s2 ->
  ifsize A < c -> exists s', ill P (l1 ++ l0 ++ l2) C s')
  as IHcut by (intros ; eapply H ; myeeasy).
clear H.
induction s using (well_founded_induction lt_wf).
assert (
  forall A l0 l1 l2 C s1 s2,
  ill P l0 A s1 -> ill P (l1 ++ A :: l2) C s2 ->
  s1 + s2 < s -> ifsize A <= c -> exists s', ill P (l1 ++ l0 ++ l2) C s')
  as IHsize by (intros ; eapply H ; myeeasy).
clear H.
intros A l0 l1 l2 C s1 s2 Hl Hr Heqs Hc.
rewrite_all Heqs ; clear s Heqs.
inversion_ill Hr f' X l' Hl2 Hr2 HP2 Hax.
- (* ax_ir *)
  eexists.
  destruct l1 ; inversion H ; subst ; list_simpl...
  destruct l1 ; inversion H2.
- (* ex_ir *)
  admit.
- (* one_irr *)
  destruct l1 ; inversion H.
- (* one_ilr *)
  dichot_elt_app_exec Hr2 ; subst.
  + list_simpl.
    rewrite app_assoc in Hl2.
    eapply IHsize in Hl...
    destruct Hl as [s' Hl].
    list_simpl in Hl.
    eexists.
    apply one_ilr...
  + destruct l5 ; inversion Hr1 ; subst.
    * admit.
    * rewrite 2 app_assoc.
      list_simpl in Hl2.
      eapply IHsize in Hl...
      destruct Hl as [s' Hl].
      eexists.
      apply one_ilr.
      list_simpl...
- (* tens_irr *)
  dichot_elt_app_exec H ; subst.
  + apply (IHsize _ _ _ _ _ _ _ Hl) in Hl2...
    destruct Hl2 as [s' Hl2].
    eexists.
    rewrite 2 app_assoc.
    apply tens_irr ; list_simpl...
  + apply (IHsize _ _ _ _ _ _ _ Hl) in Hr2...
    destruct Hr2 as [s' Hr2].
    eexists.
    list_simpl.
    apply tens_irr...
- (* tens_ilr *)
  admit.
- (* lpam_irr *)
  list_simpl in Hl2.
  apply (IHsize _ _ _ _ _ _ _ Hl) in Hl2...
  destruct Hl2 as [s' Hl2].
  eexists.
  apply lpam_irr ; list_simpl...
- (* lpam_ilr *)
  admit.
- (* lmap_irr *)
  rewrite app_comm_cons in Hl2.
  apply (IHsize _ _ _ _ _ _ _ Hl) in Hl2...
  destruct Hl2 as [s' Hl2].
  list_simpl in Hl2.
  eexists.
  apply lmap_irr...
- (* lmap_ilr *)
  admit.
- (* neg_irr *)
  rewrite app_comm_cons in Hl2.
  apply (IHsize _ _ _ _ _ _ _ Hl) in Hl2...
  destruct Hl2 as [s' Hl2].
  list_simpl in Hl2.
  eexists.
  apply neg_irr...
- (* neg_ilr *)
  admit.
- (* top_irr *)
  eexists.
  apply top_irr.
- (* with_irr *)
  apply (IHsize _ _ _ _ _ _ _ Hl) in Hl2...
  destruct Hl2 as [s1' Hl2].
  apply (IHsize _ _ _ _ _ _ _ Hl) in Hr2...
  destruct Hr2 as [s2' Hr2].
  eexists.
  apply with_irr...
- (* with_ilr1 *)
  admit.
- (* with_ilr2 *)
  admit.
- (* zero_ilr *)
  dichot_elt_app_exec H ; subst.
  + list_simpl.
    eexists.
    apply zero_ilr.
  + destruct l5 ; inversion H1 ; subst.
    * admit.
    * rewrite 2 app_assoc.
      eexists.
      apply zero_ilr.
- (* plus_irr1 *)
  apply (IHsize _ _ _ _ _ _ _ Hl) in Hl2...
  destruct Hl2 as [s' Hl2].
  eexists.
  apply plus_irr1...
- (* plus_irr2 *)
  apply (IHsize _ _ _ _ _ _ _ Hl) in Hl2...
  destruct Hl2 as [s' Hl2].
  eexists.
  apply plus_irr2...
- (* plus_ilr *)
  admit.
- (* oc_irr *)
  rewrite H in Hl2.
  apply (IHsize _ _ _ _ _ _ _ Hl) in Hl2...
  destruct Hl2 as [s' Hl2].
  symmetry in H ; decomp_map H ; subst.
  admit.
- (* de_ilr *)
  admit.
- (* wk_ilr *)
  admit.
- (* co_ilr *)
  admit.
- (* cut_ir *)
  rewrite f' in P_cutfree ; inversion P_cutfree.
- (* gax_ir *)
  apply Hgax in Hax...
Admitted.

Lemma cut_admissible_ill_axfree : forall P, (forall l C, ~ ipgax P l C) ->
  forall l C s, ill P l C s -> exists s', ill (cutrm_ipfrag P) l C s'.
Proof with myeeasy.
intros P Hgax l C s pi.
induction pi ;
  try (eexists ; constructor ; myeeasy ; fail) ;
  try (destruct IHpi as [s' IHpi] ; eexists ; constructor ; myeeasy ; fail) ;
  try (destruct IHpi1 as [s'1 IHpi1] ;
       destruct IHpi2 as [s'2 IHpi2] ; eexists ; constructor ; myeeasy ; fail).
- destruct IHpi as [s' IHpi].
  eexists.
  apply (ex_ir _ l1)...
- destruct IHpi1 as [s'1 IHpi1].
  destruct IHpi2 as [s'2 IHpi2].
  eapply cut_ir_axfree...
Qed.


