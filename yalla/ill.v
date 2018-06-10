(* ill library for yalla *)

(* output in Type *)

(* TODO clean file *)

(** * Intuitionistic Linear Logic *)

(* TODO update Makefile *)

Require Import CRelationClasses.
Require Import CMorphisms.
Require Import Omega.

Require Import Injective.
Require Import Bool_more.
Require Import List_more.
Require Import List_Type.
Require Import List_Type_more.
Require Import Permutation_Type_more.
Require Import CyclicPerm_Type.
Require Import Permutation_Type_solve.
Require Import CPermutation_Type_solve.
Require Import genperm_Type.

Require Import ll.
Require Export iformulas.


(** ** Intuitionistic fragments for proofs *)

Record ipfrag := mk_ipfrag {
  ipcut : bool ;
  ipgax : { iptypgax : Type & iptypgax -> list iformula * iformula } ; (* Many thanks to Damien Pous! *)
  ipperm : bool }.

Definition le_ipfrag P Q :=
  prod 
     (Bool.leb (ipcut P) (ipcut Q))
  (prod
     (forall a, { b | projT2 (ipgax P) a = projT2 (ipgax Q) b })
     (Bool.leb (ipperm P) (ipperm Q))).

Lemma le_ipfrag_trans : forall P Q R,
  le_ipfrag P Q -> le_ipfrag Q R -> le_ipfrag P R.
Proof with myeeasy.
intros P Q R H1 H2.
destruct H1 as (Hc1 & Ha1 & Hp1).
destruct H2 as (Hc2 & Ha2 & Hp2).
nsplit 3 ; try (eapply leb_trans ; myeeasy).
intros a.
destruct (Ha1 a) as [b Heq].
destruct (Ha2 b) as [c Heq2].
exists c ; etransitivity...
Qed.

Instance le_ipfrag_po : PreOrder le_ipfrag.
Proof.
split.
- nsplit 3 ; try reflexivity.
  simpl ; intros a.
  exists a ; reflexivity.
- intros P Q R.
  apply le_ipfrag_trans.
Qed.

Definition cutupd_ipfrag P b := mk_ipfrag b (ipgax P) (ipperm P).

Definition axupd_ipfrag P G := mk_ipfrag (ipcut P) G (ipperm P).

Definition cutrm_ipfrag P := cutupd_ipfrag P false.


(** ** Rules *)

Inductive ill P : list iformula -> iformula -> Type :=
| ax_ir : forall X, ill P (ivar X :: nil) (ivar X)
| ex_ir : forall l1 l2 A, ill P l1 A -> PEperm_Type (ipperm P) l1 l2 ->
                          ill P l2 A
| one_irr : ill P nil ione
| one_ilr : forall l1 l2 A, ill P (l1 ++ l2) A ->
                            ill P (l1 ++ ione :: l2) A
| tens_irr : forall A B l1 l2,
             ill P l1 A -> ill P l2 B -> ill P (l1 ++ l2) (itens A B)
| tens_ilr : forall A B l1 l2 C,
             ill P (l1 ++ A :: B :: l2) C -> ill P (l1 ++ itens A B :: l2) C
| lpam_irr : forall A B l,
             ill P (l ++ A :: nil) B -> ill P l (ilpam A B)
| lpam_ilr : forall A B l0 l1 l2 C,
                           ill P l0 A -> ill P (l1 ++ B :: l2) C ->
                           ill P (l1 ++ ilpam A B :: l0 ++ l2) C
| lmap_irr : forall A B l,
             ill P (A :: l) B -> ill P l (ilmap A B)
| lmap_ilr : forall A B l0 l1 l2 C,
                  ill P l0 A -> ill P (l1 ++ B :: l2) C ->
                  ill P (l1 ++ l0 ++ ilmap A B :: l2) C
| neg_irr : forall A l, ill P (A :: l) N -> ill P l (ineg A)
| neg_ilr : forall A l, ill P l A -> ill P (l ++ ineg A :: nil) N
| top_irr : forall l, ill P l itop
| with_irr : forall A B l,
             ill P l A -> ill P l B -> ill P l (iwith A B)
| with_ilr1 : forall A B l1 l2 C, ill P (l1 ++ A :: l2) C->
                           ill P (l1 ++ iwith A B :: l2) C
| with_ilr2 : forall A B l1 l2 C, ill P (l1 ++ A :: l2) C ->
                           ill P (l1 ++ iwith B A :: l2) C
| zero_ilr : forall l1 l2 C, ill P (l1 ++ izero :: l2) C
| plus_irr1 : forall A B l, ill P l A -> ill P l (iplus A B)
| plus_irr2 : forall A B l, ill P l A -> ill P l (iplus B A)
| plus_ilr : forall A B l1 l2 C,
             ill P (l1 ++ A :: l2) C -> ill P (l1 ++ B :: l2) C ->
             ill P (l1 ++ iplus A B :: l2) C
| oc_irr : forall A l,
           ill P (map ioc l) A -> ill P (map ioc l) (ioc A)
| de_ilr : forall A l1 l2 C,
           ill P (l1 ++ A :: l2) C -> ill P (l1 ++ ioc A :: l2) C
| wk_ilr : forall A l1 l2 C,
           ill P (l1 ++ l2) C -> ill P (l1 ++ ioc A :: l2) C
| co_ilr : forall A lw l1 l2 C,
            ill P (l1 ++ ioc A :: map ioc lw ++ ioc A :: l2) C ->
                        ill P (l1 ++ map ioc lw ++ ioc A :: l2) C
| cut_ir {f : ipcut P = true} : forall A l0 l1 l2 C,
           ill P l0 A -> ill P (l1 ++ A :: l2) C-> ill P (l1 ++ l0 ++ l2) C
| gax_ir : forall a,
           ill P (fst (projT2 (ipgax P) a)) (snd (projT2 (ipgax P) a)).


Instance ill_perm {P} : forall A,
  Proper ((@PEperm_Type _ (ipperm P)) ==> Basics.arrow) (fun l => ill P l A).
Proof.
intros A l1 l2 HP pi.
eapply ex_ir ; eassumption.
Qed.

Fixpoint ipsize {P l A} (pi : ill P l A) :=
match pi with
| ax_ir _ _ => 1
| ex_ir _ _ _ _ pi0 _ => S (ipsize pi0)
| one_irr _ => 1
| one_ilr _ _ _ _ pi0 => S (ipsize pi0)
| tens_irr _ _ _ _ _ pi1 pi2 => S (ipsize pi1 + ipsize pi2)
| tens_ilr _ _ _ _ _ _ pi0 => S (ipsize pi0)
| lpam_irr _ _ _ _ pi0 => S (ipsize pi0)
| lpam_ilr _ _ _ _ _ _ _ pi1 pi2 => S (ipsize pi1 + ipsize pi2)
| lmap_irr _ _ _ _ pi0 => S (ipsize pi0)
| lmap_ilr _ _ _ _ _ _ _ pi1 pi2 => S (ipsize pi1 + ipsize pi2)
| neg_irr _ _ _ pi0 => S (ipsize pi0)
| neg_ilr _ _ _ pi0 => S (ipsize pi0)
| top_irr _ _ => 1
| with_irr _ _ _ _ pi1 pi2 => S (max (ipsize pi1) (ipsize pi2))
| with_ilr1 _ _ _ _ _ _ pi0 => S (ipsize pi0)
| with_ilr2 _ _ _ _ _ _ pi0 => S (ipsize pi0)
| zero_ilr _ _ _ _ => 1
| plus_irr1 _ _ _ _ pi0 => S (ipsize pi0)
| plus_irr2 _ _ _ _ pi0 => S (ipsize pi0)
| plus_ilr _ _ _ _ _ _ pi1 pi2 => S (max (ipsize pi1) (ipsize pi2))
| oc_irr _ _ _ pi0 => S (ipsize pi0)
| de_ilr _ _ _ _ _ pi0 => S (ipsize pi0)
| wk_ilr _ _ _ _ _ pi0 => S (ipsize pi0)
| co_ilr _ _ _ _ _ _ pi0 => S (ipsize pi0)
| cut_ir _ _ _ _ _ _ pi1 pi2 => S (ipsize pi1 + ipsize pi2)
| gax_ir _ _ => 1
end.

Lemma stronger_ipfrag P Q : le_ipfrag P Q -> forall l A, ill P l A -> ill Q l A.
Proof with myeeasy.
intros Hle l A H.
induction H ; try (constructor ; myeasy ; fail).
- apply (ex_ir _ l1)...
  destruct Hle as (_ & _ & Hp).
  hyps_PEperm_Type_unfold ; unfold PEperm_Type.
  destruct (ipperm P) ; destruct (ipperm Q) ;
    simpl in Hp ; try inversion Hp ; subst...
- destruct Hle as [Hcut _].
  rewrite f in Hcut.
  eapply (@cut_ir _ Hcut)...
- destruct Hle as (_ & Hgax & _).
  destruct (Hgax a) as [b Heq].
  rewrite Heq.
  apply gax_ir.
Qed.

(** Generalized weakening for lists *)
Lemma wk_list_ilr {P} : forall l l1 l2 C,
  ill P (l1 ++ l2) C -> ill P (l1 ++ map ioc l ++ l2) C.
Proof with myeeasy.
induction l ; intros...
apply wk_ilr.
apply IHl...
Qed.

(** Generalized contraction for lists *)
Lemma co_list_ilr {P} : forall l lw l1 l2 C,
  ill P (l1 ++ map ioc l ++ map ioc lw ++ map ioc l ++ l2) C ->
  ill P (l1 ++ map ioc lw ++ map ioc l ++ l2) C.
Proof with myeeasy ; try PEperm_Type_solve.
induction l ; intros...
simpl in X.
rewrite app_assoc in X.
rewrite <- map_app in X.
apply co_ilr in X.
eapply (ex_ir _ _
  (l1 ++ map ioc l ++ map ioc (lw ++ a :: nil) ++ map ioc l ++ l2))
  in X.
- apply IHl in X.
  eapply ex_ir...
  list_simpl...
- list_simpl...
Qed.

(** Axiom expansion *)
Lemma ax_exp_ill {P} : forall A, ill P (A :: nil) A.
Proof with myeeasy.
induction A.
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


(* TODO
Axiom cut_ir_axfree : forall P, (forall l C, ~ ipgax P l C) -> forall A l0 l1 l2 C s1 s2,
  ill P l0 A s1 -> ill P (l1 ++ A :: l2) C s2 -> exists s,
    ill P (l1 ++ l0 ++ l2) C s.

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
*)


(** ** Relating negation and implication *)

Lemma ilmap_to_ineg {P} : forall A, ill P (ilmap A N :: nil) (ineg A).
Proof.
intros A.
apply neg_irr.
cons2app.
rewrite <- (app_nil_l _).
apply lmap_ilr ; apply ax_exp_ill.
Qed.

Lemma ineg_to_ilmap {P} : forall A, ill P (ineg A :: nil) (ilmap A N).
Proof.
intros A.
apply lmap_irr.
cons2app.
apply neg_ilr.
apply ax_exp_ill.
Qed.

Lemma neg_pam_rule {P} :
  (forall a, In_Type N (fst (projT2 (ipgax P) a)) -> False) ->
  forall l0 l1 l2 C D (pi0 : ill P l0 C) (pi : ill P (l1 ++ N :: l2) D),
    { pi : ill P (l1 ++ l0 ++ ineg C :: l2) D
         & ipsize pi < S (ipsize pi0 + ipsize pi) }.
Proof with myeeasy ; try omega.
intros Hgax.
intros l0 l1 l2 C D pi0 pi.
remember (l1 ++ N :: l2) as l.
revert l1 l2 Heql.
induction pi ; intros l1' l2' Heq ; subst ;
  try (destruct (IHpi _ _ eq_refl) as [pi' Hs]) ;
  try (destruct (IHpi1 _ _ eq_refl) as [pi1' Hs1]) ;
  try (destruct (IHpi2 _ _ eq_refl) as [pi2' Hs2]).
- destruct l1' ; inversion Heq ; subst.
  + exists (neg_ilr _ _ _ pi0)...
  + destruct l1' ; inversion H1.
- case_eq (ipperm P) ; intros Hperm ; rewrite_all Hperm.
  + apply PEperm_Type_vs_elt_inv in p.
    destruct p as [(l3 & l4) Heq HP] ; simpl in HP ; subst.
    destruct (IHpi _ _ eq_refl) as [pi' Hs].
    assert (PEperm_Type (ipperm P) (l3 ++ l0 ++ ineg C :: l4)
                                   (l1' ++ l0 ++ ineg C :: l2')) as HP'.
    { rewrite Hperm.
      symmetry.
      apply Permutation_Type_app_middle.
      apply Permutation_Type_elt... }
    exists (ex_ir _ _ _ _ pi' HP')...
  + simpl in p ; subst.
    destruct (IHpi _ _ eq_refl) as [pi' Hs].
    exists pi'...
- destruct l1' ; inversion Heq.
- dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_assoc in IHpi.
    assert (pi':=IHpi _ _ eq_refl).
    list_simpl in pi'.
    destruct pi' as [pi' Hs].
    list_simpl.
    exists (one_ilr _ _ _ _ pi')...
  + destruct l3 ; inversion Heq1 ; subst.
    list_simpl in IHpi.
    assert (pi':=IHpi _ _ eq_refl).
    rewrite app_comm_cons in pi'.
    rewrite 2 app_assoc in pi'.
    destruct pi' as [pi' Hs].
    rewrite app_comm_cons.
    rewrite 2 app_assoc.
    exists (one_ilr _ _ _ _ pi')...
- dichot_Type_elt_app_exec Heq ; subst.
  + destruct (IHpi1 _ _ eq_refl) as [pi' Hs].
    rewrite app_comm_cons.
    rewrite 2 app_assoc.
    rewrite <- (app_assoc l1').
    exists (tens_irr _ _ _ _ _ pi' pi2)...
  + destruct (IHpi2 _ _ eq_refl) as [pi' Hs].
    list_simpl.
    exists (tens_irr _ _ _ _ _ pi1 pi')...
- dichot_Type_elt_app_exec Heq ; subst.
  + rewrite 2 app_comm_cons in IHpi.
    rewrite app_assoc in IHpi.
    assert (pi' := IHpi _ _ eq_refl).
    list_simpl in pi'.
    destruct pi' as [pi' Hs].
    list_simpl.
    exists (tens_ilr _ _ _ _ _ _ pi')...
  + destruct l3 ; inversion Heq1 ; subst.
    list_simpl in IHpi.
    assert (pi' := IHpi _ _ eq_refl).
    rewrite app_comm_cons in pi'.
    rewrite 2 app_assoc in pi'.
    destruct pi' as [pi' Hs].
    rewrite app_comm_cons.
    rewrite 2 app_assoc.
    exists (tens_ilr _ _ _ _ _ _ pi')...
- list_simpl in IHpi.
  assert (pi' := IHpi _ _ eq_refl).
  rewrite app_comm_cons in pi'.
  rewrite 2 app_assoc in pi'.
  destruct pi' as [pi' Hs].
  rewrite app_assoc.
  exists (lpam_irr _ _ _ _ pi')...
- dichot_Type_elt_app_exec Heq ; subst.
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * destruct (IHpi1 _ _ eq_refl) as [pi' Hs].
      list_simpl.
      rewrite (app_comm_cons _ _ (ineg C)).
      rewrite app_comm_cons.
      rewrite 2 (app_assoc _ _ l3).
      rewrite <- 2 app_comm_cons.
      exists (lpam_ilr _ _ _ _ _ _ _ pi' pi2)...
    * rewrite app_comm_cons in IHpi2.
      rewrite app_assoc in IHpi2.
      assert (pi' := IHpi2 _ _ eq_refl).
      list_simpl in pi'.
      destruct pi' as [pi' Hs].
      list_simpl.
      exists (lpam_ilr _ _ _ _ _ _ _ pi1 pi')...
  + destruct l4 ; inversion Heq1 ; subst.
    list_simpl in IHpi2.
    assert (pi' := IHpi2 _ _ eq_refl).
    rewrite (app_comm_cons _ _ (ineg C)) in pi'.
    rewrite 2 app_assoc in pi'.
    destruct pi' as [pi' Hs].
    rewrite (app_comm_cons _ _ (ineg C)).
    rewrite 2 app_assoc.
    exists (lpam_ilr _ _ _ _ _ _ _ pi1 pi')...
- rewrite app_comm_cons in IHpi.
  destruct (IHpi _ _ eq_refl) as [pi' Hs].
  exists (lmap_irr _ _ _ _ pi')...
- dichot_Type_elt_app_exec Heq ; subst.
  + list_simpl in IHpi2.
    assert (pi' := IHpi2 _ _ eq_refl).
    rewrite app_comm_cons in pi'.
    rewrite 2 app_assoc in pi'.
    destruct pi' as [pi' Hs].
    rewrite app_comm_cons.
    rewrite 2 app_assoc.
    exists (lmap_ilr _ _ _ _ _ _ _ pi1 pi')...
  + symmetry in Heq1.
    dichot_Type_elt_app_exec Heq1 ; subst.
    * rewrite app_comm_cons in IHpi2.
      rewrite app_assoc in IHpi2.
      assert (pi' := IHpi2 _ _ eq_refl).
      list_simpl in pi'.
      destruct pi' as [pi' Hs].
      list_simpl.
      exists (lmap_ilr _ _ _ _ _ _ _ pi1 pi')...
    * destruct l5 ; inversion Heq2 ; subst.
      assert (pi' := IHpi1 _ _ eq_refl).
      destruct pi' as [pi' Hs].
      list_simpl.
      rewrite app_comm_cons.
      rewrite (app_assoc l4).
      rewrite (app_assoc (l4 ++ _)).
      rewrite <- (app_assoc l4).
      exists (lmap_ilr _ _ _ _ _ _ _ pi' pi2)...
- rewrite app_comm_cons in IHpi.
  destruct (IHpi _ _ eq_refl) as [pi' Hs].
  exists (neg_irr _ _ _ pi')...
- dichot_Type_elt_app_exec Heq ; subst.
  + destruct l1 ; inversion Heq1.
  + destruct l2 ; inversion Heq1 ; subst.
    assert (pi' := IHpi _ _ eq_refl).
    destruct pi' as [pi' Hs].
    rewrite ? app_comm_cons.
    rewrite ? app_assoc.
    rewrite <- (app_assoc l1').
    exists (neg_ilr _ _ _ pi')...
- exists (top_irr _ _)...
- exists (with_irr _ _ _ _ pi1' pi2')...
- dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_comm_cons in IHpi.
    rewrite app_assoc in IHpi.
    assert (pi' := IHpi _ _ eq_refl).
    list_simpl in pi'.
    destruct pi' as [pi' Hs].
    list_simpl.
    exists (with_ilr1 _ _ _ _ _ _ pi')...
  + destruct l3 ; inversion Heq1 ; subst.
    list_simpl in IHpi.
    assert (pi' := IHpi _ _ eq_refl).
    rewrite app_comm_cons in pi'.
    rewrite 2 app_assoc in pi'.
    destruct pi' as [pi' Hs].
    rewrite app_comm_cons.
    rewrite 2 app_assoc.
    exists (with_ilr1 _ _ _ _ _ _ pi')...
- dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_comm_cons in IHpi.
    rewrite app_assoc in IHpi.
    assert (pi' := IHpi _ _ eq_refl).
    list_simpl in pi'.
    destruct pi' as [pi' Hs].
    list_simpl.
    exists (with_ilr2 _ _ _ _ _ _ pi')...
  + destruct l3 ; inversion Heq1 ; subst.
    list_simpl in IHpi.
    assert (pi' := IHpi _ _ eq_refl).
    rewrite app_comm_cons in pi'.
    rewrite 2 app_assoc in pi'.
    destruct pi' as [pi' Hs].
    rewrite app_comm_cons.
    rewrite 2 app_assoc.
    exists (with_ilr2 _ _ _ _ _ _ pi')...
- dichot_Type_elt_app_exec Heq ; subst ; list_simpl.
  + exists (zero_ilr _ _ _ _)...
  + destruct l3 ; inversion Heq1 ; subst.
    rewrite app_comm_cons.
    rewrite 2 app_assoc.
    exists (zero_ilr _ _ _ _)...
- exists (plus_irr1 _ _ _ _ pi')...
- exists (plus_irr2 _ _ _ _ pi')...
- dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_comm_cons in IHpi1.
    rewrite app_assoc in IHpi1.
    assert (pi1' := IHpi1 _ _ eq_refl).
    list_simpl in pi1'.
    rewrite app_comm_cons in IHpi2.
    rewrite app_assoc in IHpi2.
    assert (pi2' := IHpi2 _ _ eq_refl).
    list_simpl in pi2'.
    destruct pi1' as [pi1' Hs1].
    destruct pi2' as [pi2' Hs2].
    list_simpl.
    exists (plus_ilr _ _ _ _ _ _ pi1' pi2')...
  + destruct l3 ; inversion Heq1 ; subst.
    list_simpl in IHpi1.
    assert (pi1' := IHpi1 _ _ eq_refl).
    rewrite app_comm_cons in pi1'.
    rewrite 2 app_assoc in pi1'.
    list_simpl in IHpi2.
    assert (pi2' := IHpi2 _ _ eq_refl).
    rewrite app_comm_cons in pi2'.
    rewrite 2 app_assoc in pi2'.
    destruct pi1' as [pi1' Hs1].
    destruct pi2' as [pi2' Hs2].
    rewrite app_comm_cons.
    rewrite 2 app_assoc.
    exists (plus_ilr _ _ _ _ _ _ pi1' pi2')...
- symmetry in Heq.
  decomp_map_Type Heq.
  inversion Heq3.
- dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_comm_cons in IHpi.
    rewrite app_assoc in IHpi.
    assert (pi' := IHpi _ _ eq_refl).
    list_simpl in pi'.
    destruct pi' as [pi' Hs].
    list_simpl.
    exists (de_ilr _ _ _ _ _ pi')...
  + destruct l3 ; inversion Heq1 ; subst.
    list_simpl in IHpi.
    assert (pi' := IHpi _ _ eq_refl).
    rewrite app_comm_cons in pi'.
    rewrite 2 app_assoc in pi'.
    destruct pi' as [pi' Hs].
    rewrite app_comm_cons.
    rewrite 2 app_assoc.
    exists (de_ilr _ _ _ _ _ pi')...
- dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_assoc in IHpi.
    assert (pi' := IHpi _ _ eq_refl).
    list_simpl in pi'.
    destruct pi' as [pi' Hs].
    list_simpl.
    exists (wk_ilr _ _ _ _ _ pi')...
  + destruct l3 ; inversion Heq1 ; subst.
    list_simpl in IHpi.
    assert (pi' := IHpi _ _ eq_refl).
    rewrite app_comm_cons in pi'.
    rewrite 2 app_assoc in pi'.
    destruct pi' as [pi' Hs].
    rewrite app_comm_cons.
    rewrite 2 app_assoc.
    exists (wk_ilr _ _ _ _ _ pi')...
- dichot_Type_elt_app_exec Heq ; subst.
  + list_simpl in IHpi.
    assert (pi' := IHpi _ _ eq_refl).
    rewrite app_comm_cons in pi'.
    rewrite 2 app_assoc in pi'.
    destruct pi' as [pi' Hs].
    rewrite app_comm_cons.
    rewrite 2 app_assoc.
    exists (co_ilr _ _ _ _ _ _ pi')...
  + symmetry in Heq1.
    dichot_Type_elt_app_exec Heq1 ; subst.
    * rewrite 2 app_comm_cons in IHpi.
      rewrite 2 app_assoc in IHpi.
      assert (pi' := IHpi _ _ eq_refl).
      list_simpl in pi'.
      destruct pi' as [pi' Hs].
      list_simpl.
      exists (co_ilr _ _ _ _ _ _ pi')...
    * symmetry in Heq0.
      decomp_map_Type Heq0 ; subst.
      destruct l6 ; inversion Heq2.
- dichot_Type_elt_app_exec Heq ; subst.
  + list_simpl in IHpi2.
    assert (pi' := IHpi2 _ _ eq_refl).
    rewrite app_comm_cons in pi'.
    rewrite 2 app_assoc in pi'.
    destruct pi' as [pi' Hs].
    rewrite app_comm_cons.
    rewrite 2 app_assoc.
    eexists (@cut_ir _ f _ _ _ _ _ pi1 pi')...
  + symmetry in Heq1.
    dichot_Type_elt_app_exec Heq1 ; subst.
    * destruct (IHpi1 _ _ eq_refl) as [pi' Hs].
      list_simpl.
      rewrite app_comm_cons.
      rewrite (app_assoc l4).
      rewrite (app_assoc (l4 ++ _)).
      rewrite <- (app_assoc l4).
      eexists (@cut_ir _ f _ _ _ _ _ pi' pi2)...
    * rewrite app_comm_cons in IHpi2.
      rewrite app_assoc in IHpi2.
      assert (pi' := IHpi2 _ _ eq_refl).
      list_simpl in pi'.
      destruct pi' as [pi' Hs].
      list_simpl.
      eexists (@cut_ir _ f _ _ _ _ _ pi1 pi')...
- exfalso.
  apply (Hgax a).
  rewrite Heq.
  apply in_Type_elt.
Qed.


(** ** Characterization of [ill] as a fragment of [ll] *)

Require Import ll_fragments.

Section Conservativity.

(** Embedding of [IAtom] into [Atom] *)
Variable i2a : IAtom -> Atom.
Hypothesis i2a_inj : injective i2a.

(** *** Embedding of [ill] into [ll] *)

Fixpoint ill2ll A :=
match A with
| ivar x    => var (i2a x)
| ione      => one
| itens A B => tens (ill2ll A) (ill2ll B)
| ilpam A B => parr (ill2ll B) (dual (ill2ll A))
| ilmap A B => parr (dual (ill2ll A)) (ill2ll B)
| ineg A    => parr (dual (ill2ll A)) (var (i2a atN))
| itop      => top
| iwith A B => awith (ill2ll A) (ill2ll B)
| izero     => zero
| iplus A B => aplus (ill2ll A) (ill2ll B)
| ioc A     => oc (ill2ll A)
end.

Lemma ill2ll_map_ioc : forall l,
  map dual (map ill2ll (map ioc l)) = map wn (map dual (map ill2ll l)).
Proof with try (list_simpl ; reflexivity).
induction l...
list_simpl.
rewrite IHl...
Qed.

Lemma ill2ll_map_ioc_inv : forall l1 l2,
  map wn l1 = map dual (map ill2ll l2) ->
    { l2' | l2 = map ioc l2' & l1 = map dual (map ill2ll l2') }.
Proof with try reflexivity.
intros l1 l2 Heq ; revert l1 Heq ; induction l2 ; intros l1 Heq ;
  destruct l1 ; inversion Heq.
- exists nil ; split...
- destruct a ; inversion H0.
  apply IHl2 in H1.
  destruct H1 as [l0 Heq1' Heq'2] ; subst.
  exists (a :: l0) ; split...
Qed.

(** *** Comparisons between [ill] and [ll] *)

Lemma wn_not_idefin : forall A F,
  ll_mix0 (dual (ill2ll A) :: nil) -> ll_mix0 (oc F :: ill2ll A :: nil)
    -> False.
Proof with myeeasy.
cut (forall A F l2,
  ll_mix0 (dual (ill2ll A) :: nil) ->
  Permutation_Type (oc F :: ill2ll A :: nil) l2 -> ll_mix0 l2 -> False).
{ intros H A F pi1 pi2 ; eapply H... }
induction A ; intros F l2 pi1 HP2 pi2 ; simpl in pi1 ; simpl in HP2.
- remember (covar (i2a i) :: nil) as l1 ; revert Heql1 ;
    clear - pi1 ; induction pi1 ; intros Heql1 ;
    try (now inversion Heql1) ; subst.
  symmetry in p ; apply Permutation_Type_length_1_inv in p.
  apply IHpi1...
- revert HP2 ; clear - pi2 ; induction pi2 ; intros HP2 ;
    try (now (apply Permutation_Type_length in HP2 ; inversion HP2)) ;
    try (now (apply Permutation_Type_length_2_inv in HP2 ; inversion HP2)).
  + apply IHpi2.
    symmetry in p.
    transitivity l2...
  + apply Permutation_Type_length_2_inv in HP2.
    destruct HP2 ; inversion e.
    destruct l ; inversion H1.
- rewrite <- (app_nil_l (parr _ _ :: _)) in pi1.
  eapply parr_rev_axat in pi1 ;
    [ | intros a ; inversion a | ]...
  list_simpl in pi1.
  assert ((ll_mix0 (oc F :: ill2ll A1 :: nil) * ll_mix0 (ill2ll A2 :: nil))
        + (ll_mix0 (ill2ll A1 :: nil) * ll_mix0 (oc F :: ill2ll A2 :: nil)))
    as [[pi2' pi2''] | [pi2' pi2'']].
  { revert HP2 ; clear - pi2 ; induction pi2 ; intros HP2 ;
      try (now (apply Permutation_Type_length in HP2 ; inversion HP2)) ;
      try (now (apply Permutation_Type_length_2_inv in HP2 ; inversion HP2)).
    - apply IHpi2.
      symmetry in p ; etransitivity...
    - apply Permutation_Type_length_2_inv in HP2.
      destruct HP2 ; inversion e ; subst.
      destruct l2 ; inversion H2 ; subst.
      + destruct l1 ; inversion H2 ; subst.
        left ; split...
        eapply ex_r ; [ apply pi2_1 | PCperm_Type_solve ]...
      + apply app_eq_nil in H1 ; destruct H1 ; subst.
        right ; split...
        eapply ex_r ; [ apply pi2_2 | PCperm_Type_solve ]...
    - apply Permutation_Type_length_2_inv in HP2.
      destruct HP2 ; inversion e.
      destruct l ; inversion H1. }
  + eapply cut_mix0_r in pi1 ; [ | rewrite bidual ]...
    eapply IHA1 ; [ apply pi1 | reflexivity | ]...
  + eapply ex_r in pi1 ; [ | apply Permutation_Type_swap ].
    eapply cut_mix0_r in pi1 ; [ | rewrite bidual ]...
    eapply IHA2 ; [ apply pi1 | reflexivity | ]...
- eapply tens_rev_axat in pi1 ;
    [ | intros a ; inversion a | ]...
  cons2app in HP2.
  assert (Heq2 := HP2).
  symmetry in Heq2 ; apply Permutation_Type_vs_elt_inv in Heq2.
  destruct Heq2 as ((l' & l'') & Heq2) ; subst.
  eapply parr_rev_axat in pi2 ;
    [ | intros a ; inversion a | ]...
  destruct pi1 as [pi1' pi1''].
  rewrite bidual in pi1'.
  eapply (cut_mix0_r _ (l' ++ ill2ll A2 :: l'')) in pi1' ;
    [ | eapply ex_r ; [ apply pi2 | PCperm_Type_solve ]].
  eapply IHA2.
  + eassumption.
  + apply Permutation_Type_app_inv in HP2 ; simpl in HP2.
    etransitivity ; [ apply Permutation_Type_swap | ].
    apply Permutation_Type_cons ; [ reflexivity | ]...
  + eapply ex_r ; [ apply pi1' | ].
    PCperm_Type_solve.
- eapply tens_rev_axat in pi1 ;
    [ | intros a ; inversion a | ]...
  cons2app in HP2.
  assert (Heq2 := HP2).
  symmetry in Heq2 ; apply Permutation_Type_vs_elt_inv in Heq2.
  destruct Heq2 as ((l' & l'') & Heq2) ; subst.
  eapply parr_rev_axat in pi2 ;
    [ | intros a ; inversion a | ]...
  destruct pi1 as [pi1' pi1''].
  rewrite bidual in pi1''.
  eapply (cut_mix0_r _ (l' ++ ill2ll A2 :: l'')) in pi1'' ;
    [ | eapply ex_r ; [ apply pi2 | PCperm_Type_solve ]].
  eapply IHA2.
  + eassumption.
  + apply Permutation_Type_app_inv in HP2 ; simpl in HP2.
    etransitivity ; [ apply Permutation_Type_swap | ].
    apply Permutation_Type_cons ; [ reflexivity | ]...
  + eapply ex_r ; [ apply pi1'' | ].
    PCperm_Type_solve.
- eapply tens_rev_axat in pi1 ;
    [ | intros a ; inversion a | ]...
  destruct pi1 as [pi1' _].
  clear - pi1'.
  assert ({ l & Permutation_Type (covar (i2a atN) :: nil) l })
    as [l HP] by (eexists ; reflexivity).
  eapply ex_r in pi1' ; [ | apply HP ].
  revert HP ; induction pi1' ; intros HP ;
    try (now (apply Permutation_Type_length in HP ; inversion HP)) ;
    try (now (apply Permutation_Type_length_1_inv in HP ; inversion HP)).
  apply IHpi1'.
  symmetry in p ; etransitivity...
- remember (zero :: nil) as l1 ; revert Heql1 ;
    clear - pi1 ; induction pi1 ; intros Heql1 ;
    try (now inversion Heql1) ; subst.
  symmetry in p ; apply Permutation_Type_length_1_inv in p.
  apply IHpi1...
- eapply plus_rev_axat in pi1 ;
    [ | intros a ; inversion a | ]...
  destruct pi1 as [ pi1 | pi1 ].
  + cons2app in HP2.
    assert (Heq2 := HP2).
    symmetry in Heq2 ; apply Permutation_Type_vs_elt_inv in Heq2.
    destruct Heq2 as ((l' & l'') & Heq2) ; subst.
    eapply with_rev1_noax in pi2 ;
      [ | intros a ; inversion a | ]...
    eapply IHA1.
    * eassumption.
    * apply Permutation_Type_app_inv in HP2 ; simpl in HP2.
      etransitivity ; [ apply Permutation_Type_swap | ].
      apply Permutation_Type_cons ; [ reflexivity | ]...
    * eapply ex_r ; [ apply pi2 | ].
      PCperm_Type_solve.
  + cons2app in HP2.
    assert (Heq2 := HP2).
    symmetry in Heq2 ; apply Permutation_Type_vs_elt_inv in Heq2.
    destruct Heq2 as ((l' & l'') & Heq2) ; subst.
    eapply with_rev2_noax in pi2 ;
      [ | intros a ; inversion a | ]...
    eapply IHA2.
    * eassumption.
    * apply Permutation_Type_app_inv in HP2 ; simpl in HP2.
      etransitivity ; [ apply Permutation_Type_swap | ].
      apply Permutation_Type_cons ; [ reflexivity | ]...
    * eapply ex_r ; [ apply pi2 | ].
      PCperm_Type_solve.
- revert HP2 ; clear - pi2 ; induction pi2 ; intros HP2 ;
    try (now (apply Permutation_Type_length in HP2 ; inversion HP2)) ;
    try (now (apply Permutation_Type_length_2_inv in HP2 ; inversion HP2)).
  + apply IHpi2.
    symmetry in p ; etransitivity...
  + apply Permutation_Type_length_2_inv in HP2.
    destruct HP2 ; inversion e.
    destruct l ; inversion H1.
- assert (pi0 := pi1).
  eapply with_rev1_noax in pi1 ;
    [ | intros a ; inversion a | rewrite app_nil_l ; reflexivity ]...
  eapply with_rev2_noax in pi0 ;
    [ | intros a ; inversion a | rewrite app_nil_l ; reflexivity ]...
  assert (ll_mix0 (oc F :: ill2ll A1 :: nil)
        + ll_mix0 (oc F :: ill2ll A2 :: nil))
    as [ pi2' | pi2' ].
  { revert HP2 ; clear - pi2 ; induction pi2 ; intros HP2 ;
      try (now (apply Permutation_Type_length in HP2 ; inversion HP2)) ;
      try (now (apply Permutation_Type_length_2_inv in HP2 ; inversion HP2)).
    - apply IHpi2.
      symmetry in p ; etransitivity...
    - apply Permutation_Type_length_2_inv in HP2.
      destruct HP2 ; inversion e ; subst.
      left.
      eapply ex_r ; [ apply pi2 | PCperm_Type_solve ].
    - apply Permutation_Type_length_2_inv in HP2.
      destruct HP2 ; inversion e ; subst.
      right.
      eapply ex_r ; [ apply pi2 | PCperm_Type_solve ].
    - apply Permutation_Type_length_2_inv in HP2.
      destruct HP2 ; inversion e.
      destruct l ; inversion H1. }
  + eapply IHA1...
  + eapply IHA2...
- revert HP2 ; clear - pi2 ; induction pi2 ; intros HP2 ;
    try (now (apply Permutation_Type_length in HP2 ; inversion HP2)) ;
    try (now (apply Permutation_Type_length_2_inv in HP2 ; inversion HP2)).
  + apply IHpi2.
    symmetry in p ; etransitivity...
  + apply Permutation_Type_length_2_inv in HP2.
    destruct HP2 ; inversion e ; destruct l ; inversion H1.
Qed.

Lemma bot_not_idefin : forall A,
  ll_mix0 (dual (ill2ll A) :: nil) -> ll_mix0 (one :: ill2ll A :: nil)
    -> False.
Proof with myeeasy.
intros A pi1 pi2.
eapply cut_mix0_r in pi2.
- list_simpl in pi2.
  eapply ex_r in pi2 ; [ | apply Permutation_Type_swap ].
  eapply wn_not_idefin...
- apply bot_r.
  change nil with (map wn nil).
  apply oc_r.
  apply one_r.
Qed.

Lemma wn_one_not_idefin : forall A,
  ll_mix0 (wn one :: dual (ill2ll A) :: nil)-> ll_mix0 (oc bot :: ill2ll A :: nil)
    -> False.
Proof with myeeasy.
intros A pi1 pi2.
eapply cut_mix0_r in pi1.
- list_simpl in pi1.
  eapply wn_not_idefin...
- change nil with (map wn nil).
  apply oc_r.
  apply bot_r.
  apply mix0_r...
Qed.

Lemma oc_bot_not_idefin : forall A,
  ll_ll (oc bot :: dual (ill2ll A) :: nil) -> ll_mix0 (wn one :: ill2ll A :: nil)
    -> False.
Proof with myeeasy.
assert (forall l, ll_ll (map dual (map ill2ll l)) ->
          (Forall_Type (fun F => ll_mix0 (ill2ll F :: nil)) l) -> False)
  as Hgen.
{ intros l pi.
  remember (map dual (map ill2ll l)) as l0 ; revert l Heql0.
  induction pi ; intros l' Heq HF ; subst ;
    try (now inversion f).
  - destruct l' ; inversion Heq.
    destruct l' ; inversion Heq.
    destruct i0 ; inversion H3.
  - apply PCperm_Type_map_inv in p.
    destruct p as [ l1' Heq HP ] ; subst.
    symmetry in HP.
    apply PCperm_Type_map_inv in HP.
    destruct HP as [ l1'' Heq HP ] ; subst.
    eapply IHpi.
    + reflexivity.
    + eapply Permutation_Type_Forall_Type...
      apply HP.
  - destruct l' ; inversion Heq.
    destruct i ; inversion H0.
  - destruct l' ; inversion Heq ; subst.
    inversion HF.
    eapply IHpi...
  - destruct l' ; inversion Heq.
    decomp_map H1 ; decomp_map H1 ; subst.
    destruct i ; inversion H0 ; subst.
    + inversion HF ; subst.
      simpl in X ; eapply parr_rev_axat in X ;
        [ | intros a ; inversion a | rewrite app_nil_l ; reflexivity ].
      list_simpl in X.
      apply Forall_Type_app_inv in X0 ; destruct X0.
      rewrite bidual in pi1.
      assert (ll_mix0 (ill2ll i1 :: nil)) as pi0.
      { eapply (stronger_pfrag _ pfrag_mix0) in pi1 ;
          [ | nsplit 5 ; myeasy ; intros a ; inversion a ].
        revert pi1 f0 ; clear ; induction l5 ; intros pi HF.
        - assumption.
        - inversion HF ; subst.
          simpl in pi ; eapply ex_r in pi ; [ | apply Permutation_Type_swap ].
          apply (cut_mix0_r _ _ _ pi) in X.
          eapply IHl5... }
      eapply ex_r in X ; [ | apply Permutation_Type_swap ].
      apply (cut_mix0_r _ _ _ X) in pi0.
      apply (IHpi2 (i2 :: l4))...
      constructor...
    + inversion HF ; subst.
      simpl in X ; eapply parr_rev_axat in X ;
        [ | intros a ; inversion a | rewrite app_nil_l ; reflexivity ].
      list_simpl in X.
      apply Forall_Type_app_inv in X0 ; destruct X0.
      rewrite bidual in pi2.
      assert (ll_mix0 (ill2ll i1 :: nil)) as pi0.
      { eapply (stronger_pfrag _ pfrag_mix0) in pi2 ;
          [ | nsplit 5 ; myeasy ; intros a ; inversion a ].
        revert pi2 f ; clear ; induction l4 ; intros pi HF.
        - assumption.
        - inversion HF ; subst.
          simpl in pi ; eapply ex_r in pi ; [ | apply Permutation_Type_swap ].
          apply (cut_mix0_r _ _ _ pi) in X.
          eapply IHl4... }
      apply (cut_mix0_r _ _ _ X) in pi0.
      apply (IHpi1 (i2 :: l5))...
      constructor...
    + inversion HF ; subst.
      simpl in X ; eapply parr_rev_axat in X ;
        [ | intros a ; inversion a | rewrite app_nil_l ; reflexivity ].
      list_simpl in X.
      apply Forall_Type_app_inv in X0 ; destruct X0.
      rewrite bidual in pi2.
      assert (ll_mix0 (ill2ll i :: nil)) as pi0.
      { eapply (stronger_pfrag _ pfrag_mix0) in pi2 ;
          [ | nsplit 5 ; myeasy ; intros a ; inversion a ].
        revert pi2 f ; clear ; induction l4 ; intros pi HF.
        - assumption.
        - inversion HF ; subst.
          simpl in pi ; eapply ex_r in pi ; [ | apply Permutation_Type_swap ].
          apply (cut_mix0_r _ _ _ pi) in X.
          eapply IHl4... }
      apply (cut_mix0_r _ _ _ X) in pi0.
      apply (IHpi1 (ivar atN :: l5))...
      constructor...
  - destruct l' ; inversion Heq.
    destruct i ; inversion H0 ; subst.
    inversion HF ; subst.
    simpl in X.
    eapply tens_rev_axat in X ; [ | intros a ; inversion a | ]...
    destruct X as [pi1 pi2].
    apply (IHpi (i2 :: i1 :: l'))...
    constructor...
    constructor...
  - destruct l' ; inversion Heq.
    destruct i ; inversion H0 ; subst.
    inversion HF ; subst.
    clear - X.
    assert ({ l & Permutation_Type (ill2ll izero :: nil) l }) as [l HP]
      by (eexists ; reflexivity ).
    eapply ex_r in X ; [ | apply HP ].
    revert HP ; clear - X ; induction X ; intros HP ;
      try (now (apply Permutation_Type_length in HP ; inversion HP)) ;
      try (now (apply Permutation_Type_length_1_inv in HP ; inversion HP)).
    apply IHX.
    symmetry in p ; etransitivity...
  - destruct l' ; inversion Heq.
    destruct i ; inversion H0 ; subst.
    inversion HF ; subst.
    simpl in X ; rewrite <- (app_nil_l (awith _ _ :: _)) in X.
    eapply with_rev1_noax in X ;
      [ | intros a ; inversion a | ]...
    apply (IHpi (i1 :: l'))...
    constructor...
  - destruct l' ; inversion Heq.
    destruct i ; inversion H0 ; subst.
    inversion HF ; subst.
    simpl in X ; rewrite <- (app_nil_l (awith _ _ :: _)) in X.
    eapply with_rev2_noax in X ;
      [ | intros a ; inversion a | ]...
    apply (IHpi (i2 :: l'))...
    constructor...
  - destruct l' ; inversion Heq.
    destruct i ; inversion H0 ; subst.
    inversion HF ; subst.
    simpl in X ; eapply plus_rev_axat in X ; [ | intros a ; inversion a | ]...
    destruct X as [pi | pi].
    + apply (IHpi1 (i1 :: l'))...
      constructor...
    + apply (IHpi2 (i2 :: l'))...
      constructor...
  - destruct l' ; inversion Heq.
    destruct i ; inversion H0.
  - destruct l' ; inversion Heq.
    destruct i ; inversion H0 ; subst.
    inversion HF ; subst.
    simpl in X ; rewrite <- (app_nil_l (oc _ :: _)) in X.
    eapply oc_rev_noax in X ;
      [ | intros a ; inversion a | ]...
    apply (IHpi (i :: l'))...
    constructor...
  - destruct l' ; inversion Heq.
    destruct i ; inversion H0 ; subst.
    inversion HF ; subst.
    simpl in X ; rewrite <- (app_nil_l (oc _ :: _)) in X.
    eapply oc_rev_noax in X ;
      [ | intros a ; inversion a | ]...
    apply (IHpi l')...
  - destruct l' ; inversion Heq.
    destruct i ; inversion H0.
    decomp_map H1.
    decomp_map H1 ; subst.
    apply ill2ll_map_ioc_inv in H4.
    destruct H4 as [l2' Heq' Heq''] ; subst.
    inversion HF ; subst.
    apply (IHpi (ioc i :: map ioc l2' ++ ioc i :: l4))...
    + list_simpl ; rewrite <- ? ill2ll_map_ioc...
    + constructor...
      apply Forall_Type_app_inv in X0.
      destruct X0.
      apply Forall_Type_app...
      constructor...
  - inversion a. }
intros A pi1 pi2.
eapply cut_ll_r in pi1.
eapply cut_mix0_r in pi2.
- change (dual (ill2ll A) :: nil)
    with (map dual (map ill2ll (A :: nil))) in pi1.
  rewrite app_nil_r in pi1.
  list_simpl in pi2.
  eapply Hgen...
  constructor ; [ | constructor ]...
- change nil with (map wn nil).
  apply oc_r.
  apply bot_r.
  apply mix0_r...
- apply de_r.
  apply one_r.
Qed.


(** Translation of proof fragments *)
Definition i2pfrag P := {|
  pcut := ipcut P ;
  pgax := existT (fun x => x -> list formula) (projT1 (ipgax P))
          (fun a => ill2ll (snd (projT2 (ipgax P) a))
                    :: rev (map dual (map ill2ll (fst (projT2 (ipgax P) a))))) ;
  pmix0 := false ;
  pmix2 := false ;
  pperm := ipperm P |}.

Lemma cutrm_i2pfrag : forall P,
  cutrm_pfrag (i2pfrag P) = i2pfrag (cutrm_ipfrag P).
Proof.
reflexivity.
Qed.

Proposition ill_to_ll {P} : forall l C, ill P l C ->
  ll (i2pfrag P) (ill2ll C :: rev (map dual (map ill2ll l))).
Proof with myeeasy.
intros l C Hill.
induction Hill ; 
  list_simpl ;
  try list_simpl in IHHill ;
  try list_simpl in IHHill1 ;
  try list_simpl in IHHill2.
- eapply ex_r.
  apply ax_r.
  apply PCperm_Type_swap.
- eapply ex_r...
  hyps_PEperm_Type_unfold ; unfold PCperm_Type ; simpl ; destruct ipperm.
  * apply Permutation_Type_cons...
    apply Permutation_Type_map.
    apply Permutation_Type_map.
    apply Permutation_Type_rev'...
  * subst...
- apply one_r.
- rewrite app_comm_cons.
  eapply ex_r ; [ | apply PCperm_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply bot_r.
  eapply ex_r...
  rewrite ? app_comm_cons.
  apply PCperm_Type_app_comm.
- apply tens_r...
- rewrite app_comm_cons.
  eapply ex_r ; [ | apply PCperm_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply parr_r.
  eapply ex_r...
  rewrite ? app_comm_cons.
  apply PCperm_Type_app_comm.
- apply parr_r...
- rewrite app_comm_cons.
  rewrite app_assoc.
  eapply ex_r ; [ | apply PCperm_Type_app_comm ].
  rewrite bidual.
  rewrite ? app_assoc.
  rewrite <- ? app_comm_cons.
  apply tens_r...
  eapply ex_r...
  rewrite ? app_comm_cons.
  apply PCperm_Type_app_comm.
- apply parr_r...
  eapply ex_r...
  symmetry.
  rewrite (app_comm_cons _ _ (ill2ll B)).
  apply PCperm_Type_last.
- rewrite app_comm_cons.
  eapply ex_r ; [ | apply PCperm_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  rewrite <- ? app_assoc.
  rewrite bidual.
  apply tens_r...
  eapply ex_r...
  rewrite ? app_comm_cons.
  apply PCperm_Type_app_comm.
- apply parr_r...
  eapply ex_r...
  symmetry.
  rewrite (app_comm_cons _ _ (ill2ll N)).
  apply PCperm_Type_last.
- cons2app.
  eapply ex_r ; [ | apply PCperm_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  rewrite <- ? app_assoc.
  rewrite bidual.
  list_simpl.
  apply tens_r...
  apply ax_r.
- apply top_r.
- apply with_r...
- rewrite ? app_comm_cons.
  eapply ex_r ; [ | apply PCperm_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply plus_r1...
  eapply ex_r...
  rewrite ? app_comm_cons.
  apply PCperm_Type_app_comm.
- rewrite ? app_comm_cons.
  eapply ex_r ; [ | apply PCperm_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply plus_r2...
  eapply ex_r...
  rewrite ? app_comm_cons.
  apply PCperm_Type_app_comm.
- rewrite ? app_comm_cons.
  eapply ex_r ; [ | apply PCperm_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply top_r...
- apply plus_r1...
- apply plus_r2...
- rewrite ? app_comm_cons.
  eapply ex_r ; [ | apply PCperm_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply with_r...
  + eapply ex_r ; [ apply IHHill1 | ].
    rewrite ? app_comm_cons.
    apply PCperm_Type_app_comm.
  + eapply ex_r ; [ apply IHHill2 | ].
    rewrite ? app_comm_cons.
    apply PCperm_Type_app_comm.
- assert (map dual (map ill2ll (map ioc (rev l))) =
          map wn (map dual (map ill2ll (rev l)))) as Hwn.
  { remember (rev l) as l'.
    clear ; induction l'...
    simpl ; rewrite IHl'... }
  rewrite_all Hwn.
  apply oc_r...
- rewrite ? app_comm_cons.
  eapply ex_r ; [ | apply PCperm_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply de_r...
  eapply ex_r...
  rewrite ? app_comm_cons.
  apply PCperm_Type_app_comm.
- rewrite app_comm_cons.
  eapply ex_r ; [ | apply PCperm_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply wk_r.
  eapply ex_r...
  rewrite ? app_comm_cons.
  apply PCperm_Type_app_comm.
- assert (map dual (map ill2ll (map ioc (rev lw))) =
          map wn (map dual (map ill2ll (rev lw)))) as Hwn.
  { remember (rev lw) as l'.
    clear ; induction l'...
    simpl ; rewrite IHl'... }
  rewrite_all Hwn.
  rewrite ? app_comm_cons.
  eapply ex_r ; [ | apply PCperm_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  rewrite <- ? app_assoc.
  apply co_r...
  eapply ex_r...
  rewrite ? app_comm_cons.
  rewrite (app_assoc (wn _ :: _)).
  apply PCperm_Type_app_comm.
- rewrite app_comm_cons.
  eapply ex_r ; [ | apply PCperm_Type_app_comm ].
  rewrite <- app_assoc.
  assert (pcut (i2pfrag P) = true) as fc by (now simpl).
  eapply (@cut_r _ fc)...
  eapply ex_r...
  rewrite ? app_comm_cons.
  apply PCperm_Type_app_comm.
- replace (ill2ll (snd (projT2 (ipgax P) a))
   :: map dual (map ill2ll (rev (fst (projT2 (ipgax P) a)))))
  with (projT2 (pgax (i2pfrag P)) a) by (simpl ; rewrite 2 map_rev ; reflexivity).
  apply gax_r.
Qed.


(** *** Conservativity with constraints on [izero] *)

(** Constraints on the presence of [izero] for conservativity *)
Inductive zeropos : iformula -> Type :=
| zp_izero   : zeropos izero
| zp_itens_l : forall A B, zeropos A -> zeropos (itens A B)
| zp_itens_r : forall A B, zeropos A -> zeropos (itens B A)
| zp_iwith_l : forall A B, zeropos A -> zeropos (iwith A B)
| zp_iwith_r : forall A B, zeropos A -> zeropos (iwith B A)
| zp_iplus   : forall A B, zeropos A -> zeropos B -> zeropos (iplus A B)
| zp_ioc     : forall A, zeropos A -> zeropos (ioc A).

Lemma zeropos_ilr {P} : forall D, zeropos D -> forall l1 l2 C,
  ill P (l1 ++ D :: l2) C.
Proof with myeeasy.
intros D Hzp ; induction Hzp ; intros l1 l2 C ;
  try now (constructor ; intuition).
apply tens_ilr.
cons2app ; rewrite app_assoc.
apply IHHzp.
Qed.

Lemma ill2ll_zeropos : forall C D, zeropos C -> ill2ll C = ill2ll D -> zeropos D.
Proof with try assumption.
intros C D Hz.
revert D ; induction Hz ; intros D Heq ; destruct D ; inversion Heq ;
  try apply IHHz in H0 ; try (now constructor).
- apply zp_itens_r.
  apply IHHz in H1...
- apply zp_iwith_r.
  apply IHHz in H1...
- constructor.
  + apply IHHz1 in H0...
  + apply IHHz2 in H1...
Qed.

Inductive nonzerospos : iformula -> Type :=
| nzsp_ivar  : forall x, nonzerospos (ivar x)
| nzsp_ione  : nonzerospos ione
| nzsp_itens : forall A B, nonzerospos A -> nonzerospos B -> nonzerospos (itens A B)
| nzsp_ilpam : forall A B, nonzerospos A -> nonzerospos B ->
                             (zeropos B -> False) -> nonzerospos (ilpam A B)
| nzsp_ilmap : forall A B, nonzerospos A -> nonzerospos B ->
                             (zeropos B -> False) -> nonzerospos (ilmap A B)
| nzsp_ineg : forall A, nonzerospos A -> nonzerospos (ineg A)
| nzsp_itop  : nonzerospos itop
| nzsp_iwith : forall A B, nonzerospos A -> nonzerospos B -> nonzerospos (iwith A B)
| nzsp_izero : nonzerospos izero
| nzsp_iplus : forall A B, nonzerospos A -> nonzerospos B -> nonzerospos (iplus A B)
| nzsp_ioc   : forall A, nonzerospos A -> nonzerospos (ioc A).

Definition easyipgax_nzeropos P := forall a,
  (forall D, ill2ll (snd (projT2 (ipgax P) a)) = dual (ill2ll D) ->
     { Zll : _ & zeropos (fst Zll) & D :: (fst (projT2 (ipgax P) a))
                                   = fst (snd Zll) ++ fst Zll :: snd (snd Zll) })
* (forall l C,
     PCperm_Type (ipperm P) (ill2ll (snd (projT2 (ipgax P) a))
                            :: rev (map dual (map ill2ll (fst (projT2 (ipgax P) a)))))
                       (ill2ll C :: rev (map dual (map ill2ll l)))
     -> { b | fst (projT2 (ipgax P) b) = l & snd (projT2 (ipgax P) b) = C })
* (In_Type N (fst (projT2 (ipgax P) a)) -> False).


Lemma dual_jfragment_zeropos {P} : ipcut P = false -> easyipgax_nzeropos P -> forall l0,
  Forall_Type nonzerospos l0 -> ll (i2pfrag P) (map dual (map ill2ll l0)) ->
  { Cll : _ & zeropos (fst Cll) & l0 = fst (snd Cll) ++ fst Cll :: snd (snd Cll) }.
Proof with myeeasy.
intros Hcut Hgax.
intros l0 Hnzsp Hll.
remember (map dual (map ill2ll l0)) as l.
revert l0 Hnzsp Heql.
induction Hll ; intros l0 Hnzsp HP.
- exfalso.
  destruct l0 ; inversion HP.
  destruct l0 ; inversion HP.
  destruct i0 ; inversion H3.
- subst.
  rewrite map_map in p.
  apply PCperm_Type_map_inv in p.
  destruct p as [l' Heq HP] ; subst.
  apply PCperm_perm_Type in HP.
  apply (Permutation_Type_Forall_Type _ _ _ HP) in Hnzsp.
  apply IHHll in Hnzsp ; [ | rewrite <- map_map ]...
  destruct Hnzsp as [(C & l1 & l2) Hz Heq] ; unfold id in Heq ; subst.
  unfold id in HP ; apply Permutation_Type_vs_elt_inv in HP.
  destruct HP as ((l' & l'') & HP) ; subst.
  exists (C,(l',l''))...
- inversion f.
- inversion f.
- destruct l0 ; inversion HP.
  destruct i ; inversion H0.
- rewrite map_map in HP.
  decomp_map_Type HP ; subst.
  rewrite <- map_map in IHHll.
  inversion Hnzsp ; subst.
  apply IHHll in H2...
  destruct H2
    as [(C & l1' & l2') Hzp Heq2] ; subst.
  exists (C,(x :: l1',l2'))...
- rewrite map_map in HP.
  decomp_map_Type HP ; subst.
  destruct x ; inversion HP1 ; subst.
  + rewrite <- map_map in IHHll2.
    assert (Forall_Type nonzerospos (x2 :: l4)) as Hnzsp'.
    { inversion Hnzsp ; subst.
      apply Forall_Type_app_inv in H2.
      destruct H2 as [H2 _].
      inversion H1.
      constructor... }
    apply IHHll2 in Hnzsp'...
    destruct Hnzsp'
      as [(C & l1' & l2') Hzp Heq2] ; subst.
    destruct l1' ; inversion Heq2 ; subst.
    * exfalso.
      inversion Hnzsp ; subst.
      inversion H1.
      apply H5...
    * exists (C,(ilpam x1 i :: l1',l2' ++ l5))...
      list_simpl...
  + assert (Forall_Type nonzerospos (x2 :: l5)) as Hnzsp'.
    { inversion Hnzsp ; subst.
      apply Forall_Type_app_inv in H2.
      destruct H2 as [_ H2].
      inversion H1.
      constructor... }
    rewrite <- map_map in IHHll1.
    apply IHHll1 in Hnzsp'...
    destruct Hnzsp'
      as [(C & l1' & l2') Hzp Heq2] ; subst.
    destruct l1' ; inversion Heq2 ; subst.
    * exfalso.
      inversion Hnzsp ; subst.
      inversion H1.
      apply H5...
    * exists (C,(ilmap x1 i :: l4 ++ l1',l2'))...
      list_simpl...
  + assert (Forall_Type nonzerospos (N :: l5)) as Hnzsp'.
    { inversion Hnzsp ; subst.
      apply Forall_Type_app_inv in H2.
      destruct H2 as [_ H2].
      inversion H1.
      constructor...
      constructor. }
    rewrite <- map_map in IHHll1.
    apply IHHll1 in Hnzsp'...
    destruct Hnzsp'
      as [(C & l1' & l2') Hzp Heq2] ; subst.
    destruct l1' ; inversion Heq2 ; subst.
    * exfalso.
      inversion Hzp.
    * exists (C,(ineg x :: l4 ++ l1',l2'))...
      list_simpl...
- rewrite map_map in HP.
  decomp_map_Type HP ; subst.
  destruct x ; inversion HP1 ; subst.
  rewrite <- map_map in IHHll.
  assert (Forall_Type nonzerospos (x2 :: x1 :: l2)) as Hnzsp'.
  { inversion Hnzsp ; subst.
    inversion H1 ; subst.
    constructor...
    constructor... }
  apply IHHll in Hnzsp'...
  destruct Hnzsp'
    as [(C & l1' & l2') Hzp Heq2] ; subst.
  destruct l1' ; inversion Heq2 ; [ | destruct l1' ; inversion Heq2 ] ; subst.
  + exists (itens x1 C,(nil,l2))...
    apply zp_itens_r...
  + exists (itens C i,(nil,l2'))...
    apply zp_itens_l...
  + exists (C,(itens i0 i :: l1',l2'))...
- decomp_map_Type HP ; decomp_map_Type HP ; simpl in HP3 ; subst.
  destruct x0 ; inversion HP1.
  exists (izero,(nil,l3)) ; simpl...
  constructor.
- rewrite map_map in HP.
  decomp_map_Type HP ; subst.
  destruct x ; inversion HP1 ; subst.
  rewrite <- map_map in IHHll.
  assert (Forall_Type nonzerospos (x1 :: l2)) as Hnzsp'.
  { inversion Hnzsp ; subst.
    inversion H1 ; subst.
    constructor... }
  apply IHHll in Hnzsp'...
  destruct Hnzsp'
    as [(C & l1' & l2') Hzp Heq2] ; subst.
  destruct l1' ; inversion Heq2 ; subst.
  + exists (iwith C x2,(nil,l2'))...
    apply zp_iwith_l...
  + exists (C,(iwith i x2 :: l1',l2'))...
- rewrite map_map in HP.
  decomp_map_Type HP ; subst.
  destruct x ; inversion HP1 ; subst.
  rewrite <- map_map in IHHll.
  assert (Forall_Type nonzerospos (x2 :: l2)) as Hnzsp'.
  { inversion Hnzsp ; subst.
    inversion H1 ; subst.
    constructor... }
  apply IHHll in Hnzsp'...
  destruct Hnzsp'
    as [(C & l1' & l2') Hzp Heq2] ; subst.
  destruct l1' ; inversion Heq2 ; subst.
  + exists (iwith x1 C,(nil,l2'))...
    apply zp_iwith_r...
  + exists (C,(iwith x1 i :: l1',l2'))...
- rewrite map_map in HP.
  decomp_map_Type HP ; subst.
  destruct x ; inversion HP1 ; subst.
  rewrite <- map_map in IHHll2.
  assert (Forall_Type nonzerospos (x2 :: l2)) as Hnzsp'.
  { inversion Hnzsp ; subst.
    inversion H1 ; subst.
    constructor... }
  apply IHHll2 in Hnzsp'...
  destruct Hnzsp'
    as [(C & l1' & l2') Hzp Heq2] ; subst.
  destruct l1' ; inversion Heq2 ; subst.
  + assert (Forall_Type nonzerospos (x1 :: l2')) as Hnzsp''.
    { inversion Hnzsp ; subst.
      inversion H1 ; subst.
      constructor... }
    rewrite <- map_map in IHHll1.
    apply IHHll1 in Hnzsp''...
    destruct Hnzsp''
      as [(C' & l1'' & l2'') Hzp' Heq3] ; subst.
    destruct l1'' ; inversion Heq3 ; subst.
    * exists (iplus C' C,(nil,l2''))...
      constructor...
    * exists (C',(iplus i C :: l1'',l2''))...
  + exists (C,(iplus x1 i :: l1',l2'))...
- exfalso.
  destruct l0 ; inversion HP.
  destruct i ; inversion H0.
- rewrite map_map in HP.
  decomp_map_Type HP ; subst.
  destruct x ; inversion HP1 ; subst.
  rewrite <- map_map in IHHll.
  assert (Forall_Type nonzerospos (x :: l2)) as Hnzsp'.
  { inversion Hnzsp ; subst.
    inversion H1 ; subst.
    constructor... }
  apply IHHll in Hnzsp'...
  destruct Hnzsp'
    as [(C & l1' & l2') Hzp Heq2] ; subst.
  destruct l1' ; inversion Heq2 ; subst.
  + exists (ioc C,(nil,l2'))...
    constructor...
  + exists (C,(ioc i :: l1',l2'))...
- rewrite map_map in HP.
  decomp_map_Type HP ; subst.
  rewrite <- map_map in IHHll.
  inversion Hnzsp.
  apply IHHll in H2...
  destruct H2 as [(C & l1' & l2') Hzp Heq2] ; subst.
  exists (C,(x :: l1',l2'))...
- rewrite map_map in HP.
  decomp_map_Type HP ; subst.
  destruct x ; inversion HP1 ; subst.
  assert ({ lw' | lw = map dual (map ill2ll lw') & map ioc lw' = l3 })
    as [lw' Heq' Heq''] ; subst.
  { clear - HP3.
    revert lw HP3 ; induction l3 ; intros lw Heq ;
      simpl in Heq ; destruct lw ; inversion Heq.
    - exists nil ; split...
    - destruct a ; inversion H0 ; subst.
      apply IHl3 in H1.
      destruct H1 as [lw' Heq' Heq''] ; subst.
      exists (a :: lw') ; split... }
  assert (Forall_Type nonzerospos (ioc x :: map ioc lw' ++ ioc x :: l4)) as Hnzsp'.
  { inversion Hnzsp ; subst.
    apply Forall_Type_app_inv in H2.
    destruct H2 as [H2l H2r].
    constructor...
    apply Forall_Type_app...
    constructor... }
  rewrite <- (map_map _ _ l4) in IHHll.
  apply IHHll in Hnzsp' ; [ | rewrite <- ill2ll_map_ioc ; list_simpl ] ...
  destruct Hnzsp'
    as [(C & l1' & l2') Hzp Heq2] ; subst.
  destruct l1' ; inversion Heq2 ; subst.
  + exists (ioc x,(nil,map ioc lw' ++ l4))...
  + dichot_Type_elt_app_exec H1.
    * subst.
      exists (C,(ioc x :: map ioc lw' ++ l,l2'))...
      list_simpl...
    * destruct l0 ; inversion H2 ; subst.
      -- exists (ioc x,(nil,map ioc lw' ++ l2'))...
      -- rewrite H0.
         exists (C,(ioc x :: l1',l0 ++ l4))...
         list_simpl...
- simpl in f.
  rewrite f in Hcut.
  inversion Hcut.
- unfold i2pfrag in HP ; simpl in HP.
  destruct l0 ; inversion HP.
  apply (fst (Hgax a)) in H0.
  destruct H0 as [(Z & lz1 & lz2) Hz Heq].
  destruct lz1 ; inversion Heq ; subst.
  + exists (Z,(nil,l0))...
  + list_simpl in H1.
    rewrite H2 in H1 ; list_simpl in H1.
    decomp_map_Type H1.
    apply dual_inj in H1 ; subst.
    simpl in H4 ; decomp_map_Type H4 ; subst.
    apply ill2ll_zeropos in H1...
    rewrite app_comm_cons.
    exists (x0,(i0::l4,l6))...
Qed.

(** Cut-free conservativity *)
Theorem ll_to_ill_nzeropos_cutfree {P} : ipcut P = false -> easyipgax_nzeropos P ->
  forall l, ll (i2pfrag P) l -> forall l0 C, Forall_Type nonzerospos (C :: l0) ->
    PCperm_Type (pperm (i2pfrag P)) l (ill2ll C :: rev (map dual (map ill2ll l0))) ->
      ill P l0 C.
Proof with myeeasy.
intros Hcut Hgax.
intros l Hll ; induction Hll ; intros l0 C Hnzsp HP.
- apply PCperm_Type_length_2_inv in HP.
  destruct HP as [HP | HP] ; inversion HP ; destruct C ; inversion H0.
  destruct l0 using rev_ind_Type ; inversion H1.
  list_simpl in H3 ; inversion H3.
  destruct l0 using rev_ind_Type ; list_simpl in H5 ; inversion H5.
  destruct x ; inversion H4.
  rewrite <- H2 in H6.
  apply i2a_inj in H6 ; subst.
  apply ax_ir.
- apply IHHll...
  etransitivity...
- exfalso ; apply PCperm_Type_nil_cons in HP...
- inversion f.
- apply PCperm_Type_length_1_inv in HP.
  inversion HP.
  destruct C ; inversion H0.
  destruct l0 using rev_ind_Type ; list_simpl in H1 ; inversion H1.
  apply one_irr.
- list_simpl in HP.
  symmetry in HP.
  apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq.
  + destruct C ; inversion H0.
  + symmetry in H1.
    decomp_map_Type H1 ; decomp_map_Type H4 ; subst.
    apply (f_equal (@rev _)) in H7.
    rewrite rev_involutive in H7 ; simpl in H4 ; simpl in H6 ; simpl in H8 ; subst.
    destruct x0 ; inversion H1.
    list_simpl.
    apply one_ilr.
    apply IHHll.
    * inversion Hnzsp.
      constructor...
      list_simpl in H3.
      apply Forall_Type_app_inv in H3.
      destruct H3 as [H3l H3r].
      inversion H3r.
      apply Forall_Type_app...
    * list_simpl.
      apply PEperm_PCperm_Type in HP ; unfold id in HP ; simpl in HP.
      PCperm_Type_solve.
- list_simpl in HP.
  symmetry in HP.
  apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq.
  + destruct C ; inversion H0 ; subst.
    list_simpl in HP.
    rewrite map_map in HP.
    apply PEperm_Type_map_inv in HP.
    destruct HP as [l3 Heq' HP].
    rewrite <- map_map in Heq'.
    decomp_map_Type Heq' ; decomp_map_Type Heq' ; simpl in Heq'3 ; simpl in Heq'4 ; subst.
    inversion Hnzsp ; inversion H2 ; subst.
    apply Forall_Type_rev in H3.
    apply (PEperm_Type_Forall_Type _ _ _ _ HP) in H3 ; simpl in H3.
    apply Forall_Type_app_inv in H3.
    destruct H3 as [H3l H3r].
    apply PEperm_Type_rev in HP ; list_simpl in HP ; symmetry in HP.
    eapply ex_ir ; [ | exact HP ].
    apply tens_irr.
    * apply IHHll1.
      -- constructor...
         apply Forall_Type_rev...
      -- list_simpl...
    * apply IHHll2.
      -- constructor...
         apply Forall_Type_rev...
      -- list_simpl...
  + symmetry in H1.
    decomp_map_Type H1 ; decomp_map_Type H4 ; simpl in H4 ; simpl in H6 ; simpl in H8 ; subst.
    inversion Hnzsp ; subst.
    apply Forall_Type_rev in H3.
    rewrite <- H7 in H3.
    apply Forall_Type_app_inv in H3.
    destruct H3 as [H3l H3r].
    inversion H3r ; subst.
    apply (Forall_Type_app _ _ _ H4) in H3l.
    assert ({ pl : _ & 
       PEperm_Type (ipperm P) (l8 ++ l6) (fst pl ++ snd pl) &
       l2 ++ l1 = map dual (map ill2ll (fst pl)) ++ ill2ll C :: map dual (map ill2ll (snd pl)) /\
       (ipperm P = false -> l8 = fst pl /\ l6 = snd pl) }) as  HP0.
    { clear - HP.
      case_eq (ipperm P) ; intros Hperm ; rewrite_all Hperm.
      - apply PEperm_Type_vs_elt_inv in HP.
        destruct HP as [(ll & lr) Heq HP0] ; simpl in HP0.
        rewrite <- 2 map_app in HP0.
        rewrite map_map in HP0.
        symmetry in HP0.
        apply Permutation_Type_map_inv in HP0.
        destruct HP0 as [l3 Heq1 HP].
        rewrite <- map_map in Heq1.
        decomp_map_Type Heq1 ; decomp_map_Type Heq1 ; simpl in Heq4 ; simpl in Heq5 ; subst.
        eexists ; simpl ; [ | split ]...
        intros Hb ; inversion Hb.
      - simpl in HP.
        exists (l8,l6) ; simpl ; [ | split ]...
        intros ; split ; reflexivity. }
    destruct HP0 as [(ll & lr) HP0 (Heq' & HPeq)].
    dichot_Type_elt_app_exec Heq' ; subst.
    * symmetry in Heq'1.
      decomp_map_Type Heq'1 ; decomp_map_Type Heq'1 ;
        simpl in Heq'1 ; simpl in Heq'4 ; simpl in Heq'5 ; subst.
      apply (PEperm_Type_Forall_Type _ _ _ _ HP0) in H3l ; simpl in H3l.
      destruct x0 ; inversion H1 ; inversion H3 ; subst.
      -- simpl in H7.
         apply (f_equal (@rev _)) in H7.
         rewrite rev_involutive in H7 ; subst.
         list_simpl.
         simpl in HP0.
         apply (ex_ir _ (rev ll ++ ilpam x0_1 x0_2 :: rev l10 ++ rev l9)).
         ++ apply lpam_ilr.
            ** apply IHHll1.
               --- constructor...
                   apply Forall_Type_app_inv in H3l.
                   destruct H3l as [_ H3l].
                   apply Forall_Type_app_inv in H3l.
                   destruct H3l as [_ H3l].
                   apply Forall_Type_rev...
               --- rewrite bidual.
                   list_simpl...
            ** apply IHHll2.
               --- constructor...
                   apply Forall_Type_app_inv in H3l.
                   destruct H3l as [H3l' H3l].
                   apply Forall_Type_app_inv in H3l.
                   destruct H3l as [H3l _].
                   apply Forall_Type_rev in H3l'.
                   apply Forall_Type_rev in H3l.
                   apply Forall_Type_app...
                   constructor...
               --- list_simpl.
                   PCperm_Type_solve.
         ++ case_eq (ipperm P) ; intros Hperm ; rewrite_all Hperm.
            ** clear - HP0.
               apply Permutation_Type_rev' in HP0.
               list_simpl in HP0.
               list_simpl.
               apply Permutation_Type_elt.
               symmetry.
               etransitivity ; [ apply Permutation_Type_app_comm | ].
               perm_Type_solve.
            ** destruct (HPeq eq_refl) ; subst.
               list_simpl...
      -- simpl in Hll1.
         change (dual (ill2ll x0_2) :: map dual (map ill2ll l10))
           with (map dual (map ill2ll (x0_2 :: l10))) in Hll1.
         apply dual_jfragment_zeropos in Hll1...
         ++ destruct Hll1 as [(C1 & lz1 & lz2) HzC1 Heq1] ; simpl in Heq1.
            destruct lz1 ; inversion Heq1 ; subst.
            ** contradiction HzC1.
            ** apply (f_equal (@rev _)) in H7.
               rewrite rev_involutive in H7 ; subst.
               simpl in HP0 ; rewrite ? app_assoc in HP0.
               apply PEperm_Type_vs_elt_inv in HP0.
               destruct HP0 as [(ll1 & lr1) HP0 _] ; simpl in HP0.
               dichot_Type_elt_app_exec HP0 ; subst ; list_simpl.
               --- apply zeropos_ilr...
               --- rewrite ? app_comm_cons.
                   rewrite ? app_assoc.
                   apply zeropos_ilr...
         ++ constructor...
            apply Forall_Type_app_inv in H3l.
            destruct H3l as [_ H3l].
            apply Forall_Type_app_inv in H3l.
            destruct H3l as [_ H3l]...
      -- simpl in Hll1.
         change (covar (i2a atN) :: map dual (map ill2ll l10))
           with (map dual (map ill2ll (N :: l10))) in Hll1.
         apply dual_jfragment_zeropos in Hll1...
         ++ destruct Hll1 as [(C1 & lz1 & lz2) HzC1 Heq1].
            destruct lz1 ; inversion Heq1 ; subst.
            ** inversion HzC1.
            ** apply (f_equal (@rev _)) in H7.
               rewrite rev_involutive in H7 ; subst.
               simpl in HP0 ; rewrite ? app_assoc in HP0.
               apply PEperm_Type_vs_elt_inv in HP0.
               destruct HP0 as [(ll1 & lr1) HP0 _ ].
               dichot_Type_elt_app_exec HP0 ; subst ; list_simpl.
               --- apply zeropos_ilr...
               --- rewrite ? app_comm_cons.
                   rewrite ? app_assoc.
                   apply zeropos_ilr...
         ++ constructor...
            --- constructor.
            --- apply Forall_Type_app_inv in H3l.
                destruct H3l as [_ H3l].
                apply Forall_Type_app_inv in H3l.
                destruct H3l as [_ H3l]...
    * symmetry in Heq'0.
      decomp_map_Type Heq'0 ; decomp_map_Type Heq'0 ;
        simpl in Heq'0 ; simpl in Heq'4 ; simpl in Heq'5 ; subst.
      simpl in HP0 ; simpl in H3l ; simpl in H3r.
      apply (PEperm_Type_Forall_Type _ _ _ _ HP0) in H3l.
      destruct x0 ; inversion H1 ; inversion H3 ; subst.
      -- simpl in Hll2.
         change (dual (ill2ll x0_2) :: map dual (map ill2ll l9))
           with (map dual (map ill2ll (x0_2 :: l9))) in Hll2.
         apply dual_jfragment_zeropos in Hll2...
         ++ destruct Hll2 as [(C1 & lz1 & lz2) HzC1 Heq1].
            destruct lz1 ; inversion Heq1 ; subst.
            ** contradiction HzC1.
            ** apply (f_equal (@rev _)) in H7.
               rewrite rev_involutive in H7 ; subst.
               list_simpl in HP0.
               apply PEperm_Type_vs_elt_inv in HP0.
               destruct HP0 as [(ll1 & lr1) HP0 _ ].
               dichot_Type_elt_app_exec HP0 ; subst ; list_simpl.
               --- apply zeropos_ilr...
               --- rewrite ? app_comm_cons.
                   rewrite ? app_assoc.
                   apply zeropos_ilr...
         ++ constructor...
            apply Forall_Type_app_inv in H3l.
            destruct H3l as [H3l _].
            apply Forall_Type_app_inv in H3l.
            destruct H3l as [H3l _]...
      -- simpl in H7.
         apply (f_equal (@rev _)) in H7.
         rewrite rev_involutive in H7 ; subst.
         list_simpl.
         simpl in HP0.
         apply (ex_ir _ (rev l10 ++ rev l9 ++ ilmap x0_1 x0_2 :: rev lr)).
         ++ apply lmap_ilr.
            ** apply IHHll2.
               --- constructor...
                   apply Forall_Type_app_inv in H3l.
                   destruct H3l as [H3l _].
                   apply Forall_Type_app_inv in H3l.
                   destruct H3l as [H3l _].
                   apply Forall_Type_rev...
               --- rewrite bidual.
                   list_simpl...
            ** apply IHHll1.
               --- constructor...
                   apply Forall_Type_app_inv in H3l.
                   destruct H3l as [H3l' H3l].
                   apply Forall_Type_app_inv in H3l'.
                   destruct H3l' as [_ H3l'].
                   apply Forall_Type_rev in H3l'.
                   apply Forall_Type_rev in H3l.
                   apply Forall_Type_app...
                   constructor...
               --- list_simpl.
                   PCperm_Type_solve.
         ++ case_eq (ipperm P) ; intros Hperm ; rewrite_all Hperm.
            ** clear - HP0.
               apply Permutation_Type_rev' in HP0.
               list_simpl in HP0.
               list_simpl.
               rewrite app_assoc.
               apply Permutation_Type_elt.
               etransitivity ; [ apply Permutation_Type_app_comm | ].
               perm_Type_solve.
            ** destruct (HPeq eq_refl) ; subst.
               list_simpl...
      -- simpl in H7.
         apply (f_equal (@rev _)) in H7.
         rewrite rev_involutive in H7 ; subst.
         list_simpl.
         simpl in HP0.
         apply (ex_ir _ (rev l10 ++ rev l9 ++ ineg x0 :: rev lr)).
         ++ apply neg_pam_rule.
            ** intros a.
               apply Hgax.
            ** apply IHHll2.
               --- constructor...
                   apply Forall_Type_app_inv in H3l.
                   destruct H3l as [H3l _].
                   apply Forall_Type_app_inv in H3l.
                   destruct H3l as [H3l _].
                   apply Forall_Type_rev...
               --- rewrite bidual.
                   list_simpl...
            ** apply IHHll1.
               --- constructor...
                   apply Forall_Type_app_inv in H3l.
                   destruct H3l as [H3l' H3l].
                   apply Forall_Type_app_inv in H3l'.
                   destruct H3l' as [_ H3l'].
                   apply Forall_Type_rev in H3l'.
                   apply Forall_Type_rev in H3l.
                   apply Forall_Type_app...
                   constructor...
                   constructor.
               --- list_simpl.
                   PCperm_Type_solve.
         ++ case_eq (ipperm P) ; intros Hperm ; rewrite_all Hperm.
            ** clear - HP0.
               apply Permutation_Type_rev' in HP0.
               list_simpl in HP0.
               list_simpl.
               rewrite app_assoc.
               apply Permutation_Type_elt.
               etransitivity ; [ apply Permutation_Type_app_comm | ].
               perm_Type_solve.
            ** destruct (HPeq eq_refl) ; subst.
               list_simpl...
- list_simpl in HP.
  symmetry in HP.
  apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq ; subst.
  + list_simpl in HP.
    rewrite map_map in HP.
    apply PEperm_Type_map_inv in HP.
    destruct HP as [l3 Heq' HP].
    rewrite <- map_map in Heq' ; subst.
    inversion Hnzsp ; subst.
    apply Forall_Type_rev in H3.
    apply (PEperm_Type_Forall_Type _ _ _ _ HP) in H3.
    destruct C ; inversion H0 ; inversion H2 ; subst.
    * apply lpam_irr.
      symmetry in HP.
      apply PEperm_Type_rev in HP.
      rewrite rev_involutive in HP.
      apply (ex_ir _ (rev l3 ++ C1 :: nil)) ; [ | apply PEperm_Type_add_inside ]...
      apply IHHll.
      -- constructor...
         apply Forall_Type_app ; [ | constructor ] ; try constructor...
         apply Forall_Type_rev...
      -- list_simpl...
    * apply lmap_irr.
      symmetry in HP.
      apply PEperm_Type_rev in HP.
      rewrite rev_involutive in HP.
      apply (ex_ir _ (C1 :: rev l3)) ; [ | apply PEperm_Type_cons ]...
      apply IHHll.
      -- constructor...
         constructor...
         apply Forall_Type_rev...
      -- list_simpl ; PCperm_Type_solve.
    * apply neg_irr.
      symmetry in HP.
      apply PEperm_Type_rev in HP.
      rewrite rev_involutive in HP.
      apply (ex_ir _ (C :: rev l3)) ; [ | apply PEperm_Type_cons ]...
      apply IHHll.
      -- constructor ; [ constructor | ]...
         constructor...
         apply Forall_Type_rev...
      -- list_simpl ; PCperm_Type_solve.
  + symmetry in H1.
    decomp_map_Type H1 ; decomp_map_Type H3 ; simpl in H3 ; simpl in H5 ; simpl in H7 ; subst.
    simpl in H6 ; apply (f_equal (@rev _)) in H6.
    rewrite rev_involutive in H6 ; subst.
    destruct x0 ; inversion H1 ; subst.
    list_simpl.
    apply tens_ilr.
    apply IHHll.
    * inversion Hnzsp.
      constructor...
      list_simpl in H3.
      apply Forall_Type_app_inv in H3.
      destruct H3 as [H3l H3r].
      inversion H3r.
      inversion H5 ; subst.
      apply Forall_Type_app...
      constructor...
      constructor...
    * list_simpl.
      rewrite HP ; PCperm_Type_solve.
- list_simpl in HP.
  symmetry in HP.
  apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq ; subst.
  + destruct C ; inversion H0 ; subst.
    apply top_irr.
  + symmetry in H1.
    decomp_map_Type H1 ; decomp_map_Type H3 ; simpl in H3 ; simpl in H5 ; simpl in H7 ; subst.
    apply (f_equal (@rev _)) in H6.
    rewrite rev_involutive in H6 ; subst.
    destruct x0 ; inversion H1 ; subst.
    list_simpl.
    apply zero_ilr.
- list_simpl in HP.
  symmetry in HP.
  apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq ; subst.
  + list_simpl in HP.
    rewrite map_map in HP.
    apply PEperm_Type_map_inv in HP.
    destruct HP as [l3 Heq' HP].
    rewrite <- map_map in Heq' ; subst.
    inversion Hnzsp ; subst.
    apply Forall_Type_rev in H3.
    apply (PEperm_Type_Forall_Type _ _ _ _ HP) in H3.
    destruct C ; inversion H0 ; subst.
    inversion H2 ; subst.
    symmetry in HP.
    apply PEperm_Type_rev in HP.
    rewrite rev_involutive in HP.
    apply (ex_ir _ (rev l3)) ; [ | apply HP ].
    apply plus_irr1.
    apply IHHll.
    * constructor...
      apply Forall_Type_rev...
    * list_simpl...
  + symmetry in H1.
    decomp_map_Type H1 ; decomp_map_Type H3 ; simpl in H3 ; simpl in H5 ; simpl in H7 ; subst.
    apply (f_equal (@rev _)) in H6.
    rewrite rev_involutive in H6 ; subst.
    destruct x0 ; inversion H1 ; subst.
    list_simpl.
    apply with_ilr1.
    apply IHHll.
    * inversion Hnzsp.
      constructor...
      list_simpl in H3.
      apply Forall_Type_app_inv in H3.
      destruct H3 as [H3l H3r].
      inversion H3r.
      inversion H5 ; subst.
      apply Forall_Type_app...
      constructor...
    * list_simpl.
      rewrite HP ; PCperm_Type_solve.
- list_simpl in HP.
  symmetry in HP.
  apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq ; subst.
  + list_simpl in HP.
    rewrite map_map in HP.
    apply PEperm_Type_map_inv in HP.
    destruct HP as [l3 Heq' HP].
    rewrite <- map_map in Heq' ; subst.
    inversion Hnzsp ; subst.
    apply Forall_Type_rev in H3.
    apply (PEperm_Type_Forall_Type _ _ _ _ HP) in H3.
    destruct C ; inversion H0 ; subst.
    inversion H2 ; subst.
    symmetry in HP.
    apply PEperm_Type_rev in HP.
    rewrite rev_involutive in HP.
    apply (ex_ir _ (rev l3)) ; [ | apply HP ].
    apply plus_irr2.
    apply IHHll.
    * constructor...
      apply Forall_Type_rev...
    * list_simpl...
  + symmetry in H1.
    decomp_map_Type H1 ; decomp_map_Type H3 ; simpl in H3 ; simpl in H5 ; simpl in H7 ; subst.
    apply (f_equal (@rev _)) in H6.
    rewrite rev_involutive in H6 ; subst.
    destruct x0 ; inversion H1 ; subst.
    list_simpl.
    apply with_ilr2.
    apply IHHll.
    * inversion Hnzsp.
      constructor...
      list_simpl in H3.
      apply Forall_Type_app_inv in H3.
      destruct H3 as [H3l H3r].
      inversion H3r.
      inversion H5 ; subst.
      apply Forall_Type_app...
      constructor...
    * list_simpl.
      rewrite HP ; PCperm_Type_solve.
- list_simpl in HP.
  symmetry in HP.
  apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq ; subst.
  + list_simpl in HP.
    rewrite map_map in HP.
    apply PEperm_Type_map_inv in HP.
    destruct HP as [l3 Heq' HP].
    rewrite <- map_map in Heq' ; subst.
    inversion Hnzsp ; subst.
    apply Forall_Type_rev in H3.
    apply (PEperm_Type_Forall_Type _ _ _ _ HP) in H3.
    destruct C ; inversion H0 ; subst.
    inversion H2 ; subst.
    symmetry in HP.
    apply PEperm_Type_rev in HP.
    rewrite rev_involutive in HP.
    apply (ex_ir _ (rev l3)) ; [ | apply HP ].
    apply with_irr.
    * apply IHHll1.
      -- constructor...
         apply Forall_Type_rev...
      -- list_simpl...
    * apply IHHll2.
      -- constructor...
         apply Forall_Type_rev...
      -- list_simpl...
  + symmetry in H1.
    decomp_map_Type H1 ; decomp_map_Type H3 ; simpl in H3 ; simpl in H5 ; simpl in H7 ; subst.
    apply (f_equal (@rev _)) in H6.
    rewrite rev_involutive in H6 ; subst.
    destruct x0 ; inversion H1 ; subst.
    list_simpl.
    apply plus_ilr.
    * apply IHHll1.
      -- inversion Hnzsp.
         constructor...
         list_simpl in H3.
         apply Forall_Type_app_inv in H3.
         destruct H3 as [H3l H3r].
         inversion H3r.
         inversion H5 ; subst.
         apply Forall_Type_app...
         constructor...
      -- list_simpl.
         rewrite HP ; PCperm_Type_solve.
    * apply IHHll2.
      -- inversion Hnzsp.
         constructor...
         list_simpl in H3.
         apply Forall_Type_app_inv in H3.
         destruct H3 as [H3l H3r].
         inversion H3r.
         inversion H5 ; subst.
         apply Forall_Type_app...
         constructor...
      -- list_simpl.
         rewrite HP ; PCperm_Type_solve.
- list_simpl in HP.
  symmetry in HP.
  apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq ; subst.
  + list_simpl in HP.
    rewrite map_map in HP.
    apply PEperm_Type_map_inv in HP.
    destruct HP as [l3 Heq' HP].
    rewrite <- (map_map _ _ l3) in Heq'.
    destruct (ill2ll_map_ioc_inv _ _ Heq') as [l0' Heq'' _] ; subst.
    inversion Hnzsp ; subst.
    apply Forall_Type_rev in H3.
    apply (PEperm_Type_Forall_Type _ _ _ _ HP) in H3.
    destruct C ; inversion H0 ; subst.
    inversion H2 ; subst.
    symmetry in HP.
    apply PEperm_Type_rev in HP.
    rewrite rev_involutive in HP.
    apply (ex_ir _ (rev (map ioc l0'))) ; [ | apply HP ].
    list_simpl.
    apply oc_irr.
    apply IHHll.
    * constructor...
      apply Forall_Type_rev in H3 ; list_simpl in H3...
    * rewrite Heq'.
      list_simpl...
  + symmetry in H1.
    decomp_map_Type H1 ; decomp_map_Type H3 ; simpl in H3 ; simpl in H5 ; simpl in H7 ; subst.
    destruct x0 ; inversion H1.
- list_simpl in HP.
  symmetry in HP.
  apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq ; subst.
  + destruct C ; inversion H0.
  + symmetry in H1.
    decomp_map_Type H1 ; decomp_map_Type H3 ; simpl in H3 ; simpl in H5 ; simpl in H7 ; subst.
    apply (f_equal (@rev _)) in H6.
    rewrite rev_involutive in H6 ; subst.
    destruct x0 ; inversion H1 ; subst.
    list_simpl.
    apply de_ilr.
    apply IHHll.
    * inversion Hnzsp.
      constructor...
      list_simpl in H3.
      apply Forall_Type_app_inv in H3.
      destruct H3 as [H3l H3r].
      inversion H3r.
      inversion H5 ; subst.
      apply Forall_Type_app...
      constructor...
    * list_simpl.
      rewrite HP ; PCperm_Type_solve.
- list_simpl in HP.
  symmetry in HP.
  apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq ; subst.
  + destruct C ; inversion H0.
  + symmetry in H1.
    decomp_map_Type H1 ; decomp_map_Type H3 ; simpl in H3 ; simpl in H5 ; simpl in H7 ; subst.
    apply (f_equal (@rev _)) in H6.
    rewrite rev_involutive in H6 ; subst.
    destruct x0 ; inversion H1 ; subst.
    list_simpl.
    apply wk_ilr.
    apply IHHll.
    * inversion Hnzsp.
      constructor...
      list_simpl in H3.
      apply Forall_Type_app_inv in H3.
      destruct H3 as [H3l H3r].
      inversion H3r.
      inversion H5 ; subst.
      apply Forall_Type_app...
    * list_simpl.
      apply PEperm_PCperm_Type in HP ; unfold id in HP.
      PCperm_Type_solve.
- list_simpl in HP.
  symmetry in HP.
  apply PCperm_Type_vs_cons_inv in HP.
  destruct HP as [(l' & l'') Heq HP].
  destruct l' ; inversion Heq ; subst.
  + destruct C ; inversion H0.
  + symmetry in H1.
    decomp_map_Type H1 ; decomp_map_Type H3 ; simpl in H3 ; simpl in H5 ; simpl in H7 ; subst.
    apply (f_equal (@rev _)) in H6.
    rewrite rev_involutive in H6 ; subst.
    destruct x0 ; inversion H1 ; subst.
    list_simpl.
    case_eq (ipperm P) ; intros Hperm ; rewrite_all Hperm.
    * assert (HP' := HP).
      apply Permutation_Type_vs_elt_inv in HP'.
      destruct HP' as [(l' & l'') Heq'].
      dichot_Type_elt_app_exec Heq' ; subst.
      -- contradict Heq'0.
         clear.
         revert lw ; induction l' ; intros lw Heq.
         ++ destruct lw ; inversion Heq.
            destruct C ; inversion H0.
         ++ destruct lw ; inversion Heq.
            apply IHl' in H1...
      -- simpl in HP.
         rewrite app_assoc in HP.
         apply Permutation_Type_app_inv in HP.
         rewrite <- ? map_app in HP.
         rewrite map_map in HP.
         rewrite <- app_assoc in HP.
         apply Permutation_Type_map_inv in HP.
         destruct HP as [l3' Heq' HP].
         decomp_map_Type Heq' ; simpl in Heq'2 ; simpl in Heq'4 ; simpl in Heq'5.
         rewrite <- (map_map _ _ l0) in Heq'2.
         assert (Heq''2 := Heq'2).
         apply ill2ll_map_ioc_inv in Heq''2.
         destruct Heq''2 as [lw' Heq''2 _] ; subst.
         rewrite_all Heq'2.
         apply (ex_ir _ (rev l4 ++ map ioc (rev lw') ++ ioc x0 :: rev l8)).
         ++ apply co_ilr.
            apply IHHll.
            ** inversion Hnzsp.
               constructor...
               list_simpl in H3.
               apply Forall_Type_app_inv in H3.
               destruct H3 as [H3l H3r].
               inversion H3r ; subst.
               apply Forall_Type_rev in H3l ; rewrite rev_involutive in H3l.
               apply Forall_Type_rev in H6 ; rewrite rev_involutive in H6.
               apply (Forall_Type_app _ _ _ H3l) in H6.
               apply (Permutation_Type_Forall_Type _ _ _ HP) in H6.
               apply Forall_Type_app_inv in H6.
               destruct H6 as [H6l H6r].
               apply Forall_Type_app_inv in H6r.
               destruct H6r as [H6rl H6rr].
               apply Forall_Type_rev in H6l.
               list_simpl in  H6l.
               apply Forall_Type_rev in H6rl.
               apply Forall_Type_rev in H6rr.
               apply Forall_Type_app...
               constructor...
               apply Forall_Type_app...
               constructor...
            ** rewrite <- (map_map _ _ l4).
               rewrite <- (map_map _ _ l8).
               simpl ; rewrite Hperm ; list_simpl.
               perm_Type_solve.
         ++ rewrite Hperm.
            rewrite app_assoc.
            apply Permutation_Type_elt.
            symmetry.
            etransitivity ; [ apply Permutation_Type_app_comm | ].
            rewrite <- rev_app_distr.
            simpl in HP.
            apply Permutation_Type_rev' in HP.
            etransitivity ; [ apply HP | ].
            perm_Type_solve.
    * simpl in HP.
      dichot_Type_elt_app_exec HP.
      -- contradict HP0.
         clear.
         revert lw ; induction l7 ; intros lw Heq.
         ++ destruct lw ; inversion Heq.
            destruct C ; inversion H0.
         ++ destruct lw ; inversion Heq.
            apply IHl7 in H1...
      -- symmetry in HP0.
         decomp_map_Type HP0 ; decomp_map_Type HP0 ; simpl in HP3 ; simpl in HP5 ; simpl in HP6 ; subst.
         assert (HP4 := HP3).
         apply ill2ll_map_ioc_inv in HP4.
         destruct HP4 as [lw' HP4 _] ; subst.
         rewrite_all HP3.
         list_simpl.
         apply co_ilr.
         apply IHHll.
         ++ inversion Hnzsp.
            constructor...
            list_simpl in H3.
            apply Forall_Type_app_inv in H3.
            destruct H3 as [H3l H3r].
            apply Forall_Type_app_inv in H3r.
            destruct H3r as [H3rl H3rr].
            inversion H3rr ; subst.
            apply Forall_Type_app...
            constructor...
            apply Forall_Type_app...
         ++ simpl ; rewrite Hperm ; list_simpl.
            cperm_Type_solve.
- simpl in f.
  rewrite Hcut in f.
  inversion f.
- apply (Hgax a) in HP.
  destruct HP as [b Heq1 Heq2] ; subst.
  apply gax_ir.
Qed.


(** Axiom-free conservativity *)
Proposition ll_to_ill_nzeropos_axfree {P} : (forall l C, ~ ipgax P l C) -> forall l s,
  ll (i2pfrag P) l s -> forall l0 C, Forall nonzerospos (C :: l0) ->
    PCperm (pperm (i2pfrag P)) l (ill2ll C :: rev (map dual (map ill2ll l0))) ->
      exists s', ill P l0 C s'.
Proof with myeeasy.
intros P_axfree l s pi l0 C Hnz HP.
apply cut_admissible_axfree in pi.
- clear s ; destruct pi as [s pi]. 
  rewrite cutrm_i2pfrag in pi.
  eapply ll_to_ill_nzeropos_cutfree in pi...
  + clear s ; destruct pi as [s pi].
    eexists.
    eapply (stronger_ipfrag)...
    nsplit 3...
    simpl ; intros...
  + intros l1 C1 Hgax.
    apply P_axfree in Hgax.
    inversion Hgax.
- intros l1 Hgax.
  destruct Hgax as (l' & C0 & Heq & Hgax).
  apply P_axfree in Hgax...
Qed.


(** Axiom expansion using embedding into [ll] *)
Lemma ax_exp_ill_nzeropos_by_ll {P} : forall A, nonzerospos A ->
  exists s, ill P (A :: nil) A s.
Proof with myeeasy.
intros A Hnz.
assert (Hax :=
  @ax_exp (i2pfrag (axupd_ipfrag P (fun _ _ => False))) (ill2ll A)).
destruct Hax as [s pi].
eapply ll_to_ill_nzeropos_axfree in pi...
- clear s ; destruct pi as [s pi].
  eexists.
  eapply stronger_ipfrag...
  nsplit 3...
  intros l a Hax.
  inversion Hax.
- intros l a Hax.
  inversion Hax.
- constructor...
  constructor...
  constructor.
- PCperm_solve.
Qed.

(** Cut elimination *)
Lemma cut_ir_nzeropos_axfree_by_ll {P} : (forall l C, ~ ipgax P l C) ->
  forall A l0 l1 l2 C s1 s2, Forall nonzerospos (C :: l1 ++ l0 ++ l2) ->
  ill P l0 A s1 -> ill P (l1 ++ A :: l2) C s2 -> exists s,
    ill P (l1 ++ l0 ++ l2) C s.
Proof with myeeasy.
intros P_axfree A l0 l1 l2 C s1 s2 Hnz pi1 pi2.
apply ill_to_ll in pi1.
clear s1 ; destruct pi1 as [s1 pi1].
apply ill_to_ll in pi2.
clear s2 ; destruct pi2 as [s2 pi2].
rewrite <- ? map_rev in pi2.
rewrite rev_app_distr in pi2 ; simpl in pi2.
rewrite ? map_app in pi2 ; simpl in pi2.
rewrite <- ? app_assoc in pi2.
rewrite <- ? app_comm_cons in pi2 ; simpl in pi2.
rewrite app_comm_cons in pi2.
eapply ex_r in pi2 ; [ | apply PCperm_app_comm ].
rewrite <- ? app_comm_cons in pi2.
assert (forall l, ~ pgax (i2pfrag P) l) as P_axfree'.
{ intros l Hgax.
  destruct Hgax as (l' & C' & _ & Hgax).
  apply P_axfree in Hgax... }
apply (cut_r_axfree P_axfree' _ _ _ _ _ pi2) in pi1.
clear s1 ; destruct pi1 as [s1 pi1].
eapply ll_to_ill_nzeropos_axfree in pi1...
PCperm_solve.
Qed.

Proposition cut_admissible_ill_nzeropos_axfree_by_ll {P} : (forall l C, ~ ipgax P l C) ->
  forall l C s, Forall nonzerospos (C :: l) -> ill P l C s ->
    exists s', ill (cutrm_ipfrag P) l C s'.
Proof with myeeasy.
intros P_axfree l C s Hnz pi.
apply ill_to_ll in pi.
clear s ; destruct pi as [s pi].
apply cut_admissible_axfree in pi.
- clear s ; destruct pi as [s pi].
  rewrite cutrm_i2pfrag in pi.
  eapply ll_to_ill_nzeropos_cutfree in pi...
  intros l1 C1 Hgax.
  apply P_axfree in Hgax.
  inversion Hgax.
- intros l0 (l1 & C1 & _ & Hax).
  apply P_axfree in Hax...
Qed.


(** *** Conservativity with constraints on the left of [ilpam] *)

(** Constraints on the left of [ilpam] for conservativity *)
Inductive oclike : iformula -> Prop :=
| ocl_ivar    : forall X, oclike (ivar X)
| ocl_ione    : oclike ione
| ocl_itens   : forall A B, oclike A -> oclike B -> oclike (itens A B)
| ocl_iwith_l : forall A B, oclike A -> oclike (iwith A B)
| ocl_iwith_r : forall A B, oclike A -> oclike (iwith B A)
| ocl_izero   : oclike izero
| ocl_iplus   : forall A B, oclike A -> oclike B -> oclike (iplus A B)
| ocl_ioc     : forall A, oclike (ioc A).

Inductive oclpam : iformula -> Prop :=
| oclm_ivar  : forall x, oclpam (ivar x)
| oclm_ione  : oclpam ione
| oclm_itens : forall A B, oclpam A -> oclpam B -> oclpam (itens A B)
| oclm_ilpam : forall A B, oclike A -> oclpam A -> oclpam B -> oclpam (ilpam A B)
| oclm_ilmap : forall A B, oclike A -> oclpam A -> oclpam B -> oclpam (ilmap A B)
| oclm_ineg  : forall A, oclike A -> oclpam A -> oclpam (ineg A)
| oclm_itop  : oclpam itop
| oclm_iwith : forall A B, oclpam A -> oclpam B -> oclpam (iwith A B)
| oclm_izero : oclpam izero
| oclm_iplus : forall A B, oclpam A -> oclpam B -> oclpam (iplus A B)
| oclm_ioc   : forall A, oclpam A -> oclpam (ioc A).

(*
Definition easyipgax_oclpam P := forall l0 C, ipgax P l0 C ->
   (forall l C',
     PCperm (ipperm P) (ill2ll C :: rev (map dual (map ill2ll l0)))
                       (ill2ll C' :: l)
     -> C = C' /\ l = rev (map dual (map ill2ll l0)))
/\ ~ In N l0.
*)

(** Cut-free conservativity *)
(* TODO try following statement for possibly shorter proof:
Theorem ll_to_ill_oclpam_cutfree {P} : ipcut P = false -> (forall l C, ~ ipgax P l C) -> ipperm P = true ->
  forall l s, ll (i2pfrag P) l s -> forall l0 l1 C, Forall oclpam (C :: l0) ->
    Forall oclike l1 ->
    PCperm (pperm (i2pfrag P)) l (ill2ll C :: map ill2ll l1 ++ rev (map dual (map ill2ll l0))) ->
      forall l2, (l1 = nil -> l2 = nil) -> exists s', ill P (l0 ++ l2) C s'.
Proof with myeeasy.
intros Hcut Hgax Hperm.
intros l s Hll ; induction Hll ; intros l0 lo C Hoclm Hocl HP lwk Hnil ; try (now inversion f).
- apply PCperm_length_2_inv in HP.
  destruct HP as [HP | HP] ; inversion HP ; destruct C ; inversion H0 ; subst.
  destruct lo ; list_simpl in H1 ; inversion H1.
  + induction l0 using rev_ind ; list_simpl in H2 ; inversion H2.
    induction l0 using rev_ind ; list_simpl in H4 ; inversion H4.
    destruct x ; inversion H3.
    apply i2a_inj in H5 ; subst.
    rewrite (Hnil eq_refl).
    eexists ; apply ax_ir.
  + destruct i0 ; inversion H2.
- rewrite HP in H.
  eapply IHHll in H...
- apply PCperm_length_1_inv in HP.
  inversion HP ; destruct C ; inversion H0 ; subst.
  destruct lo ; inversion H1.
  induction l0 using rev_ind ; list_simpl in H1 ; inversion H1.
  rewrite (Hnil eq_refl).
  eexists ; apply one_irr.
- symmetry in HP ; apply PCperm_vs_cons_inv in HP.
  destruct HP as (l' & l'' & HP & Heq).
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  symmetry in H1 ; dichot_elt_app_exec H1 ; subst ;
    [ decomp_map H0 ; destruct x ; inversion H0
    | list_simpl in H2 ; decomp_map H2 ; decomp_map H3 ; destruct x ; inversion H2 ;
                                                         destruct x0 ; inversion H3 ] ; subst.
  apply (f_equal (@rev _)) in H6 ; list_simpl in H6 ; subst.
  apply PEperm_PCperm in HP ; unfold id in HP.
  assert (HP' := PCperm_trans _ _ _ _ HP (PCperm_app_comm _ _ _)).
  specialize IHHll with (rev l8 ++ rev l6) lo C lwk.
  list_simpl in IHHll ; list_simpl in HP' ; eapply IHHll in HP'...
  + destruct HP' as [s' IH] ; list_simpl in IH.
    eexists ; list_simpl ; apply one_ilr...
  + inversion Hoclm ; constructor...
    apply Forall_app_inv in H4 ; destruct H4 as [Hl Hr] ; apply Forall_app...
    inversion Hr...
- symmetry in HP ; apply PCperm_vs_cons_inv in HP.
  destruct HP as (l' & l'' & HP & Heq).
  simpl in HP ; rewrite Hperm in HP ; simpl in HP.
  apply Permutation_app_app_inv in HP.
  destruct HP as (l3' & l3'' & l4' & l4'' & HP1 & HP2 & HP3 & HP4).
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  + apply Permutation_nil in HP4 ; apply app_eq_nil in HP4 ; destruct HP4 ; subst.
    list_simpl in HP1 ; rewrite <- HP1 in HP3.
    list_simpl in HP2 ; rewrite <- HP2 in HP3.
    clear l3' l3'' HP1 HP2.
    apply Permutation_app_app_inv in HP3.
    destruct HP3 as (l3' & l3'' & l4' & l4'' & HP1 & HP2 & HP3 & HP4).
    symmetry in HP1 ; apply Permutation_map_inv in HP1.
    destruct HP1 as (l3 & Heq1 & HP1).
    decomp_map Heq1 ; subst.
    list_simpl in HP2.
    rewrite map_map in HP2.
    symmetry in HP2 ; apply Permutation_map_inv in HP2.
    destruct HP2 as (l3 & Heq2 & HP2).
    rewrite <- Permutation_rev in HP2.
    rewrite <- map_map in Heq2.
    decomp_map Heq2 ; decomp_map Heq2 ; subst.
    specialize IHHll1 with (rev l9) l5 C1 lwk.
    specialize IHHll2 with (rev l8) l4 C2 lwk.
    rewrite HP1 in Hocl.
    apply Forall_app_inv in Hocl ; destruct Hocl as [Hocl2 Hocl1].
Qed.
*)
Theorem ll_to_ill_oclpam_cutfree {P} :
  ipcut P = false -> (forall l C, ~ ipgax P l C) -> ipperm P = true ->
  forall l s, ll (i2pfrag P) l s -> forall l0 l1 C, Forall oclpam (C :: l0) ->
    Forall oclike l1 ->
    PCperm (pperm (i2pfrag P)) l
           (ill2ll C :: map ill2ll l1 ++ rev (map dual (map ill2ll l0))) ->
      (exists s', ill P l0 C s')
  /\  (l1 <> nil -> forall l2, exists s', ill P (l0 ++ l2) C s').
Proof with myeeasy.
intros Hcut Hgax Hperm.
intros l s Hll ; induction Hll ;
  intros l0 lo C Hoclm Hocl HP ; try (now inversion f).
- apply PCperm_length_2_inv in HP.
  destruct HP as [HP | HP] ; inversion HP ; destruct C ; inversion H0 ; subst.
  destruct lo ; list_simpl in H1 ; inversion H1.
  + induction l0 using rev_ind ; list_simpl in H2 ; inversion H2.
    induction l0 using rev_ind ; list_simpl in H4 ; inversion H4.
    destruct x ; inversion H3.
    apply i2a_inj in H5 ; subst.
    split.
    * eexists ; apply ax_ir.
    * intros Hnil.
      exfalso.
      apply Hnil...
  + destruct i0 ; inversion H2.
- rewrite HP in H.
  apply IHHll in H...
- apply PCperm_length_1_inv in HP.
  inversion HP ; destruct C ; inversion H0 ; subst.
  destruct lo ; inversion H1.
  induction l0 using rev_ind ; list_simpl in H1 ; inversion H1.
  split.
  + eexists ; apply one_irr.
  + intros Hnil.
    exfalso.
    apply Hnil...
- symmetry in HP ; apply PCperm_vs_cons_inv in HP.
  destruct HP as (l' & l'' & HP & Heq).
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  symmetry in H1 ; dichot_elt_app_exec H1 ; subst ;
    [ decomp_map H0 ; destruct x ; inversion H0
    | list_simpl in H2 ; decomp_map H2 ; decomp_map H3 ; destruct x ; inversion H2 ;
                                                         destruct x0 ; inversion H3 ] ; subst.
  apply (f_equal (@rev _)) in H6 ; list_simpl in H6 ; subst.
  apply PEperm_PCperm in HP ; unfold id in HP.
  assert (HP' := PCperm_trans _ _ _ _ HP (PCperm_app_comm _ _ _)).
  specialize IHHll with (rev l8 ++ rev l6) lo C.
  list_simpl in IHHll ; list_simpl in HP' ; apply IHHll in HP'...
  + destruct HP' as [[s' IH1] IH2].
    split.
    * eexists ; apply one_ilr...
    * intros Hnil l2.
      destruct (IH2 Hnil l2) as [s'' IH].
      list_simpl in IH.
      eexists ; list_simpl ; apply one_ilr...
  + inversion Hoclm ; constructor...
    apply Forall_app_inv in H4 ; destruct H4 as [Hl Hr] ; apply Forall_app...
    inversion Hr...
- symmetry in HP ; apply PCperm_vs_cons_inv in HP.
  destruct HP as (l' & l'' & HP & Heq).
  simpl in HP ; rewrite Hperm in HP ; simpl in HP.
  apply Permutation_app_app_inv in HP.
  destruct HP as (l3' & l3'' & l4' & l4'' & HP1 & HP2 & HP3 & HP4).
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  + apply Permutation_nil in HP4 ; apply app_eq_nil in HP4 ; destruct HP4 ; subst.
    list_simpl in HP1 ; rewrite <- HP1 in HP3.
    list_simpl in HP2 ; rewrite <- HP2 in HP3.
    clear l3' l3'' HP1 HP2.
    apply Permutation_app_app_inv in HP3.
    destruct HP3 as (l3' & l3'' & l4' & l4'' & HP1 & HP2 & HP3 & HP4).
    symmetry in HP1 ; apply Permutation_map_inv in HP1.
    destruct HP1 as (l3 & Heq1 & HP1).
    decomp_map Heq1 ; subst.
    list_simpl in HP2.
    rewrite map_map in HP2.
    symmetry in HP2 ; apply Permutation_map_inv in HP2.
    destruct HP2 as (l3 & Heq2 & HP2).
    rewrite <- Permutation_rev in HP2.
    rewrite <- map_map in Heq2.
    decomp_map Heq2 ; decomp_map Heq2 ; subst.
    specialize IHHll1 with (rev l9) l5 C1.
    specialize IHHll2 with (rev l8) l4 C2.
    rewrite HP1 in Hocl.
    apply Forall_app_inv in Hocl ; destruct Hocl as [Hocl2 Hocl1].
    apply IHHll1 in Hocl1 ; [ apply IHHll2 in Hocl2 | | ].
    * destruct Hocl1 as [[s1' IH1] IH2].
      destruct Hocl2 as [[s2' IH3] IH4].
      split.
      -- eexists ; eapply ex_ir ; [ apply tens_irr | ]...
         rewrite (Permutation_rev (l8 ++ l9)) in HP2 ; list_simpl in HP2.
         rewrite Hperm ; simpl ; perm_solve.
      -- intros Hnil lw.
         destruct lo ; [ exfalso ; apply Hnil ; reflexivity | ].
         symmetry in HP1 ; apply Permutation_vs_cons_inv in HP1.
         destruct HP1 as (ll & lr & Heq3).
         dichot_elt_app_exec Heq3 ; subst.
         ++ assert (ll ++ i :: l <> nil) as Hnil2
              by (clear ; intros H ; destruct ll ; inversion H).
            destruct (IH4 Hnil2 lw) as [s'' IH].
            eexists ; eapply ex_ir ; [apply tens_irr | ]...
            rewrite (Permutation_rev (l8 ++ l9)) in HP2 ; list_simpl in HP2.
            rewrite Hperm ; simpl ; perm_solve.
         ++ assert (l3 ++ i :: lr <> nil) as Hnil2
              by (clear ; intros H ; destruct l3 ; inversion H).
            destruct (IH2 Hnil2 lw) as [s'' IH].
            eexists ; eapply ex_ir ; [apply tens_irr | ]...
            rewrite (Permutation_rev (l8 ++ l9)) in HP2 ; list_simpl in HP2.
            rewrite Hperm ; simpl ; perm_solve.
    * inversion Hoclm ; subst.
      inversion H2 ; subst.
      constructor...
      rewrite HP2 in H3.
      apply Forall_app_inv in H3 ; destruct H3 as [H3 _].
      apply Forall_rev...
    * simpl ; rewrite Hperm ; simpl ; perm_solve.
    * inversion Hoclm.
      inversion H2.
      constructor...
      rewrite HP2 in H3.
      apply Forall_rev.
      apply Forall_app_inv in H3 ; apply H3...
    * simpl ; rewrite Hperm ; simpl ; perm_solve.
  + dichot_elt_app_exec H1 ; subst.
    * decomp_map H0 ; subst.
      destruct x ; inversion H0 ; subst.
      assert (HP4' := HP4).
      symmetry in HP4' ; apply Permutation_vs_cons_inv in HP4'.
      destruct HP4' as (ll & lr & Heq').
      apply Permutation_app_app_inv in HP3.
      destruct HP3 as (l3l & l3r & l4l & l4r & HP3' & HP3'' & HP3''' & HP3'''').
      symmetry in HP3' ; apply Permutation_map_inv in HP3'.
      destruct HP3' as (l3 & Heq'' & HP3').
      decomp_map Heq'' ; subst.
      list_simpl in HP3''.
      rewrite map_map in HP3''.
      symmetry in HP3'' ; apply Permutation_map_inv in HP3''.
      destruct HP3'' as (l3 & Heq'' & HP3'').
      rewrite <- Permutation_rev in HP3''.
      rewrite <- map_map in Heq''.
      decomp_map Heq'' ; decomp_map Heq'' ; subst.
      rewrite HP3''' in HP1.
      rewrite HP3'''' in HP2.
      dichot_elt_app_exec Heq' ; subst.
      -- list_simpl in HP4 ; apply Permutation_cons_app_inv in HP4.
         symmetry in HP4 ; apply Permutation_map_inv in HP4.
         destruct HP4 as (l3 & Heq' & HP).
         decomp_map Heq' ; subst.
         specialize IHHll2 with (rev l11) (x2 :: l7 ++ l10 ++ l14) C.
         assert (Forall oclike (x2 :: l7 ++ l10 ++ l14)) as Hocl'.
         { rewrite HP in Hocl.
           apply Forall_app_inv in Hocl ; destruct Hocl as [Hocl2 Hocl1].
           inversion Hocl1.
           inversion H2.
           constructor...
           rewrite HP3' in H3 ; apply Forall_app_inv in H3 ; destruct H3 ; apply Forall_app...
           rewrite app_assoc in Hocl2.
           apply Forall_app_inv in Hocl2 ; destruct Hocl2... }
         apply IHHll2 in Hocl'.
         ++ destruct Hocl' as [_ Hocl'].
            assert (x2 :: l7 ++ l10 ++ l14 <> nil) as Hnil
              by (intros Hnil ; inversion Hnil).
            split.
            ** eapply Hocl' in Hnil.
               destruct Hnil as [s' Hnil].
               eexists ; eapply ex_ir ; [ apply Hnil | ].
               rewrite Hperm ; simpl ; rewrite HP3''.
               apply Permutation_app_tail.
               symmetry ; apply Permutation_rev.
            ** intros Hnil' l.
               eapply Hocl' in Hnil.
               destruct Hnil as [s' Hnil].
               eexists ; eapply ex_ir ; [ apply Hnil | ].
               rewrite Hperm ; simpl ; rewrite HP3''.
               rewrite <- app_assoc.
               apply Permutation_app_tail.
               symmetry ; apply Permutation_rev.
         ++ inversion Hoclm ; constructor...
            rewrite HP3'' in H3.
            apply Forall_rev.
            apply Forall_app_inv in H3 ; apply H3.
         ++ list_simpl ; rewrite Hperm ; simpl.
            perm_solve.
      -- list_simpl in HP4 ; rewrite app_assoc in HP4 ; apply Permutation_cons_app_inv in HP4.
         symmetry in HP4 ; apply Permutation_map_inv in HP4.
         destruct HP4 as (l' & Heq' & HP).
         list_simpl in Heq' ; decomp_map Heq' ; subst.
         specialize IHHll1 with (rev l12) (x1 :: l8 ++ l13 ++ l14) C.
         assert (Forall oclike (x1 :: l8 ++ l13 ++ l14)) as Hocl'.
         { rewrite HP in Hocl.
           apply Forall_app_inv in Hocl ; destruct Hocl as [Hocl2 Hocl1].
           inversion Hocl1.
           inversion H2.
           constructor...
           rewrite HP3' in H3 ; apply Forall_app_inv in H3 ; destruct H3 ; apply Forall_app...
           apply Forall_app_inv in Hocl2 ; destruct Hocl2... }
         apply IHHll1 in Hocl'.
         ++ destruct Hocl' as [_ Hocl'].
            assert (x1 :: l8 ++ l13 ++ l14 <> nil) as Hnil
              by (intros Hnil ; inversion Hnil).
            split.
            ** eapply Hocl' in Hnil.
               destruct Hnil as [s' Hnil].
               eexists ; eapply ex_ir ; [ apply Hnil | ].
               rewrite Hperm ; simpl ; rewrite HP3''.
               etransitivity ; [ | apply Permutation_app_comm ].
               apply Permutation_app_tail.
               symmetry ; apply Permutation_rev.
            ** intros Hnil' l.
               eapply Hocl' in Hnil.
               destruct Hnil as [s' Hnil].
               eexists ; eapply ex_ir ; [ apply Hnil | ].
               rewrite Hperm ; simpl ; rewrite HP3''.
               rewrite <- app_assoc.
               etransitivity ; [ | apply Permutation_app_comm ].
               rewrite app_assoc ; apply Permutation_app_tail.
               apply Permutation_app_tail.
               symmetry ; apply Permutation_rev.
         ++ inversion Hoclm ; constructor...
            rewrite HP3'' in H3.
            apply Forall_rev.
            apply Forall_app_inv in H3 ; apply H3.
         ++ list_simpl ; rewrite Hperm ; simpl.
            perm_solve.
    * list_simpl in H2 ; decomp_map H2 ; subst.
      decomp_map H3 ; subst.
      apply (f_equal (@rev _)) in H4 ; list_simpl in H4 ; subst.
      destruct x0 ; inversion H2 ; subst.
      -- assert (HP4' := HP4).
         symmetry in HP4' ; apply Permutation_vs_cons_inv in HP4'.
         destruct HP4' as (l4a & l4b & Heq').
         dichot_elt_app_exec Heq' ; subst.
         ++ rewrite map_map in HP3.
            symmetry in HP3 ; apply Permutation_map_inv in HP3.
            destruct HP3 as (l3''' & Heq' & HP3).
            decomp_map Heq' ; subst.
            rewrite <- map_map in HP1.
            rewrite <- map_map in HP2.
            list_simpl in HP4 ; apply Permutation_cons_app_inv in HP4.
            apply Permutation_app_app_inv in HP4.
            destruct HP4 as (l3a & l3b & l3c & l3d & HP4' & HP4'' & HP4''' & HP4'''').
            apply Permutation_app_app_inv in HP4''''.
            destruct HP4'''' as (l3e & l3f & l3g & l3h & HP4a & HP4b & HP4c & HP4d).
            rewrite HP4''' in HP1.
            rewrite HP4a in HP1.
            symmetry in HP4' ; apply Permutation_map_inv in HP4'.
            destruct HP4' as (l3' & Heq' & HP4').
            decomp_map Heq' ; subst.
            rewrite HP4d in HP4''.
            rewrite map_map in HP4''.
            symmetry in HP4'' ; apply Permutation_map_inv in HP4''.
            destruct HP4'' as (l4' & Heq' & HP4'').
            decomp_map Heq' ; subst.
            rewrite <- (map_map _ _ l11) in HP1.
            rewrite <- (map_map _ _ l13) in HP1. 
            symmetry in HP4c ; apply Permutation_map_inv in HP4c.
            destruct HP4c as (l4' & Heq' & HP4c).
            decomp_map Heq' ; subst.
            rewrite <- (map_map _ _ l14) in HP4b.
            rewrite HP4b in HP2.
            specialize IHHll2 with (rev (x0_2 :: l4 ++ l11 ++ l13)) (l9 ++ l15) C.
            rewrite HP4' in Hocl.
            apply Forall_app_inv in Hocl ; destruct Hocl as [Hocl1 Hocl2].
            specialize IHHll1 with (rev (l6 ++ l14)) l16 x0_1.
            rewrite HP4c in Hocl2.
            apply Forall_app_inv in Hocl2 ; destruct Hocl2 as [Hocl2 Hocl3].
            assert (Hocl4 := Forall_app _ _ _ Hocl1 Hocl2).
            apply IHHll2 in Hocl4 ; [ apply IHHll1 in Hocl3 | | ].
            ** split.
               --- destruct Hocl4 as [[s2' Hocl4] _].
                   destruct Hocl3 as [[s1' Hocl3] _].
                   eexists.
                   apply (ex_ir _ (rev (l4 ++ l11 ++ l13) ++
                                     ilpam x0_1 x0_2 :: rev (l6 ++ l14) ++ nil)).
                   +++ apply lpam_ilr...
                   +++ rewrite Hperm ; simpl ; rewrite HP3 ; rewrite HP4'' ; perm_solve.
               --- intros Hnil lw ; destruct lo ; [ contradiction Hnil ; reflexivity | ].
                   rewrite HP4c in HP4' ; rewrite app_assoc in HP4'.
                   symmetry in HP4' ; apply Permutation_vs_cons_inv in HP4'.
                   destruct HP4' as (l4l & l4r & Heq').
                   dichot_elt_app_exec Heq' ; subst.
                   +++ rewrite <- Heq'0 in Hocl4.
                       assert (l4l ++ i :: l0 <> nil) as Hnil'
                         by (intros Hnil' ; destruct l4l ; inversion Hnil').
                       apply (proj2 Hocl4) with lw in Hnil'.
                       destruct Hnil' as [s2' Hnil'].
                       destruct Hocl3 as [[s1' Hocl3] _].
                       eexists.
                       apply (ex_ir _ (rev (l4 ++ l11 ++ l13) ++
                                         ilpam x0_1 x0_2 :: rev (l6 ++ l14) ++ lw)).
                       *** apply lpam_ilr...
                           eapply ex_ir ; [ apply Hnil' | ].
                           rewrite Hperm ; simpl ; perm_solve.
                       *** rewrite Hperm ; simpl ; rewrite HP3 ; rewrite HP4'' ; perm_solve.
                   +++ assert (l17 ++ i :: l4r <> nil) as Hnil'
                         by (intros Hnil' ; destruct l17 ; inversion Hnil').
                       apply (proj2 Hocl3) with lw in Hnil'.
                       destruct Hnil' as [s1' Hnil'].
                       destruct Hocl4 as [[s2' Hocl4] _].
                       eexists.
                       apply (ex_ir _ (rev (l4 ++ l11 ++ l13) ++
                                         ilpam x0_1 x0_2 :: (rev (l6 ++ l14) ++ lw) ++ nil)).
                       *** apply lpam_ilr...
                       *** rewrite Hperm ; simpl ; rewrite HP3 ; rewrite HP4'' ; perm_solve.
            ** inversion Hoclm ; subst.
               apply Forall_app_inv in H3 ; destruct H3 as [Hoclm1 Hoclm2].
               inversion Hoclm2 ; subst.
               inversion H3 ; constructor...
               rewrite HP3 in Hoclm1.
               apply Forall_rev.
               apply Forall_app.
               --- list_simpl in Hoclm1 ; apply Forall_app_inv in Hoclm1.
                   rewrite <- Permutation_rev in Hoclm1.
                   apply Hoclm1.
               --- rewrite HP4'' in H4.
                   list_simpl in H4 ; apply Forall_app_inv in H4.
                   rewrite <- Permutation_rev in H4.
                   apply H4.
            ** simpl ; rewrite Hperm ; simpl.
               rewrite bidual.
               perm_solve.
            ** inversion Hoclm ; constructor ; subst...
               list_simpl.
               apply Forall_app_inv in H3 ; destruct H3 as [Hoclm1 Hoclm2].
               inversion Hoclm2 ; subst.
               rewrite HP4'' in H4.
               list_simpl in H4.
               apply Forall_app_inv in H4.
               destruct H4 as [H4l H4r] ; apply Forall_app_inv in H4r.
               apply Forall_app ; [ apply H4r | ].
               apply Forall_app ; [ apply H4r | ].
               rewrite HP3 in Hoclm1.
               inversion H3.
               apply Forall_app ; [ | constructor ; [assumption | constructor] ].
               list_simpl in Hoclm1.
               apply Forall_app_inv in Hoclm1.
               apply Hoclm1.
            ** list_simpl ; rewrite Hperm ; simpl.
               perm_solve.
         ++ rewrite map_map in HP3.
            symmetry in HP3 ; apply Permutation_map_inv in HP3.
            destruct HP3 as (l3''' & Heq' & HP3).
            decomp_map Heq' ; subst.
            rewrite <- map_map in HP1.
            rewrite <- map_map in HP2.
            rewrite app_assoc in HP4 ; apply Permutation_cons_app_inv in HP4.
            list_simpl in HP4 ; apply Permutation_app_app_inv in HP4.
            destruct HP4 as (l3a & l3b & l3c & l3d & HP4' & HP4'' & HP4''' & HP4'''').
            apply Permutation_app_app_inv in HP4''''.
            destruct HP4'''' as (l3e & l3f & l3g & l3h & HP4a & HP4b & HP4c & HP4d).
            symmetry in HP4' ; apply Permutation_map_inv in HP4'.
            destruct HP4' as (l3' & Heq' & HP4').
            decomp_map Heq' ; subst.
            rewrite HP4d in HP4''.
            rewrite map_map in HP4''.
            symmetry in HP4'' ; apply Permutation_map_inv in HP4''.
            destruct HP4'' as (l4'' & Heq' & HP4'').
            decomp_map Heq' ; subst.
            rewrite HP4a in HP2.
            rewrite <- (map_map _ _ l13) in HP2. 
            symmetry in HP4c ; apply Permutation_map_inv in HP4c.
            destruct HP4c as (l4'' & Heq' & HP4c).
            decomp_map Heq' ; subst.
            rewrite <- (map_map _ _ l14) in HP4b.
            rewrite HP4b in HP2.
            specialize IHHll1 with (rev (l13 ++ l6 ++ l14)) (x0_1 :: l15 ++ l16) C.
            assert (x0_1 :: l15 ++ l16 <> nil) as Hnil
              by (intros Hnil ; inversion Hnil).
            inversion Hoclm ; subst.
            apply Forall_app_inv in H3 ; destruct H3 as [Hoclm1 Hoclm2].
            inversion Hoclm2 ; subst.
            inversion H3 ; subst.
            rewrite HP4' in Hocl.
            rewrite HP4c in Hocl.
            apply Forall_app_inv in Hocl ; destruct Hocl as [_ Hocl].
            assert (Hocl' := Forall_cons _ H5 Hocl).
            apply IHHll1 in Hocl' ; [ split | | ].
            ** apply (proj2 Hocl') with (ilpam x0_1 x0_2 :: rev l4 ++ rev l11) in Hnil.
               destruct Hnil as [s' Hnil].
               eexists ; eapply ex_ir ; [ apply Hnil | ].
               simpl ; rewrite Hperm ; simpl.
               rewrite HP3 ; rewrite HP4'' ; list_simpl.
               perm_solve.
            ** intros Hnil' lw.
               apply (proj2 Hocl') with (ilpam x0_1 x0_2 :: rev l4 ++ rev l11 ++ lw) in Hnil.
               destruct Hnil as [s' Hnil].
               eexists ; eapply ex_ir ; [ apply Hnil | ].
               simpl ; rewrite Hperm ; simpl.
               rewrite HP3 ; rewrite HP4'' ; list_simpl.
               perm_solve.
            ** constructor...
               rewrite HP4'' in H4.
               list_simpl in H4 ; list_simpl.
               rewrite app_assoc in H4.
               apply Forall_app_inv in H4 ; destruct H4 as [H4 _].
               apply Forall_app_inv in H4 ; destruct H4 as [H4l H4r].
               rewrite HP3 in Hoclm1.
               list_simpl in Hoclm1 ; apply Forall_app_inv in Hoclm1 ;
                 destruct Hoclm1 as [Hoclm1 _].
               apply Forall_app...
               apply Forall_app...
            ** list_simpl ; rewrite Hperm ; simpl.
               rewrite bidual ; perm_solve.
      -- assert (HP4' := HP4).
         symmetry in HP4' ; apply Permutation_vs_cons_inv in HP4'.
         destruct HP4' as (l4a & l4b & Heq').
         dichot_elt_app_exec Heq' ; subst.
         ++ rewrite map_map in HP3.
            symmetry in HP3 ; apply Permutation_map_inv in HP3.
            destruct HP3 as (l3''' & Heq' & HP3).
            decomp_map Heq' ; subst.
            rewrite <- map_map in HP1.
            list_simpl in HP4 ; apply Permutation_cons_app_inv in HP4.
            apply Permutation_app_app_inv in HP4.
            destruct HP4 as (l3a & l3b & l3c & l3d & HP4' & HP4'' & HP4''' & HP4'''').
            apply Permutation_app_app_inv in HP4''''.
            destruct HP4'''' as (l3e & l3f & l3g & l3h & HP4a & HP4b & HP4c & HP4d).
            rewrite HP4''' in HP1.
            rewrite HP4a in HP1.
            symmetry in HP4' ; apply Permutation_map_inv in HP4'.
            destruct HP4' as (l3' & Heq' & HP4').
            decomp_map Heq' ; subst.
            rewrite HP4d in HP4''.
            rewrite map_map in HP4''.
            symmetry in HP4'' ; apply Permutation_map_inv in HP4''.
            destruct HP4'' as (l4' & Heq' & HP4'').
            decomp_map Heq' ; subst.
            rewrite <- (map_map _ _ l11) in HP1.
            rewrite <- (map_map _ _ l13) in HP1. 
            symmetry in HP4c ; apply Permutation_map_inv in HP4c.
            destruct HP4c as (l4' & Heq' & HP4c).
            decomp_map Heq' ; subst.
            specialize IHHll2 with (rev (l4 ++ l11 ++ l13)) (x0_1 :: l9 ++ l15) C.
            rewrite HP4' in Hocl.
            apply Forall_app_inv in Hocl ; destruct Hocl as [Hocl1 Hocl2].
            rewrite HP4c in Hocl2.
            apply Forall_app_inv in Hocl2 ; destruct Hocl2 as [Hocl2 _].
            assert (Hocl3 := Forall_app _ _ _ Hocl1 Hocl2).
            inversion Hoclm ; subst.
            apply Forall_app_inv in H3 ; destruct H3 as [_ H3].
            inversion H3 ; inversion H4 ; subst.
            assert (Hocl4 := Forall_cons _ H8 Hocl3).
            apply IHHll2 in Hocl4.
            ** assert (x0_1 :: l9 ++ l15 <> nil) as Hnil
                 by (intros Hnil ; inversion Hnil).
               split.
               --- apply (proj2 Hocl4) with (ilmap x0_1 x0_2 :: rev l6 ++ rev l14) in Hnil.
                   destruct Hnil as [s2' Hnil].
                   eexists.
                   eapply ex_ir ; [ apply Hnil | ].
                   rewrite Hperm ; simpl.
                   apply Permutation_elt.
                   rewrite HP3 ; rewrite HP4'' ; perm_solve.
               --- intros Hnil' lw.
                   apply (proj2 Hocl4) with (ilmap x0_1 x0_2 :: lw ++ rev l6 ++ rev l14) in Hnil.
                   destruct Hnil as [s2' Hnil].
                   eexists.
                   eapply ex_ir ; [ apply Hnil | ].
                   rewrite Hperm ; simpl.
                   rewrite <- app_assoc ; rewrite <- app_comm_cons ; apply Permutation_elt.
                   rewrite HP3 ; rewrite HP4'' ; perm_solve.
            ** constructor...
               rewrite HP4'' in H5.
               list_simpl in H5.
               apply Forall_app_inv in H5 ; destruct H5 as [_ Hoclm1].
               inversion Hoclm ; subst.
               apply Forall_app_inv in H6 ; destruct H6 as [Hoclm2 _].
               rewrite HP3 in Hoclm2.
               list_simpl in Hoclm2.
               apply Forall_app_inv in Hoclm2 ; destruct Hoclm2 as [_ Hoclm2].
               rewrite rev_app_distr.
               apply Forall_app...
               list_simpl...
            ** simpl ; rewrite Hperm ; list_simpl.
               rewrite bidual ; rewrite HP1.
               perm_solve.
         ++ rewrite map_map in HP3.
            symmetry in HP3 ; apply Permutation_map_inv in HP3.
            destruct HP3 as (l3''' & Heq' & HP3).
            decomp_map Heq' ; subst.
            rewrite <- map_map in HP1.
            rewrite <- map_map in HP2.
            rewrite app_assoc in HP4 ; apply Permutation_cons_app_inv in HP4.
            apply Permutation_app_app_inv in HP4.
            destruct HP4 as (l3a & l3b & l3c & l3d & HP4' & HP4'' & HP4''' & HP4'''').
            apply Permutation_app_app_inv in HP4'''.
            destruct HP4''' as (l3e & l3f & l3g & l3h & HP4a & HP4b & HP4c & HP4d).
            rewrite HP4a in HP1.
            symmetry in HP4' ; apply Permutation_map_inv in HP4'.
            destruct HP4' as (l3' & Heq' & HP4').
            decomp_map Heq' ; subst.
            rewrite HP4d in HP4''.
            rewrite map_map in HP4''.
            symmetry in HP4'' ; apply Permutation_map_inv in HP4''.
            destruct HP4'' as (l4'' & Heq' & HP4'').
            decomp_map Heq' ; subst.
            rewrite <- (map_map _ _ l13) in HP1. 
            symmetry in HP4c ; apply Permutation_map_inv in HP4c.
            destruct HP4c as (l4'' & Heq' & HP4c).
            decomp_map Heq' ; subst.
            rewrite <- (map_map _ _ l14) in HP4b.
            rewrite HP4b in HP2.
            specialize IHHll2 with (rev (l4 ++ l13)) l15 x0_1.
            rewrite HP4' in Hocl.
            apply Forall_app_inv in Hocl ; destruct Hocl as [Hocl1 Hocl2].
            rewrite HP4'''' in HP2.
            rewrite <- (map_map _ _ l12) in HP2. 
            specialize IHHll1 with (rev (x0_2 :: l6 ++ l14 ++ l12)) (l10 ++ l16) C.
            rewrite HP4c in Hocl1.
            apply Forall_app_inv in Hocl1 ; destruct Hocl1 as [Hocl3 Hocl4].
            assert (Hocl5 := Forall_app _ _ _ Hocl2 Hocl4).
            apply IHHll2 in Hocl3 ; [ apply IHHll1 in Hocl5 | | ].
            ** split.
               --- destruct Hocl5 as [[s2' Hocl5] _].
                   destruct Hocl3 as [[s1' Hocl3] _].
                   eexists.
                   apply (ex_ir _ (nil ++ rev (l4 ++ l13) ++
                                     ilmap x0_1 x0_2 :: rev (l6 ++ l14 ++ l12))).
                   +++ apply lmap_ilr...
                       eapply ex_ir ; [ apply Hocl5 | ].
                       rewrite Hperm ; simpl ; perm_solve.
                   +++ rewrite Hperm ; simpl ; rewrite HP3 ; rewrite HP4'' ; perm_solve.
               --- intros Hnil lw ; destruct lo ; [ contradiction Hnil ; reflexivity | ].
                   rewrite HP4c in HP4'.
                   symmetry in HP4' ; apply Permutation_vs_cons_inv in HP4'.
                   destruct HP4' as (l4l & l4r & Heq').
                   rewrite <- app_assoc in Heq'.
                   dichot_elt_app_exec Heq' ; subst.
                   +++ assert (l4l ++ i :: l <> nil) as Hnil'
                         by (intros Hnil' ; destruct l4l ; inversion Hnil').
                       apply (proj2 Hocl3) with lw in Hnil'.
                       destruct Hnil' as [s2' Hnil'].
                       destruct Hocl5 as [[s1' Hocl5] _].
                       eexists.
                       apply (ex_ir _ (nil ++ (rev (l4 ++ l13) ++ lw) ++
                                     ilmap x0_1 x0_2 :: rev (l6 ++ l14 ++ l12))).
                       *** apply lmap_ilr...
                           eapply ex_ir ; [ apply Hocl5 | ].
                           rewrite Hperm ; simpl ; perm_solve.
                       *** rewrite Hperm ; simpl ; rewrite HP3 ; rewrite HP4'' ; perm_solve.
                   +++ assert (l17 ++ i :: l4r <> nil) as Hnil'
                         by (intros Hnil' ; destruct l17 ; inversion Hnil').
                       rewrite Heq'1 in Hnil'.
                       assert (l10 ++ l16 <> nil) as Hnil''.
                       { intros Hnil''.
                         apply Hnil'.
                         clear - Hnil''.
                         apply app_eq_nil in Hnil''.
                         destruct Hnil'' ; subst... }
                       apply (proj2 Hocl5) with lw in Hnil''.
                       destruct Hnil'' as [s1' Hnil''].
                       destruct Hocl3 as [[s2' Hocl3] _].
                       eexists.
                       apply (ex_ir _ (lw ++ rev (l4 ++ l13) ++
                                     ilmap x0_1 x0_2 :: rev (l6 ++ l14 ++ l12))).
                       *** apply lmap_ilr...
                           eapply ex_ir ; [ apply Hnil'' | ].
                           rewrite Hperm ; simpl ; perm_solve.
                       *** rewrite Hperm ; simpl ; rewrite HP3 ; rewrite HP4'' ; perm_solve.
            ** inversion Hoclm ; subst.
               apply Forall_app_inv in H3 ; destruct H3 as [Hoclm1 Hoclm2].
               inversion Hoclm2 ; subst.
               inversion H3 ; constructor...
               rewrite HP3 in Hoclm1.
               apply Forall_rev.
               constructor...
               apply Forall_app.
               --- list_simpl in Hoclm1 ; apply Forall_app_inv in Hoclm1.
                   rewrite <- Permutation_rev in Hoclm1.
                   apply Hoclm1.
               --- rewrite HP4'' in H4.
                   list_simpl in H4 ; apply Forall_app_inv in H4 ; destruct H4 as [H4l H4r].
                   apply Forall_rev in H4l.
                   rewrite rev_involutive in H4l.
                   apply Forall_app...
                   apply Forall_app_inv in H4r ; destruct H4r as [H4r _].
                   apply Forall_rev in H4r.
                   rewrite rev_involutive in H4r...
            ** simpl ; rewrite Hperm ; simpl.
               list_simpl ; rewrite HP2.
               perm_solve.
            ** inversion Hoclm ; subst...
               apply Forall_app_inv in H3 ; destruct H3 as [Hoclm1 Hoclm2].
               inversion Hoclm2 ; subst.
               rewrite HP4'' in H4.
               list_simpl in H4.
               apply Forall_app_inv in H4.
               destruct H4 as [H4l H4r] ; apply Forall_app_inv in H4r.
               destruct H4r as [_ H4r].
               inversion H3 ; subst ; constructor...
               list_simpl ; apply Forall_app...
               rewrite HP3 in Hoclm1.
               list_simpl in Hoclm1 ; apply Forall_app_inv in Hoclm1.
               apply Hoclm1.
            ** list_simpl ; rewrite Hperm ; simpl.
               rewrite bidual ; perm_solve.
      -- assert (HP4' := HP4).
         symmetry in HP4' ; apply Permutation_vs_cons_inv in HP4'.
         destruct HP4' as (l4a & l4b & Heq').
         dichot_elt_app_exec Heq' ; subst.
         ++ rewrite map_map in HP3.
            symmetry in HP3 ; apply Permutation_map_inv in HP3.
            destruct HP3 as (l3''' & Heq' & HP3).
            decomp_map Heq' ; subst.
            rewrite <- map_map in HP1.
            list_simpl in HP4 ; apply Permutation_cons_app_inv in HP4.
            apply Permutation_app_app_inv in HP4.
            destruct HP4 as (l3a & l3b & l3c & l3d & HP4' & HP4'' & HP4''' & HP4'''').
            apply Permutation_app_app_inv in HP4''''.
            destruct HP4'''' as (l3e & l3f & l3g & l3h & HP4a & HP4b & HP4c & HP4d).
            rewrite HP4''' in HP1.
            rewrite HP4a in HP1.
            symmetry in HP4' ; apply Permutation_map_inv in HP4'.
            destruct HP4' as (l3' & Heq' & HP4').
            decomp_map Heq' ; subst.
            rewrite HP4d in HP4''.
            rewrite map_map in HP4''.
            symmetry in HP4'' ; apply Permutation_map_inv in HP4''.
            destruct HP4'' as (l4' & Heq' & HP4'').
            decomp_map Heq' ; subst.
            rewrite <- (map_map _ _ l11) in HP1.
            rewrite <- (map_map _ _ l13) in HP1. 
            symmetry in HP4c ; apply Permutation_map_inv in HP4c.
            destruct HP4c as (l4' & Heq' & HP4c).
            decomp_map Heq' ; subst.
            specialize IHHll2 with (rev (l4 ++ l11 ++ l13)) (x0 :: l9 ++ l15) C.
            rewrite HP4' in Hocl.
            apply Forall_app_inv in Hocl ; destruct Hocl as [Hocl1 Hocl2].
            rewrite HP4c in Hocl2.
            apply Forall_app_inv in Hocl2 ; destruct Hocl2 as [Hocl2 _].
            assert (Hocl3 := Forall_app _ _ _ Hocl1 Hocl2).
            inversion Hoclm ; subst.
            apply Forall_app_inv in H3 ; destruct H3 as [_ H3].
            inversion H3 ; inversion H4 ; subst.
            assert (Hocl4 := Forall_cons _ H7 Hocl3).
            apply IHHll2 in Hocl4.
            ** assert (x0 :: l9 ++ l15 <> nil) as Hnil
                 by (intros Hnil ; inversion Hnil).
               split.
               --- apply (proj2 Hocl4) with (ineg x0 :: rev l6 ++ rev l14) in Hnil.
                   destruct Hnil as [s2' Hnil].
                   eexists.
                   eapply ex_ir ; [ apply Hnil | ].
                   rewrite Hperm ; simpl.
                   apply Permutation_elt.
                   rewrite HP3 ; rewrite HP4'' ; perm_solve.
               --- intros Hnil' lw.
                   apply (proj2 Hocl4) with (ineg x0 :: lw ++ rev l6 ++ rev l14) in Hnil.
                   destruct Hnil as [s2' Hnil].
                   eexists.
                   eapply ex_ir ; [ apply Hnil | ].
                   rewrite Hperm ; simpl.
                   rewrite <- app_assoc ; rewrite <- app_comm_cons ; apply Permutation_elt.
                   rewrite HP3 ; rewrite HP4'' ; perm_solve.
            ** constructor...
               rewrite HP4'' in H5.
               list_simpl in H5.
               apply Forall_app_inv in H5 ; destruct H5 as [_ Hoclm1].
               inversion Hoclm ; subst.
               apply Forall_app_inv in H6 ; destruct H6 as [Hoclm2 _].
               rewrite HP3 in Hoclm2.
               list_simpl in Hoclm2.
               apply Forall_app_inv in Hoclm2 ; destruct Hoclm2 as [_ Hoclm2].
               rewrite rev_app_distr.
               apply Forall_app...
               list_simpl...
            ** simpl ; rewrite Hperm ; list_simpl.
               rewrite bidual ; rewrite HP1.
               perm_solve.
         ++ rewrite map_map in HP3.
            symmetry in HP3 ; apply Permutation_map_inv in HP3.
            destruct HP3 as (l3''' & Heq' & HP3).
            decomp_map Heq' ; subst.
            rewrite <- map_map in HP1.
            rewrite <- map_map in HP2.
            rewrite app_assoc in HP4 ; apply Permutation_cons_app_inv in HP4.
            apply Permutation_app_app_inv in HP4.
            destruct HP4 as (l3a & l3b & l3c & l3d & HP4' & HP4'' & HP4''' & HP4'''').
            apply Permutation_app_app_inv in HP4'''.
            destruct HP4''' as (l3e & l3f & l3g & l3h & HP4a & HP4b & HP4c & HP4d).
            rewrite HP4a in HP1.
            symmetry in HP4' ; apply Permutation_map_inv in HP4'.
            destruct HP4' as (l3' & Heq' & HP4').
            decomp_map Heq' ; subst.
            rewrite HP4d in HP4''.
            rewrite map_map in HP4''.
            symmetry in HP4'' ; apply Permutation_map_inv in HP4''.
            destruct HP4'' as (l4'' & Heq' & HP4'').
            decomp_map Heq' ; subst.
            rewrite <- (map_map _ _ l13) in HP1. 
            symmetry in HP4c ; apply Permutation_map_inv in HP4c.
            destruct HP4c as (l4'' & Heq' & HP4c).
            decomp_map Heq' ; subst.
            rewrite <- (map_map _ _ l14) in HP4b.
            rewrite HP4b in HP2.
            specialize IHHll2 with (rev (l4 ++ l13)) l15 x0.
            rewrite HP4' in Hocl.
            apply Forall_app_inv in Hocl ; destruct Hocl as [Hocl1 Hocl2].
            rewrite HP4'''' in HP2.
            rewrite <- (map_map _ _ l12) in HP2. 
            specialize IHHll1 with (rev (ivar atN :: l6 ++ l14 ++ l12)) (l10 ++ l16) C.
            rewrite HP4c in Hocl1.
            apply Forall_app_inv in Hocl1 ; destruct Hocl1 as [Hocl3 Hocl4].
            assert (Hocl5 := Forall_app _ _ _ Hocl2 Hocl4).
            apply IHHll2 in Hocl3 ; [ apply IHHll1 in Hocl5 | | ].
            ** split.
               --- destruct Hocl5 as [[s2' Hocl5] _].
                   destruct Hocl3 as [[s1' Hocl3] _].
                   apply neg_pam_rule with _ (rev l6 ++ rev l14) (rev l12) _ C _ (S s2') in Hocl3.
                   +++ destruct Hocl3 as [s2'' [Hocl3 _]].
                       eexists.
                       eapply ex_ir ; [ apply Hocl3 | ].
                       rewrite Hperm ; simpl.
                       rewrite app_assoc.
                       apply Permutation_elt.
                       rewrite HP3 ; rewrite HP4'' ; perm_solve.
                   +++ clear - Hgax.
                       intros l C Hax.
                       exfalso.
                       apply Hgax in Hax...
                   +++ eapply ex_ir ; [ apply Hocl5 | ].
                       rewrite Hperm ; simpl ; perm_solve.
               --- intros Hnil lw ; destruct lo ; [ contradiction Hnil ; reflexivity | ].
                   rewrite HP4c in HP4'.
                   symmetry in HP4' ; apply Permutation_vs_cons_inv in HP4'.
                   destruct HP4' as (l4l & l4r & Heq').
                   rewrite <- app_assoc in Heq'.
                   dichot_elt_app_exec Heq' ; subst.
                   +++ assert (l4l ++ i :: l <> nil) as Hnil'
                         by (intros Hnil' ; destruct l4l ; inversion Hnil').
                       apply (proj2 Hocl3) with lw in Hnil'.
                       destruct Hnil' as [s2' Hnil'].
                       destruct Hocl5 as [[s1' Hocl5] _].
                       apply neg_pam_rule with _ (rev l6 ++ rev l14) (rev l12) _ C _ (S s1') in Hnil'.
                       *** destruct Hnil' as [s2'' [Hnil' _]]...
                           eexists.
                           eapply ex_ir ; [ apply Hnil' | ].
                           rewrite Hperm ; simpl ; list_simpl.
                           rewrite 4 app_assoc.
                           apply Permutation_elt.
                           rewrite HP3 ; rewrite HP4'' ; perm_solve.
                       *** clear - Hgax.
                           intros l C Hax.
                           exfalso.
                           apply Hgax in Hax...
                       *** eapply ex_ir ; [ apply Hocl5 | ].
                           rewrite Hperm ; simpl ; perm_solve.
                   +++ assert (l17 ++ i :: l4r <> nil) as Hnil'
                         by (intros Hnil' ; destruct l17 ; inversion Hnil').
                       rewrite Heq'1 in Hnil'.
                       assert (l10 ++ l16 <> nil) as Hnil''.
                       { intros Hnil''.
                         apply Hnil'.
                         clear - Hnil''.
                         apply app_eq_nil in Hnil''.
                         destruct Hnil'' ; subst... }
                       apply (proj2 Hocl5) with lw in Hnil''.
                       destruct Hnil'' as [s1' Hnil''].
                       destruct Hocl3 as [[s2' Hocl3] _].
                       apply neg_pam_rule with _ (rev l6 ++ rev l14) (rev l12 ++ lw) _ C _ (S s1') in Hocl3.
                       *** destruct Hocl3 as [s2'' [Hocl3 _]]...
                           eexists.
                           eapply ex_ir ; [ apply Hocl3 | ].
                           rewrite Hperm ; simpl ; list_simpl.
                           rewrite 3 app_assoc.
                           apply Permutation_elt.
                           rewrite HP3 ; rewrite HP4'' ; perm_solve.
                       *** clear - Hgax.
                           intros l C Hax.
                           exfalso.
                           apply Hgax in Hax...
                       *** eapply ex_ir ; [ apply Hnil'' | ].
                           rewrite Hperm ; simpl ; perm_solve.
            ** inversion Hoclm ; subst.
               apply Forall_app_inv in H3 ; destruct H3 as [Hoclm1 Hoclm2].
               inversion Hoclm2 ; subst.
               inversion H3 ; constructor...
               rewrite HP3 in Hoclm1.
               apply Forall_rev.
               constructor ; [ | apply Forall_app ].
               --- constructor.
               --- list_simpl in Hoclm1 ; apply Forall_app_inv in Hoclm1.
                   rewrite <- Permutation_rev in Hoclm1.
                   apply Hoclm1.
               --- rewrite HP4'' in H4.
                   list_simpl in H4 ; apply Forall_app_inv in H4 ; destruct H4 as [H4l H4r].
                   apply Forall_rev in H4l.
                   rewrite rev_involutive in H4l.
                   apply Forall_app...
                   apply Forall_app_inv in H4r ; destruct H4r as [H4r _].
                   apply Forall_rev in H4r.
                   rewrite rev_involutive in H4r...
            ** simpl ; rewrite Hperm ; simpl.
               list_simpl ; rewrite HP2.
               perm_solve.
            ** inversion Hoclm ; subst...
               apply Forall_app_inv in H3 ; destruct H3 as [Hoclm1 Hoclm2].
               inversion Hoclm2 ; subst.
               rewrite HP4'' in H4.
               list_simpl in H4.
               apply Forall_app_inv in H4.
               destruct H4 as [H4l H4r] ; apply Forall_app_inv in H4r.
               destruct H4r as [_ H4r].
               inversion H3 ; subst ; constructor...
               list_simpl ; apply Forall_app...
               rewrite HP3 in Hoclm1.
               list_simpl in Hoclm1 ; apply Forall_app_inv in Hoclm1.
               apply Hoclm1.
            ** list_simpl ; rewrite Hperm ; simpl.
               rewrite bidual ; perm_solve.
- symmetry in HP ; apply PCperm_vs_cons_inv in HP.
  destruct HP as (l' & l'' & HP & Heq).
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  + specialize IHHll with (l0 ++ C1 :: nil) lo C2.
    apply IHHll in Hocl.
    * destruct Hocl as [[s' IH1] IH2].
      split.
      -- eexists ; apply lpam_irr...
      -- intros Hnil l2.
         destruct (IH2 Hnil l2) as [s'' IH].
         list_simpl in IH.
         eexists ; list_simpl ; apply lpam_irr.
         eapply ex_ir...
         rewrite Hperm ; simpl ; perm_solve.
    * inversion Hoclm ; subst.
      inversion H2 ; subst.
      constructor...
      apply Forall_app...
      constructor...
      constructor.
    * simpl in HP ; rewrite Hperm in HP ; simpl in HP.
      simpl ; rewrite Hperm ; simpl.
      perm_solve.
  + specialize IHHll with (C1 :: l0) lo C2.
    apply IHHll in Hocl.
    * destruct Hocl as [[s' IH1] IH2].
      split.
      -- eexists ; apply lmap_irr...
      -- intros Hnil l2.
         destruct (IH2 Hnil l2) as [s'' IH].
         list_simpl in IH.
         eexists ; list_simpl ; apply lmap_irr.
         eapply ex_ir...
    * inversion Hoclm ; subst.
      inversion H2 ; subst.
      constructor...
      constructor...
    * simpl in HP ; rewrite Hperm in HP ; simpl in HP.
      simpl ; rewrite Hperm ; simpl.
      perm_solve.
  + specialize IHHll with (C :: l0) lo N.
    apply IHHll in Hocl.
    * destruct Hocl as [[s' IH1] IH2].
      split.
      -- eexists ; apply neg_irr...
      -- intros Hnil l2.
         destruct (IH2 Hnil l2) as [s'' IH].
         list_simpl in IH.
         eexists ; list_simpl ; apply neg_irr.
         eapply ex_ir...
    * inversion Hoclm ; subst.
      inversion H2 ; subst.
      constructor...
      -- constructor.
      -- constructor...
    * simpl in HP ; rewrite Hperm in HP ; simpl in HP.
      simpl ; rewrite Hperm ; simpl.
      perm_solve.
  + symmetry in H1 ; dichot_elt_app_exec H1 ; subst ;
    [ decomp_map H0 ; destruct x ; inversion H0
    | list_simpl in H2 ; decomp_map H2 ; decomp_map H3 ; destruct x ; inversion H2 ;
                                                         destruct x0 ; inversion H3 ] ; subst.
    * exfalso.
      apply Forall_app_inv in Hocl.
      destruct Hocl as [_ Hocl].
      inversion Hocl.
      inversion H2.
    * exfalso.
      apply Forall_app_inv in Hocl.
      destruct Hocl as [_ Hocl].
      inversion Hocl.
      inversion H2.
    * exfalso.
      apply Forall_app_inv in Hocl.
      destruct Hocl as [_ Hocl].
      inversion Hocl.
      inversion H2.
    * apply (f_equal (@rev _)) in H6 ; list_simpl in H6 ; subst.
      apply (@PEperm_cons _ _ _ (dual (ill2ll x0_1)) eq_refl) in HP.
      apply (@PEperm_cons _ _ _ (dual (ill2ll x0_2)) eq_refl) in HP.
      apply PEperm_PCperm in HP ; unfold id in HP.
      rewrite 2 app_comm_cons in HP.
      assert (HP' := PCperm_trans _ _ _ _ HP (PCperm_app_comm _ _ _)).
      specialize IHHll with (rev (x0_2 :: x0_1 :: l8) ++ rev l6) lo C.
      list_simpl in IHHll ; list_simpl in HP' ; apply IHHll in HP'...
      -- destruct HP' as [[s' IH1] IH2].
         split.
         ++ eexists ; apply tens_ilr...
         ++ intros Hnil l2.
            destruct (IH2 Hnil l2) as [s'' IH].
            list_simpl in IH.
            eexists ; list_simpl ; apply tens_ilr...
      -- inversion Hoclm ; constructor...
         apply Forall_app_inv in H4 ; destruct H4 as [Hl Hr] ; apply Forall_app...
         inversion Hr.
         inversion H6.
         constructor...
         constructor...
- symmetry in HP ; apply PCperm_vs_cons_inv in HP.
  destruct HP as (l' & l'' & HP & Heq).
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  + split ; intros ; eexists ; apply top_irr.
  + symmetry in H1 ; dichot_elt_app_exec H1 ; subst ;
      [ decomp_map H0 ; destruct x ; inversion H0
      | list_simpl in H2 ; decomp_map H2 ; decomp_map H3 ; destruct x ; inversion H2 ;
                                                           destruct x0 ; inversion H3 ] ; subst.
    * exfalso.
      apply Forall_app_inv in Hocl ; destruct Hocl as [_ Hocl] ; inversion Hocl.
      inversion H2.
    * apply (f_equal (@rev _)) in H6 ; list_simpl in H6 ; subst.
      split ; intros ; eexists ; list_simpl ; apply zero_ilr.
- symmetry in HP ; apply PCperm_vs_cons_inv in HP.
  destruct HP as (l' & l'' & HP & Heq).
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  + apply (@PEperm_cons _ _ _ (ill2ll C1) eq_refl) in HP.
    apply PEperm_PCperm in HP ; unfold id in HP.
    rewrite app_comm_cons in HP.
    assert (HP' := PCperm_trans _ _ _ _ HP (PCperm_app_comm _ _ _)).
    specialize IHHll with l0 lo C1.
    list_simpl in IHHll ; list_simpl in HP' ; apply IHHll in HP'...
    * destruct HP' as [[s' IH1] IH2].
      split.
      -- eexists ; apply plus_irr1...
      -- intros Hnil l2.
         destruct (IH2 Hnil l2) as [s'' IH].
         list_simpl in IH.
         eexists ; list_simpl ; apply plus_irr1...
    * inversion Hoclm ; subst.
      inversion H2 ; subst.
      constructor...
  + symmetry in H1 ; dichot_elt_app_exec H1 ; subst ;
    [ decomp_map H0 ; destruct x ; inversion H0
    | list_simpl in H2 ; decomp_map H2 ; decomp_map H3 ; destruct x ; inversion H2 ;
                                                         destruct x0 ; inversion H3 ] ; subst.
    * apply (@PEperm_cons _ _ _ (ill2ll x1) eq_refl) in HP.
      apply PEperm_PCperm in HP ; unfold id in HP.
      rewrite app_comm_cons in HP.
      assert (HP' := PCperm_trans _ _ _ _ HP (PCperm_app_comm _ _ _)).
      specialize IHHll with l0 (l3 ++ x1 :: l5) C.
      list_simpl in IHHll ; list_simpl in HP' ; apply IHHll in HP'...
      -- destruct HP' as [[s' IH1] IH2].
         split.
         ++ eexists...
         ++ intros _ l2.
            apply IH2.
            intros Hnil ; destruct l3 ; inversion Hnil.
      -- apply Forall_app_inv in Hocl ; destruct Hocl as [Hocll Hoclr] ; apply Forall_app...
         inversion Hoclr.
         inversion H2.
         constructor...
    * apply (f_equal (@rev _)) in H6 ; list_simpl in H6 ; subst.
      apply (@PEperm_cons _ _ _ (dual (ill2ll x0_1)) eq_refl) in HP.
      apply PEperm_PCperm in HP ; unfold id in HP.
      rewrite app_comm_cons in HP.
      assert (HP' := PCperm_trans _ _ _ _ HP (PCperm_app_comm _ _ _)).
      specialize IHHll with (rev (x0_1 :: l8) ++ rev l6) lo C.
      list_simpl in IHHll ; list_simpl in HP' ; apply IHHll in HP'...
      -- destruct HP' as [[s' IH1] IH2].
         split.
         ++ eexists ; apply with_ilr1...
         ++ intros Hnil l2.
            destruct (IH2 Hnil l2) as [s'' IH].
            list_simpl in IH.
            eexists ; list_simpl ; apply with_ilr1...
      -- inversion Hoclm ; constructor...
         apply Forall_app_inv in H4 ; destruct H4 as [Hl Hr] ; apply Forall_app...
         inversion Hr.
         inversion H6.
         constructor...
- symmetry in HP ; apply PCperm_vs_cons_inv in HP.
  destruct HP as (l' & l'' & HP & Heq).
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  + apply (@PEperm_cons _ _ _ (ill2ll C2) eq_refl) in HP.
    apply PEperm_PCperm in HP ; unfold id in HP.
    rewrite app_comm_cons in HP.
    assert (HP' := PCperm_trans _ _ _ _ HP (PCperm_app_comm _ _ _)).
    specialize IHHll with l0 lo C2.
    list_simpl in IHHll ; list_simpl in HP' ; apply IHHll in HP'...
    * destruct HP' as [[s' IH1] IH2].
      split.
      -- eexists ; apply plus_irr2...
      -- intros Hnil l2.
         destruct (IH2 Hnil l2) as [s'' IH].
         list_simpl in IH.
         eexists ; list_simpl ; apply plus_irr2...
    * inversion Hoclm ; subst.
      inversion H2 ; subst.
      constructor...
  + symmetry in H1 ; dichot_elt_app_exec H1 ; subst ;
    [ decomp_map H0 ; destruct x ; inversion H0
    | list_simpl in H2 ; decomp_map H2 ; decomp_map H3 ; destruct x ; inversion H2 ;
                                                         destruct x0 ; inversion H3 ] ; subst.
    * apply (@PEperm_cons _ _ _ (ill2ll x2) eq_refl) in HP.
      apply PEperm_PCperm in HP ; unfold id in HP.
      rewrite app_comm_cons in HP.
      assert (HP' := PCperm_trans _ _ _ _ HP (PCperm_app_comm _ _ _)).
      specialize IHHll with l0 (l3 ++ x2 :: l5) C.
      list_simpl in IHHll ; list_simpl in HP' ; apply IHHll in HP'...
      -- destruct HP' as [[s' IH1] IH2].
         split.
         ++ eexists...
         ++ intros _ l2.
            apply IH2.
            intros Hnil ; destruct l3 ; inversion Hnil.
      -- apply Forall_app_inv in Hocl ; destruct Hocl as [Hocll Hoclr] ; apply Forall_app...
         inversion Hoclr.
         inversion H2.
         constructor...
    * apply (f_equal (@rev _)) in H6 ; list_simpl in H6 ; subst.
      apply (@PEperm_cons _ _ _ (dual (ill2ll x0_2)) eq_refl) in HP.
      apply PEperm_PCperm in HP ; unfold id in HP.
      rewrite app_comm_cons in HP.
      assert (HP' := PCperm_trans _ _ _ _ HP (PCperm_app_comm _ _ _)).
      specialize IHHll with (rev (x0_2 :: l8) ++ rev l6) lo C.
      list_simpl in IHHll ; list_simpl in HP' ; apply IHHll in HP'...
      -- destruct HP' as [[s' IH1] IH2].
         split.
         ++ eexists ; apply with_ilr2...
         ++ intros Hnil l2.
            destruct (IH2 Hnil l2) as [s'' IH].
            list_simpl in IH.
            eexists ; list_simpl ; apply with_ilr2...
      -- inversion Hoclm ; constructor...
         apply Forall_app_inv in H4 ; destruct H4 as [Hl Hr] ; apply Forall_app...
         inversion Hr.
         inversion H6.
         constructor...
- symmetry in HP ; apply PCperm_vs_cons_inv in HP.
  destruct HP as (l' & l'' & HP & Heq).
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  + assert (HP1 := HP).
    apply (@PEperm_cons _ _ _ (ill2ll C1) eq_refl) in HP1.
    apply PEperm_PCperm in HP1 ; unfold id in HP1.
    rewrite app_comm_cons in HP1.
    assert (HP1' := PCperm_trans _ _ _ _ HP1 (PCperm_app_comm _ _ _)).
    specialize IHHll1 with l0 lo C1.
    list_simpl in IHHll1 ; list_simpl in HP1' ; apply IHHll1 in HP1'...
    * destruct HP1' as [[s1' IH1] IH2].
      apply (@PEperm_cons _ _ _ (ill2ll C2) eq_refl) in HP.
      apply PEperm_PCperm in HP ; unfold id in HP.
      rewrite app_comm_cons in HP.
      assert (HP2' := PCperm_trans _ _ _ _ HP (PCperm_app_comm _ _ _)).
      specialize IHHll2 with l0 lo C2.
      list_simpl in IHHll2 ; list_simpl in HP2' ; apply IHHll2 in HP2'...
      -- destruct HP2' as [[s2' IH3] IH4].
         split.
         ++ eexists ; apply with_irr...
         ++ intros Hnil l2.
            destruct (IH2 Hnil l2) as [s'' IH].
            destruct (IH4 Hnil l2) as [s''' IH'].
            list_simpl in IH ; list_simpl in IH'.
            eexists ; list_simpl ; apply with_irr...
      -- inversion Hoclm ; subst.
         inversion H2 ; subst.
         constructor...
    * inversion Hoclm ; subst.
      inversion H2 ; subst.
      constructor...
  + symmetry in H1 ; dichot_elt_app_exec H1 ; subst ;
    [ decomp_map H0 ; destruct x ; inversion H0
    | list_simpl in H2 ; decomp_map H2 ; decomp_map H3 ; destruct x ; inversion H2 ;
                                                         destruct x0 ; inversion H3 ] ; subst.
    * apply Forall_app_inv in Hocl ; destruct Hocl as [Hocll Hoclr].
      inversion Hoclr.
      inversion H2.
      -- apply (@PEperm_cons _ _ _ (ill2ll x1) eq_refl) in HP.
         apply PEperm_PCperm in HP ; unfold id in HP.
         rewrite app_comm_cons in HP.
         assert (HP' := PCperm_trans _ _ _ _ HP (PCperm_app_comm _ _ _)).
         specialize IHHll1 with l0 (l3 ++ x1 :: l5) C.
         list_simpl in IHHll1 ; list_simpl in HP' ; apply IHHll1 in HP'...
         ++ destruct HP' as [[s' IH1] IH2].
            split.
            ** eexists...
            ** intros _ l2.
               apply IH2.
               intros Hnil ; destruct l3 ; inversion Hnil.
         ++ apply Forall_app...
            constructor...
      -- apply (@PEperm_cons _ _ _ (ill2ll x2) eq_refl) in HP.
         apply PEperm_PCperm in HP ; unfold id in HP.
         rewrite app_comm_cons in HP.
         assert (HP' := PCperm_trans _ _ _ _ HP (PCperm_app_comm _ _ _)).
         specialize IHHll2 with l0 (l3 ++ x2 :: l5) C.
         list_simpl in IHHll2 ; list_simpl in HP' ; apply IHHll2 in HP'...
         ++ destruct HP' as [[s' IH1] IH2].
            split.
            ** eexists...
            ** intros _ l2.
               apply IH2.
               intros Hnil ; destruct l3 ; inversion Hnil.
         ++ apply Forall_app...
            constructor...
    * apply (f_equal (@rev _)) in H6 ; list_simpl in H6 ; subst.
      assert (HP1 := HP).
      apply (@PEperm_cons _ _ _ (dual (ill2ll x0_1)) eq_refl) in HP1.
      apply PEperm_PCperm in HP1 ; unfold id in HP1.
      rewrite app_comm_cons in HP1.
      assert (HP1' := PCperm_trans _ _ _ _ HP1 (PCperm_app_comm _ _ _)).
      specialize IHHll1 with (rev (x0_1 :: l8) ++ rev l6) lo C.
      list_simpl in IHHll1 ; list_simpl in HP1' ; apply IHHll1 in HP1'...
      -- destruct HP1' as [[s' IH1] IH2].
         apply (@PEperm_cons _ _ _ (dual (ill2ll x0_2)) eq_refl) in HP.
         apply PEperm_PCperm in HP ; unfold id in HP.
         rewrite app_comm_cons in HP.
         assert (HP2' := PCperm_trans _ _ _ _ HP (PCperm_app_comm _ _ _)).
         specialize IHHll2 with (rev (x0_2 :: l8) ++ rev l6) lo C.
         list_simpl in IHHll2 ; list_simpl in HP2' ; apply IHHll2 in HP2'...
         ++ destruct HP2' as [[s'' IH3] IH4].
            split.
            ** eexists ; apply plus_ilr...
            ** intros Hnil l2.
               destruct (IH2 Hnil l2) as [s1'' IH5].
               list_simpl in IH5.
               destruct (IH4 Hnil l2) as [s2'' IH6].
               list_simpl in IH6.
               eexists ; list_simpl ; apply plus_ilr...
         ++ inversion Hoclm ; constructor...
            apply Forall_app_inv in H4 ; destruct H4 as [Hl Hr] ; apply Forall_app...
            inversion Hr.
            inversion H6.
            constructor...
      -- inversion Hoclm ; constructor...
         apply Forall_app_inv in H4 ; destruct H4 as [Hl Hr] ; apply Forall_app...
         inversion Hr.
         inversion H6.
         constructor...
- symmetry in HP ; apply PCperm_vs_cons_inv in HP.
  destruct HP as (l' & l'' & HP & Heq).
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  + symmetry in HP ; apply PEperm_map_inv in HP.
    destruct HP as (l'' & Heq' & HPE).
    decomp_map Heq'.
    destruct lo ; destruct l4 ; inversion Heq'3 ; subst.
    * split.
      -- list_simpl in Heq'4.
         symmetry in Heq'4.
         apply ill2ll_map_ioc_inv in Heq'4.
         destruct Heq'4 as (l2' & Heq' & Heq'') ; subst.
         apply (f_equal (@rev _)) in Heq' ; list_simpl in Heq' ; subst.
         specialize IHHll with ((rev (map ioc l2'))) nil C.
         destruct l3 ; inversion Heq'2.
         rewrite HPE in IHHll.
         list_simpl in IHHll.
         apply IHHll in Hocl...
         ++ destruct Hocl as [[s' Hocl] _].
            eexists ; apply oc_irr...
         ++ inversion Hoclm ; subst.
            inversion H2 ; subst.
            constructor...
         ++ rewrite ill2ll_map_ioc...
      -- intros Hnil ; contradiction Hnil...
    * exfalso ; destruct i ; inversion H1.
  + exfalso.
    symmetry in H1 ; dichot_elt_app_exec H1 ; subst ;
      [ decomp_map H0 ; destruct x ; inversion H0
      | list_simpl in H2 ; decomp_map H2 ; decomp_map H3 ; destruct x ; inversion H2 ;
                                                           destruct x0 ; inversion H3 ] ; subst.
    symmetry in HP ; apply PEperm_map_inv in HP.
    destruct HP as (l'' & Heq' & _).
    decomp_map Heq'.
    destruct C ; inversion Heq'1.
- symmetry in HP ; apply PCperm_vs_cons_inv in HP.
  destruct HP as (l' & l'' & HP & Heq).
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  symmetry in H1 ; dichot_elt_app_exec H1 ; subst ;
    [ decomp_map H0 ; destruct x ; inversion H0
    | list_simpl in H2 ; decomp_map H2 ; decomp_map H3 ; destruct x ; inversion H2 ;
                                                         destruct x0 ; inversion H3 ] ; subst.
  apply (f_equal (@rev _)) in H6 ; list_simpl in H6 ; subst.
  apply (@PEperm_cons _ _ _ (dual (ill2ll x0)) eq_refl) in HP.
  apply PEperm_PCperm in HP ; unfold id in HP.
  rewrite app_comm_cons in HP.
  assert (HP' := PCperm_trans _ _ _ _ HP (PCperm_app_comm _ _ _)).
  specialize IHHll with (rev (x0 :: l8) ++ rev l6) lo C.
  list_simpl in IHHll ; list_simpl in HP' ; apply IHHll in HP'...
  + destruct HP' as [[s' IH1] IH2].
    split.
    * eexists ; apply de_ilr...
    * intros Hnil l2.
      destruct (IH2 Hnil l2) as [s'' IH].
      list_simpl in IH.
      eexists ; list_simpl ; apply de_ilr...
  + inversion Hoclm ; constructor...
    apply Forall_app_inv in H4 ; destruct H4 as [Hl Hr] ; apply Forall_app...
    inversion Hr.
    inversion H6.
    constructor...
- symmetry in HP ; apply PCperm_vs_cons_inv in HP.
  destruct HP as (l' & l'' & HP & Heq).
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  symmetry in H1 ; dichot_elt_app_exec H1 ; subst ;
    [ decomp_map H0 ; destruct x ; inversion H0
    | list_simpl in H2 ; decomp_map H2 ; decomp_map H3 ; destruct x ; inversion H2 ;
                                                         destruct x0 ; inversion H3 ] ; subst.
  apply (f_equal (@rev _)) in H6 ; list_simpl in H6 ; subst.
  apply PEperm_PCperm in HP ; unfold id in HP.
  assert (HP' := PCperm_trans _ _ _ _ HP (PCperm_app_comm _ _ _)).
  specialize IHHll with (rev l8 ++ rev l6) lo C.
  list_simpl in IHHll ; list_simpl in HP' ; apply IHHll in HP'...
  + destruct HP' as [[s' IH1] IH2].
    split.
    * eexists ; apply wk_ilr...
    * intros Hnil l2.
      destruct (IH2 Hnil l2) as [s'' IH].
      list_simpl in IH.
      eexists ; list_simpl ; apply wk_ilr...
  + inversion Hoclm ; constructor...
    apply Forall_app_inv in H4 ; destruct H4 as [Hl Hr] ; apply Forall_app...
    inversion Hr...
- symmetry in HP ; apply PCperm_vs_cons_inv in HP.
  destruct HP as (l' & l'' & HP & Heq).
  destruct l' ; inversion Heq ; [ destruct C ; inversion H0 | ] ; subst.
  symmetry in H1 ; dichot_elt_app_exec H1 ; subst ;
    [ decomp_map H0 ; destruct x ; inversion H0
    | list_simpl in H2 ; decomp_map H2 ; decomp_map H3 ; destruct x ; inversion H2 ;
                                                         destruct x0 ; inversion H3 ] ; subst.
  apply (f_equal (@rev _)) in H6 ; list_simpl in H6 ; subst.
  assert (PCperm (ipperm P) (wn (dual (ill2ll x0)) :: map wn lw ++ wn (dual (ill2ll x0)) :: l)
         (ill2ll C :: map ill2ll lo ++ map dual (map ill2ll (l6 ++ ioc x0 :: ioc x0 :: l8)))) as HP'.
  { rewrite Hperm ; list_simpl.
    rewrite (app_comm_cons _ _ (ill2ll C)).
    rewrite app_assoc.
    apply Permutation_cons_app.
    etransitivity ; [ symmetry ; apply Permutation_middle | ].
    apply Permutation_cons_app.
    simpl in HP ; rewrite Hperm in HP ; simpl in HP ; rewrite HP.
    perm_solve. }
  specialize IHHll with (rev (ioc x0 :: ioc x0 :: l8) ++ rev l6) lo C.
  list_simpl in IHHll ; list_simpl in HP' ;  apply IHHll in HP'...
  + destruct HP' as [[s' IH1] IH2].
    split.
    * eexists.
      eapply ex_ir ; [ apply co_ilr | ].
      -- rewrite app_nil_l.
         eapply ex_ir ; [ apply IH1 | ].
         rewrite Hperm ; simpl.
         symmetry ; apply Permutation_cons_app.
         assert (map ioc nil = nil) as Hnil by reflexivity.
         rewrite Hnil.
         rewrite app_nil_l.
         apply Permutation_cons_app.
         reflexivity.
      -- rewrite Hperm ; simpl ; perm_solve.
    * intros Hnil l2.
      destruct (IH2 Hnil l2) as [s'' IH].
      list_simpl in IH.
      eexists.
      eapply ex_ir ; [ apply co_ilr | ].
      -- rewrite app_nil_l.
         eapply ex_ir ; [ apply IH | ].
         rewrite Hperm ; simpl.
         symmetry ; apply Permutation_cons_app.
         assert (map ioc nil = nil) as Hnil' by reflexivity.
         rewrite Hnil'.
         rewrite app_nil_l.
         apply Permutation_cons_app.
         reflexivity.
      -- rewrite Hperm ; simpl ; perm_solve.
  + inversion Hoclm ; constructor...
    apply Forall_app_inv in H4 ; destruct H4 as [Hl Hr] ; apply Forall_app...
    inversion Hr.
    inversion H6.
    constructor...
- simpl in f ; rewrite f in Hcut ; inversion Hcut.
- exfalso.
  destruct H as (l0' & C' & _ & Higax).
  eapply Hgax...
(*
simpl in H.
  destruct H as (l0' & C' & Heq & Higax) ; subst.
  apply Hgax in HP...
  destruct HP ; subst.
  assert (forall A B, oclike A -> ill2ll A = dual (ill2ll B) -> forall l, exists s, ill P l B s)
    as Hocldual'.
  { induction A ; intros B HoclA Heq l ; try (now inversion HoclA) ; destruct B ; inversion Heq.
    - inversion HoclA ; subst.
      eapply IHA2 in H2...
      destruct H2 as [s' H2].
      eexists ; apply lpam_irr...
    - inversion HoclA ; subst.
      eapply IHA1 in H1...
      destruct H1 as [s' H1].
      eexists ; apply lmap_irr...
    - destruct A1 ; inversion H1.
    - inversion HoclA ; subst.
      + eapply IHA1 in H1...
        destruct H1 as [s' H1].
        eexists ; apply plus_irr1...
      + eapply IHA2 in H2...
        destruct H2 as [s' H2].
        eexists ; apply plus_irr2...
    - eexists ; apply top_irr.
    - inversion HoclA ; subst.
      eapply IHA1 in H1...
      destruct H1 as [s1 H1].
      eapply IHA2 in H2...
      destruct H2 as [s2 H2].
      eexists ; apply with_irr... }
*)
Qed.

Proposition ll_to_ill_oclpam_axfree {P} : ipperm P = true ->
  (forall l C, ~ ipgax P l C) -> forall l s,
  ll (i2pfrag P) l s -> forall l0 C, Forall oclpam (C :: l0) ->
    Permutation l (ill2ll C :: rev (map dual (map ill2ll l0))) ->
      exists s', ill P l0 C s'.
Proof with myeeasy.
intros Hperm P_axfree l s pi l0 C Hoclm HP.
apply cut_admissible_axfree in pi.
- clear s ; destruct pi as [s pi]. 
  rewrite cutrm_i2pfrag in pi.
  eapply ll_to_ill_oclpam_cutfree with _ _ _ nil _ in pi...
  + clear s ; destruct pi as [[s pi] _].
    eexists.
    eapply (stronger_ipfrag)...
    nsplit 3...
    simpl ; intros...
  + constructor.
  + simpl ; rewrite Hperm ; simpl...
- intros l1 Hgax.
  destruct Hgax as (l' & C0 & Heq & Hgax).
  apply P_axfree in Hgax...
Qed.

End Conservativity.


(** ** Fragments of [ill] *)

Section Fragments.

(** Version of [ill] with a predicate parameter for constraining sequents inside proofs. *)
Inductive ill_ps P (PS : list iformula -> iformula -> Prop)
          : list iformula -> iformula -> Prop :=
| ax_ps_ir : forall X, PS (ivar X :: nil) (ivar X) ->
                ill_ps P PS (ivar X :: nil) (ivar X)
| ex_ps_ir : forall l1 l2 A, PS l2 A -> ill_ps P PS l1 A ->
                 PEperm (ipperm P) l1 l2 -> ill_ps P PS l2 A
| one_ps_irr : PS nil ione -> ill_ps P PS nil ione
| one_ps_ilr : forall l1 l2 A, PS (l1 ++ ione :: l2) A ->
                              ill_ps P PS (l1 ++ l2) A ->
                              ill_ps P PS (l1 ++ ione :: l2) A
| tens_ps_irr : forall A B l1 l2, PS (l1 ++ l2) (itens A B) ->
                    ill_ps P PS l1 A -> ill_ps P PS l2 B ->
                    ill_ps P PS (l1 ++ l2) (itens A B)
| tens_ps_ilr : forall A B l1 l2 C, PS (l1 ++ itens A B :: l2) C ->
                    ill_ps P PS (l1 ++ A :: B :: l2) C ->
                    ill_ps P PS (l1 ++ itens A B :: l2) C
| lpam_ps_irr : forall A B l, PS l (ilpam A B) ->
                    ill_ps P PS (l ++ A :: nil) B ->
                    ill_ps P PS l (ilpam A B)
| lpam_ps_ilr : forall A B l0 l1 l2 C, PS (l1 ++ ilpam A B :: l0 ++ l2) C ->
                    ill_ps P PS l0 A -> ill_ps P PS (l1 ++ B :: l2) C ->
                    ill_ps P PS (l1 ++ ilpam A B :: l0 ++ l2) C
| lmap_ps_irr : forall A B l, PS l (ilmap A B) ->
                    ill_ps P PS (A :: l) B ->
                    ill_ps P PS l (ilmap A B)
| lmap_ps_ilr : forall A B l0 l1 l2 C, PS (l1 ++ l0 ++ ilmap A B :: l2) C ->
                    ill_ps P PS l0 A -> ill_ps P PS (l1 ++ B :: l2) C ->
                    ill_ps P PS (l1 ++ l0 ++ ilmap A B :: l2) C
| neg_ps_irr : forall A l, PS l (ineg A) -> ill_ps P PS (A :: l) N ->
                          ill_ps P PS l (ineg A)
| neg_ps_ilr : forall A l, PS (l ++ ineg A :: nil) N -> ill_ps P PS l A ->
                          ill_ps P PS (l ++ ineg A :: nil) N
| top_ps_irr : forall l, PS l itop -> ill_ps P PS l itop
| with_ps_irr : forall A B l, PS l (iwith A B) ->
                    ill_ps P PS l A -> ill_ps P PS l B ->
                    ill_ps P PS l (iwith A B)
| with_ps_ilr1 : forall A B l1 l2 C, PS (l1 ++ iwith A B :: l2) C ->
                           ill_ps P PS (l1 ++ A :: l2) C ->
                           ill_ps P PS (l1 ++ iwith A B :: l2) C
| with_ps_ilr2 : forall A B l1 l2 C, PS (l1 ++ iwith B A :: l2) C ->
                           ill_ps P PS (l1 ++ A :: l2) C ->
                           ill_ps P PS (l1 ++ iwith B A :: l2) C
| zero_ps_ilr : forall l1 l2 C, PS (l1 ++ izero :: l2) C ->
                                         ill_ps P PS (l1 ++ izero :: l2) C
| plus_ps_irr1 : forall A B l, PS l (iplus A B) ->
                               ill_ps P PS l A ->
                               ill_ps P PS l (iplus A B)
| plus_ps_irr2 : forall A B l, PS l (iplus B A) ->
                               ill_ps P PS l A ->
                               ill_ps P PS l (iplus B A)
| plus_ps_ilr : forall A B l1 l2 C, PS (l1 ++ iplus A B :: l2) C ->
                        ill_ps P PS (l1 ++ A :: l2) C ->
                        ill_ps P PS (l1 ++ B :: l2) C ->
                        ill_ps P PS (l1 ++ iplus A B :: l2) C
| oc_ps_irr : forall A l, PS (map ioc l) (ioc A) ->
                          ill_ps P PS (map ioc l) A ->
                          ill_ps P PS (map ioc l) (ioc A)
| de_ps_ilr : forall A l1 l2 C, PS (l1 ++ ioc A :: l2) C ->
                        ill_ps P PS (l1 ++ A :: l2) C ->
                        ill_ps P PS (l1 ++ ioc A :: l2) C
| wk_ps_ilr : forall A l1 l2 C, PS (l1 ++ ioc A :: l2) C ->
                        ill_ps P PS (l1 ++ l2) C ->
                        ill_ps P PS (l1 ++ ioc A :: l2) C
| co_ps_ilr : forall A lw l1 l2 C, PS (l1 ++ map ioc lw ++ ioc A :: l2) C ->
                        ill_ps P PS (l1 ++ ioc A :: map ioc lw
                                  ++ ioc A :: l2) C ->
                        ill_ps P PS (l1 ++ map ioc lw ++ ioc A :: l2) C
| cut_ps_ir {f : ipcut P = true} : forall A l0 l1 l2 C,
                               PS (l1 ++ l0 ++ l2) C ->
                               ill_ps P PS l0 A -> ill_ps P PS (l1 ++ A :: l2) C ->
                               ill_ps P PS (l1 ++ l0 ++ l2) C
| gax_ps_ir : forall l A, PS l A -> ipgax P l A -> ill_ps P PS l A.

Lemma stronger_ps_ipfrag P Q : le_ipfrag P Q ->
  forall PS l A, ill_ps P PS l A -> ill_ps Q PS l A.
Proof with myeeasy.
intros Hle PS l A H.
induction H ; try (constructor ; myeasy ; fail).
- apply (ex_ps_ir _ _ l1)...
  inversion Hle.
  destruct H3 as (_ & Hp).
  unfold PEperm in H1.
  unfold PEperm.
  destruct (ipperm P) ; destruct (ipperm Q) ;
    simpl in Hp ; try inversion Hp ; subst...
- inversion Hle.
  rewrite f in H2.
  simpl in H2.
  eapply (@cut_ps_ir _ _ H2)...
- apply gax_ps_ir...
  apply Hle...
Qed.

Lemma ill_ps_stronger {P} : forall (PS QS : list iformula -> iformula -> Prop) l A,
  ill_ps P PS l A -> (forall x y, PS x y -> QS x y) -> ill_ps P QS l A.
Proof with try eassumption.
intros PS QS l A pi Hs.
induction pi ;
  try (constructor ; try apply Hs ; eassumption ; fail).
- eapply ex_ps_ir...
  apply Hs...
- eapply (@cut_ps_ir _ _ f)...
  apply Hs...
Qed.

Lemma ill_ps_is_ps {P} : forall l A PS, ill_ps P PS l A -> PS l A.
Proof.
intros l A PS pi.
inversion pi ; try assumption.
Qed.

Lemma ill_ps_is_ill {P} : forall l A PS, ill_ps P PS l A -> exists s, ill P l A s.
Proof with try eassumption.
intros l A PS pi.
induction pi ;
  try (destruct IHpi as [s IHpi]) ;
  try (destruct IHpi1 as [s1 IHpi1]) ;
  try (destruct IHpi2 as [s2 IHpi2]) ;
  eexists ;
  try (constructor ; eassumption ; fail).
- eapply ex_ir...
- eapply (@cut_ir _ f)...
Qed.

Lemma ill_is_ill_ps {P} : forall l A s, ill P l A s -> ill_ps P (fun _ _ => True) l A.
Proof with myeeasy.
intros l A s pi.
induction pi ;
  try (constructor ; myeasy ; fail).
- eapply ex_ps_ir...
- eapply (@cut_ps_ir _ _ f)...
Qed.

(** A fragment is a subset stable under sub-formula *)
Definition ifragment (FS : iformula -> Prop) :=
  forall A, FS A -> forall B, isubform B A -> FS B.

(** Conservativity over fragments *)
Lemma iconservativity {P} : ipcut P = false -> forall FS, ifragment FS ->
  forall l A, ill_ps P (fun _ _ => True) l A -> Forall FS (A :: l) ->
    ill_ps P (fun l A => Forall FS (A :: l)) l A.
Proof with try eassumption ; try reflexivity.
intros P_cutfree FS HFS l A pi.
induction pi ; intros HFrag ;
  inversion HFrag ; subst.
- apply ax_ps_ir...
- apply (ex_ps_ir _ _ l1)...
  apply IHpi...
  apply PEperm_sym in H0.
  constructor...
  eapply PEperm_Forall...
- apply one_ps_irr...
- apply one_ps_ilr...
  apply IHpi...
  constructor...
  apply Forall_app_inv in H3.
  destruct H3 as [ HFhd HFtl ].
  inversion HFtl ; apply Forall_app...
- apply Forall_app_inv in H3.
  destruct H3.
  apply tens_ps_irr...
  + apply IHpi1...
    constructor...
    eapply HFS...
    apply isub_tens_l...
  + apply IHpi2...
    constructor...
    eapply HFS...
    apply isub_tens_r...
- apply tens_ps_ilr...
  apply IHpi.
  constructor...
  apply Forall_app_inv in H3.
  destruct H3 as [ HFhd HFtl ].
  inversion HFtl ; apply Forall_app...
  constructor ; [ | constructor ]...
  + eapply HFS...
    apply isub_tens_l...
  + eapply HFS...
    apply isub_tens_r...
- apply lpam_ps_irr...
  apply IHpi.
  constructor...
  + eapply HFS...
    apply isub_lpam_r...
  + apply Forall_app...
    constructor ; [ | constructor ]...
    eapply HFS...
    apply isub_lpam_l...
- apply lpam_ps_ilr...
  + apply IHpi1...
    apply Forall_app_inv in H3.
    destruct H3 as [ HFhd HFtl ].
    inversion HFtl.
    apply Forall_app_inv in H4.
    destruct H4.
    constructor...
    eapply HFS...
    apply isub_lpam_l...
  + apply IHpi2...
    apply Forall_app_inv in H3.
    destruct H3 as [ HFhd HFtl ].
    inversion HFtl.
    apply Forall_app_inv in H4.
    destruct H4.
    constructor...
    apply Forall_app...
    constructor...
    eapply HFS...
    apply isub_lpam_r...
- apply lmap_ps_irr...
  apply IHpi.
  constructor...
  + eapply HFS...
    apply isub_lmap_r...
  + constructor...
    eapply HFS...
    apply isub_lmap_l...
- apply lmap_ps_ilr...
  + apply IHpi1...
    apply Forall_app_inv in H3.
    destruct H3 as [ HFhd HFtl ].
    apply Forall_app_inv in HFtl.
    destruct HFtl.
    inversion H1.
    constructor...
    eapply HFS...
    apply isub_lmap_l...
  + apply IHpi2...
    apply Forall_app_inv in H3.
    destruct H3 as [ HFhd HFtl ].
    apply Forall_app_inv in HFtl.
    destruct HFtl.
    inversion H1.
    constructor...
    apply Forall_app...
    constructor...
    eapply HFS...
    apply isub_lmap_r...
- apply neg_ps_irr...
  apply IHpi.
  constructor...
  + eapply HFS...
    apply isub_neg_N.
  + constructor...
    eapply HFS...
    constructor...
- apply neg_ps_ilr...
  apply IHpi...
  apply Forall_app_inv in H3.
  destruct H3 as [ HFhd HFtl ].
  inversion HFtl ; subst.
  constructor...
  eapply HFS...
  apply isub_neg_l...
- apply top_ps_irr...
- apply with_ps_irr...
  + apply IHpi1...
    constructor...
    eapply HFS...
    apply isub_with_l...
  + apply IHpi2...
    constructor...
    eapply HFS...
    apply isub_with_r...
- apply with_ps_ilr1...
  apply IHpi.
  constructor...
  apply Forall_app_inv in H3.
  destruct H3 as [ HFhd HFtl ].
  inversion HFtl ; apply Forall_app...
  constructor...
  eapply HFS...
  apply isub_with_l...
- apply with_ps_ilr2...
  apply IHpi.
  constructor...
  apply Forall_app_inv in H3.
  destruct H3 as [ HFhd HFtl ].
  inversion HFtl ; apply Forall_app...
  constructor...
  eapply HFS...
  apply isub_with_r...
- apply zero_ps_ilr...
- apply plus_ps_irr1...
  apply IHpi.
  constructor...
  eapply HFS...
  apply isub_plus_l...
- apply plus_ps_irr2...
  apply IHpi.
  constructor...
  eapply HFS...
  apply isub_plus_r...
- apply plus_ps_ilr...
  + apply IHpi1...
    constructor...
    apply Forall_app_inv in H3.
    destruct H3 as [ HFhd HFtl ].
    inversion HFtl ; apply Forall_app...
    constructor...
    eapply HFS...
    apply isub_plus_l...
  + apply IHpi2...
    constructor...
    apply Forall_app_inv in H3.
    destruct H3 as [ HFhd HFtl ].
    inversion HFtl ; apply Forall_app...
    constructor...
    eapply HFS...
    apply isub_plus_r...
- apply oc_ps_irr...
  apply IHpi.
  constructor...
  eapply HFS...
  apply isub_oc...
- apply de_ps_ilr...
  apply IHpi.
  constructor...
  apply Forall_app_inv in H3.
  destruct H3 as [ HFhd HFtl ].
  inversion HFtl ; apply Forall_app...
  constructor...
  eapply HFS...
  apply isub_oc...
- apply wk_ps_ilr...
  apply IHpi...
  constructor...
  apply Forall_app_inv in H3.
  destruct H3 as [ HFhd HFtl ].
  inversion HFtl ; apply Forall_app...
- apply co_ps_ilr...
  apply IHpi.
  constructor...
  apply Forall_app_inv in H3.
  destruct H3 as [ HFhd HFtl ].
  apply Forall_app...
  apply Forall_app_inv in HFtl.
  destruct HFtl.
  inversion H1.
  constructor...
  apply Forall_app...
- rewrite P_cutfree in f.
  inversion f.
- apply gax_ps_ir...
Qed.

(** Sub-formula property *)
Proposition isubformula {P} : ipcut P = false -> forall l A s,
  ill P l A s -> ill_ps P (fun l' C => isubform_list (C :: l') (A :: l)) l A.
Proof with try eassumption ; try reflexivity.
intros P_cutfree l A s pi.
apply ill_is_ill_ps in pi.
apply iconservativity...
- intros C Hf B Hs.
  remember (A :: l) as l'.
  revert Hf ; clear - Hs ; induction l' ; intro Hf ;
    inversion Hf ; subst. 
  + apply Exists_cons_hd.
    etransitivity...
  + apply Exists_cons_tl.
    apply IHl'...
- apply (isub_id_list (A :: l) nil).
Qed.

(** Embedding of [IAtom] into [Atom] *)
Variable i2a : IAtom -> Atom.
Hypothesis i2a_inj : injective i2a.

Lemma cut_admissible_nzeropos_ifragment {P} : (forall l A, ~ ipgax P l A) ->
  forall FS, ifragment FS -> (forall C, FS C -> nonzerospos C) -> forall l A,
    ill_ps P (fun l A => Forall FS (A :: l)) l A ->
    ill_ps (cutrm_ipfrag P) (fun l A => Forall FS (A :: l)) l A.
Proof with myeeasy.
intros P_axfree FS HFS Hnz l A pi.
assert (Forall FS (A :: l)) as HFSl by (destruct pi ; myeeasy).
apply ill_ps_is_ill in pi.
destruct pi as [s pi].
eapply cut_admissible_ill_nzeropos_axfree_by_ll in pi...
- clear s ; destruct pi as [s pi].
  apply ill_is_ill_ps in pi.
  apply iconservativity...
- eapply Forall_impl...
Qed.

Lemma iconservativity_cut_nzeropos_axfree {P} : (forall l A, ~ ipgax P l A) ->
  forall FS, ifragment FS -> (forall C, FS C -> nonzerospos C) -> 
    forall l A s, ill P l A s -> Forall FS (A :: l) ->
      ill_ps P (fun l A => Forall FS (A :: l)) l A.
Proof with try eassumption ; try reflexivity.
intros P_axfree FS Hf Hnz l A s pi HFS.
eapply cut_admissible_ill_nzeropos_axfree_by_ll in pi...
- clear s ; destruct pi as [s pi].
  apply ill_is_ill_ps in pi.
  eapply iconservativity in pi...
  clear - pi ; induction pi ;
    try (constructor ; assumption ; fail).
  + eapply ex_ps_ir...
  + eapply @cut_ps_ir...
    destruct P.
    inversion f.
- eapply Forall_impl...
Qed.

End Fragments.


(** ** Non conservativity of [ll] over [ill]. *)

Section Non_Conservativity.

Variable P : ipfrag.
Hypothesis fp : ipperm P = true.
Hypothesis fc : ipcut P = false.
Hypothesis fg : forall l a, ~ ipgax P l a.

Variable i2a : IAtom -> Atom.

Variable x : IAtom.
Variable y : IAtom.
Variable z : IAtom.

(** Counter example from Harold Schellinx *)
Definition cons_counter_ex :=
  ilpam (ilpam (ilpam (ivar x) (ivar y)) izero)
        (itens (ivar x) (ilpam izero (ivar z))).

Lemma counter_haszero : ~ nonzerospos cons_counter_ex.
Proof.
intros Hnzsp.
inversion Hnzsp.
inversion H1.
apply H8.
constructor.
Qed.

Lemma counter_ll_prove : exists n,
  ll (i2pfrag i2a P) (ill2ll i2a cons_counter_ex :: nil) n.
Proof with myeeasy.
eexists ; simpl.
apply parr_r.
eapply ex_r ; [ | apply PCperm_swap ].
rewrite <- (app_nil_l (tens (var _) _ :: _)).
apply tens_r.
- apply parr_r.
  eapply ex_r ;
    [ | unfold PCperm ; simpl ; rewrite fp ;
        symmetry ; apply Permutation_cons_append ].
  eapply ex_r ;
    [ | unfold PCperm ; simpl ; rewrite fp ;
        symmetry ; apply Permutation_cons_append ].
  rewrite <- ? app_comm_cons.
  rewrite app_comm_cons.
  apply tens_r.
  + eapply ex_r ; [ apply ax_r | PCperm_solve ].
  + apply parr_r.
    eapply ex_r ;
    [ | unfold PCperm ; simpl ; rewrite fp ;
        symmetry ; apply Permutation_cons_append ].
    rewrite <- ? app_comm_cons.
    apply top_r.
- apply top_r.
Qed.

Fact no_at_prove_ill : forall i n, ~ ill P nil (ivar i) n.
Proof with myeasy.
intros i n.
induction n using (well_founded_induction lt_wf).
intros pi.
inversion pi ;
  try (now (destruct l1 ; inversion H0)) ;
  subst...
- symmetry in H1.
  apply PEperm_nil in H1 ; subst.
  apply H in H0...
- destruct l1 ; destruct l0 ; inversion H0.
- destruct l ; inversion H0.
- destruct l1 ; destruct lw ; inversion H0.
- rewrite fc in f ; inversion f.
- apply fg in H0...
Qed.

Fact no_biat_prove_ill : forall i j, i <> j -> forall n,
  ~ ill P (ivar i :: nil) (ivar j) n.
Proof with myeasy.
intros i j Ha n.
induction n using (well_founded_induction lt_wf).
intros pi.
inversion pi ;
  try now (destruct l1 ; inversion H0 ; subst ;
           destruct l1 ; try inversion H6 ; try inversion H7) ;
  subst...
- apply Ha...
- symmetry in H1.
  apply PEperm_length_1_inv in H1 ; subst.
  apply H in H0...
- destruct l1 ; destruct l0 ; inversion H0 ;
    try destruct l0 ; try destruct l1 ; inversion H7.
- destruct l ; inversion H0 ; subst.
  destruct l ; inversion H6.
- destruct l1 ; inversion H0 ; subst.
  + rewrite app_nil_l in H1 ; inversion H1.
  + inversion H1.
    destruct l1 ; inversion H4.
- destruct l1 ; destruct lw ; inversion H0 ; destruct l1 ; inversion H6.
- rewrite fc in f ; inversion f.
- apply fg in H0...
Qed.

Fact no_biat_map_prove_ill : forall i j, i <> j ->
  forall n, ~ ill P nil (ilpam (ivar i) (ivar j)) n.
Proof with myeasy.
intros i j Ha n.
induction n using (well_founded_induction lt_wf).
intros pi.
inversion pi ;
  try now (destruct l1 ; inversion H0) ;
  subst...
- symmetry in H1.
  apply PEperm_nil in H1 ; subst.
  apply H in H0...
- apply no_biat_prove_ill in H4...
- destruct l1 ; destruct l0 ; inversion H0.
- destruct l1 ; destruct lw ; inversion H0.
- rewrite fc in f ; inversion f.
- apply fg in H0...
Qed.

(** We need two distinct atoms *)
Hypothesis twoat : x <> y.

Fact pre_pre_counter_ex_ill : forall n,
  ~ ill P (ilpam (ilpam (ivar x) (ivar y)) izero :: nil) (ivar x) n.
Proof with myeasy.
induction n using (well_founded_induction lt_wf).
intro pi.
inversion pi ;
  try (destruct l1 ; inversion H0 ; subst ;
       destruct l1 ;
       try (inversion H6 ; fail) ;
       try (inversion H7 ; fail) ;
       fail) ;
  subst...
- symmetry in H1.
  apply PEperm_length_1_inv in H1 ; subst.
  apply H in H0...
- destruct l1 ; inversion H0 ; try rewrite app_nil_l in H0 ; subst.
  + apply app_eq_nil in H6.
    destruct H6 ; subst.
    apply no_biat_map_prove_ill in H1...
  + destruct l1 ; inversion H5.
- destruct l1 ; destruct l0 ; inversion H0 ; 
    try destruct l0 ; try destruct l1 ; inversion H5.
- destruct l ; inversion H0 ; subst.
  destruct l ; inversion H4.
- destruct l1 ; inversion H1 ; destruct l1 ; inversion H3.
- destruct l1 ; destruct lw ; inversion H0 ; destruct l1 ; inversion H4.
- rewrite fc in f ; inversion f.
- apply fg in H0...
Qed.

Fact pre_counter_ex_ill : forall n,
  ~ @ill P (ilpam (ilpam (ivar x) (ivar y)) izero :: nil)
           (itens (ivar x) (ilpam izero (ivar z))) n.
Proof with myeasy.
induction n using (well_founded_induction lt_wf).
intro pi.
inversion pi ;
  try (destruct l1 ; inversion H0 ; subst ;
       destruct l1 ;
       try (inversion H6 ; fail) ;
       try (inversion H7 ; fail) ;
       fail) ;
  subst...
- symmetry in H1.
  apply PEperm_length_1_inv in H1 ; subst.
  apply H in H0...
- destruct l1 ; inversion H0 ; try rewrite app_nil_l in H0 ; subst.
  + apply no_at_prove_ill in H3...
  + apply app_eq_nil in H4.
    destruct H4 ; subst.
    apply pre_pre_counter_ex_ill in H3...
- destruct l1 ; inversion H0 ; subst.
  + apply app_eq_nil in H6.
    destruct H6 ; subst.
    apply no_biat_map_prove_ill in H1...
  + destruct l1 ; inversion H5.
- destruct l1 ; destruct l0 ; inversion H0 ; 
    try destruct l0 ; try destruct l1 ; inversion H5.
- destruct l1 ; inversion H1 ; destruct l1 ; inversion H3.
- destruct l1 ; destruct lw ; inversion H0 ; destruct l1 ; inversion H4.
- rewrite fc in f ; inversion f.
- apply fg in H0...
Qed.

Fact counter_ex_ill : forall n, ~ @ill P nil cons_counter_ex n.
Proof with myeasy.
induction n using (well_founded_induction lt_wf).
intro pi.
inversion pi ;
  try now (destruct l1 ; inversion H0) ;
  subst.
- symmetry in H1.
  apply PEperm_nil in H1 ; subst.
  apply H in H0...
- apply pre_counter_ex_ill in H4...
- destruct l1 ; destruct l0 ; inversion H0.
- destruct l1 ; destruct lw ; inversion H0.
- rewrite fc in f ; inversion f.
- apply fg in H0...
Qed.

End Non_Conservativity.


