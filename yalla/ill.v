(* ill library for yalla *)
(* Coq 8.6 *)
(* v 1.0   Olivier Laurent *)


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
| lmap_irr : forall A B l s,
                    ill P (l ++ A :: nil) B s ->
                    ill P l (ilmap A B) (S s)
| lmap_ilr : forall A B l0 l1 l2 C s1 s2,
                           ill P l0 A s1 -> ill P (l1 ++ B :: l2) C s2 ->
                           ill P (l1 ++ ilmap A B :: l0 ++ l2) C (S (s1 + s2))
| lpam_irr : forall A B l s,
                           ill P (A :: l) B s ->
                           ill P l (ilpam A B) (S s)
| lpam_ilr : forall A B l0 l1 l2 C s1 s2,
                           ill P l0 A s1 -> ill P (l1 ++ B :: l2) C s2 ->
                           ill P (l1 ++ l0 ++ ilpam A B :: l2) C (S (s1 + s2))
| top_irr {ft : iftop = true} : forall l, ill P l (@itop ft) 1
| with_irr : forall A B l s1 s2,
                           ill P l A s1 -> ill P l B s2 ->
                           ill P l (iwith A B) (S (max s1 s2))
| with_ilr1 : forall A B l1 l2 C s, ill P (l1 ++ A :: l2) C s ->
                           ill P (l1 ++ iwith A B :: l2) C (S s)
| with_ilr2 : forall A B l1 l2 C s, ill P (l1 ++ A :: l2) C s ->
                           ill P (l1 ++ iwith B A :: l2) C (S s)
| zero_ilr {fz : ifzer = true} : forall l1 l2 C, ill P (l1 ++ @izero fz :: l2) C 1
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


(** ** Characterization of [ill] as a fragment of [ll] *)

Section LL_fragment.

(** The results of the section hold without [izero] only. *)
Context {fz : ifzer = false}.

(** *** Embedding of [ill] into [ll] *)

(** Embedding of [IAtom] into [Atom] *)
Variable i2a : IAtom -> Atom.
Hypothesis i2a_inj : injective i2a.

Fixpoint ill2ll A :=
match A with
| ivar x    => var (i2a x)
| ione      => one
| itens A B => tens (ill2ll A) (ill2ll B)
| ilmap A B => parr (ill2ll B) (dual (ill2ll A))
| ilpam A B => parr (dual (ill2ll A)) (ill2ll B)
| itop      => top
| iwith A B => awith (ill2ll A) (ill2ll B)
| izero     => zero
| iplus A B => aplus (ill2ll A) (ill2ll B)
| ioc A     => oc (ill2ll A)
end.

Lemma ill2ll_not_dual : forall A B, dual (ill2ll A) <> ill2ll B.
Proof with myeasy.
induction A ; intros B Heq ; destruct B ; inversion Heq.
- apply IHA2 in H0...
- apply IHA1 in H1...
- apply IHA2 in H1...
- apply IHA2 in H0...
- rewrite fz0 in fz ; inversion fz.
- apply IHA1 in H0...
- rewrite fz0 in fz ; inversion fz.
- apply IHA1 in H0...
Qed.

Lemma ill2ll_not_dual_elt : forall l1 l2 l A,
  ~ l1 ++ ill2ll A :: l2 = map dual (map ill2ll l).
Proof with try assumption.
intros l1 l2 l A Heq.
revert l1 l2 Heq ; induction l ; intros l1 l2 Heq ;
  destruct l1 ; inversion Heq.
- symmetry in H0.
  apply ill2ll_not_dual in H0...
- apply IHl in H1...
Qed.

Lemma ill2ll_inj : injective ill2ll.
Proof with myeasy.
intros A.
induction A ; intros B Heq ; destruct B ; inversion Heq ;
  try apply IHA in H0 ;
  try apply IHA1 in H0 ; try apply IHA2 in H1 ; subst...
- apply i2a_inj in H0 ; subst...
- apply dual_inj in H1.
  apply IHA1 in H1.
  apply IHA2 in H0 ; subst...
- contradict H1.
  apply ill2ll_not_dual.
- contradict H0.
  apply ill2ll_not_dual.
- apply dual_inj in H0.
  apply IHA1 in H0 ; subst...
- apply uniq_itop.
- apply uniq_izero.
Qed.


(** *** The input/output fragment of [ll]: [jfragment] *)
Definition jfragment A := exists B, A = ill2ll B \/ A = dual (ill2ll B).

Lemma j_is_fragment : fragment jfragment.
Proof.
intros A HfA B Hsf.
induction Hsf ; 
  try (apply IHHsf ;
       destruct HfA as [B0 [ HFA | HFA ]] ;
       destruct B0 ; inversion HFA ; subst ;
       eexists ;
       try (now left) ;
       try (now right)).
- assumption.
- rewrite bidual.
  left ; reflexivity.
- rewrite bidual.
  left ; reflexivity.
Qed.

(** Sequents with exactly one output formula *)
Definition jsequent l := exists l0 C,
  CPermutation l (ill2ll C :: rev (map dual (map ill2ll l0))).

Lemma is_jsequent : forall A l, jsequent (ill2ll A :: map dual (map ill2ll l)).
Proof.
intros A l.
exists (rev l) ; exists A.
now list_simpl.
Qed.

Lemma jsequent_PCperm b : forall l, jsequent l -> exists l0 C,
  PCperm b l (ill2ll C :: rev (map dual (map ill2ll l0))).
Proof.
intros l (l0 & C & HC).
exists l0 ; exists C.
apply cperm_PCperm.
assumption.
Qed.

Lemma PCperm_jsequent b : forall l l0 C,
  PCperm b l (ill2ll C :: rev (map dual (map ill2ll l0))) -> jsequent l.
Proof.
intros l l0 C HP.
destruct b.
- assert (HP' := HP).
  apply Permutation_vs_cons_inv in HP'.
  destruct HP' as (l2 & l3 & HP') ; subst.
  symmetry in HP.
  apply Permutation_cons_app_inv in HP.
  rewrite <- ? map_rev in HP.
  symmetry in HP.
  apply Permutation_map_inv in HP.
  destruct HP as (l1 & Heq & HP).
  symmetry in HP.
  apply Permutation_map_inv in HP.
  destruct HP as (l4 & Heq2 & HP) ; subst.
  decomp_map Heq ; subst.
  decomp_map Heq ; subst.
  exists (rev (l3 ++ l2)) ; exists C.
  list_simpl ; cperm_solve.
- exists l0 ; exists C.
  assumption.
Qed.

Lemma jsequent_app : forall l1 l2, jsequent (l1 ++ l2) -> exists l,
     (l2 = map dual (map ill2ll l) /\ jsequent l1)
  \/ (l1 = map dual (map ill2ll l) /\ jsequent l2).
Proof with myeasy.
intros l1 l2 Hi.
assert (Hi' := Hi).
destruct Hi' as (l0 & C & Hi').
apply cperm_vs_cons_inv in Hi'.
destruct Hi' as (l3 & l4 & Heq1 & Heq2).
rewrite <- ? map_rev in Heq1.
symmetry in Heq1.
decomp_map Heq1.
decomp_map Heq1 ; subst.
clear Heq1.
revert l1 l2 l7 Heq2 Hi ; induction l8 ; intros l1 l2 l7 H Hi.
- destruct l1.
  + exists nil ; right ; split...
  + inversion H.
    decomp_map H2.
    decomp_map H2 ; subst.
    exists l6 ; left ; split...
    exists (rev l5) ; exists C.
    list_simpl...
- destruct l1.
  + exists nil ; right ; split...
  + inversion H.
    apply IHl8 in H2...
    * destruct H2 as [l' [[Heq1 Heq2] | [Heq1 Heq2]]] ; subst.
      -- exists l' ; left ; split...
         destruct Heq2 as (l'' & C0 & Heq).
         eapply (PCperm_jsequent true)...
         apply cperm_perm in Heq.
         apply (@Permutation_cons _ _ (dual (ill2ll a)) eq_refl) in Heq.
         etransitivity ; [ apply Heq | ].
         etransitivity ; [ apply perm_swap | ].
         apply Permutation_cons...
         replace (dual (ill2ll a) :: rev (map dual (map ill2ll l'')))
           with (rev (map dual (map ill2ll (l'' ++ a :: nil))))...
         list_simpl...
      -- exists (a :: l') ; right ; split...
    * exists (rev (l7 ++ l8)) ; exists C...
      rewrite H2...
      list_simpl ; cperm_solve.
Qed.

Lemma jsequent_is_jfragment : forall l, jsequent l -> Forall jfragment l.
Proof with myeeasy.
intros l Hi.
destruct Hi as (l' & C & HP).
symmetry in HP.
eapply cperm_Forall...
constructor.
- exists C ; left...
- clear ; induction l'.
  + constructor.
  + list_simpl in IHl'.
    list_simpl.
    apply Forall_app...
    constructor ; [ | constructor ]...
    exists a ; right...
Qed.

Lemma uniq_jsequent {b} : forall l1 l2 C1 C2,
  PCperm b (ill2ll C1 :: rev (map dual (map ill2ll l1)))
           (ill2ll C2 :: rev (map dual (map ill2ll l2))) ->
    C1 = C2 /\ PEperm b l1 l2.
Proof with myeeasy.
intros l1 l2 C1 C2 HP.
hyps_PCperm_unfold ; unfold PEperm ; destruct b. 
- assert (HP' := HP).
  apply Permutation_vs_cons_inv in HP'.
  destruct HP' as (l' & l'' & Heq).
  destruct l' ; inversion Heq.
  + split.
    * apply ill2ll_inj...
    * rewrite H0 in HP.
      apply Permutation_cons_inv in HP.
      apply Permutation_rev' in HP.
      rewrite ? rev_involutive in HP.
      apply Permutation_map_inv_inj in HP ; [ | apply dual_inj ].
      apply Permutation_map_inv_inj in HP ; [ | apply ill2ll_inj ]...
  + symmetry in H1.
    contradict H1.
    list_simpl.
    apply ill2ll_not_dual_elt.
- inversion HP.
  destruct l0 ; destruct l3 ; inversion H0.
  + inversion H ; subst.
    apply ill2ll_inj in H4.
    assert (Heq := eq_refl (rev (rev (map dual (map ill2ll l1))))).
    rewrite ? app_nil_r in H5.
    rewrite H5 in Heq at 1.
    rewrite ? rev_involutive in Heq.
    apply map_inj in Heq ; [ | apply dual_inj ].
    apply map_inj in Heq ; [ | apply ill2ll_inj ] ; subst.
    split...
  + inversion H ; subst.
    apply ill2ll_inj in H4.
    assert (Heq := eq_refl (rev (rev (map dual (map ill2ll l1))))).
    rewrite ? app_nil_r in H3.
    rewrite <- H3 in Heq at 1.
    rewrite ? rev_involutive in Heq.
    apply map_inj in Heq ; [ | apply dual_inj ].
    apply map_inj in Heq ; [ | apply ill2ll_inj ] ; subst.
    split...
  + exfalso.
    inversion H ; subst.
    list_simpl in H3.
    eapply ill2ll_not_dual_elt...
Qed.

Lemma uniq_jfragment_jsequent {b} : forall A C l l0 B, A = ill2ll B ->
  PCperm b (A :: l) (ill2ll C :: rev (map dual (map ill2ll l0))) ->
     A = ill2ll C /\ PEperm b l (rev (map dual (map ill2ll l0))).
Proof with (try reflexivity ; try eassumption).
intros A C l l0 B HA HP.
assert (Hs := PCperm_jsequent _ _ _ _ HP).
unfold PCperm in HP ; unfold PEperm ; destruct b.
- assert (Heq := HP).
  symmetry in Heq.
  apply Permutation_vs_cons_inv in Heq.
  destruct Heq as (l1 & l2 & Heq).
  apply jsequent_is_jfragment in Hs.
  apply (Permutation_Forall _ _ _ HP) in Hs.
  rewrite Heq in Hs.
  apply Forall_app_inv in Hs.
  destruct Hs as (Hl1 & Hl2).
  destruct l1 ; inversion Heq ; subst.
  + apply ill2ll_inj in H0 ; subst.
    apply Permutation_cons_inv in HP.
    split...
  + exfalso.
    symmetry in H1.
    rewrite <- ? map_rev in H1.
    eapply ill2ll_not_dual_elt...
- inversion HP.
  destruct l1 ; destruct l2 ; inversion H0 ; subst.
  + inversion H.
    apply ill2ll_inj in H2 ; subst.
    list_simpl ; split...
  + inversion H.
    apply ill2ll_inj in H2 ; subst.
    list_simpl ; split...
  + exfalso.
    inversion H.
    list_simpl in H3.
    eapply ill2ll_not_dual_elt...
Qed.

Lemma uniq_not_jfragment_jsequent {b} : forall A C l l0 B, A = dual (ill2ll B) ->
  PCperm b (A :: l) (ill2ll C :: rev (map dual (map ill2ll l0))) ->
    exists l1 l2, PEperm b l (rev (map dual (map ill2ll l1))
                   ++ ill2ll C :: rev (map dual (map ill2ll l2)))
               /\ PEperm b (rev (map dual (map ill2ll l2)) ++ A
                   :: rev (map dual (map ill2ll l1))) (rev (map dual (map ill2ll l0))).
Proof with (try reflexivity ; try eassumption).
intros A C l l0 B HA HP.
unfold PCperm in HP ; unfold PEperm ; destruct b.
- assert (Heq := HP).
  symmetry in Heq.
  apply Permutation_vs_cons_inv in Heq.
  destruct Heq as (l1 & l2 & Heq).
  destruct l1 ; inversion Heq ; subst.
  + exfalso.
    symmetry in H0.
    apply ill2ll_not_dual in H0...
  + rewrite <- ? map_rev in H1.
    symmetry in H1.
    decomp_map H1.
    decomp_map H3 ; subst.
    apply dual_inj in H1 ; apply ill2ll_inj in H1 ; subst.
    rewrite <- ? map_rev in HP.
    rewrite <- H6 in HP.
    list_simpl in HP.
    rewrite app_comm_cons in HP.
    apply Permutation_cons_app_inv in HP.
    simpl in HP.
    exists (rev l9) ; exists (rev l7) ; split.
    * list_simpl ; perm_solve.
    * list_simpl.
      rewrite <- H6.
      list_simpl ; perm_solve.
- inversion HP.
  destruct l1 ; destruct l2 ; inversion H0 ; subst ; inversion H.
  + exfalso.
    apply ill2ll_not_dual in H2...
  + exfalso.
    apply ill2ll_not_dual in H2...
  + rewrite <- ? map_rev in H3.
    decomp_map H3.
    decomp_map H5 ; subst.
    exists (rev l8) ; exists (rev l6) ; split ; list_simpl...
Qed.

(** Translation of proof fragments *)
Definition i2pfrag P := {|
  pcut := ipcut P ;
  pgax := fun l =>
            exists l0 C, 
               l = ill2ll C :: rev (map dual (map ill2ll l0))
            /\ ipgax P l0 C ;
  pmix0 := false ;
  pmix2 := false ;
  pperm := ipperm P |}.

Lemma cutrm_i2pfrag : forall P,
  cutrm_pfrag (i2pfrag P) = i2pfrag (cutrm_ipfrag P).
Proof.
reflexivity.
Qed.

Proposition ill_to_ll {P} : forall l C s, ill P l C s -> exists s',
  ll (i2pfrag P) (ill2ll C :: rev (map dual (map ill2ll l))) s'.
Proof with myeeasy.
intros l C s Hill.
induction Hill ; 
  try (destruct IHHill as [s' IHHill]) ;
  try (destruct IHHill1 as [s1' IHHill1]) ;
  try (destruct IHHill2 as [s2' IHHill2]) ;
  list_simpl ;
  try list_simpl in IHHill ;
  try list_simpl in IHHill1 ;
  try list_simpl in IHHill2 ;
  eexists.
- eapply ex_r.
  apply ax_r.
  apply PCperm_swap.
- eapply ex_r...
  hyps_PEperm_unfold ; unfold PCperm ; simpl ; destruct ipperm.
  * apply Permutation_cons...
    apply Permutation_map.
    apply Permutation_map.
    apply Permutation_rev'...
  * rewrite H...
- apply one_r.
- rewrite app_comm_cons.
  eapply ex_r ; [ | apply PCperm_app_comm ].
  rewrite <- ? app_comm_cons.
  apply bot_r.
  eapply ex_r...
  rewrite ? app_comm_cons.
  apply PCperm_app_comm.
- apply tens_r...
- rewrite app_comm_cons.
  eapply ex_r ; [ | apply PCperm_app_comm ].
  rewrite <- ? app_comm_cons.
  apply parr_r.
  eapply ex_r...
  rewrite ? app_comm_cons.
  apply PCperm_app_comm.
- apply parr_r...
- rewrite app_comm_cons.
  rewrite app_assoc.
  eapply ex_r ; [ | apply PCperm_app_comm ].
  rewrite bidual.
  rewrite ? app_assoc.
  rewrite <- ? app_comm_cons.
  apply tens_r...
  eapply ex_r...
  rewrite ? app_comm_cons.
  apply PCperm_app_comm.
- apply parr_r...
  eapply ex_r...
  symmetry.
  rewrite (app_comm_cons _ _ (ill2ll B)).
  apply PCperm_last.
- rewrite app_comm_cons.
  eapply ex_r ; [ | apply PCperm_app_comm ].
  rewrite <- ? app_comm_cons.
  rewrite <- ? app_assoc.
  rewrite bidual.
  apply tens_r...
  eapply ex_r...
  rewrite ? app_comm_cons.
  apply PCperm_app_comm.
- apply top_r.
- apply with_r...
- rewrite ? app_comm_cons.
  eapply ex_r ; [ | apply PCperm_app_comm ].
  rewrite <- ? app_comm_cons.
  apply plus_r1...
  eapply ex_r...
  rewrite ? app_comm_cons.
  apply PCperm_app_comm.
- rewrite ? app_comm_cons.
  eapply ex_r ; [ | apply PCperm_app_comm ].
  rewrite <- ? app_comm_cons.
  apply plus_r2...
  eapply ex_r...
  rewrite ? app_comm_cons.
  apply PCperm_app_comm.
- rewrite ? app_comm_cons.
  eapply ex_r ; [ | apply PCperm_app_comm ].
  rewrite <- ? app_comm_cons.
  apply top_r...
- apply plus_r1...
- apply plus_r2...
- rewrite ? app_comm_cons.
  eapply ex_r ; [ | apply PCperm_app_comm ].
  rewrite <- ? app_comm_cons.
  apply with_r...
  + eapply ex_r ; [ apply IHHill1 | ].
    rewrite ? app_comm_cons.
    apply PCperm_app_comm.
  + eapply ex_r ; [ apply IHHill2 | ].
    rewrite ? app_comm_cons.
    apply PCperm_app_comm.
- assert (map dual (map ill2ll (map ioc (rev l))) =
          map wn (map dual (map ill2ll (rev l)))) as Hwn.
  { remember (rev l) as l'.
    clear ; induction l'...
    simpl ; rewrite IHl'... }
  rewrite_all Hwn.
  apply oc_r...
- rewrite ? app_comm_cons.
  eapply ex_r ; [ | apply PCperm_app_comm ].
  rewrite <- ? app_comm_cons.
  apply de_r...
  eapply ex_r...
  rewrite ? app_comm_cons.
  apply PCperm_app_comm.
- rewrite app_comm_cons.
  eapply ex_r ; [ | apply PCperm_app_comm ].
  rewrite <- ? app_comm_cons.
  apply wk_r.
  eapply ex_r...
  rewrite ? app_comm_cons.
  apply PCperm_app_comm.
- assert (map dual (map ill2ll (map ioc (rev lw))) =
          map wn (map dual (map ill2ll (rev lw)))) as Hwn.
  { remember (rev lw) as l'.
    clear ; induction l'...
    simpl ; rewrite IHl'... }
  rewrite_all Hwn.
  rewrite ? app_comm_cons.
  eapply ex_r ; [ | apply PCperm_app_comm ].
  rewrite <- ? app_comm_cons.
  rewrite <- ? app_assoc.
  apply co_r...
  eapply ex_r...
  rewrite ? app_comm_cons.
  rewrite (app_assoc (wn _ :: _)).
  apply PCperm_app_comm.
- rewrite app_comm_cons.
  eapply ex_r ; [ | apply PCperm_app_comm ].
  rewrite <- app_assoc.
  assert (pcut (i2pfrag P) = true) as fc by (now simpl).
  eapply (@cut_r _ fc)...
  eapply ex_r...
  rewrite ? app_comm_cons.
  apply PCperm_app_comm.
- apply gax_r.
  exists l ; exists A ; split...
  list_simpl...
Qed.

(** [jfragment] is preserved upwardly inside [ll] proofs *)
Lemma ll_j_is_ll_ps_j_cutfree {P} : pcut P = false ->
  (forall l, pgax P l -> Forall jfragment l) -> forall l s,
     ll P l s -> Forall jfragment l -> ll_ps P (Forall jfragment) l.
Proof with myeeasy.
intros P_cutfree Hax l s Hll Hf.
apply ll_is_ll_ps in Hll.
eapply conservativity...
apply j_is_fragment.
Qed.

Lemma ll_i_is_ll_ps_i_axfree {P} : (forall l, ~ pgax P l) -> forall l s,
  ll P l s -> Forall jfragment l -> ll_ps P (Forall jfragment) l.
Proof with myeeasy.
intros P_axfree l s Hll Hf.
eapply conservativity_cut_axfree in Hll...
apply j_is_fragment.
Qed.

(** [jfragment] implies at least one output formula *)
Lemma ll_ps_j_has_jformula {P} : forall l,
  ll_ps (i2pfrag P) (Forall jfragment) l -> exists l1 l2 A,
    l = l1 ++ ill2ll A :: l2.
Proof with myeeasy.
intros l Hll.
induction Hll ;
  try (destruct IHHll as (l1' & l1'' & A0 & Heq)) ;
  try (destruct IHHll1 as (l1' & l1'' & A1 & Heq1)) ;
  try (destruct IHHll2 as (l2' & l2'' & A2 & Heq2)) ;
  subst.
- inversion H.
  destruct H2 as [A [ H2 | H2 ]] ; destruct A ; inversion H2.
  exists (covar X :: nil) ; exists nil ; exists (ivar i) ; subst...
- symmetry in H0.
  hyps_PCperm_unfold ; destruct pperm.
  + apply Permutation_vs_elt_inv in H0.
    destruct H0 as (l0 & l0' & H0) ; subst.
    exists l0 ; exists l0' ; exists A0...
  + apply cperm_vs_elt_inv in H0.
    destruct H0 as (l0 & l0' & H0 & H0') ; subst.
    exists l0 ; exists l0' ; exists A0...
- inversion f.
- inversion f.
- exists nil ; exists nil ; exists ione...
- exists (bot :: l1') ; exists l1'' ; exists A0...
- destruct l1' ; inversion Heq1 ;
    [ destruct l2' ; inversion Heq2 | ] ; subst.
  + inversion H ; subst ; destruct H2 as [D [Ht | Ht]] ;
      destruct D ; inversion Ht ; subst.
    * rewrite Ht.
      exists nil ; exists (l2'' ++ l1'') ; exists (itens D1 D2)...
    * exfalso.
      symmetry in H2.
      apply ill2ll_not_dual in H2...
    * exfalso.
      symmetry in H1.
      apply ill2ll_not_dual in H1...
  + exists (tens (ill2ll A1) f :: l2') ; exists (l2'' ++ l1'') ; exists A2.
    list_simpl...
  + exists (tens f B :: l2 ++ l1') ; exists l1'' ; exists A1.
    list_simpl...
- destruct l1' ; inversion Heq ;
    [ | destruct l1' ; inversion H2 ] ; subst.
  + inversion H ; subst ; destruct H2 as [D [Ht | Ht]] ;
      destruct D ; inversion Ht ; subst.
    * rewrite Ht.
      exists nil ; exists l ; exists (ilmap D1 D2)...
    * exfalso.
      inversion Ht.
      symmetry in H2.
      apply ill2ll_not_dual in H2...
    * exfalso.
      inversion Ht.
      symmetry in H2.
      apply ill2ll_not_dual in H2...
  + inversion H ; subst ; destruct H3 as [D [Ht | Ht]] ;
      destruct D ; inversion Ht ; subst.
    * exfalso.
      inversion Ht.
      symmetry in H1.
      apply ill2ll_not_dual in H1...
    * rewrite Ht.
      exists nil ; exists l1'' ; exists (ilpam D1 D2)...
    * exfalso.
      inversion Ht.
      symmetry in H1.
      apply ill2ll_not_dual in H1...
  + exists (parr f f0 :: l1') ; exists l1'' ; exists A0...
- assert (iftop = true) as ft.
  { inversion H ; inversion H2 ; subst.
    destruct H4 ; destruct x0 ; inversion H0...
    rewrite fz0 in fz ; inversion fz. }
  exists nil ; exists l ; exists (@itop ft)...
- destruct l1' ; inversion Heq ; subst.
  + inversion H ; subst ; destruct H2 as [D [Ht | Ht]] ;
      destruct D ; inversion Ht ; subst.
    * apply ill2ll_inj in H1 ; subst.
      rewrite Ht.
      exists nil ; exists l1'' ; exists (iplus D1 D2)...
    * symmetry in H1.
      apply ill2ll_not_dual in H1...
  + exists (aplus f B :: l1') ; exists l1'' ; exists A0...
- destruct l1' ; inversion Heq ; subst.
  + inversion H ; subst ; destruct H2 as [D [Ht | Ht]] ;
      destruct D ; inversion Ht ; subst.
    * apply ill2ll_inj in H2 ; subst.
      rewrite Ht.
      exists nil ; exists l1'' ; exists (iplus D1 D2)...
    * symmetry in H2.
      apply ill2ll_not_dual in H2...
  + exists (aplus B f :: l1') ; exists l1'' ; exists A0...
- destruct l1' ; inversion Heq1 ; subst.
  + inversion H ; subst ; destruct H2 as [D [Ht | Ht]] ;
      destruct D ; inversion Ht ; subst.
    * rewrite Ht.
      exists nil ; exists l1'' ; exists (iwith D1 D2)...
    * exfalso.
      symmetry in H1.
      apply ill2ll_not_dual in H1...
  + exists (awith f B :: l1') ; exists l1'' ; exists A1...
- destruct l1' ; inversion Heq ; subst.
  + inversion H ; subst ; destruct H2 as [D [Ht | Ht]] ;
      destruct D ; inversion Ht ; subst.
    rewrite Ht.
    exists nil ; exists (map wn l) ; exists (ioc D)...
  + rewrite H2.
    exists (oc f :: l1') ; exists l1'' ; exists A0...
- destruct l1' ; inversion Heq ; subst.
  + exfalso.
    inversion H ; subst ; destruct H2 as [D [Ht | Ht]] ;
      destruct D ; inversion Ht ; subst.
    symmetry in H1.
    apply ill2ll_not_dual in H1...
  + exists (wn f :: l1') ; exists l1'' ; exists A0...
- exists (wn A :: l1') ; exists l1'' ; exists A0...
- destruct l1' ; inversion Heq ; subst.
  + exfalso.
    destruct A0 ; inversion H1.
  + assert (exists l'', map wn lw ++ wn A :: l'' = l1') as Hwn.
    { clear - H2.
      revert lw H2 ; induction l1' ; intros lw H.
      - destruct lw ; inversion H ; destruct A0 ; inversion H1.
      - destruct lw ; inversion H ; subst.
        + exists l1'...
        + apply IHl1' in H2.
          destruct H2 as [l'' H2].
          exists l''.
          simpl ; rewrite H2... }
    destruct Hwn as [l'' Hwn] ; subst.
    inversion Heq.
    rewrite <- ? app_assoc in H1.
    rewrite <- ? app_comm_cons in H1.
    apply app_inv_head in H1.
    inversion H1 ; subst.
    exists (wn A :: map wn lw ++ l'') ; exists l1'' ; exists A0.
    list_simpl...
- destruct l1' ; inversion Heq1 ; [ destruct l2' ; inversion Heq2 | ] ; subst.
  + exfalso.
    apply ill2ll_not_dual in H1...
  + exists l2' ; exists (l2'' ++ l1'') ; exists A2 ; list_simpl...
  + exists (l2 ++ l1') ; exists l1'' ; exists A1 ; list_simpl...
- destruct H0 as (l0 & C & Heq1 & Heq2) ; subst.
  exists nil ; exists (rev (map dual (map ill2ll l0))) ; exists C...
Qed.

(** [jfragment] implies [jsequent] *)
Lemma ll_ps_j_is_ll_ps_jsequent {P} : forall l,
  ll_ps (i2pfrag P) (Forall jfragment) l -> jsequent l ->
    ll_ps (i2pfrag P) jsequent l.
Proof with myeeasy ; try (apply is_jsequent ; fail).
intros l Hll Hc.
induction Hll ;
  try (assert (Hc0 := Hc) ;
       destruct Hc0 as (l0 & C0 & Hc0)).
- apply ax_ps_r...
- eapply ex_ps_r...
  apply IHHll.
  eapply cperm_PCperm in Hc0.
  eapply PCperm_jsequent.
  etransitivity...
- inversion f.
- inversion f.
- apply one_ps_r.
  exists nil ; exists ione...
- apply bot_ps_r...
  apply IHHll.
  inversion H ; subst ; destruct H2 as [D [Ht | Ht]] ;
    destruct D ; inversion Ht ; subst.
  rewrite Ht in Hc0.
  eapply (cperm_PCperm false) in Hc0.
  eapply uniq_not_jfragment_jsequent in Hc0...
  destruct Hc0 as (l1 & l2 & HP1 & HP2).
  exists (l1 ++ l2) ; exists C0.
  simpl in HP1 ; simpl in HP2 ; subst.
  list_simpl ; cperm_solve.
- inversion H ; subst ; destruct H2 as [D [Ht | Ht]] ;
    destruct D ; inversion Ht ; subst.
  + eapply (cperm_PCperm false) in Hc0.
    eapply uniq_jfragment_jsequent in Hc0...
    destruct Hc0 as [_ Hc0].
    rewrite <- ? map_rev in Hc0.
    apply PEperm_map_inv in Hc0.
    destruct Hc0 as (l3 & Heq & HP).
    symmetry in HP.
    apply PEperm_map_inv in HP.
    destruct HP as (l4 & Heq2 & HP) ; subst.
    decomp_map Heq.
    decomp_map Heq ; subst.
    apply tens_ps_r...
    * apply IHHll1...
    * apply IHHll2...
  + assert (Hc0' := Hc0).
    eapply (cperm_PCperm false) in Hc0'.
    eapply uniq_not_jfragment_jsequent in Hc0'...
    destruct Hc0' as (l3 & l4 & HP3 & _).
    simpl in HP3 ; dichot_app_exec HP3.
    * exfalso.
      clear - fz i2a_inj Hll2 HP0.
      rewrite <- ? map_rev in HP0.
      decomp_map HP0.
      decomp_map HP0 ; subst.
      apply ll_ps_j_has_jformula in Hll2.
      destruct Hll2 as (l1 & l2 & A & Heq).
      destruct l1 ; inversion Heq.
      -- apply ill2ll_not_dual in H0...
      -- symmetry in H1.
         eapply ill2ll_not_dual_elt...
    * destruct l5 ; subst.
      -- exfalso.
         apply ll_ps_j_has_jformula in Hll2.
         destruct Hll2 as (l2 & l5 & A & Heq).
         destruct l2 ; inversion Heq.
         ++ apply ill2ll_not_dual in H1...
         ++ symmetry in H2.
            rewrite <- ? map_rev in H2.
            rewrite app_nil_r in H2.
            eapply ill2ll_not_dual_elt...
      -- inversion HP1 ; subst.
         rewrite <- ? map_rev in H2.
         decomp_map H2.
         decomp_map H2 ; subst.
         apply tens_ps_r...
         ++ apply IHHll1.
            rewrite bidual...
         ++ apply IHHll2.
            exists (l3 ++ D2 :: rev l7) ; exists C0.
            list_simpl ; cperm_solve.
  + assert (Hc0' := Hc0).
    eapply (cperm_PCperm false) in Hc0'.
    eapply uniq_not_jfragment_jsequent in Hc0'...
    destruct Hc0' as (l3 & l4 & HP3 & _).
    simpl in HP3 ; dichot_app_exec HP3.
    * rewrite <- ? map_rev in HP0.
      decomp_map HP0.
      decomp_map HP0 ; subst.
      apply tens_ps_r...
      -- apply IHHll1.
         exists (rev l9 ++ D2 :: l4) ; exists C0.
         list_simpl ; cperm_solve.
      -- apply IHHll2.
         rewrite bidual...
    * destruct l5 ; subst.
      -- simpl in HP1 ; subst.
         apply tens_ps_r...
         ++ apply IHHll1.
            exists (D2 :: l4) ; exists C0.
            list_simpl ; cperm_solve.
         ++ apply IHHll2.
            rewrite bidual.
            list_simpl... 
      -- exfalso.
         apply ll_ps_j_has_jformula in Hll1.
         inversion HP1.
         rewrite <- ? map_rev in H2.
         decomp_map H2.
         decomp_map H2 ; subst.
         destruct Hll1 as (l1 & l2 & A & Hll1).
         change (dual (ill2ll D2) :: map dual (map ill2ll l8))
           with (map dual (map ill2ll (D2 :: l8))) in Hll1.
         symmetry in Hll1.
         eapply ill2ll_not_dual_elt...
- apply parr_ps_r...
  apply IHHll.
  inversion H ; subst ; destruct H2 as [D [Ht | Ht]] ;
    destruct D ; inversion Ht ; subst.
  + eapply (cperm_PCperm false) in Hc0.
    eapply uniq_jfragment_jsequent in Hc0...
    destruct Hc0 as [_ Hc0] ; simpl in Hc0 ; subst.
    exists (l0 ++ D1 :: nil) ; exists D2.
    list_simpl...
  + eapply (cperm_PCperm false) in Hc0.
    eapply uniq_jfragment_jsequent in Hc0...
    destruct Hc0 as [_ Hc0] ; simpl in Hc0 ; subst.
    exists (D1 :: l0) ; exists D2.
    list_simpl ; cperm_solve.
  + eapply (cperm_PCperm false) in Hc0.
    eapply uniq_not_jfragment_jsequent in Hc0...
    simpl in Hc0.
    destruct Hc0 as (l1 & l2 & Hc1 & Hc2) ; subst.
    exists (l1 ++ D1 :: D2 :: l2) ; exists C0.
    list_simpl ; cperm_solve.
- apply top_ps_r...
- apply plus_ps_r1...
  apply IHHll.
  inversion H ; subst.
  destruct H2 as [D [Ht | Ht]] ; destruct D ; inversion Ht ; subst.
  + eapply (cperm_PCperm false) in Hc0.
    eapply uniq_jfragment_jsequent in Hc0...
    destruct Hc0 as [_ Hc0] ; simpl in Hc0 ; subst.
    list_simpl...
  + eapply (cperm_PCperm false) in Hc0.
    eapply uniq_not_jfragment_jsequent in Hc0...
    simpl in Hc0.
    destruct Hc0 as (l1 & l2 & Hc1 & Hc2) ; subst.
    exists (l1 ++ D1 :: l2) ; exists C0.
    list_simpl ; cperm_solve.
- apply plus_ps_r2...
  apply IHHll.
  inversion H ; subst.
  destruct H2 as [D [Ht | Ht]] ; destruct D ; inversion Ht ; subst.
  + eapply (cperm_PCperm false) in Hc0.
    eapply uniq_jfragment_jsequent in Hc0...
    destruct Hc0 as [_ Hc0] ; simpl in Hc0 ; subst.
    list_simpl...
  + eapply (cperm_PCperm false) in Hc0.
    eapply uniq_not_jfragment_jsequent in Hc0...
    simpl in Hc0.
    destruct Hc0 as (l1 & l2 & Hc1 & Hc2) ; subst.
    exists (l1 ++ D2 :: l2) ; exists C0.
    list_simpl ; cperm_solve.
- apply with_ps_r...
  + apply IHHll1.
    inversion H ; subst.
    destruct H2 as [D [Ht | Ht]] ; destruct D ; inversion Ht ; subst.
    * eapply (cperm_PCperm false) in Hc0.
      eapply uniq_jfragment_jsequent in Hc0...
      destruct Hc0 as [_ Hc0] ; simpl in Hc0 ; subst.
      list_simpl...
    * eapply (cperm_PCperm false) in Hc0.
      eapply uniq_not_jfragment_jsequent in Hc0...
      simpl in Hc0.
      destruct Hc0 as (l1 & l2 & Hc1 & Hc2) ; subst.
      exists (l1 ++ D1 :: l2) ; exists C0.
      list_simpl ; cperm_solve.
  + apply IHHll2.
    inversion H ; subst.
    destruct H2 as [D [Ht | Ht]] ; destruct D ; inversion Ht ; subst.
    * eapply (cperm_PCperm false) in Hc0.
      eapply uniq_jfragment_jsequent in Hc0...
      destruct Hc0 as [_ Hc0] ; simpl in Hc0 ; subst.
      list_simpl...
    * eapply (cperm_PCperm false) in Hc0.
      eapply uniq_not_jfragment_jsequent in Hc0...
      simpl in Hc0.
      destruct Hc0 as (l1 & l2 & Hc1 & Hc2) ; subst.
      exists (l1 ++ D2 :: l2) ; exists C0.
      list_simpl ; cperm_solve.
- apply oc_ps_r...
  apply IHHll.
  inversion H ; subst.
  destruct H2 as [D [Ht | Ht]] ; destruct D ; inversion Ht ; subst.
  eapply (cperm_PCperm false) in Hc0.
  eapply uniq_jfragment_jsequent in Hc0...
  destruct Hc0 as [_ Hc0].
  rewrite Hc0.
  list_simpl...
- apply de_ps_r...
  apply IHHll.
  inversion H ; subst.
  destruct H2 as [D [Ht | Ht]] ; destruct D ; inversion Ht ; subst.
  eapply (cperm_PCperm false) in Hc0.
  eapply uniq_not_jfragment_jsequent in Hc0...
  simpl in Hc0.
  destruct Hc0 as (l1 & l2 & Hc1 & Hc2) ; subst.
  exists (l1 ++ D :: l2) ; exists C0.
  list_simpl ; cperm_solve.
- apply wk_ps_r...
  apply IHHll.
  inversion H ; subst.
  destruct H2 as [D [Ht | Ht]] ; destruct D ; inversion Ht ; subst.
  eapply (cperm_PCperm false) in Hc0.
  eapply uniq_not_jfragment_jsequent in Hc0...
  simpl in Hc0.
  destruct Hc0 as (l1 & l2 & Hc1 & Hc2) ; subst.
  exists (l1 ++ l2) ; exists C0.
  list_simpl ; cperm_solve.
- apply co_ps_r...
  apply IHHll.
  inversion H ; subst.
  destruct H2 as [D [Ht | Ht]] ; destruct D ; inversion Ht ; subst.
  eapply (cperm_PCperm false) in Hc0.
  eapply uniq_not_jfragment_jsequent in Hc0...
  simpl in Hc0.
  destruct Hc0 as (l1 & l2 & Hc1 & Hc2) ; subst.
  assert (exists l' l'' l''', map wn lw = rev (map dual (map ill2ll l'))
                      /\ l = rev (map dual (map ill2ll (l''))) ++ ill2ll C0 ::
                             rev (map dual (map ill2ll (l'''))))
    as (l' & l'' & l''' & Heq1 & Heq2).
  { clear - Hc1.
    revert lw l l2 Hc1 ; induction l1 using rev_ind ; intros lw l l2 H.
    - destruct lw.
      + exists nil ; exists nil ; exists l2 ; split...
      + inversion H.
        destruct C0 ; inversion H1.
    - destruct lw.
      + exists nil ; exists (l1 ++ x :: nil) ; exists l2 ; split...
      + inversion H.
        rewrite <- ? map_rev in H.
        rewrite rev_unit in H ; simpl in H.
        rewrite ? map_rev in H.
        inversion H.
        apply IHl1 in H3.
        destruct H3 as (l' & l'' & l''' & Heq1 & Heq2).
        simpl ; rewrite H2 ; rewrite Heq1.
        exists (l' ++ x :: nil) ; exists l'' ; exists l''' ; split...
        list_simpl... }
  subst.
  rewrite Heq1.
  exists (l'' ++ ioc D :: l' ++ ioc D :: l''') ; exists C0.
  list_simpl ; cperm_solve.
- apply jsequent_app in Hc.
  destruct Hc as [l' [[Heq Hi] | [Hi Heq]]] ; subst.
  + assert (Hll := Hll1).
    apply ll_ps_is_ps in Hll.
    inversion Hll ; subst.
    destruct H2 as [D [Ht | Ht]] ; subst.
    * apply (@cut_ps_r _ _ f A).
      -- apply cperm_perm in Hc0.
         eapply (PCperm_jsequent true)...
      -- apply IHHll1.
         rewrite Ht...
      -- apply IHHll2.
         rewrite <- (bidual A).
         rewrite Ht.
         destruct Hi as (l0' & C0' & Heq).
         eapply (PCperm_jsequent true)...
         apply cperm_perm in Heq.
         apply (@Permutation_cons _ _ (dual (ill2ll D)) eq_refl) in Heq.
         etransitivity ; [ apply Heq | ].
         etransitivity ; [ apply perm_swap | ].
         apply Permutation_cons...
         replace (dual (ill2ll D) :: rev (map dual (map ill2ll l0')))
           with (rev (map dual (map ill2ll (l0' ++ D :: nil))))...
         list_simpl...
    * exfalso.
      apply ll_ps_j_has_jformula in Hll1.
      destruct Hll1 as (l1 & l3 & C & Heq).
      rewrite Ht in Heq.
      change (dual (ill2ll D) :: map dual (map ill2ll l'))
        with (map dual (map ill2ll (D :: l'))) in Heq.
      symmetry in Heq.
      eapply ill2ll_not_dual_elt...
  + assert (Hll := Hll1).
    apply ll_ps_is_ps in Hll.
    inversion Hll ; subst.
    destruct H2 as [D [Ht | Ht]] ; subst.
    * exfalso.
      apply ll_ps_j_has_jformula in Hll2.
      destruct Hll2 as (l2 & l3 & C & Heq2).
      rewrite <- (bidual A) in Heq2.
      rewrite Ht in Heq2.
      change (dual (ill2ll D) :: map dual (map ill2ll l'))
            with (map dual (map ill2ll (D :: l'))) in Heq2.
      symmetry in Heq2.
      eapply ill2ll_not_dual_elt...
    * apply (@cut_ps_r _ _ f A).
      -- apply cperm_perm in Hc0.
         eapply (PCperm_jsequent true)...
      -- apply IHHll1.
         destruct Heq as (l0' & C0' & Heq).
         rewrite Ht.
         eapply (PCperm_jsequent true)...
         apply cperm_perm in Heq.
         apply (@Permutation_cons _ _ (dual (ill2ll D)) eq_refl) in Heq.
         etransitivity ; [ apply Heq | ].
         etransitivity ; [ apply perm_swap | ].
         apply Permutation_cons...
         replace (dual (ill2ll D) :: rev (map dual (map ill2ll l0')))
           with (rev (map dual (map ill2ll (l0' ++ D :: nil))))...
         list_simpl...
      -- apply IHHll2.
         rewrite <- (bidual A).
         rewrite Ht.
         rewrite bidual...
- apply gax_ps_r...
Qed.

Lemma ll_ps_j_is_ll_ps_jsequent_topfree {P} : iftop = false -> forall l,
  ll_ps (i2pfrag P) (Forall jfragment) l -> ll_ps (i2pfrag P) jsequent l.
Proof with myeeasy ; try PCperm_solve.
intros ft l Hll.
induction Hll ;
  try (assert (Hc := IHHll) ; apply ll_ps_is_ps in Hc) ;
  try (assert (Hc1 := IHHll1) ; apply ll_ps_is_ps in Hc1) ;
  try (assert (Hc2 := IHHll2) ; apply ll_ps_is_ps in Hc2).
- apply ax_ps_r.
  inversion H ; subst.
  inversion H2.
  destruct H0 ; destruct x ; inversion H0 ; subst...
  exists (ivar i :: nil) ; exists (ivar i).
  cperm_solve.
- eapply ex_ps_r...
  destruct Hc as (l0 & C & Hc). 
  eapply cperm_PCperm in Hc.
  symmetry in H0.
  eapply PCperm_jsequent.
  etransitivity...
- inversion f.
- inversion f.
- apply one_ps_r.
  exists nil ; exists ione...
- apply bot_ps_r...
  apply (jsequent_PCperm true) in Hc.
  destruct Hc as (l0 & C & Hc).
  inversion H ; subst ; destruct H2 as [D [Hi | Hi]] ;
    destruct D ; inversion Hi ; subst ;
    rewrite Hi.
  apply (PCperm_jsequent true _ (ione :: l0) C)...
- apply tens_ps_r...
  inversion H ; subst ; destruct H2 as [D [Hi | Hi]] ;
    destruct D ; inversion Hi ; subst ;
    rewrite Hi.
  + apply (jsequent_PCperm false) in Hc1.
    destruct Hc1 as (l1' & C1 & Hc1).
    eapply uniq_jfragment_jsequent in Hc1...
    destruct Hc1 as [_ Hc1].
    rewrite <- ? map_rev in Hc1.
    apply PEperm_map_inv in Hc1.
    destruct Hc1 as (l3 & Heq & HP).
    symmetry in HP.
    apply PEperm_map_inv in HP.
    destruct HP as (l4 & Heq2 & HP) ; subst.
    apply (jsequent_PCperm false) in Hc2.
    destruct Hc2 as (l2' & C2 & Hc2).
    eapply uniq_jfragment_jsequent in Hc2...
    destruct Hc2 as [_ Hc2].
    rewrite <- ? map_rev in Hc2.
    apply PEperm_map_inv in Hc2.
    destruct Hc2 as (l3 & Heq & HP2).
    symmetry in HP2.
    apply PEperm_map_inv in HP2.
    destruct HP2 as (l5 & Heq2 & HP2) ; subst.
    rewrite <- ? map_app.
    apply is_jsequent.
  + rewrite bidual in Hc1.
    apply (jsequent_PCperm false) in Hc1.
    destruct Hc1 as (l1' & C1 & Hc1).
    eapply uniq_jfragment_jsequent in Hc1...
    destruct Hc1 as [_ Hc1].
    rewrite <- ? map_rev in Hc1.
    apply PEperm_map_inv in Hc1.
    destruct Hc1 as (l3 & Heq & HP).
    symmetry in HP.
    apply PEperm_map_inv in HP.
    destruct HP as (l4 & Heq2 & HP) ; subst.
    apply (jsequent_PCperm false) in Hc2.
    destruct Hc2 as (l2' & C2 & Hc2).
    eapply uniq_not_jfragment_jsequent in Hc2...
    destruct Hc2 as (l5 & l6 & HP2 & _).
    apply (PCperm_jsequent true _
                           (rev l4 ++ @ilmap D1 D2 :: l5 ++ l6) C2).
    simpl in HP2 ; subst ; list_simpl ; perm_solve.
  + rewrite bidual in Hc2.
    apply (jsequent_PCperm false) in Hc2.
    destruct Hc2 as (l2' & C2 & Hc2).
    eapply uniq_jfragment_jsequent in Hc2...
    destruct Hc2 as [_ Hc2].
    rewrite <- ? map_rev in Hc2.
    apply PEperm_map_inv in Hc2.
    destruct Hc2 as (l3 & Heq & HP).
    symmetry in HP.
    apply PEperm_map_inv in HP.
    destruct HP as (l4 & Heq2 & HP) ; subst.
    apply (jsequent_PCperm false) in Hc1.
    destruct Hc1 as (l1' & C1 & Hc1).
    eapply uniq_not_jfragment_jsequent in Hc1...
    destruct Hc1 as (l5 & l6 & HP2 & _).
    apply (PCperm_jsequent true _
                           (rev l4 ++ @ilpam D1 D2 :: l5 ++ l6) C1).
    simpl in HP2 ; subst ; list_simpl ; perm_solve.
- apply parr_ps_r...
  inversion H ; subst ; destruct H2 as [D [Hi | Hi]] ;
    destruct D ; inversion Hi ; subst ;
    rewrite Hi.
  + apply (jsequent_PCperm false) in Hc.
    destruct Hc as (l0 & C & Hc).
    eapply uniq_jfragment_jsequent in Hc...
    destruct Hc as [_ Hc] ; simpl in Hc.
    destruct l0 using rev_ind ; list_simpl in Hc ; inversion Hc ; subst.
    apply is_jsequent.
  + apply (jsequent_PCperm false) in Hc.
    destruct Hc as (l0 & C & Hc).
    apply (cperm_trans (ill2ll D2 :: l ++ dual (ill2ll D1) :: nil))
      in Hc ; [ | rewrite app_comm_cons ; symmetry ; apply cperm_last ].
    apply (cperm_PCperm false) in Hc.
    eapply uniq_jfragment_jsequent in Hc...
    destruct Hc as [_ Hc] ; simpl in Hc.
    destruct l0.
    * exfalso.
      destruct l ; inversion Hc.
    * list_simpl in Hc.
      assert (Heq := eq_refl (rev (l ++ dual (ill2ll D1) :: nil))).
      rewrite Hc in Heq at 1.
      list_simpl in Heq.
      inversion Heq.
      rewrite <- (rev_involutive l).
      rewrite <- H2.
      rewrite <- ? map_rev.
      apply is_jsequent.
  + assert (Hc' := Hc).
    apply (jsequent_PCperm false) in Hc.
    destruct Hc as (l0 & C & Hc).
    eapply uniq_not_jfragment_jsequent in Hc...
    simpl in Hc.
    destruct Hc as (l1 & l2 & Hc1 & Hc2) ; subst.
    destruct l1 using rev_ind.
    * exfalso.
      inversion Hc1.
      apply ill2ll_not_dual in H1...
    * list_simpl in Hc1.
      inversion Hc1 ; subst.
      exists (l1 ++ itens D1 D2 :: l2) ; exists C.
      list_simpl...
- inversion H ; inversion H2 ; inversion H4 ;
    destruct x0 ; inversion H5.
  + rewrite ft0 in ft ; inversion ft.
  + rewrite fz0 in fz ; inversion fz.
- apply plus_ps_r1...
  inversion H ; subst ; destruct H2 as [D [Hi | Hi]] ;
    destruct D ; inversion Hi ; subst ;
    rewrite Hi.
  + apply (jsequent_PCperm true) in Hc.
    destruct Hc as (l0 & C & Hc).
    eapply uniq_jfragment_jsequent in Hc...
    destruct Hc as [_ Hc] ; simpl in Hc.
    apply (PCperm_jsequent true _ l0 (iplus D1 D2))...
  + apply (jsequent_PCperm false) in Hc.
    destruct Hc as (l0 & C & Hc).
    eapply uniq_not_jfragment_jsequent in Hc...
    simpl in Hc.
    destruct Hc as (l1 & l2 & Hc1 & Hc2) ; subst.
    exists (l1 ++ iwith D1 D2 :: l2) ; exists C.
    list_simpl...
- apply plus_ps_r2...
  inversion H ; subst ; destruct H2 as [D [Hi | Hi]] ;
    destruct D ; inversion Hi ; subst ;
    rewrite Hi.
  + apply (jsequent_PCperm true) in Hc.
    destruct Hc as (l0 & C & Hc).
    eapply uniq_jfragment_jsequent in Hc...
    destruct Hc as [_ Hc] ; simpl in Hc.
    apply (PCperm_jsequent true _ l0 (iplus D1 D2))...
  + apply (jsequent_PCperm false) in Hc.
    destruct Hc as (l0 & C & Hc).
    eapply uniq_not_jfragment_jsequent in Hc...
    simpl in Hc.
    destruct Hc as (l1 & l2 & Hc1 & Hc2) ; subst.
    exists (l1 ++ iwith D1 D2 :: l2) ; exists C.
    list_simpl...
- apply with_ps_r...
  inversion H ; subst ; destruct H2 as [D [Hi | Hi]] ;
    destruct D ; inversion Hi ; subst ;
    rewrite Hi.
  + apply (jsequent_PCperm true) in Hc1.
    destruct Hc1 as (l0 & C & Hc).
    eapply uniq_jfragment_jsequent in Hc...
    destruct Hc as [_ Hc] ; simpl in Hc.
    apply (PCperm_jsequent true _ l0 (iwith D1 D2))...
  + apply (jsequent_PCperm false) in Hc1.
    destruct Hc1 as (l0 & C & Hc).
    eapply uniq_not_jfragment_jsequent in Hc...
    simpl in Hc.
    destruct Hc as (l1 & l2 & Hc1 & _) ; subst.
    exists (l1 ++ iplus D1 D2 :: l2) ; exists C.
    list_simpl...
- apply oc_ps_r...
  inversion H ; subst ; destruct H2 as [D [Hi | Hi]] ;
    destruct D ; inversion Hi ; subst ;
    rewrite Hi.
  apply (jsequent_PCperm true) in Hc.
  destruct Hc as (l0 & C & Hc).
  eapply uniq_jfragment_jsequent in Hc...
  destruct Hc as [_ Hc] ; simpl in Hc.
  apply (PCperm_jsequent true _ l0 (ioc D))...
- apply de_ps_r...
  inversion H ; subst ; destruct H2 as [D [Hi | Hi]] ;
    destruct D ; inversion Hi ; subst ;
    rewrite Hi.
  apply (jsequent_PCperm false) in Hc.
  destruct Hc as (l0 & C & Hc).
  eapply uniq_not_jfragment_jsequent in Hc...
  simpl in Hc.
  destruct Hc as (l1 & l2 & Hc1 & _) ; subst.
  exists (l1 ++ ioc D :: l2) ; exists C.
  list_simpl...
- apply wk_ps_r...
  apply (jsequent_PCperm true) in Hc.
  destruct Hc as (l0 & C & Hc).
  inversion H ; subst ; destruct H2 as [D [Hi | Hi]] ;
    destruct D ; inversion Hi ; subst ;
    rewrite Hi.
  apply (PCperm_jsequent true _ (ioc D :: l0) C)...
- apply co_ps_r...
  inversion H ; subst ; destruct H2 as [D [Hi | Hi]] ;
    destruct D ; inversion Hi ; subst ;
    rewrite Hi.
  apply (jsequent_PCperm false) in Hc.
  destruct Hc as (l0 & C & Hc).
  eapply uniq_not_jfragment_jsequent in Hc...
  simpl in Hc.
  destruct Hc as (l1 & l2 & Hc1 & _) ; subst.
  apply (PCperm_jsequent true _ (l1 ++ l2) C).
  etransitivity ; [ apply Permutation_middle | ].
  simpl ; rewrite Hc1...
- apply (@cut_ps_r _ _ f A)...
  apply ll_ps_is_ps in Hll2.
  inversion Hll2 ; subst.
  destruct H2 as [C [Hi | Hi]] ; subst.
  + apply (jsequent_PCperm false) in Hc1.
    destruct Hc1 as (l0 & C1 & Hc1).
    eapply uniq_not_jfragment_jsequent in Hc1...
    simpl in Hc1.
    destruct Hc1 as (l1' & l2' & Hc1 & _) ; subst.
    apply (jsequent_PCperm false) in Hc2.
    destruct Hc2 as (l0' & C2 & Hc2).
    eapply uniq_jfragment_jsequent in Hc2...
    destruct Hc2 as [_ Hc2] ; simpl in Hc2 ; subst.
    apply (PCperm_jsequent true _ (l0' ++ l1' ++ l2') C1).
    list_simpl...
  + apply (jsequent_PCperm false) in Hc2.
    destruct Hc2 as (l0' & C2 & Hc2).
    eapply uniq_not_jfragment_jsequent in Hc2...
    simpl in Hc2.
    destruct Hc2 as (l1' & l2' & Hc2 & _) ; subst.
    rewrite bidual in Hc1.
    apply (jsequent_PCperm false) in Hc1.
    destruct Hc1 as (l0 & C1 & Hc1).
    eapply uniq_jfragment_jsequent in Hc1...
    destruct Hc1 as [_ Hc1] ; simpl in Hc1 ; subst.
    apply (PCperm_jsequent true _ (l0 ++ l1' ++ l2') C2).
    list_simpl...
- apply gax_ps_r...
  destruct H0 as (l0 & C & H0 & _) ; subst.
  rewrite <- ? map_rev.
  apply is_jsequent.
Qed.

(** [jsequent] implies image of [ill] *)
Lemma ll_ps_jsequent_is_ill {P} : forall l,
  ll_ps (i2pfrag P) jsequent l -> forall l0 C,
    PCperm (pperm (i2pfrag P)) l (ill2ll C :: rev (map dual (map ill2ll l0))) ->
      exists s, ill P l0 C s.
Proof with myeeasy.
intros l Hll ; induction Hll ; intros l0 C HP.
- eexists.
  assert (Hi := jsequent_is_jfragment _ H).
  inversion Hi ; subst.
  inversion H2.
  destruct H0 ; destruct x ; inversion H0 ; subst.
  apply (PCperm_trans _ (ill2ll (ivar i) ::
                          rev (map dual (map ill2ll (ivar i :: nil))))) in HP ;
    [ | apply PCperm_swap ].
  apply uniq_jsequent in HP.
  destruct HP as [Heq1 Heq2] ; subst.
  eapply ex_ir...
  apply ax_ir.
- apply IHHll.
  etransitivity...
- exfalso ; apply PCperm_nil_cons in HP...
- inversion f.
- change nil with (rev (map dual (map ill2ll nil))) in HP.
  apply jsequent_is_jfragment in H.
  inversion H.
  inversion H2.
  destruct H4 as [H4 | H4] ; destruct x0 ; inversion H4.
  rewrite H4 in HP.
  apply uniq_jsequent in HP.
  destruct HP as [Heq1 Heq2].
  apply PEperm_nil in Heq2 ; subst.
  eexists.
  apply one_irr.
- eapply (uniq_not_jfragment_jsequent _ _ _ _ ione) in HP ; [ | now simpl ].
  destruct HP as (l1 & l2 & HP1 & HP2).
  apply PEperm_PCperm in HP1.
  symmetry in HP1.
  eapply (PCperm_trans _ _ _ _) in HP1 ; [ | apply PCperm_app_comm ].
  symmetry in HP1.
  rewrite <- app_comm_cons in HP1.
  rewrite <- rev_app_distr in HP1.
  rewrite <- ? map_app in HP1.
  apply IHHll in HP1.
  destruct HP1 as [s pi].
  eexists.
  apply PEperm_rev in HP2.
  rewrite ? rev_app_distr in HP2.
  simpl in HP2.
  rewrite <- ? map_rev in HP2.
  rewrite ? rev_involutive in HP2.
  change (bot :: nil) with (map dual (map ill2ll (ione :: nil))) in HP2.
  rewrite <- app_assoc in HP2.
  rewrite <- ? map_app in HP2.
  rewrite <- app_comm_cons in HP2.
  rewrite app_nil_l in HP2.
  apply PEperm_map_inv_inj in HP2 ; [ | apply dual_inj ].
  apply PEperm_map_inv_inj in HP2 ; [ | apply ill2ll_inj ].
  eapply ex_ir ; [ | apply HP2 ].
  apply one_ilr...
- apply jsequent_is_jfragment in H.
  inversion H ; subst ; destruct H2 as [D [Ht | Ht]] ;
    destruct D ; inversion Ht ; subst.
  + eapply uniq_jfragment_jsequent in HP...
    destruct HP as [Heq HP].
    destruct C ; inversion Heq.
    apply ill2ll_inj in H1.
    apply ill2ll_inj in H2 ; subst.
    rewrite <- ? map_rev in HP.
    apply PEperm_map_inv in HP.
    destruct HP as (l3 & Heq1 & HP1).
    symmetry in HP1.
    apply PEperm_map_inv in HP1.
    destruct HP1 as (l4 & Heq2 & HP2) ; subst.
    decomp_map Heq1.
    decomp_map Heq1 ; subst.
    specialize IHHll1 with (rev l7) C1.
    rewrite <- ? map_rev in IHHll1.
    rewrite rev_involutive in IHHll1.
    assert (pi1 := IHHll1 (PCperm_refl _ _)).
    destruct pi1 as [s1 pi1].
    specialize IHHll2 with (rev l6) C2.
    rewrite <- ? map_rev in IHHll2.
    rewrite rev_involutive in IHHll2.
    assert (pi2 := IHHll2 (PCperm_refl _ _)).
    destruct pi2 as [s2 pi2].
    eexists.
    rewrite <- (rev_involutive l0).
    apply PEperm_rev in HP2.
    symmetry in HP2.
    eapply ex_ir...
    rewrite rev_app_distr.
    apply tens_irr...
  + eapply uniq_not_jfragment_jsequent in HP...
    destruct HP as (l1' & l2' & Heq1 & Heq0).
    assert (HP := Heq1).
    apply PEperm_vs_elt_inv in Heq1.
    destruct Heq1 as (l3 & l4 & Heq1).
    dichot_elt_app_exec Heq1 ; subst.
    * assert (PEperm (ipperm P) (l1' ++ ilmap D1 D2 :: l2') l0) as Hl0.
      { clear - fz i2a_inj Heq0.
        apply (PEperm_map_inv_inj _ ill2ll) ; [ apply ill2ll_inj | ].
        apply (PEperm_map_inv_inj _ dual) ; [ apply dual_inj | ].
        list_simpl.
        apply PEperm_rev in Heq0.
        list_simpl in Heq0... }
      rewrite <- ? app_assoc in HP.
      rewrite <- ? app_comm_cons in HP.
      hyps_PEperm_unfold ; simpl in IHHll1 ; simpl in IHHll2 ; simpl in HP ;
        case_eq (ipperm P) ; intros Heqb ; rewrite_all Heqb.
      -- apply (Permutation_trans (Permutation_app_comm _ _)) in HP.
         rewrite <- ? app_comm_cons in HP.
         apply Permutation_cons_app_inv in HP.
         rewrite <- ? map_rev in HP.
         apply (Permutation_trans (Permutation_app_comm _ _)) in HP.
         rewrite app_assoc in HP.
         apply Permutation_app_app_inv in HP.
         destruct HP
           as (l3' & l3'' & l4' & l4'' & Heq1' & Heq2' & Heq3' & Heq4').
         symmetry in Heq3'.
         apply Permutation_map_inv in Heq3'.
         destruct Heq3' as (l6 & Heq6 & HP6).
         symmetry in HP6.
         apply Permutation_map_inv in HP6.
         destruct HP6 as (l6' & Heq6' & HP6) ; subst.
         decomp_map Heq6.
         decomp_map Heq6 ; subst.
         symmetry in Heq4'.
         apply Permutation_map_inv in Heq4'.
         destruct Heq4' as (l8 & Heq8 & HP8).
         symmetry in HP8.
         apply Permutation_map_inv in HP8.
         destruct HP8 as (l8' & Heq8' & HP8) ; subst.
         decomp_map Heq8.
         decomp_map Heq8 ; subst.
         rewrite <- ? map_app in Heq2'.
         apply (@Permutation_cons _ _ (ill2ll D1) eq_refl) in Heq2'.
         rewrite <- (rev_involutive (l7 ++ l9)) in Heq2'.
         rewrite 2 map_rev in Heq2'.
         rewrite bidual in IHHll1.
         apply IHHll1 in Heq2'.
         destruct Heq2' as [s1 pi1].
         rewrite <- ? map_app in Heq1'.
         apply (@Permutation_cons _ _ (dual (ill2ll D2)) eq_refl) in Heq1'.
         symmetry in Heq1'.
         rewrite app_comm_cons in Heq1'.
         apply (Permutation_cons_app _ _ (ill2ll C)) in Heq1'.
         symmetry in Heq1'.
         rewrite <- (rev_involutive (l6 ++ l8)) in Heq1'.
         rewrite 2 map_rev in Heq1'.
         replace (dual (ill2ll D2) ::
                   rev (map dual (map ill2ll (rev (l6 ++ l8)))))
           with (rev (map dual (map ill2ll (rev (D2 :: l6 ++ l8)))))
           in Heq1' by (list_simpl ; myeasy).
         apply IHHll2 in Heq1'.
         destruct Heq1' as [s2 pi2].
         eexists.
         eapply ex_ir ; [ | rewrite Heqb ; apply Hl0 ].
         assert (Permutation (rev l8 ++ ilmap D1 D2 :: 
                         (rev l9 ++ rev l7) ++ rev l6)
                (l1' ++ ilmap D1 D2 :: l2'))
           as HP10.
         { apply Permutation_rev' in HP8.
           rewrite rev_involutive in HP8.
           apply (@Permutation_cons _ _ (ilmap D1 D2) eq_refl) in HP8.
           apply (Permutation_app_head l1') in HP8.
           symmetry in HP8.
           etransitivity ; [ | apply HP8 ].
           apply Permutation_rev' in HP6.
           rewrite rev_involutive in HP6.
           apply (Permutation_app_tail (ilmap D1 D2 :: rev (l8 ++ l9))) in HP6.
           symmetry in HP6.
           etransitivity ; [ | apply HP6 ].
           list_simpl ; perm_solve. }
         eapply ex_ir ; [ | rewrite Heqb ; apply HP10 ].
         rewrite rev_app_distr in pi1.
         apply lmap_ilr...
         eapply ex_ir ; [ apply pi2 | rewrite Heqb ].
         list_simpl ; perm_solve.
      -- dichot_elt_app_exec HP.
         ++ exfalso.
            rewrite <- ? map_rev in HP0.
            eapply ill2ll_not_dual_elt...
         ++ destruct l4 ; inversion HP1 ; subst.
            ** rewrite <- ? map_rev in H1.
               decomp_map H1.
               decomp_map H1 ; subst.
               specialize IHHll1 with (rev l5) D1.
               rewrite bidual in IHHll1.
               rewrite <- ? map_rev in IHHll1.
               rewrite rev_involutive in IHHll1.
               assert (pi1 := IHHll1 (cperm_refl _)).
               destruct pi1 as [s1 pi1].
               specialize IHHll2 with (l1' ++ D2 :: rev l4) C.
               rewrite <- ? map_rev in IHHll2.
               rewrite rev_app_distr in IHHll2.
               simpl in IHHll2.
               rewrite rev_involutive in IHHll2.
               rewrite ? map_app in IHHll2 ; simpl in IHHll2.
               rewrite <- ? app_assoc in IHHll2.
               rewrite <- ? app_comm_cons in IHHll2 ; simpl in IHHll2.
               rewrite ? app_comm_cons in IHHll2.
               assert (pi2 := IHHll2 (cperm _ _)).
               destruct pi2 as [s2 pi2].
               eexists.
               inversion HP1.
               rewrite <- ? map_app in H2.
               rewrite <- ? map_rev in H2.
               apply (map_inj dual) in H2 ; [ | apply dual_inj ].
               apply (map_inj ill2ll) in H2 ; [ | apply ill2ll_inj ].
               rewrite <- (rev_involutive l2').
               rewrite <- H1.
               rewrite rev_app_distr.
               apply lmap_ilr...
            ** exfalso.
               rewrite <- ? map_rev in H2.
               eapply ill2ll_not_dual_elt...
    * exfalso ; clear - fz i2a_inj Hll1.
      apply ll_ps_is_ps in Hll1.
      destruct Hll1 as (l' & C0 & HP).
      rewrite bidual in HP.
      apply (cperm_PCperm true) in HP.
      apply (uniq_jfragment_jsequent _ _ _ _ D1) in HP...
      destruct HP as [_ HP].
      rewrite <- ? map_rev in HP.
      symmetry in HP.
      apply PEperm_vs_elt_inv in HP.
      destruct HP as (l2 & l3 & HP).
      symmetry in HP.
      eapply ill2ll_not_dual_elt...
  + eapply uniq_not_jfragment_jsequent in HP...
    destruct HP as (l1' & l2' & Heq1 & Heq0).
    assert (HP := Heq1).
    apply PEperm_vs_elt_inv in Heq1.
    destruct Heq1 as (l3 & l4 & Heq1).
    dichot_elt_app_exec Heq1 ; subst.
    * exfalso ; clear - fz i2a_inj Hll2.
      apply ll_ps_is_ps in Hll2.
      destruct Hll2 as (l' & C0 & HP).
      rewrite bidual in HP.
      apply (cperm_PCperm true) in HP.
      apply (uniq_jfragment_jsequent _ _ _ _ D1) in HP...
      destruct HP as [_ HP].
      rewrite <- ? map_rev in HP.
      symmetry in HP.
      apply PEperm_vs_elt_inv in HP.
      destruct HP as (l1 & l2 & HP).
      symmetry in HP.
      eapply ill2ll_not_dual_elt...
    * assert (PEperm (ipperm P) (l1' ++ ilpam D1 D2 :: l2') l0) as Hl0.
      { clear - fz i2a_inj Heq0.
        apply (PEperm_map_inv_inj _ ill2ll) ; [ apply ill2ll_inj | ].
        apply (PEperm_map_inv_inj _ dual) ; [ apply dual_inj | ].
        list_simpl.
        apply PEperm_rev in Heq0.
        list_simpl in Heq0... }
      rewrite <- ? app_assoc in HP.
      rewrite <- ? app_comm_cons in HP.
      hyps_PEperm_unfold ; simpl in IHHll1 ; simpl in IHHll2 ; simpl in HP ;
        case_eq (ipperm P) ; intros Heqb ; rewrite_all Heqb.
      -- rewrite app_assoc in HP.
         apply (Permutation_trans (Permutation_app_comm _ _)) in HP.
         rewrite <- ? app_comm_cons in HP.
         apply Permutation_cons_app_inv in HP.
         rewrite <- ? map_rev in HP.
         apply (Permutation_trans (Permutation_app_comm _ _)) in HP.
         rewrite <- app_assoc in HP.
         apply Permutation_app_app_inv in HP.
         destruct HP as (l3' & l3'' & l4' & l4'' & Heq1' & Heq2' & Heq3' & Heq4').
         symmetry in Heq3'.
         apply Permutation_map_inv in Heq3'.
         destruct Heq3' as (l6 & Heq6 & HP6).
         symmetry in HP6.
         apply Permutation_map_inv in HP6.
         destruct HP6 as (l6' & Heq6' & HP6) ; subst.
         decomp_map Heq6.
         decomp_map Heq6 ; subst.
         symmetry in Heq4'.
         apply Permutation_map_inv in Heq4'.
         destruct Heq4' as (l8 & Heq8 & HP8).
         symmetry in HP8.
         apply Permutation_map_inv in HP8.
         destruct HP8 as (l8' & Heq8' & HP8) ; subst.
         decomp_map Heq8.
         decomp_map Heq8 ; subst.
         rewrite <- ? map_app in Heq1'.
         apply (@Permutation_cons _ _ (ill2ll D1) eq_refl) in Heq1'.
         rewrite <- (rev_involutive (l6 ++ l8)) in Heq1'.
         rewrite 2 map_rev in Heq1'.
         rewrite bidual in IHHll2.
         apply IHHll2 in Heq1'.
         destruct Heq1' as [s1 pi1].
         rewrite <- ? map_app in Heq2'.
         apply (@Permutation_cons _ _ (dual (ill2ll D2)) eq_refl) in Heq2'.
         symmetry in Heq2'.
         rewrite app_comm_cons in Heq2'.
         apply (Permutation_cons_app _ _ (ill2ll C)) in Heq2'.
         symmetry in Heq2'.
         rewrite <- (rev_involutive (l7 ++ l9)) in Heq2'.
         rewrite 2 map_rev in Heq2'.
         replace (dual (ill2ll D2) ::
                    rev (map dual (map ill2ll (rev (l7 ++ l9)))))
           with (rev (map dual (map ill2ll (rev (D2 :: l7 ++ l9)))))
           in Heq2' by (list_simpl ; myeasy).
         apply IHHll1 in Heq2'.
         destruct Heq2' as [s2 pi2].
         eexists.
         eapply ex_ir ; [ | rewrite Heqb ; apply Hl0 ].
         assert (Permutation (rev l9 ++ rev (l6 ++ l8) ++ 
                         ilpam D1 D2 :: rev l7)
                (l1' ++ ilpam D1 D2 :: l2'))
           as HP10.
         { apply Permutation_rev' in HP8.
           rewrite rev_involutive in HP8.
           apply (@Permutation_cons _ _ (ilpam D1 D2) eq_refl) in HP8.
           apply (Permutation_app_head l1') in HP8.
           symmetry in HP8.
           etransitivity ; [ | apply HP8 ].
           apply Permutation_rev' in HP6.
           rewrite rev_involutive in HP6.
           apply (Permutation_app_tail (ilpam D1 D2 :: rev (l8 ++ l9))) in HP6.
           symmetry in HP6.
           etransitivity ; [ | apply HP6 ].
           list_simpl ; perm_solve. }
         eapply ex_ir ; [ | rewrite Heqb ; apply HP10 ].
         rewrite rev_app_distr in pi1.
         apply lpam_ilr...
         ++ eapply ex_ir ; [ apply pi1 | rewrite Heqb ].
            simpl ; rewrite ? rev_app_distr ; perm_solve.
         ++ simpl in pi2 ; rewrite ? rev_app_distr in pi2.
            eapply ex_ir ; [ apply pi2 | rewrite Heqb ; PEperm_solve ].
      -- dichot_elt_app_exec HP ; subst.
         ++ exfalso.
            rewrite <- ? map_rev in HP1.
            symmetry in HP1.
            rewrite app_assoc in HP1.
            eapply ill2ll_not_dual_elt...
         ++ symmetry in HP0.
            rewrite <- ? map_rev in HP0.
            decomp_map HP0.
            decomp_map HP0 ; subst.
            assert (map dual (map ill2ll l7) = l5
                   /\ rev (map dual (map ill2ll l2')) = l4)
              as [Heq1' Heq2'] ; subst.
            { clear - fz HP1.
              rewrite <- ? map_rev in HP1.
              rewrite <- ? map_rev.
              remember (rev l2') as l2 ; clear l2' Heql2.
              revert l2 l4 l7 HP1 ; induction l5 ; intros l2 l4 l7 H ;
                destruct l7 ; inversion H.
              - split...
              - exfalso.
                apply ill2ll_not_dual in H1...
              - exfalso.
                symmetry in H2.
                eapply ill2ll_not_dual_elt...
              - apply IHl5 in H2.
                destruct H2 ; subst.
                split... }
            specialize IHHll2 with (rev l6) D1.
            rewrite bidual in IHHll2.
            rewrite <- ? map_rev in IHHll2.
            rewrite rev_involutive in IHHll2.
            assert (pi1 := IHHll2 (cperm_refl _)).
            destruct pi1 as [s1 pi1].
            specialize IHHll1 with (rev l7 ++ D2 :: l2') C.
            rewrite <- ? map_rev in IHHll1.
            rewrite rev_app_distr in IHHll1.
            simpl in IHHll1.
            rewrite rev_involutive in IHHll1.
            rewrite ? map_app in IHHll1 ; simpl in IHHll1.
            rewrite <- ? app_assoc in IHHll1.
            rewrite <- ? app_comm_cons in IHHll1 ; simpl in IHHll1.
            rewrite ? app_comm_cons in IHHll1.
            assert (pi2 := IHHll1 (cperm _ _)).
            destruct pi2 as [s2 pi2].
            eexists.
            rewrite <- (rev_involutive l1').
            rewrite <- HP0.
            rewrite rev_app_distr.
            rewrite <- app_assoc.
            apply lpam_ilr...
- apply jsequent_is_jfragment in H.
  inversion H ; subst ; destruct H2 as [D [Ht | Ht]] ;
    destruct D ; inversion Ht ; subst.
  + eapply uniq_jfragment_jsequent in HP...
    destruct HP as [Heq HP].
    destruct C ; inversion Heq.
    * apply ill2ll_inj in H1.
      apply dual_inj in H2 ; apply ill2ll_inj in H2 ; subst.
      apply (PEperm_cons _ (dual (ill2ll C1)) (dual (ill2ll C1))) in HP...
      apply (PEperm_cons _ (ill2ll C2) (ill2ll C2)) in HP...
      apply PEperm_PCperm in HP.
      replace (dual (ill2ll C1) :: rev (map dual (map ill2ll l0)))
        with (rev (map dual (map ill2ll (l0 ++ C1 :: nil)))) in HP
        by now (rewrite <- ? map_rev ; rewrite rev_unit).
      apply IHHll in HP.
      destruct HP as [s pi].
      eexists.
      apply lmap_irr...
    * exfalso.
      apply ill2ll_not_dual in H2...
  + eapply uniq_jfragment_jsequent in HP...
    destruct HP as [Heq HP].
    destruct C ; inversion Heq.
    * exfalso.
      apply ill2ll_not_dual in H1...
    * apply ill2ll_inj in H2.
      apply dual_inj in H1 ; apply ill2ll_inj in H1 ; subst.
      apply (PEperm_app_tail _ _ _ (dual (ill2ll C1) :: nil)) in HP.
      apply (PEperm_cons _ (ill2ll C2) (ill2ll C2)) in HP...
      apply PEperm_PCperm in HP ; unfold id in HP.
      replace (rev (map dual (map ill2ll l0)) ++ dual (ill2ll C1) :: nil)
         with (rev (map dual (map ill2ll (C1 :: l0)))) in HP
         by now (rewrite <- ? map_rev ; simpl ;rewrite ? map_app).
      rewrite app_comm_cons in HP.
      apply (PCperm_trans _ _ _ _ (PCperm_last _ _ _)) in HP.
      apply IHHll in HP.
      destruct HP as [s pi].
      eexists.
      apply lpam_irr...
  + eapply uniq_not_jfragment_jsequent in HP...
    destruct HP as (l1 & l2 & Heq1 & Heq2).
    apply (PEperm_cons _ (dual (ill2ll D1)) (dual (ill2ll D1))) in Heq1...
    apply (PEperm_cons _ (dual (ill2ll D2)) (dual (ill2ll D2))) in Heq1...
    apply PEperm_PCperm in Heq1.
    rewrite 2 app_comm_cons in Heq1.
    assert (HPC := @PCperm_app_comm).
    assert (HP := PCperm_trans _ _ _ _ Heq1 (HPC _ _ _ _)).
    rewrite <- app_comm_cons in HP.
    specialize IHHll with (l1 ++ D1 :: D2 :: l2) C.
    rewrite <- ? map_rev in IHHll.
    rewrite rev_app_distr in IHHll.
    rewrite ? map_app in IHHll ; simpl in IHHll.
    rewrite ? map_app in IHHll ; simpl in IHHll.
    rewrite <- ? app_assoc in IHHll.
    rewrite <- ? map_rev in HP.
    apply IHHll in HP.
    destruct HP as [s pi].
    eexists.
    assert (PEperm (pperm (i2pfrag P)) (l1 ++ itens D1 D2 :: l2) l0) as Hl.
    { rewrite Ht in Heq2.
      replace (dual (ill2ll (itens D1 D2)) :: rev (map dual (map ill2ll l1)))
         with (rev (map dual (map ill2ll (l1 ++ itens D1 D2 :: nil))))
         in Heq2 by (list_simpl ; myeasy).
      rewrite <- rev_app_distr in Heq2.
      rewrite <- ? map_app in Heq2.
      apply PEperm_rev in Heq2.
      rewrite ? rev_involutive in Heq2.
      rewrite <- ? app_assoc in Heq2.
      rewrite <- app_comm_cons in Heq2.
      rewrite app_nil_l in Heq2.
      apply PEperm_map_inv_inj in Heq2 ; [ | apply dual_inj ].
      apply PEperm_map_inv_inj in Heq2 ; [ | apply ill2ll_inj ]... }
    eapply ex_ir ; [ | apply Hl].
    apply tens_ilr...
- eexists.
  assert (iftop = true) as ft.
  { apply jsequent_is_jfragment in H.
    inversion H ; inversion H2 ; subst.
    destruct H4 ; destruct x0 ; inversion H0...
    rewrite fz0 in fz ; inversion fz. }
  apply (uniq_jfragment_jsequent _ _ _ _ (@itop ft)) in HP...
  destruct HP as [Heq HP].
  destruct C ; inversion Heq.
  apply top_irr.
- apply jsequent_is_jfragment in H.
  inversion H ; subst ; destruct H2 as [D [Ht | Ht]] ;
    destruct D ; inversion Ht ; subst.
  + eapply uniq_jfragment_jsequent in HP...
    destruct HP as [Heq HP].
    destruct C ; inversion Heq.
    apply ill2ll_inj in H1.
    apply ill2ll_inj in H2 ; subst.
    apply (PEperm_cons _ (ill2ll C1) (ill2ll C1)) in HP...
    apply PEperm_PCperm in HP.
    apply IHHll in HP.
    destruct HP as [s pi].
    eexists.
    apply plus_irr1...
  + eapply uniq_not_jfragment_jsequent in HP...
    destruct HP as (l1 & l2 & Heq1 & Heq2).
    apply (PEperm_cons _ (dual (ill2ll D1)) (dual (ill2ll D1))) in Heq1...
    apply PEperm_PCperm in Heq1.
    rewrite app_comm_cons in Heq1.
    assert (HPC := @PCperm_app_comm).
    assert (HP := PCperm_trans _ _ _ _ Heq1 (HPC _ _ _ _)).
    rewrite <- app_comm_cons in HP.
    specialize IHHll with (l1 ++ D1 :: l2) C.
    rewrite <- ? map_rev in IHHll.
    rewrite rev_app_distr in IHHll.
    rewrite ? map_app in IHHll ; simpl in IHHll.
    rewrite ? map_app in IHHll ; simpl in IHHll.
    rewrite <- ? app_assoc in IHHll.
    rewrite <- ? map_rev in HP.
    apply IHHll in HP.
    destruct HP as [s pi].
    eexists.
    assert (PEperm (pperm (i2pfrag P)) (l1 ++ iwith D1 D2 :: l2) l0) as Hl.
    { rewrite Ht in Heq2.
      replace (dual (ill2ll (iwith D1 D2)) :: rev (map dual (map ill2ll l1)))
         with (rev (map dual (map ill2ll (l1 ++ iwith D1 D2 :: nil))))
         in Heq2 by (list_simpl ; myeasy).
      rewrite <- rev_app_distr in Heq2.
      rewrite <- ? map_app in Heq2.
      apply PEperm_rev in Heq2.
      rewrite ? rev_involutive in Heq2.
      rewrite <- ? app_assoc in Heq2.
      rewrite <- app_comm_cons in Heq2.
      rewrite app_nil_l in Heq2.
      apply PEperm_map_inv_inj in Heq2 ; [ | apply dual_inj ].
      apply PEperm_map_inv_inj in Heq2 ; [ | apply ill2ll_inj ]... }
    eapply ex_ir ; [ | apply Hl].
    apply with_ilr1...
- apply jsequent_is_jfragment in H.
  inversion H ; subst ; destruct H2 as [D [Ht | Ht]] ;
    destruct D ; inversion Ht ; subst.
  + eapply uniq_jfragment_jsequent in HP...
    destruct HP as [Heq HP].
    destruct C ; inversion Heq.
    apply ill2ll_inj in H1.
    apply ill2ll_inj in H2 ; subst.
    apply (PEperm_cons _ (ill2ll C2) (ill2ll C2)) in HP...
    apply PEperm_PCperm in HP.
    apply IHHll in HP.
    destruct HP as [s pi].
    eexists.
    apply plus_irr2...
  + eapply uniq_not_jfragment_jsequent in HP...
    assert (HPC := @PCperm_app_comm).
    destruct HP as (l1 & l2 & Heq1 & Heq0).
    apply (PEperm_cons _ (dual (ill2ll D2)) (dual (ill2ll D2))) in Heq1...
    apply PEperm_PCperm in Heq1.
    rewrite app_comm_cons in Heq1.
    assert (HP := PCperm_trans _ _ _ _ Heq1 (HPC _ _ _ _)).
    rewrite <- app_comm_cons in HP.
    rewrite <- ? map_rev in HP.
    specialize IHHll with (l1 ++ D2 :: l2) C.
    rewrite <- ? map_rev in IHHll.
    rewrite rev_app_distr in IHHll.
    rewrite ? map_app in IHHll ; simpl in IHHll.
    rewrite ? map_app in IHHll ; simpl in IHHll.
    rewrite <- ? app_assoc in IHHll.
    apply IHHll in HP.
    destruct HP as [s pi].
    eexists.
    assert (PEperm (pperm (i2pfrag P)) (l1 ++ iwith D1 D2 :: l2) l0) as Hl.
    { rewrite Ht in Heq0.
      replace (dual (ill2ll (iwith D1 D2)) :: rev (map dual (map ill2ll l1)))
         with (rev (map dual (map ill2ll (l1 ++ iwith D1 D2 :: nil))))
         in Heq0 by (list_simpl ; myeasy).
      rewrite <- rev_app_distr in Heq0.
      rewrite <- ? map_app in Heq0.
      apply PEperm_rev in Heq0.
      rewrite ? rev_involutive in Heq0.
      rewrite <- ? app_assoc in Heq0.
      rewrite <- app_comm_cons in Heq0.
      rewrite app_nil_l in Heq0.
      apply PEperm_map_inv_inj in Heq0 ; [ | apply dual_inj ].
      apply PEperm_map_inv_inj in Heq0 ; [ | apply ill2ll_inj ]... }
    eapply ex_ir ; [ | apply Hl].
    apply with_ilr2...
- apply jsequent_is_jfragment in H.
  inversion H ; subst ; destruct H2 as [D [Ht | Ht]] ;
    destruct D ; inversion Ht ; subst.
  + eapply uniq_jfragment_jsequent in HP...
    destruct HP as [Heq HP].
    destruct C ; inversion Heq.
    apply ill2ll_inj in H1.
    apply ill2ll_inj in H2 ; subst.
    assert (HP' := HP).
    apply (PEperm_cons _ (ill2ll C1) (ill2ll C1)) in HP...
    apply PEperm_PCperm in HP.
    apply IHHll1 in HP.
    destruct HP as [s1 pi1].
    apply (PEperm_cons _ (ill2ll C2) (ill2ll C2)) in HP'...
    apply PEperm_PCperm in HP'.
    apply IHHll2 in HP'.
    destruct HP' as [s2 pi2].
    eexists.
    apply with_irr...
  + eapply uniq_not_jfragment_jsequent in HP...
    assert (HPC := @PCperm_app_comm).
    destruct HP as (l1 & l2 & Heq1 & Heq0).
    assert (Heq2 := Heq1).
    apply (PEperm_cons _ (dual (ill2ll D1)) (dual (ill2ll D1))) in Heq1...
    apply PEperm_PCperm in Heq1.
    rewrite app_comm_cons in Heq1.
    assert (HP1 := PCperm_trans _ _ _ _ Heq1 (HPC _ _ _ _)).
    rewrite <- app_comm_cons in HP1.
    rewrite <- ? map_rev in HP1.
    specialize IHHll1 with (l1 ++ D1 :: l2) C.
    rewrite <- ? map_rev in IHHll1.
    rewrite rev_app_distr in IHHll1.
    rewrite ? map_app in IHHll1 ; simpl in IHHll1.
    rewrite ? map_app in IHHll1 ; simpl in IHHll1.
    rewrite <- ? app_assoc in IHHll1.
    apply IHHll1 in HP1.
    destruct HP1 as [s1 pi1].
    apply (PEperm_cons _ (dual (ill2ll D2)) (dual (ill2ll D2))) in Heq2...
    apply PEperm_PCperm in Heq2.
    rewrite app_comm_cons in Heq2.
    assert (HP2 := PCperm_trans _ _ _ _ Heq2 (HPC _ _ _ _)).
    rewrite <- app_comm_cons in HP2.
    rewrite <- ? map_rev in HP2.
    specialize IHHll2 with (l1 ++ D2 :: l2) C.
    rewrite <- ? map_rev in IHHll2.
    rewrite rev_app_distr in IHHll2.
    rewrite ? map_app in IHHll2 ; simpl in IHHll2.
    rewrite ? map_app in IHHll2 ; simpl in IHHll2.
    rewrite <- ? app_assoc in IHHll2.
    apply IHHll2 in HP2.
    destruct HP2 as [s2 pi2].
    eexists.
    assert (PEperm (pperm (i2pfrag P)) (l1 ++ iplus D1 D2 :: l2) l0) as Hl.
    { rewrite Ht in Heq0.
      replace (dual (ill2ll (iplus D1 D2)) :: rev (map dual (map ill2ll l1)))
         with (rev (map dual (map ill2ll (l1 ++ iplus D1 D2 :: nil))))
         in Heq0 by (list_simpl ; myeasy).
      rewrite <- rev_app_distr in Heq0.
      rewrite <- ? map_app in Heq0.
      apply PEperm_rev in Heq0.
      rewrite ? rev_involutive in Heq0.
      rewrite <- ? app_assoc in Heq0.
      rewrite <- app_comm_cons in Heq0.
      rewrite app_nil_l in Heq0.
      apply PEperm_map_inv_inj in Heq0 ; [ | apply dual_inj ].
      apply PEperm_map_inv_inj in Heq0 ; [ | apply ill2ll_inj ]... }
    eapply ex_ir ; [ | apply Hl].
    apply plus_ilr...
- apply jsequent_is_jfragment in H.
  inversion H ; subst ; destruct H2 as [D [Ht | Ht]] ;
    destruct D ; inversion Ht ; subst.
  eapply uniq_jfragment_jsequent in HP...
  destruct HP as [Heq HP].
  assert (Hwn := HP).
  destruct C ; inversion Heq.
  apply ill2ll_inj in H1 ; subst.
  apply (PEperm_cons _ (ill2ll C) (ill2ll C)) in HP...
  apply PEperm_PCperm in HP.
  apply IHHll in HP.
  destruct HP as [s pi].
  eexists.
  assert (exists l', PEperm (pperm (i2pfrag P)) (map ioc l') l0)
    as [l' Hwn2].
  { clear - Hwn.
    revert l Hwn ; induction l0 using rev_ind ; intros l Hwn.
    - exists nil...
    - rewrite <- ? map_rev in Hwn.
      rewrite rev_unit in Hwn.
      simpl in Hwn.
      symmetry in Hwn.
      apply PEperm_map_inv in Hwn.
      destruct Hwn as (l3 & Heq1 & Heq2).
      destruct l3 ; inversion Heq1.
      assert (PEperm (pperm (i2pfrag P)) (map wn l3)
                     (map dual (map ill2ll (rev l0))))
        as HP' by now rewrite <- H1.
      rewrite ? map_rev in HP'.
      apply IHl0 in HP'.
      destruct HP' as [l' HP].
      destruct x ; inversion H0.
      exists (l' ++ x :: nil).
      rewrite ? map_app ; simpl.
      rewrite <- rev_involutive.
      rewrite <- rev_involutive at 1.
      apply PEperm_rev.
      rewrite ? rev_unit.
      apply PEperm_cons...
      apply PEperm_rev... }
  eapply ex_ir ; [ | apply Hwn2 ].
  apply oc_irr.
  symmetry in Hwn2.
  eapply ex_ir...
- apply jsequent_is_jfragment in H.
  inversion H ; subst ; destruct H2 as [D [Ht | Ht]] ;
    destruct D ; inversion Ht ; subst.
  eapply uniq_not_jfragment_jsequent in HP...
  destruct HP as (l1 & l2 & Heq1 & Heq2).
  apply (PEperm_cons _ (dual (ill2ll D)) (dual (ill2ll D))) in Heq1...
  apply PEperm_PCperm in Heq1.
  rewrite app_comm_cons in Heq1.
  assert (HPC := @PCperm_app_comm).
  assert (HP := PCperm_trans _ _ _ _ Heq1 (HPC _ _ _ _)).
  rewrite <- app_comm_cons in HP.
  specialize IHHll with (l1 ++ D :: l2) C.
  rewrite <- ? map_rev in IHHll.
  rewrite rev_app_distr in IHHll.
  rewrite ? map_app in IHHll ; simpl in IHHll.
  rewrite ? map_app in IHHll ; simpl in IHHll.
  rewrite <- ? app_assoc in IHHll.
  rewrite <- ? map_rev in HP.
  apply IHHll in HP.
  destruct HP as [s pi].
  eexists.
  assert (PEperm (pperm (i2pfrag P)) (l1 ++ ioc D :: l2) l0) as Hl.
  { rewrite Ht in Heq2.
    replace (dual (ill2ll (ioc D)) :: rev (map dual (map ill2ll l1)))
      with (rev (map dual (map ill2ll (l1 ++ ioc D :: nil))))
      in Heq2 by (list_simpl ; myeasy).
    rewrite <- rev_app_distr in Heq2.
    rewrite <- ? map_app in Heq2.
    apply PEperm_rev in Heq2.
    rewrite ? rev_involutive in Heq2.
    rewrite <- ? app_assoc in Heq2.
    rewrite <- app_comm_cons in Heq2.
    rewrite app_nil_l in Heq2.
    apply PEperm_map_inv_inj in Heq2 ; [ | apply dual_inj ].
    apply PEperm_map_inv_inj in Heq2 ; [ | apply ill2ll_inj ]... }
  eapply ex_ir ; [ | apply Hl].
  apply de_ilr...
- apply jsequent_is_jfragment in H.
  inversion H ; subst ; destruct H2 as [D [Ht | Ht]] ;
    destruct D ; inversion Ht ; subst.
  eapply uniq_not_jfragment_jsequent in HP...
  destruct HP as (l1 & l2 & Heq1 & Heq2).
  apply PEperm_PCperm in Heq1.
  assert (HPC := @PCperm_app_comm).
  assert (HP := PCperm_trans _ _ _ _ Heq1 (HPC _ _ _ _)).
  rewrite <- app_comm_cons in HP.
  specialize IHHll with (l1 ++ l2) C.
  rewrite <- ? map_rev in IHHll.
  rewrite rev_app_distr in IHHll.
  rewrite ? map_app in IHHll ; simpl in IHHll.
  rewrite <- ? map_rev in HP.
  apply IHHll in HP.
  destruct HP as [s pi].
  eexists.
  assert (PEperm (pperm (i2pfrag P)) (l1 ++ ioc D :: l2) l0) as Hl.
  { rewrite Ht in Heq2.
    replace (dual (ill2ll (ioc D)) :: rev (map dual (map ill2ll l1)))
      with (rev (map dual (map ill2ll (l1 ++ ioc D :: nil))))
      in Heq2 by (list_simpl ; myeasy).
    rewrite <- rev_app_distr in Heq2.
    rewrite <- ? map_app in Heq2.
    apply PEperm_rev in Heq2.
    rewrite ? rev_involutive in Heq2.
    rewrite <- ? app_assoc in Heq2.
    rewrite <- app_comm_cons in Heq2.
    rewrite app_nil_l in Heq2.
    apply PEperm_map_inv_inj in Heq2 ; [ | apply dual_inj ].
    apply PEperm_map_inv_inj in Heq2 ; [ | apply ill2ll_inj ]... }
  eapply ex_ir ; [ | apply Hl].
  apply wk_ilr...
- apply jsequent_is_jfragment in H.
  inversion H ; subst ; destruct H2 as [D [Ht | Ht]] ;
    destruct D ; inversion Ht ; subst.
  eapply uniq_not_jfragment_jsequent in HP...
  destruct HP as (l1 & l2 & Heq1 & Heq2).
  simpl in Heq1 ; simpl in Heq2.
  rewrite <- ? map_rev in Heq1.
  hyps_PEperm_unfold ; unfold PCperm in IHHll ; simpl in IHHll ;
    case_eq (ipperm P) ; intros Heqb ; rewrite_all Heqb.
  + apply (@Permutation_cons _ _ (wn (dual (ill2ll D))) eq_refl) in Heq1...
    apply (@Permutation_cons _ _ (wn (dual (ill2ll D))) eq_refl) in Heq1...
    rewrite ? app_comm_cons in Heq1.
    assert (HP := Permutation_trans Heq1 (Permutation_app_comm _ _)).
    apply (Permutation_trans
      (Permutation_app_tail l (Permutation_sym (Permutation_cons_append _ _))))
      in HP.
    rewrite <- ? app_assoc in HP.
    rewrite <- ? app_comm_cons in HP ; simpl in HP.
    specialize IHHll with (l1 ++ ioc D :: ioc D :: l2) C.
    rewrite <- ? map_rev in IHHll.
    rewrite rev_app_distr in IHHll ; simpl in IHHll.
    rewrite <- ? app_assoc in IHHll.
    rewrite ? map_app in IHHll ; simpl in IHHll.
    apply IHHll in HP.
    destruct HP as [s pi].
    eexists.
    replace (wn (dual (ill2ll D)) :: rev (map dual (map ill2ll l1)))
      with (rev (map dual (map ill2ll (l1 ++ ioc D :: nil))))
      in Heq2 by (list_simpl ; rewrite ? (uniq_wn _ f) ; myeasy).
    rewrite <- rev_app_distr in Heq2.
    apply Permutation_rev' in Heq2.
    rewrite ? rev_involutive in Heq2.
    rewrite <- ? map_app in Heq2.
    apply Permutation_map_inv_inj in Heq2 ; [ | apply dual_inj ].
    apply Permutation_map_inv_inj in Heq2 ; [ | apply ill2ll_inj ].
    eapply ex_ir ; [ | rewrite Heqb ; apply Heq2 ].
    rewrite <- app_assoc.
    rewrite <- app_comm_cons ; simpl.
    rewrite <- (app_nil_l (ioc _ :: _)).
    change nil with (map ioc nil).
    apply co_ilr...
  + dichot_app_exec Heq1.
    * decomp_map Heq0.
      decomp_map Heq0 ; subst.
      assert (exists l7', l7 = map ioc l7') as [l7' Hwn] ; subst.
      { clear - Heq4.
        revert lw Heq4 ; induction l7 ; intros lw H.
        - exists nil...
        - destruct lw ; inversion H ; subst.
         apply IHl7 in H2.
         destruct H2 as [l7' H2] ; subst.
         destruct a ; inversion H1.
         exists (a :: l7')... }
      rewrite Heq4 in IHHll.
      specialize IHHll
        with (rev l8 ++ ioc D :: rev (map ioc l7') ++ ioc D :: l2) C.
      rewrite <- ? map_rev in IHHll.
      rewrite ? rev_app_distr in IHHll ; simpl in IHHll.
      rewrite ? rev_app_distr in IHHll ; simpl in IHHll.
      rewrite ? rev_involutive in IHHll.
      rewrite <- ? app_assoc in IHHll.
      rewrite <- ? app_comm_cons in IHHll ; simpl in IHHll.
      rewrite ? map_app in IHHll ; simpl in IHHll.
      rewrite ? map_app in IHHll ; simpl in IHHll.
      rewrite <- ? map_rev in IHHll.
      rewrite ? rev_involutive in IHHll.
      rewrite ? app_comm_cons in IHHll.
      rewrite app_assoc in IHHll.
      assert (pi := IHHll (cperm _ _)).
      destruct pi as [s pi].
      rewrite <- ? app_comm_cons in pi.
      eexists.
      assert (l1 ++ ioc D :: l2 = l0) as Hl0 ; subst.
      { clear - fz i2a_inj Heq2.
        apply (map_inj ill2ll) ; [ apply ill2ll_inj | ].
        apply (map_inj dual) ; [ apply dual_inj | ].
        rewrite ? map_app.
        rewrite <- rev_involutive.
        rewrite <- Heq2 ; simpl.
        list_simpl... }
      rewrite <- (rev_involutive l1).
      rewrite <- Heq0.
      rewrite ? rev_app_distr.
      rewrite <- map_rev.
      rewrite <- ? app_assoc.
      apply co_ilr...
    * assert (l4 = nil) as Hl4 ; subst.
      { destruct l4 ; inversion Heq3 ; subst...
        exfalso.
        remember (map dual (map ill2ll (rev l1))) as l'.
        symmetry in Heq0.
        decomp_map Heq0.
        destruct C ; inversion Heq0. }
      simpl in Heq3 ; subst.
      rewrite app_nil_r in Heq0.
      rewrite Heq0 in IHHll.
      specialize IHHll
        with (ioc D :: l1 ++ ioc D :: l2) C.
      rewrite <- ? map_rev in IHHll ; simpl in IHHll.
      rewrite ? map_app in IHHll.
      rewrite ? rev_app_distr in IHHll ; simpl in IHHll.
      rewrite <- ? app_assoc in IHHll.
      rewrite <- ? app_comm_cons in IHHll ; simpl in IHHll.
      rewrite ? map_app in IHHll ; simpl in IHHll.
      rewrite <- (app_nil_l (ill2ll C :: _)) in IHHll.
      rewrite ? app_comm_cons in IHHll.
      rewrite ? app_assoc in IHHll.
      rewrite <- (app_assoc _ _ (wn (dual (ill2ll D)) :: nil)) in IHHll.
      assert (pi := IHHll (cperm _ _)).
      destruct pi as [s pi].
      rewrite <- ? app_comm_cons in pi.
      eexists.
      assert (l1 ++ ioc D :: l2 = l0) as Hl0 ; subst.
      { clear - fz i2a_inj Heq2.
        apply (map_inj ill2ll) ; [ apply ill2ll_inj | ].
        apply (map_inj dual) ; [ apply dual_inj | ].
        rewrite ? map_app.
        rewrite <- rev_involutive.
        rewrite <- Heq2 ; simpl.
        list_simpl... }
      assert (exists l1', l1 = map ioc l1') as [l1' Hwn] ; subst.
      { clear - Heq0.
        revert lw Heq0 ; induction l1 using rev_ind ; intros lw H.
        - exists nil...
        - destruct lw ; rewrite rev_unit in H ; inversion H ; subst.
          apply IHl1 in H2.
          destruct H2 as [l1' H2] ; subst.
          destruct x ; inversion H1.
          exists (l1' ++ x :: nil).
          rewrite map_app... }
      rewrite <- (app_nil_l (map ioc l1')).
      rewrite <- app_assoc.
      apply co_ilr...
- assert (Hll := Hll1).
  apply ll_ps_is_ps in Hll.
  apply jsequent_is_jfragment in Hll.
  inversion Hll ; subst.
  apply jsequent_app in H.
  destruct H as [l [[Heq Hi] | [Heq Hi]]] ; subst.
  + destruct H2 as [D [Ht | Ht]] ; subst.
    * rewrite_all Ht.
      specialize IHHll1 with (rev l) D.
      rewrite <- ? map_rev in IHHll1.
      rewrite rev_involutive in IHHll1.
      assert (pi1 := IHHll1 (PCperm_refl _ _)).
      destruct pi1 as [s1 pi1].
      apply codual in Ht ; subst.
      destruct Hi as (l' & C' & Hi).
      apply cperm_vs_cons_inv in Hi.
      destruct Hi as (l'' & l''' & Heq1 & Heq2) ; subst.
      rewrite <- ? map_rev in Heq1.
      symmetry in Heq1.
      decomp_map Heq1.
      decomp_map Heq1 ; subst.
      specialize IHHll2 with (rev l5 ++ D :: rev l4) C'.
      rewrite <- ? map_rev in IHHll2.
      rewrite ? rev_app_distr in IHHll2.
      simpl in IHHll2 ; rewrite ? rev_involutive in IHHll2.
      rewrite ? map_app in IHHll2 ; simpl in IHHll2.
      rewrite <- app_assoc in IHHll2.
      rewrite <- app_comm_cons in IHHll2.
      rewrite app_nil_l in IHHll2.
      assert (CPermutation (dual (ill2ll D) :: map dual (map ill2ll l5) ++
                                  ill2ll C' :: map dual (map ill2ll l4))
                           (ill2ll C' :: map dual (map ill2ll l4) ++
                             dual (ill2ll D) :: map dual (map ill2ll l5)))
        as HC by cperm_solve.
      eapply cperm_PCperm in HC.
      apply IHHll2 in HC.
      destruct HC as [s2 pi2].
      simpl in f.
      apply (@cut_ir _ f _ _ _ _ _ _ _ pi1) in pi2.
      eexists.
      rewrite <- ? app_assoc in HP.
      apply (PCperm_trans _ _ _ _ (PCperm_app_comm _ _ _)) in HP.
      rewrite <- ? app_comm_cons in HP.
      rewrite <- ? app_assoc in HP.
      apply (uniq_jfragment_jsequent _ _ _ _ C') in HP...
      destruct HP as [HeqC Heql].
      apply ill2ll_inj in HeqC ; subst.
      rewrite <- ? map_app in Heql.
      apply PEperm_rev in Heql.
      rewrite rev_involutive in Heql.
      rewrite <- ? map_rev in Heql.
      rewrite ? rev_app_distr in Heql.
      rewrite <- app_assoc in Heql.
      apply PEperm_map_inv_inj in Heql ; [ | apply dual_inj ].
      apply PEperm_map_inv_inj in Heql ; [ | apply ill2ll_inj ].
      eapply ex_ir...
    * exfalso.
      apply ll_ps_is_ps in Hll2.
      apply dual_inj in Ht.
      rewrite Ht in Hll2.
      clear - fz Hi Hll2.
      destruct Hi as (l & C0 & Hi).
      apply cperm_vs_cons_inv in Hi.
      destruct Hi as (l3 & l4 & _ & Heq2) ; subst.
      destruct Hll2 as (l' & C1 & H).
      inversion H.
      destruct l2 ; inversion H2 ; subst.
      -- rewrite app_nil_r in H1.
         rewrite app_nil_l in H2 ; subst.
         inversion H2.
         rewrite <- ? map_rev in H4.
         eapply ill2ll_not_dual_elt...
      -- rewrite <- ? map_rev in H4.
         decomp_map H4.
         decomp_map H4 ; subst.
         destruct l8 ; inversion H1.
         ++ clear - fz H5.
            revert l4 l7 H5 ; induction l3 ; intros l4 l7 H5 ;
              destruct l7 ; inversion H5 ; subst.
            ** apply ill2ll_not_dual in H0...
            ** apply IHl3 in H1...
         ++ apply ill2ll_not_dual in H3...
  + destruct H2 as [D [Ht | Ht]] ; subst.
    * exfalso.
      apply ll_ps_is_ps in Hll1.
      apply codual in Ht ; subst.
      clear - fz Hi Hll1.
      rewrite bidual in Hll1.
      destruct Hi as (l & C0 & Hi).
      apply cperm_vs_cons_inv in Hi.
      destruct Hi as (l3 & l4 & _ & Heq2) ; subst.
      destruct Hll1 as (l' & C1 & H).
      inversion H.
      destruct l2 ; inversion H2 ; subst.
      -- rewrite app_nil_r in H1.
         rewrite app_nil_l in H2 ; subst.
         inversion H2.
         rewrite <- ? map_rev in H4.
         eapply ill2ll_not_dual_elt...
      -- rewrite <- ? map_rev in H4.
         decomp_map H4.
         decomp_map H4 ; subst.
         destruct l8 ; inversion H1.
         ++ symmetry in H5.
            eapply ill2ll_not_dual_elt...
         ++ apply ill2ll_not_dual in H3...
    * apply dual_inj in Ht ; subst.
      specialize IHHll2 with (rev l) D.
      rewrite <- ? map_rev in IHHll2.
      rewrite rev_involutive in IHHll2.
      assert (pi2 := IHHll2 (PCperm_refl _ _)).
      destruct pi2 as [s2 pi2].
      destruct Hi as (l' & C' & Hi).
      apply cperm_vs_cons_inv in Hi.
      destruct Hi as (l'' & l''' & Heq1 & Heq2) ; subst.
      rewrite <- ? map_rev in Heq1.
      symmetry in Heq1.
      decomp_map Heq1.
      decomp_map Heq1 ; subst.
      specialize IHHll1 with (rev l5 ++ D :: rev l4) C'.
      rewrite <- ? map_rev in IHHll1.
      rewrite ? rev_app_distr in IHHll1.
      simpl in IHHll1 ; rewrite ? rev_involutive in IHHll1.
      rewrite ? map_app in IHHll1 ; simpl in IHHll1.
      rewrite <- app_assoc in IHHll1.
      rewrite <- app_comm_cons in IHHll1.
      rewrite app_nil_l in IHHll1.
      assert (CPermutation (dual (ill2ll D) :: map dual (map ill2ll l5) ++
                                  ill2ll C' :: map dual (map ill2ll l4))
                           (ill2ll C' :: map dual (map ill2ll l4) ++
                             dual (ill2ll D) :: map dual (map ill2ll l5)))
        as HC by cperm_solve.
      eapply cperm_PCperm in HC.
      apply IHHll1 in HC.
      destruct HC as [s1 pi1].
      simpl in f.
      apply (@cut_ir _ f _ _ _ _ _ _ _ pi2) in pi1.
      eexists.
      rewrite app_assoc in HP.
      apply (PCperm_trans _ _ _ _ (PCperm_app_comm _ _ _)) in HP.
      rewrite <- ? app_comm_cons in HP.
      apply (uniq_jfragment_jsequent _ _ _ _ C') in HP...
      destruct HP as [HeqC Heql].
      apply ill2ll_inj in HeqC ; subst.
      rewrite <- ? map_app in Heql.
      apply PEperm_rev in Heql.
      rewrite rev_involutive in Heql.
      rewrite <- ? map_rev in Heql.
      rewrite ? rev_app_distr in Heql.
      rewrite <- app_assoc in Heql.
      apply PEperm_map_inv_inj in Heql ; [ | apply dual_inj ].
      apply PEperm_map_inv_inj in Heql ; [ | apply ill2ll_inj ].
      eapply ex_ir...
- eexists.
  destruct H0 as (l' & C0 & Heq & Hax).
  rewrite Heq in HP.
  eapply uniq_jfragment_jsequent in HP...
  destruct HP as [Heq2 HP].
  apply ill2ll_inj in Heq2 ; subst.
  apply PEperm_rev in HP.
  rewrite ? rev_involutive in HP.
  apply PEperm_map_inv_inj in HP ; [ | apply dual_inj ].
  apply PEperm_map_inv_inj in HP ; [ | apply ill2ll_inj ].
  eapply ex_ir...
  apply gax_ir...
Qed.

(** Axiom-free conservativity *)
Lemma ll_to_ill_axfree {P} : (forall l C, ~ ipgax P l C) -> forall l s,
  ll (i2pfrag P) l s -> forall l0 C,
    PCperm (pperm (i2pfrag P)) l (ill2ll C :: rev (map dual (map ill2ll l0))) ->
      exists s', ill P l0 C s'.
Proof with myeeasy.
intros P_axfree l s pi l0 C HP.
apply ll_i_is_ll_ps_i_axfree in pi.
- apply ll_ps_j_is_ll_ps_jsequent in pi.
  + eapply ll_ps_jsequent_is_ill...
  + eapply PCperm_jsequent...
- intros l1 Hgax.
  destruct Hgax as (l' & C0 & Heq & Hgax).
  apply P_axfree in Hgax...
- apply jsequent_is_jfragment.
  eapply PCperm_jsequent...
Qed.

(** Cut-free conservativity *)
Lemma ll_to_ill_cutfree {P} : ipcut P = false -> forall l s,
  ll (i2pfrag P) l s -> forall l0 C,
    PCperm (pperm (i2pfrag P)) l (ill2ll C :: rev (map dual (map ill2ll l0))) ->
      exists s', ill P l0 C s'.
Proof with myeeasy.
intros P_cutfree l s pi l0 C HP.
apply (@ll_j_is_ll_ps_j_cutfree (i2pfrag P)) in pi...
- apply ll_ps_j_is_ll_ps_jsequent in pi.
  + eapply ll_ps_jsequent_is_ill...
  + eapply PCperm_jsequent...
- intros lax Hax.
  destruct Hax as (l' & C' & Hax & _) ; subst.
  apply jsequent_is_jfragment.
  eapply (PCperm_jsequent true)...
- apply jsequent_is_jfragment.
  eapply PCperm_jsequent...
Qed.

Lemma ll_to_ill_topfree_axfree {P} : iftop = false ->
  (forall l C, ~ ipgax P l C) -> forall l s, Forall jfragment l ->
  ll (i2pfrag P) l s -> exists l0 C s',
       PCperm (pperm (i2pfrag P)) l (ill2ll C :: rev (map dual (map ill2ll l0)))
    /\ ill P l0 C s'.
Proof with myeeasy.
intros F_topfree P_axfree l s Hi pi.
apply ll_i_is_ll_ps_i_axfree in pi...
- apply ll_ps_j_is_ll_ps_jsequent_topfree in pi...
  assert (Hc := pi).
  apply ll_ps_is_ps in Hc.
  destruct Hc as (l0 & C & Hc).
  apply (cperm_PCperm (pperm (i2pfrag P))) in Hc.
  eapply ll_ps_jsequent_is_ill in pi...
  clear s ; destruct pi as [s pi].
  exists l0 ; exists C ; exists s ; split...
- intros f Hgax.
  destruct Hgax as (l' & C0 & Heq & Hgax).
  apply P_axfree in Hgax...
Qed.

Lemma ll_to_ill_topfree_cutfree {P} : iftop = false -> ipcut P = false ->
  forall l s, Forall jfragment l ->
  ll (i2pfrag P) l s -> exists l0 C s',
       PCperm (pperm (i2pfrag P)) l (ill2ll C :: rev (map dual (map ill2ll l0)))
    /\ ill P l0 C s'.
Proof with myeeasy.
intros F_topfree P_cutfree l s Hi pi.
apply (@ll_j_is_ll_ps_j_cutfree (i2pfrag P)) in pi...
- apply ll_ps_j_is_ll_ps_jsequent_topfree in pi...
  assert (Hc := pi).
  apply ll_ps_is_ps in Hc.
  destruct Hc as (l0 & C & Hc).
  apply (cperm_PCperm (pperm (i2pfrag P))) in Hc.
  eapply ll_ps_jsequent_is_ill in pi...
  clear s ; destruct pi as [s pi].
  exists l0 ; exists C ; exists s ; split...
- intros lax Hax.
  destruct Hax as (l' & C' & Hax & _) ; subst.
  apply jsequent_is_jfragment.
  eapply (PCperm_jsequent true)...
Qed.

End LL_fragment.


(** ** Properties of [ill] (deduced from those of [ll]) *)

Section Properties.

(** The results of the section hold without [izero] only. *)
Context {fz : ifzer = false}.

(** Embedding of [IAtom] into [Atom] *)
Variable i2a : IAtom -> Atom.
Hypothesis i2a_inj : injective i2a.

(** Axiom expansion *)
Lemma ax_exp_ill {P} : forall A, exists s, ill P (A :: nil) A s.
Proof with myeeasy.
intros A.
assert (Hax :=
  @ax_exp (i2pfrag i2a (axupd_ipfrag P (fun _ _ => False))) (ill2ll i2a A)).
destruct Hax as [s pi].
eapply (@ll_to_ill_axfree fz) in pi...
- clear s ; destruct pi as [s pi].
  eexists.
  eapply stronger_ipfrag...
  nsplit 3...
  intros l a Hax.
  inversion Hax.
- intros l a Hax.
  inversion Hax.
- PCperm_solve.
Qed.

(** Cut elimination *)
Lemma cut_ir_axfree {P} : (forall l C, ~ ipgax P l C) -> forall A l0 l1 l2 C s1 s2,
  ill P l0 A s1 -> ill P (l1 ++ A :: l2) C s2 -> exists s,
    ill P (l1 ++ l0 ++ l2) C s.
Proof with myeeasy.
intros P_axfree A l0 l1 l2 C s1 s2 pi1 pi2.
apply (ill_to_ll i2a) in pi1.
clear s1 ; destruct pi1 as [s1 pi1].
apply (ill_to_ll i2a) in pi2.
clear s2 ; destruct pi2 as [s2 pi2].
rewrite <- ? map_rev in pi2.
rewrite rev_app_distr in pi2 ; simpl in pi2.
rewrite ? map_app in pi2 ; simpl in pi2.
rewrite <- ? app_assoc in pi2.
rewrite <- ? app_comm_cons in pi2 ; simpl in pi2.
rewrite app_comm_cons in pi2.
eapply ex_r in pi2 ; [ | apply PCperm_app_comm ].
rewrite <- ? app_comm_cons in pi2.
assert (forall l, ~ pgax (i2pfrag i2a P) l) as P_axfree'.
{ intros l Hgax.
  destruct Hgax as (l' & C' & _ & Hgax).
  apply P_axfree in Hgax... }
apply (cut_r_axfree P_axfree' _ _ _ _ _ pi2) in pi1.
clear s1 ; destruct pi1 as [s1 pi1].
apply (ll_i_is_ll_ps_i_axfree i2a) in pi1.
- apply (@ll_ps_j_is_ll_ps_jsequent fz) in pi1...
  + eapply (@ll_ps_jsequent_is_ill fz) in pi1...
    rewrite <- ? map_rev.
    rewrite ? rev_app_distr.
    rewrite ? map_app.
    PCperm_solve.
  + exists (l1 ++ l0 ++ l2) ; exists C...
    rewrite <- ? map_rev.
    rewrite ? rev_app_distr.
    rewrite ? map_app.
    cperm_solve.
- intros f (l0' & C0' & Hax1 & Hax2).
  apply P_axfree in Hax2...
- eapply jsequent_is_jfragment.
  exists (l1 ++ l0 ++ l2); exists C.
  list_simpl ; cperm_solve.
Qed.

Proposition cut_admissible_ill_axfree {P} : (forall l C, ~ ipgax P l C) ->
  forall l C s, ill P l C s -> exists s', ill (cutrm_ipfrag P) l C s'.
Proof with myeeasy.
intros P_axfree l C s pi.
apply (ill_to_ll i2a) in pi.
clear s ; destruct pi as [s pi].
apply cut_admissible_axfree in pi.
- clear s ; destruct pi as [s pi].
  apply (ll_i_is_ll_ps_i_axfree i2a) in pi.
  + change (cutrm_pfrag (i2pfrag i2a P))
      with (i2pfrag i2a (cutrm_ipfrag P)) in pi.
    apply (@ll_ps_j_is_ll_ps_jsequent fz) in pi...
    * eapply (@ll_ps_jsequent_is_ill fz) in pi...
    * exists l ; exists C...
  + intros f (l0 & C0 & _ & Hax).
    apply P_axfree in Hax...
  + eapply jsequent_is_jfragment.
    eexists ; eexists...
- intros f (l0 & C0 & _ & Hax).
  apply P_axfree in Hax...
Qed.

End Properties.


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
| lmap_ps_irr : forall A B l, PS l (ilmap A B) ->
                    ill_ps P PS (l ++ A :: nil) B ->
                    ill_ps P PS l (ilmap A B)
| lmap_ps_ilr : forall A B l0 l1 l2 C, PS (l1 ++ ilmap A B :: l0 ++ l2) C ->
                    ill_ps P PS l0 A -> ill_ps P PS (l1 ++ B :: l2) C ->
                    ill_ps P PS (l1 ++ ilmap A B :: l0 ++ l2) C
| lpam_ps_irr : forall A B l, PS l (ilpam A B) ->
                    ill_ps P PS (A :: l) B ->
                    ill_ps P PS l (ilpam A B)
| lpam_ps_ilr : forall A B l0 l1 l2 C, PS (l1 ++ l0 ++ ilpam A B :: l2) C ->
                    ill_ps P PS l0 A -> ill_ps P PS (l1 ++ B :: l2) C ->
                    ill_ps P PS (l1 ++ l0 ++ ilpam A B :: l2) C
| top_ps_irr {ft : iftop = true} : forall l, PS l (@itop ft) ->
                                             ill_ps P PS l (@itop ft)
| with_ps_irr : forall A B l, PS l (iwith A B) ->
                    ill_ps P PS l A -> ill_ps P PS l B ->
                    ill_ps P PS l (iwith A B)
| with_ps_ilr1 : forall A B l1 l2 C, PS (l1 ++ iwith A B :: l2) C ->
                           ill_ps P PS (l1 ++ A :: l2) C ->
                           ill_ps P PS (l1 ++ iwith A B :: l2) C
| with_ps_ilr2 : forall A B l1 l2 C, PS (l1 ++ iwith B A :: l2) C ->
                           ill_ps P PS (l1 ++ A :: l2) C ->
                           ill_ps P PS (l1 ++ iwith B A :: l2) C
| zero_ps_ilr {fz : ifzer = true} : forall l1 l2 C, PS (l1 ++ @izero fz :: l2) C ->
                                                ill_ps P PS (l1 ++ @izero fz :: l2) C
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
- apply lmap_ps_irr...
  apply IHpi.
  constructor...
  + eapply HFS...
    apply isub_lmap_r...
  + apply Forall_app...
    constructor ; [ | constructor ]...
    eapply HFS...
    apply isub_lmap_l...
- apply lmap_ps_ilr...
  + apply IHpi1...
    apply Forall_app_inv in H3.
    destruct H3 as [ HFhd HFtl ].
    inversion HFtl.
    apply Forall_app_inv in H4.
    destruct H4.
    constructor...
    eapply HFS...
    apply isub_lmap_l...
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
    apply isub_lmap_r...
- apply lpam_ps_irr...
  apply IHpi.
  constructor...
  + eapply HFS...
    apply isub_lpam_r...
  + constructor...
    eapply HFS...
    apply isub_lpam_l...
- apply lpam_ps_ilr...
  + apply IHpi1...
    apply Forall_app_inv in H3.
    destruct H3 as [ HFhd HFtl ].
    apply Forall_app_inv in HFtl.
    destruct HFtl.
    inversion H1.
    constructor...
    eapply HFS...
    apply isub_lpam_l...
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
    apply isub_lpam_r...
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

(** The following results hold without [izero] only. *)
Context {fz : ifzer = false}.

(** Embedding of [IAtom] into [Atom] *)
Variable i2a : IAtom -> Atom.
Hypothesis i2a_inj : injective i2a.

Lemma cut_admissible_ifragment {P} : (forall l A, ~ ipgax P l A) ->
  forall FS, ifragment FS -> forall l A,
    ill_ps P (fun l A => Forall FS (A :: l)) l A ->
    ill_ps (cutrm_ipfrag P) (fun l A => Forall FS (A :: l)) l A.
Proof with myeeasy.
intros P_axfree FS HFS l A pi.
assert (Forall FS (A :: l)) as HFSl by (destruct pi ; myeeasy).
apply ill_ps_is_ill in pi.
destruct pi as [s pi].
eapply (@cut_admissible_ill_axfree fz) in pi...
clear s ; destruct pi as [s pi].
apply ill_is_ill_ps in pi.
apply iconservativity...
Qed.

Lemma iconservativity_cut_axfree {P} : (forall l A, ~ ipgax P l A) ->
  forall FS, ifragment FS ->
    forall l A s, ill P l A s -> Forall FS (A :: l) ->
      ill_ps P (fun l A => Forall FS (A :: l)) l A.
Proof with try eassumption ; try reflexivity.
intros P_axfree FS Hf l A s pi HFS.
eapply (@cut_admissible_ill_axfree fz) in pi...
clear s ; destruct pi as [s pi].
apply ill_is_ill_ps in pi.
eapply iconservativity in pi...
clear - pi ; induction pi ;
  try (constructor ; assumption ; fail).
- eapply ex_ps_ir...
- eapply @cut_ps_ir...
  destruct P.
  inversion f.
Qed.

End Fragments.


(** ** Non conservativity of [ll] over [ill] in presence of [izero] *)

Section Non_Conservativity.

Variable P : ipfrag.
Hypothesis fz : ifzer = true.
Hypothesis fp : ipperm P = true.
Hypothesis fc : ipcut P = false.
Hypothesis fg : forall l a, ~ ipgax P l a.

Variable i2a : IAtom -> Atom.

Variable x : IAtom.
Variable y : IAtom.
Variable z : IAtom.

(** Counter example from Harold Schellinx *)
Definition cons_counter_ex :=
  ilmap (ilmap (ilmap (ivar x) (ivar y)) (@izero fz))
        (itens (ivar x) (ilmap (@izero fz) (ivar z))).

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
  try now (destruct l1 ; inversion H0) ;
  subst...
- symmetry in H1.
  apply PEperm_nil in H1 ; subst.
  apply H in H0...
- destruct l1 ; destruct l0 ; inversion H0.
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
- destruct l1 ; inversion H0 ; subst.
  + rewrite app_nil_l in H1 ; inversion H1.
  + inversion H1.
    destruct l1 ; inversion H4.
- destruct l1 ; destruct lw ; inversion H0 ; destruct l1 ; inversion H6.
- rewrite fc in f ; inversion f.
- apply fg in H0...
Qed.

Fact no_biat_map_prove_ill : forall i j, i <> j ->
  forall n, ~ ill P nil (ilmap (ivar i) (ivar j)) n.
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
  ~ ill P (ilmap (ilmap (ivar x) (ivar y)) (@izero fz) :: nil) (ivar x) n.
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
- destruct l1 ; inversion H1 ; destruct l1 ; inversion H3.
- destruct l1 ; destruct lw ; inversion H0 ; destruct l1 ; inversion H4.
- rewrite fc in f ; inversion f.
- apply fg in H0...
Qed.

Fact pre_counter_ex_ill : forall n,
  ~ @ill P (ilmap (ilmap (ivar x) (ivar y)) (@izero fz) :: nil)
           (itens (ivar x) (ilmap (@izero fz) (ivar z))) n.
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



