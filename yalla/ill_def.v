(* ill library for yalla *)


(** * Intuitionistic Linear Logic *)
(* not cuts here, see ill_cut.v for cut admissibility, and ill_prop.v for other properties *)

Require Import CMorphisms.

Require Import Bool_more.
Require Import List_more.
Require Import List_Type_more.
Require Import Permutation_Type_more.
Require Import genperm_Type.

Require Export basic_misc.
Require Export iformulas.


(** ** Intuitionistic fragments for proofs *)

Definition NoIAxioms := (existT (fun x => x -> list iformula * iformula) _ Empty_fun).

Record ipfrag := mk_ipfrag {
  ipcut : bool ;
  ipgax : { iptypgax : Type & iptypgax -> list iformula * iformula } ;
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

Definition axupd_ipfrag P G := mk_ipfrag (ipcut P) G (ipperm P).

Definition cutupd_ipfrag P b := mk_ipfrag b (ipgax P) (ipperm P).

Definition cutrm_ipfrag P := cutupd_ipfrag P false.

Lemma cutupd_ipfrag_true : forall P, le_ipfrag P (cutupd_ipfrag P true).
Proof.
intros P.
nsplit 3 ; try reflexivity.
- apply leb_true.
- intros a ; exists a ; reflexivity.
Qed.


(** ** Rules *)

Inductive ill P : list iformula -> iformula -> Type :=
| ax_ir : forall X, ill P (ivar X :: nil) (ivar X)
| ex_ir : forall l1 l2 A, ill P l1 A -> PEperm_Type (ipperm P) l1 l2 ->
                          ill P l2 A
| ex_oc_ir : forall l1 lw lw' l2 A, ill P (l1 ++ map ioc lw ++ l2) A ->
               Permutation_Type lw lw' -> ill P (l1 ++ map ioc lw' ++ l2) A
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
| gen_irr : forall A l,
             ill P (l ++ A :: nil) N -> ill P l (igen A)
| gen_ilr : forall A l, ill P l A -> ill P (igen A :: l) N
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
| with_ilr1 : forall A B l1 l2 C, ill P (l1 ++ A :: l2) C ->
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
| co_ilr : forall A l1 l2 C,
            ill P (l1 ++ ioc A :: ioc A :: l2) C -> ill P (l1 ++ ioc A :: l2) C
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
| ex_oc_ir _ _ _ _ _ _ pi0 _ => S (ipsize pi0)
| one_irr _ => 1
| one_ilr _ _ _ _ pi0 => S (ipsize pi0)
| tens_irr _ _ _ _ _ pi1 pi2 => S (ipsize pi1 + ipsize pi2)
| tens_ilr _ _ _ _ _ _ pi0 => S (ipsize pi0)
| lpam_irr _ _ _ _ pi0 => S (ipsize pi0)
| lpam_ilr _ _ _ _ _ _ _ pi1 pi2 => S (ipsize pi1 + ipsize pi2)
| gen_irr _ _ _ pi0 => S (ipsize pi0)
| gen_ilr _ _ _ pi0 => S (ipsize pi0)
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
| co_ilr _ _ _ _ _ pi0 => S (ipsize pi0)
| cut_ir _ _ _ _ _ _ pi1 pi2 => S (ipsize pi1 + ipsize pi2)
| gax_ir _ _ => 1
end.

Lemma stronger_ipfrag P Q : le_ipfrag P Q -> forall l A, ill P l A -> ill Q l A.
Proof with myeeasy.
intros Hle l A H.
induction H ; try (econstructor ; myeeasy ; fail).
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
Lemma co_list_ilr {P} : forall l l1 l2 C,
  ill P (l1 ++ map ioc l ++ map ioc l ++ l2) C ->
  ill P (l1 ++ map ioc l ++ l2) C.
Proof with myeeasy ; try PEperm_Type_solve.
induction l ; intros l1 l2 C pi...
simpl ; apply co_ilr.
cons2app ; rewrite 2 app_assoc.
apply IHl ; list_simpl.
rewrite app_assoc ; rewrite 2 app_comm_cons.
rewrite (app_assoc _ _ l2) in pi ; rewrite <- map_app in pi.
replace (ioc a :: ioc a :: map ioc l ++ map ioc l)
  with (map ioc (a :: a :: l ++ l))
  by (list_simpl ; reflexivity).
eapply ex_oc_ir...
Qed.

(** *** Some tactics for manipulating rules *)

Ltac destruct_ill H f X l Hl Hr HP a :=
  match type of H with
  | ill _ _ _ => destruct H as [ X
                               | l ? ? Hl HP
                               | l ? ? ? ? Hl HP
                               | 
                               | ? ? ? Hl
                               | ? ? ? ? Hl Hr
                               | ? ? ? ? ? Hl
                               | ? ? ? Hl
                               | ? ? ? ? ? ? Hl Hr
                               | ? ? Hl
                               | ? ? Hl
                               | ? ? ? Hl
                               | ? ? ? ? ? ? Hl Hr
                               | ? ? Hl
                               | ? ? Hl
                               | l
                               | ? ? ? Hl Hr
                               | ? ? ? ? ? Hl
                               | ? ? ? ? ? Hl
                               | ? ? ?
                               | ? ? ? Hl
                               | ? ? ? Hl
                               | ? ? ? ? ? Hl Hr
                               | ? ? Hl
                               | ? ? ? ? Hl
                               | ? ? ? ? Hl
                               | ? ? ? ? Hl
                               | f ? ? ? ? ? Hl Hr
                               | a ] ; subst
  end.


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
- apply gen_irr.
  apply gen_ilr...
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

Lemma neg_map_rule {P} :
  (forall a, In_Type N (fst (projT2 (ipgax P) a)) -> False) ->
  forall l0 l1 l2 C D (pi0 : ill P l0 C) (pi : ill P (l1 ++ N :: l2) D),
    { pi : ill P (l1 ++ l0 ++ ineg C :: l2) D
         & ipsize pi < S (ipsize pi0 + ipsize pi) }.
Proof with myeeasy.
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
- dichot_Type_elt_app_exec Heq ; subst.
  + list_simpl in IHpi.
    assert (pi':=IHpi _ _ eq_refl).
    rewrite app_comm_cons in pi' ; rewrite 2 app_assoc in pi'.
    destruct pi' as [pi' Hs].
    rewrite app_comm_cons ; rewrite 2 app_assoc.
    exists (ex_oc_ir _ _ _ _ _ _ pi' p)...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * exfalso.
      decomp_map Heq0 ; inversion Heq0.
    * rewrite 2 app_assoc in IHpi.
      assert (pi':=IHpi _ _ eq_refl).
      list_simpl in pi' ; destruct pi' as [pi' Hs].
      list_simpl ; exists (ex_oc_ir _ _ _ _ _ _ pi' p)...
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
- list_simpl in IHpi.
  assert (pi' := IHpi _ _ eq_refl).
  rewrite app_comm_cons in pi'.
  rewrite 2 app_assoc in pi'.
  destruct pi' as [pi' Hs].
  rewrite app_assoc.
  exists (gen_irr _ _ _ pi')...
- destruct l1' ; inversion Heq ; subst.
  list_simpl.
  destruct (IHpi _ _ eq_refl) as [pi' Hs].
  list_simpl.
  exists (gen_ilr _ _ _ pi')...
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
  + rewrite 2 app_comm_cons in IHpi ; rewrite app_assoc in IHpi.
    assert (pi' := IHpi _ _ eq_refl).
    list_simpl in pi' ; destruct pi' as [pi' Hs].
    list_simpl ; exists (co_ilr _ _ _ _ _ pi')...
  + symmetry in Heq1.
    destruct l3 ; inversion Heq1 ; subst.
    list_simpl in IHpi.
    assert (pi' := IHpi _ _ eq_refl).
    rewrite app_comm_cons in pi' ; rewrite 2 app_assoc in pi'.
    destruct pi' as [pi' Hs].
    rewrite app_comm_cons ; rewrite 2 app_assoc.
    exists (co_ilr _ _ _ _ _ pi')...
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

Lemma ilpam_to_igen {P} : forall A, ill P (ilpam A N :: nil) (igen A).
Proof.
intros A.
apply gen_irr.
list_simpl.
rewrite <- (app_nil_l _).
rewrite <- (app_nil_r (A :: nil)).
apply lpam_ilr ; apply ax_exp_ill.
Qed.

Lemma igen_to_ilpam {P} : forall A, ill P (igen A :: nil) (ilpam A N).
Proof.
intros A.
apply lpam_irr.
list_simpl.
apply gen_ilr.
apply ax_exp_ill.
Qed.

Lemma gen_pam_rule {P} :
  (forall a, In_Type N (fst (projT2 (ipgax P) a)) -> False) ->
  forall l0 l1 l2 C D (pi0 : ill P l0 C) (pi : ill P (l1 ++ N :: l2) D),
    { pi : ill P (l1 ++ igen C :: l0 ++ l2) D
         & ipsize pi < S (ipsize pi0 + ipsize pi) }.
Proof with myeeasy.
intros Hgax.
intros l0 l1 l2 C D pi0 pi.
remember (l1 ++ N :: l2) as l.
revert l1 l2 Heql.
induction pi ; intros l1' l2' Heq ; subst ;
  try (destruct (IHpi _ _ eq_refl) as [pi' Hs]) ;
  try (destruct (IHpi1 _ _ eq_refl) as [pi1' Hs1]) ;
  try (destruct (IHpi2 _ _ eq_refl) as [pi2' Hs2]).
- destruct l1' ; inversion Heq ; subst.
  + list_simpl.
    exists (gen_ilr _ _ _ pi0)...
  + destruct l1' ; inversion H1.
- case_eq (ipperm P) ; intros Hperm ; rewrite_all Hperm.
  + apply PEperm_Type_vs_elt_inv in p.
    destruct p as [(l3 & l4) Heq HP] ; simpl in HP ; subst.
    destruct (IHpi _ _ eq_refl) as [pi' Hs].
    assert (PEperm_Type (ipperm P) (l3 ++ igen C :: l0 ++ l4)
                                   (l1' ++ igen C :: l0 ++ l2')) as HP'.
    { rewrite Hperm.
      symmetry.
      apply Permutation_Type_elt.
      apply Permutation_Type_app_middle... }
    exists (ex_ir _ _ _ _ pi' HP')...
  + simpl in p ; subst.
    destruct (IHpi _ _ eq_refl) as [pi' Hs].
    exists pi'...
- dichot_Type_elt_app_exec Heq ; subst.
  + list_simpl in IHpi.
    assert (pi':=IHpi _ _ eq_refl).
    rewrite app_comm_cons in pi' ; rewrite 2 app_assoc in pi'.
    destruct pi' as [pi' Hs].
    rewrite app_comm_cons ; rewrite 2 app_assoc.
    exists (ex_oc_ir _ _ _ _ _ _ pi' p)...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * exfalso.
      decomp_map Heq0 ; inversion Heq0.
    * rewrite 2 app_assoc in IHpi.
      assert (pi':=IHpi _ _ eq_refl).
      list_simpl in pi' ; destruct pi' as [pi' Hs].
      list_simpl ; exists (ex_oc_ir _ _ _ _ _ _ pi' p)...
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
  rewrite app_comm_cons.
  rewrite app_assoc.
  exists (lpam_irr _ _ _ _ pi')...
- dichot_Type_elt_app_exec Heq ; subst.
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * destruct (IHpi1 _ _ eq_refl) as [pi' Hs].
      list_simpl.
      rewrite (app_comm_cons _ _ (igen C)).
      rewrite 2 (app_assoc _ _ l3).
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
    rewrite (app_comm_cons _ _ (igen C)) in pi'.
    rewrite 2 app_assoc in pi'.
    destruct pi' as [pi' Hs].
    rewrite (app_comm_cons _ _ (igen C)).
    rewrite 2 app_assoc.
    exists (lpam_ilr _ _ _ _ _ _ _ pi1 pi')...
- list_simpl in IHpi.
  assert (pi' := IHpi _ _ eq_refl).
  rewrite app_comm_cons in pi'.
  rewrite 2 app_assoc in pi'.
  destruct pi' as [pi' Hs].
  rewrite app_comm_cons.
  rewrite app_assoc.
  exists (gen_irr _ _ _ pi')...
- destruct l1' ; inversion Heq ; subst.
  list_simpl.
  destruct (IHpi _ _ eq_refl) as [pi' Hs].
  list_simpl.
  exists (gen_ilr _ _ _ pi')...
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
  + rewrite 2 app_comm_cons in IHpi ; rewrite app_assoc in IHpi.
    assert (pi' := IHpi _ _ eq_refl).
    list_simpl in pi' ; destruct pi' as [pi' Hs].
    list_simpl ; exists (co_ilr _ _ _ _ _ pi')...
  + symmetry in Heq1.
    destruct l3 ; inversion Heq1 ; subst.
    list_simpl in IHpi.
    assert (pi' := IHpi _ _ eq_refl).
    rewrite app_comm_cons in pi' ; rewrite 2 app_assoc in pi'.
    destruct pi' as [pi' Hs].
    rewrite app_comm_cons ; rewrite 2 app_assoc.
    exists (co_ilr _ _ _ _ _ pi')...
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


(** ** Consistency properties *)

Lemma strong_contradition_general_contradiction_ill {P} : ipcut P = true ->
  ill P nil izero -> forall l C, ill P l C.
Proof.
intros Hcut pi l C.
rewrite <- (app_nil_l _).
rewrite <- (app_nil_l _).
eapply (@cut_ir _ Hcut) ; try eassumption.
apply zero_ilr.
Qed.

