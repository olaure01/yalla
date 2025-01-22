(** * Intuitionistic Linear Logic *)
(* no results about cuts here, see ill_cut.v for cut admissibility, and ill_prop.v for other properties *)

From Coq Require Import CMorphisms.
From Coq Require BoolOrder.
From OLlibs Require Import dectype funtheory List_more Permutation_Type_more GPermutation_Type.
From Yalla Require Export iformulas.

Set Implicit Arguments.


Section Atoms.

Context {preiatom : DecType}.
Notation iformula := (@iformula preiatom).

(** ** Intuitionistic fragments for proofs *)

Definition NoIAxioms := existT (fun x => x -> list iformula * iformula) _ Empty_fun.

Definition ipcut_none (A : iformula) := false.
Definition ipcut_all (A : iformula) := true.

Record ipfrag := mk_ipfrag {
  ipcut : iformula -> bool;
  ipgax : { iptypgax : Type & iptypgax -> list iformula * iformula };
  ipperm : bool }.

Definition no_iax P := notT (projT1 (ipgax P)).

Definition noN_iax P := forall a, notT (In_inf N (fst (projT2 (ipgax P) a))).

Definition atomic_iax P := forall a,
  Forall_inf iatomic (fst (projT2 (ipgax P) a)) * iatomic (snd (projT2 (ipgax P) a)).

Definition full_icut P := forall C, ipcut P C = true.

Definition no_icut P := forall C, ipcut P C = false.

Definition icut_closed P := forall a b l1 l2,
  fst (projT2 (ipgax P) b) = l1 ++ snd (projT2 (ipgax P) a) :: l2 ->
  { c | l1 ++ fst (projT2 (ipgax P) a) ++ l2 = fst (projT2 (ipgax P) c)
      & snd (projT2 (ipgax P) b) = snd (projT2 (ipgax P) c) }.

Definition le_ipfrag P Q :=
   ((forall A, Bool.le (ipcut P A) (ipcut Q A))
 * ((forall a, { b | projT2 (ipgax P) a = projT2 (ipgax Q) b })
 *  (Bool.le (ipperm P) (ipperm Q))))%type.

Lemma le_ipfrag_trans P Q R : le_ipfrag P Q -> le_ipfrag Q R -> le_ipfrag P R.
Proof.
intros [Hc1 [Ha1 Hp1]] [Hc2 [Ha2 Hp2]].
repeat split.
- intro A. now apply (BoolOrder.le_trans _ (ipcut Q A)).
- intro a. destruct (Ha1 a) as [b Heq], (Ha2 b) as [c Heq2].
  exists c. transitivity (projT2 (ipgax Q) b); assumption.
- apply (BoolOrder.le_trans _ (ipperm Q)); assumption.
Qed.

Instance le_ipfrag_po : PreOrder le_ipfrag.
Proof.
split.
- repeat split; [ reflexivity | | reflexivity ].
  intro a. exists a. reflexivity.
- intros P Q R. apply le_ipfrag_trans.
Qed.

Definition axupd_ipfrag P G := mk_ipfrag (ipcut P) G (ipperm P).

(* apply [f] to each element of [ipgax] *)
Definition axmodif_ipfrag P f := axupd_ipfrag P ((existT (fun x => x -> _) _ (fun a => f (projT2 (ipgax P) a)))).

(* extend [pgax] with familiy [f] indexed by [T] *)
Definition axext_ipfrag P T (f : T -> _) := axupd_ipfrag P ((existT (fun x => x -> _) _
  (fun a => match a with
            | inl x => projT2 (ipgax P) x
            | inr x => f x
            end))).

Definition cutupd_ipfrag P b := mk_ipfrag b (ipgax P) (ipperm P).

Definition cutrm_ipfrag P := cutupd_ipfrag P ipcut_none.

Lemma noicut_cutrm P : no_icut (cutrm_ipfrag P).
Proof. intro. reflexivity. Qed.

Lemma cutupd_ipfrag_true P : le_ipfrag P (cutupd_ipfrag P ipcut_all).
Proof.
repeat split; [ | | reflexivity ].
- intro. apply BoolOrder.le_true.
- intro a. exists a. reflexivity.
Qed.

Lemma cutrm_ipfrag_le P : le_ipfrag (cutrm_ipfrag P) P.
Proof. repeat split; [ | reflexivity ]. intro a. exists a. reflexivity. Qed.


(** ** Rules *)

Inductive ill P : list iformula -> iformula -> Type :=
| ax_ir X : ill P (ivar X :: nil) (ivar X)
| ex_ir l1 l2 A : ill P l1 A -> PEPermutation_Type (ipperm P) l1 l2 -> ill P l2 A
| ex_oc_ir l1 lw lw' l2 A :
    ill P (l1 ++ map ioc lw ++ l2) A -> Permutation_Type lw lw' -> ill P (l1 ++ map ioc lw' ++ l2) A
| one_irr : ill P nil ione
| one_ilr l1 l2 A : ill P (l1 ++ l2) A -> ill P (l1 ++ ione :: l2) A
| tens_irr A B l1 l2 : ill P l1 A -> ill P l2 B -> ill P (l1 ++ l2) (itens A B)
| tens_ilr A B l1 l2 C : ill P (l1 ++ A :: B :: l2) C -> ill P (l1 ++ itens A B :: l2) C
| lpam_irr A B l : ill P (l ++ A :: nil) B -> ill P l (ilpam A B)
| lpam_ilr A B l0 l1 l2 C : ill P l0 A -> ill P (l1 ++ B :: l2) C -> ill P (l1 ++ ilpam A B :: l0 ++ l2) C
| gen_irr A l : ill P (l ++ A :: nil) N -> ill P l (igen A)
| gen_ilr A l : ill P l A -> ill P (igen A :: l) N
| lmap_irr A B l : ill P (A :: l) B -> ill P l (ilmap A B)
| lmap_ilr A B l0 l1 l2 C : ill P l0 A -> ill P (l1 ++ B :: l2) C -> ill P (l1 ++ l0 ++ ilmap A B :: l2) C
| neg_irr A l : ill P (A :: l) N -> ill P l (ineg A)
| neg_ilr A l : ill P l A -> ill P (l ++ ineg A :: nil) N
| top_irr l : ill P l itop
| with_irr A B l : ill P l A -> ill P l B -> ill P l (iwith A B)
| with_ilr1 A B l1 l2 C : ill P (l1 ++ A :: l2) C -> ill P (l1 ++ iwith A B :: l2) C
| with_ilr2 A B l1 l2 C : ill P (l1 ++ A :: l2) C -> ill P (l1 ++ iwith B A :: l2) C
| zero_ilr l1 l2 C : ill P (l1 ++ izero :: l2) C
| plus_irr1 A B l : ill P l A -> ill P l (iplus A B)
| plus_irr2 A B l : ill P l A -> ill P l (iplus B A)
| plus_ilr A B l1 l2 C : ill P (l1 ++ A :: l2) C -> ill P (l1 ++ B :: l2) C -> ill P (l1 ++ iplus A B :: l2) C
| oc_irr A l : ill P (map ioc l) A -> ill P (map ioc l) (ioc A)
| de_ilr A l1 l2 C : ill P (l1 ++ A :: l2) C -> ill P (l1 ++ ioc A :: l2) C
| wk_ilr A l1 l2 C : ill P (l1 ++ l2) C -> ill P (l1 ++ ioc A :: l2) C
| co_ilr A l1 l2 C : ill P (l1 ++ ioc A :: ioc A :: l2) C -> ill P (l1 ++ ioc A :: l2) C
| cut_ir A (f : ipcut P A = true) l0 l1 l2 C : ill P l0 A -> ill P (l1 ++ A :: l2) C-> ill P (l1 ++ l0 ++ l2) C
| gax_ir a : ill P (fst (projT2 (ipgax P) a)) (snd (projT2 (ipgax P) a)).
#[global] Arguments ax_ir [P] _.
#[global] Arguments ex_ir [P] _ _ _ _ _.
#[global] Arguments ex_oc_ir [P] _ _ _ _ _ _ _.
#[global] Arguments one_irr {P}.
#[global] Arguments one_ilr [P] _ _ _.
#[global] Arguments tens_irr [P] _ _ _ _ _ _.
#[global] Arguments tens_ilr [P] _ _ _ _ _ _.
#[global] Arguments lpam_irr [P] _ _ _ _.
#[global] Arguments lpam_ilr [P] _ _ _ _ _ _ _ _.
#[global] Arguments gen_irr [P] _ _ _.
#[global] Arguments gen_ilr [P] _ _ _.
#[global] Arguments lmap_irr [P] _ _ _ _.
#[global] Arguments lmap_ilr [P] _ _ _ _ _ _ _ _.
#[global] Arguments neg_irr [P] _ _ _.
#[global] Arguments neg_ilr [P] _ _ _.
#[global] Arguments top_irr [P] _.
#[global] Arguments with_irr [P] _ _ _ _ _.
#[global] Arguments with_ilr1 [P] _ _ _ _ _ _.
#[global] Arguments with_ilr2 [P] _ _ _ _ _ _.
#[global] Arguments zero_ilr [P] _ _ _.
#[global] Arguments plus_irr1 [P] _ _ _ _.
#[global] Arguments plus_irr2 [P] _ _ _ _.
#[global] Arguments plus_ilr [P] _ _ _ _ _ _ _.
#[global] Arguments oc_irr [P A l] _.
#[global] Arguments de_ilr [P] _ _ _ _ _.
#[global] Arguments wk_ilr [P] _ _ _ _ _.
#[global] Arguments co_ilr [P] _ _ _ _ _.
#[global] Arguments cut_ir [P] _ f [l0 l1 l2 _] _ _.
#[global] Arguments gax_ir [P] _.

Instance ill_perm P A : Proper ((@PEPermutation_Type _ (ipperm P)) ==> arrow) (fun l => ill P l A).
Proof. intros l1 l2 HP pi. eapply ex_ir; eassumption. Qed.

Fixpoint ipsize P l A (pi : ill P l A) :=
match pi with
| ax_ir _ | one_irr | top_irr _ | zero_ilr _ _ _ | gax_ir _ => 1
| ex_ir _ _ _ pi0 _ | ex_oc_ir _ _ _ _ _ pi0 _ => S (ipsize pi0)
| one_ilr _ _ _ pi0 | tens_ilr _ _ _ _ _ pi0 | lpam_irr _ _ _ pi0 | gen_irr _ _ pi0 | gen_ilr _ _ pi0
| lmap_irr _ _ _ pi0 | neg_irr _ _ pi0 | neg_ilr _ _ pi0 => S (ipsize pi0)
| tens_irr _ _ _ _ pi1 pi2 | lpam_ilr _ _ _ _ _ _ pi1 pi2
| lmap_ilr _ _ _ _ _ _ pi1 pi2 | cut_ir _ _ pi1 pi2 => S (ipsize pi1 + ipsize pi2)
| with_ilr1 _ _ _ _ _ pi0 | with_ilr2 _ _ _ _ _ pi0 | plus_irr1 _ _ _ pi0 | plus_irr2 _ _ _ pi0 => S (ipsize pi0)
| with_irr _ _ _ pi1 pi2 | plus_ilr _ _ _ _ _ pi1 pi2 => S (max (ipsize pi1) (ipsize pi2))
| oc_irr pi0 | de_ilr _ _ _ _ pi0 | wk_ilr _ _ _ _ pi0 | co_ilr _ _ _ _ pi0 => S (ipsize pi0)
end.

Lemma stronger_ipfrag P Q (Hfrag : le_ipfrag P Q) l A : ill P l A -> ill Q l A.
Proof.
intro pi. induction pi; try (constructor; assumption).
- apply (ex_ir l1); [ assumption | ].
  destruct Hfrag as [_ [_ Hp]]. apply (PEPermutation_Type_monot (ipperm P) _ Hp), p.
- apply (ex_oc_ir _ lw); assumption.
- destruct Hfrag as [Hcut _]. specialize (Hcut A). rewrite f in Hcut. apply (cut_ir A Hcut); assumption.
- destruct Hfrag as [_ [Hgax _]], (Hgax a) as [b ->]. apply gax_ir.
Defined.

(** Proofs with sequent satisfying a given predicate *)

Fixpoint Forall_isequent P PS l A (pi : ill P l A) : Type :=
match pi with
| ax_ir _ | gax_ir _ => PS l A
| ex_ir _ _ _ pi1 _ | ex_oc_ir _ _ _ _ _ pi1 _ => Forall_isequent PS pi1 * PS l A
| one_irr => PS l A
| one_ilr _ _ _ pi1 | tens_ilr _ _ _ _ _ pi1 | lpam_irr _ _ _ pi1 | gen_irr _ _ pi1 | gen_ilr _ _ pi1
| lmap_irr _ _ _ pi1 | neg_irr _ _ pi1 | neg_ilr _ _ pi1 =>  Forall_isequent PS pi1 * PS l A
| tens_irr _ _ _ _ pi1 pi2 | lpam_ilr _ _ _ _ _ _ pi1 pi2 | lmap_ilr _ _ _ _ _ _ pi1 pi2 =>
    Forall_isequent PS pi1 * Forall_isequent PS pi2 * PS l A
| top_irr _ | zero_ilr _ _ _ => PS l A
| with_ilr1 _ _ _ _ _ pi1 | with_ilr2 _ _ _ _ _ pi1 | plus_irr1 _ _ _ pi1 | plus_irr2 _ _ _ pi1
   => Forall_isequent PS pi1 * PS l A
| with_irr _ _ _ pi1 pi2 | plus_ilr _ _ _ _ _ pi1 pi2 => Forall_isequent PS pi1 * Forall_isequent PS pi2 * PS l A
| oc_irr pi1 | de_ilr _ _ _ _ pi1 | wk_ilr _ _ _ _ pi1 | co_ilr _ _ _ _ pi1 => Forall_isequent PS pi1 * PS l A
| cut_ir _ _ pi1 pi2 => Forall_isequent PS pi1 * Forall_isequent PS pi2 * PS l A
end.

Definition Forall_iformula P FS := @Forall_isequent P (fun l A => (Forall_inf FS (A :: l))%type).

Lemma Forall_isequent_is P PS l A (pi : ill P l A) : Forall_isequent PS pi -> PS l A.
Proof. destruct pi; cbn; tauto. Qed.

Lemma Forall_isequent_impl P PS QS (HPQ : forall s x, PS s x -> QS s x) l A (pi : ill P l A) :
  Forall_isequent PS pi -> Forall_isequent QS pi.
Proof.
induction pi;
  try (now cbn; apply HPQ);
  try (now cbn; intros [IH H]; split; auto);
  try (now cbn; intros [[IH1 IH2] H]; split; auto).
Qed.

Lemma Forall_isequent_stronger_ipfrag P Q (Hfrag : le_ipfrag P Q) PS l A (pi : ill P l A) :
  Forall_isequent PS pi -> Forall_isequent PS (stronger_ipfrag Hfrag pi).
Proof.
destruct Hfrag as [Hcut [Hgax Hp]].
induction pi; intros HFS; cbn in HFS; cbn; try tauto.
destruct (Hgax a) as [b Hb].
cbn. rewrite Hb. cbn. rewrite <- Hb. assumption.
Qed.


(** Generalized weakening for lists *)
Lemma wk_list_ilr P l l1 l2 C : ill P (l1 ++ l2) C -> ill P (l1 ++ map ioc l ++ l2) C.
Proof. induction l in l1, l2, C |- *; intro pi; [ assumption | apply wk_ilr, IHl, pi ]. Qed.

(** Generalized contraction for lists *)
Lemma co_list_ilr P l l1 l2 C : ill P (l1 ++ map ioc l ++ map ioc l ++ l2) C -> ill P (l1 ++ map ioc l ++ l2) C.
Proof.
induction l in l1, l2, C |- *; intros pi; try assumption.
cbn. apply co_ilr.
cons2app. rewrite 2 app_assoc. apply IHl. list_simpl.
rewrite app_assoc, 2 app_comm_cons.
rewrite (app_assoc _ _ l2), <- map_app in pi.
replace (ioc a :: ioc a :: map ioc l ++ map ioc l)
  with (map ioc (a :: a :: l ++ l))
  by (list_simpl; reflexivity).
eapply ex_oc_ir; try eassumption.
apply Permutation_Type_cons; [ reflexivity | symmetry; apply Permutation_Type_middle ].
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
                               | ? f ? ? ? ? Hl Hr
                               | a ]; subst
  end.


(** Axiom expansion *)
Lemma ax_exp_ill P A : ill P (A :: nil) A.
Proof.
induction A.
- apply ax_ir.
- rewrite <- (app_nil_l (ione :: _)).
  apply one_ilr, one_irr.
- rewrite <- (app_nil_l (itens _ _ :: _)).
  apply tens_ilr.
  list_simpl. cons2app.
  apply tens_irr; assumption.
- apply lpam_irr.
  list_simpl.
  rewrite <- (app_nil_l (ilpam _ _ :: _)), <- (app_nil_l nil), (app_comm_cons _ _ A1).
  apply lpam_ilr; list_simpl; assumption.
- apply gen_irr, gen_ilr. assumption.
- apply lmap_irr.
  list_simpl. cons2app.
  rewrite <- (app_nil_l ((A1 :: _) ++ _)).
  apply lmap_ilr; list_simpl; assumption.
- apply neg_irr.
  cons2app. apply neg_ilr. assumption.
- apply top_irr.
- apply with_irr; rewrite <- (app_nil_l (iwith _ _ :: _)).
  + apply with_ilr1; assumption.
  + apply with_ilr2; assumption.
- rewrite <- (app_nil_l (izero :: _)).
  apply zero_ilr.
- rewrite <- (app_nil_l (iplus _ _ :: _)).
  apply plus_ilr.
  + apply plus_irr1; assumption.
  + apply plus_irr2; assumption.
- change (ioc A :: nil) with (map ioc (A :: nil)).
  apply oc_irr.
  cbn. rewrite <- (app_nil_l (ioc A :: _)). apply de_ilr. assumption.
Qed.


(** ** Consistency properties *)

Lemma strong_contradition_general_contradiction_ill P : ipcut P izero = true ->
  ill P nil izero -> forall l C, ill P l C.
Proof. intros Hcut pi l C. rewrite <- 2 (app_nil_l _). apply (@cut_ir _ _ Hcut _ _ _ _ pi), zero_ilr. Qed.

End Atoms.

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
                               | ? f ? ? ? ? Hl Hr
                               | a ]; subst
  end.
