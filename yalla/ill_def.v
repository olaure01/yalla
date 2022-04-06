(* ill library for yalla *)


(** * Intuitionistic Linear Logic *)
(* no results about cuts here, see ill_cut.v for cut admissibility, and ill_prop.v for other properties *)

From Coq Require Import CMorphisms BoolOrder.
From OLlibs Require Import dectype funtheory List_more Permutation_Type_more GPermutation_Type.
From Yalla Require Export iformulas.


Section Atoms.

Context { preiatom : DecType }.
Notation iformula := (@iformula preiatom).

(** ** Intuitionistic fragments for proofs *)

Definition NoIAxioms := (existT (fun x => x -> list iformula * iformula) _ Empty_fun).

Record ipfrag := mk_ipfrag {
  ipcut : bool;
  ipgax : { iptypgax : Type & iptypgax -> list iformula * iformula };
  ipperm : bool }.

Definition le_ipfrag P Q :=
  prod 
     (Bool.le (ipcut P) (ipcut Q))
  (prod
     (forall a, { b | projT2 (ipgax P) a = projT2 (ipgax Q) b })
     (Bool.le (ipperm P) (ipperm Q))).

Lemma le_ipfrag_trans P Q R :
  le_ipfrag P Q -> le_ipfrag Q R -> le_ipfrag P R.
Proof.
intros [Hc1 [Ha1 Hp1]] [Hc2 [Ha2 Hp2]].
repeat split.
- now apply (le_trans _ (ipcut Q)).
- intros a.
  destruct (Ha1 a) as [b Heq].
  destruct (Ha2 b) as [c Heq2].
  exists c; transitivity (projT2 (ipgax Q) b); assumption.
- now apply (le_trans _ (ipperm Q)).
Qed.

Instance le_ipfrag_po : PreOrder le_ipfrag.
Proof.
split.
- repeat split; try reflexivity.
  intros a; exists a; reflexivity.
- intros P Q R.
  apply le_ipfrag_trans.
Qed.

Definition axupd_ipfrag P G := mk_ipfrag (ipcut P) G (ipperm P).

Definition cutupd_ipfrag P b := mk_ipfrag b (ipgax P) (ipperm P).

Definition cutrm_ipfrag P := cutupd_ipfrag P false.

Lemma cutupd_ipfrag_true P : le_ipfrag P (cutupd_ipfrag P true).
Proof.
repeat split; try reflexivity.
- apply le_true.
- intros a; exists a; reflexivity.
Qed.


(** ** Rules *)

Inductive ill P : list iformula -> iformula -> Type :=
| ax_ir : forall X, ill P (ivar X :: nil) (ivar X)
| ex_ir : forall l1 l2 A, ill P l1 A -> PEPermutation_Type (ipperm P) l1 l2 ->
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
  Proper ((@PEPermutation_Type _ (ipperm P)) ==> arrow) (fun l => ill P l A).
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
Proof.
intros [Hcut [Hgax Hp]] l A H.
induction H; try now constructor.
- apply (ex_ir _ l1); [ assumption | ].
  hyps_GPermutation_Type_unfold; unfold PEPermutation_Type.
  now destruct (ipperm P); destruct (ipperm Q);
    cbn in Hp; try inversion Hp; subst.
- econstructor; eassumption.
- rewrite f in Hcut.
  eapply (@cut_ir _ Hcut); eassumption.
- destruct (Hgax a) as [b ->].
  apply gax_ir.
Qed.

(** Generalized weakening for lists *)
Lemma wk_list_ilr {P} l l1 l2 C :
  ill P (l1 ++ l2) C -> ill P (l1 ++ map ioc l ++ l2) C.
Proof.
induction l in l1, l2, C |- *; intros pi; try assumption.
apply wk_ilr.
apply IHl; assumption.
Qed.

(** Generalized contraction for lists *)
Lemma co_list_ilr {P} l l1 l2 C :
  ill P (l1 ++ map ioc l ++ map ioc l ++ l2) C ->
  ill P (l1 ++ map ioc l ++ l2) C.
Proof.
induction l in l1, l2, C |- *; intros pi; try assumption.
cbn; apply co_ilr.
cons2app; rewrite 2 app_assoc.
apply IHl; list_simpl.
rewrite app_assoc, 2 app_comm_cons.
rewrite (app_assoc _ _ l2), <- map_app in pi.
replace (ioc a :: ioc a :: map ioc l ++ map ioc l)
  with (map ioc (a :: a :: l ++ l))
  by (list_simpl; reflexivity).
eapply ex_oc_ir; try eassumption.
cbn; apply Permutation_Type_cons; [ reflexivity | ].
symmetry; apply Permutation_Type_middle.
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
Lemma ax_exp_ill {P} A : ill P (A :: nil) A.
Proof.
induction A.
- apply ax_ir.
- rewrite <- (app_nil_l (ione :: _)).
  apply one_ilr.
  apply one_irr.
- rewrite <- (app_nil_l (itens _ _ :: _)).
  apply tens_ilr.
  list_simpl ; cons2app.
  apply tens_irr; assumption.
- apply lpam_irr.
  list_simpl.
  rewrite <- (app_nil_l (ilpam _ _ :: _)).
  rewrite <- (app_nil_l nil).
  rewrite (app_comm_cons _ _ A1).
  apply lpam_ilr ; list_simpl; assumption.
- apply gen_irr.
  apply gen_ilr; assumption.
- apply lmap_irr.
  list_simpl.
  cons2app.
  rewrite <- (app_nil_l ((A1 :: _) ++ _)).
  apply lmap_ilr ; list_simpl; assumption.
- apply neg_irr.
  cons2app.
  apply neg_ilr; assumption.
- apply top_irr.
- apply with_irr.
  + rewrite <- (app_nil_l (iwith _ _ :: _)).
    apply with_ilr1; assumption.
  + rewrite <- (app_nil_l (iwith _ _ :: _)).
    apply with_ilr2; assumption.
- rewrite <- (app_nil_l (izero :: _)).
  apply zero_ilr.
- rewrite <- (app_nil_l (iplus _ _ :: _)).
  apply plus_ilr.
  + apply plus_irr1; assumption.
  + apply plus_irr2; assumption.
- change (ioc A :: nil) with (map ioc (A :: nil)).
  apply oc_irr.
  cbn ; rewrite <- (app_nil_l (ioc A :: _)).
  apply de_ilr; assumption.
Qed.


(** ** Consistency properties *)

Lemma strong_contradition_general_contradiction_ill {P} : ipcut P = true ->
  ill P nil izero -> forall l C, ill P l C.
Proof.
intros Hcut pi l C.
rewrite <- 2 (app_nil_l _).
apply (@cut_ir _ Hcut _ _ _ _ _ pi), zero_ilr.
Qed.

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
                               | f ? ? ? ? ? Hl Hr
                               | a ] ; subst
  end.
