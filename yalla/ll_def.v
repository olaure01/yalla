(** * Linear Logic with explicit permutations *)
(* not cuts here, see ll_cut.v for cut admissibility and ll_prop.v for other properties *)

From Coq Require Import CMorphisms BoolOrder PeanoNat Lia.
From Coq Require Permutation.
From OLlibs Require Import dectype funtheory List_more Dependent_Forall_Type
                           Permutation_Type_more GPermutation_Type.
From Yalla Require Export formulas.

Import EqNotations.

Set Implicit Arguments.


Section Atoms.

Context {atom : DecType}.
Notation formula := (@formula atom).

Notation Dependent_Forall_inf_forall_formula :=
  (Dependent_Forall_inf_forall (list_eq_dec (@eqb formulas_dectype) (fun x y => proj1 (eqb_eq x y))
                                                                    (fun x y => proj2 (eqb_eq x y)))).

Ltac Dependent_Forall_inversion_formula H := Dependent_Forall_inversion (@formulas_dectype atom) H.

(** ** Fragments for proofs *)

Definition NoAxioms := (existT (fun x => x -> list formula) _ Empty_fun).

Definition pcut_none (A : formula) := false.
Definition pcut_all (A : formula) := true.

Definition pmix_none (n : nat) := false.
Definition pmix_all (n : nat) := true.
Definition pmix0 n :=
match n with
| 0 => true
| _ => false
end.
Definition pmix2 n :=
match n with
| 2 => true
| _ => false
end.
Definition pmix02 n :=
match n with
| 0 | 2 => true
| _ => false
end.


(** Parameters for [ll] provability:
 - [pcut], [pmix0] and [pmix2] determine whether the corresponding rule is in the system or not;
 - [pperm] is [false] for exchange rule modulo cyclic permutations\
           and [true] for exchange rule modulo arbitrary permutations;
 - [pgax] determines the sequents which are valid as axioms in proofs.
*)
Record pfrag := mk_pfrag {
  pcut : formula -> bool;
  pgax : { ptypgax : Type & ptypgax -> list formula };
  pmix : nat -> bool;
  pperm : bool }.

Definition no_ax P := notT (projT1 (pgax P)).

Definition atomic_ax P := forall a, Forall_inf atomic (projT2 (pgax P) a).

Definition gax_excludes P A := forall a, notT (In_inf A (projT2 (pgax P) a)).

Definition full_cut P := forall C, pcut P C = true.

Definition no_cut P := forall C, pcut P C = false.

Definition cut_closed_form P C := forall a b l1 l2 l3 l4,
  projT2 (pgax P) a = l1 ++ C :: l2 -> projT2 (pgax P) b = l3 ++ dual C :: l4 ->
  { c | projT2 (pgax P) c = l3 ++ l2 ++ l1 ++ l4 }.

Definition cut_closed P := forall C, cut_closed_form P C.

(** Order relation on proof fragments: [P] is more restrictive than [Q]. *)
Definition le_pfrag P Q :=
  ((forall A, Bool.le (pcut P A) (pcut Q A))
* ((forall a, { b | projT2 (pgax P) a = projT2 (pgax Q) b })
* ((forall n, Bool.le (pmix P n) (pmix Q n))
*  (Bool.le (pperm P) (pperm Q)))))%type.

Lemma le_pfrag_trans P Q R : le_pfrag P Q -> le_pfrag Q R -> le_pfrag P R.
Proof.
intros (Hc1 & Ha1 & Hm1 & Hp1) (Hc2 & Ha2 & Hm2 & Hp2).
repeat split; try (eapply BoolOrder.le_trans; eassumption).
- intros A. apply BoolOrder.le_trans with (pcut Q A); [ apply Hc1 | apply Hc2 ].
- intros a. destruct (Ha1 a) as [b Heq]. destruct (Ha2 b) as [c Heq2].
  exists c. etransitivity; eassumption.
- intros n. apply BoolOrder.le_trans with (pmix Q n); [ apply Hm1 | apply Hm2 ].
Qed.

#[export] Instance le_pfrag_po : PreOrder le_pfrag | 50.
Proof.
split.
- repeat split; try reflexivity.
  intros a. exists a. reflexivity.
- intro. apply le_pfrag_trans.
Qed.

(** Same proof fragment as [P] but with value [G] for [pgax]. *)
Definition axupd_pfrag P G := mk_pfrag (pcut P) G (pmix P) (pperm P).

(* apply [f] to each element of [pgax] *)
Definition axmodif_pfrag P f := axupd_pfrag P ((existT (fun x => x -> _) _ (fun a => f (projT2 (pgax P) a)))).

(* extend [pgax] with familiy [f] indexed by [T] *)
Definition axext_pfrag P T (f : T -> _) := axupd_pfrag P ((existT (fun x => x -> _) _
  (fun a => match a with
            | inl x => projT2 (pgax P) x
            | inr x => f x
            end))).


(** Same proof fragment as [P] but with value [b] for [pcut]. *)
Definition cutupd_pfrag P b := mk_pfrag b (pgax P) (pmix P) (pperm P).

Lemma cutupd_pfrag_true P : le_pfrag P (cutupd_pfrag P pcut_all).
Proof.
repeat split; try reflexivity.
- intro. apply BoolOrder.le_true.
- intros a. exists a. reflexivity.
Qed.

(** Same proof fragment as [P] but without the [cut] rule. *)
Definition cutrm_pfrag P := cutupd_pfrag P pcut_none.

Lemma nocut_cutrm P : no_cut (cutrm_pfrag P).
Proof. intro. reflexivity. Qed.

Lemma cutrm_cutrm P : cutrm_pfrag (cutrm_pfrag P) = cutrm_pfrag P.
Proof. reflexivity. Qed.

Lemma cutrm_pfrag_le P : le_pfrag (cutrm_pfrag P) P.
Proof. repeat split; try reflexivity. intros a. exists a. reflexivity. Qed.


(** Same proof fragment as [P] but with a different pmix *)
Definition pmixupd_pfrag P pmix := mk_pfrag (pcut P) (pgax P) pmix (pperm P).

Definition pmixupd_point_pfrag P n b :=
  pmixupd_pfrag P (fun k => if (k =? n) then b else pmix P k).

Lemma pmixupd_point_comm P n1 n2 b1 b2 : n1 <> n2 ->
  forall k, pmix (pmixupd_point_pfrag (pmixupd_point_pfrag P n1 b1) n2 b2) k
          = pmix (pmixupd_point_pfrag (pmixupd_point_pfrag P n2 b2) n1 b1) k.
Proof.
intros Hneq k.
destruct (k =? n1) eqn:Heq1, (k =? n2) eqn:Heq2; cbn; rewrite Heq1, Heq2; try reflexivity.
contradiction Hneq. apply Nat.eqb_eq in Heq1 as <-. apply Nat.eqb_eq in Heq2 as <-. reflexivity.
Qed.

(** ** Rules *)

(** The main inductive: [ll] proofs.

All rules have their main formula at first position in the conclusion.
 - [ax_r]: identity rule restricted to propositional variables (general case proved later)
 - [ex_r]: exchange rule (parametrized by [pperm P] to determine allowed permutations)
 - [ex_wn_r]: exchange rule between [wn] formulas
 - [mix_r]: n-ary linear mix rule
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
 - [co_r]: contraction rule with [wn] context inserted between principal formulas\
           to be general enough in the cyclic permutation case
 - [cut_r]: cut rule (the order of lists is matched with the [tens_r] case)
            (available only if [pcut P A = true] where [A] is the cut formula)
 - [gax_r]: generic axiom rule (parametrized by the predicate [pgax P] over sequents)
*)
Inductive ll P : list formula -> Type :=
| ax_r X : ll P (covar X :: var X :: nil)
| ex_r l1 l2 : ll P l1 -> PCPermutation_Type (pperm P) l1 l2 -> ll P l2
| ex_wn_r l1 lw lw' l2 : ll P (l1 ++ map wn lw ++ l2) -> Permutation_Type lw lw' -> ll P (l1 ++ map wn lw' ++ l2)
| mix_r L (f : is_true (pmix P (length L))) : Forall_inf (ll P) L -> ll P (concat L)
| one_r : ll P (one :: nil)
| bot_r l : ll P l -> ll P (bot :: l)
| tens_r A B l1 l2 : ll P (A :: l1) -> ll P (B :: l2) -> ll P (tens A B :: l2 ++ l1)
| parr_r A B l : ll P (A :: B :: l) -> ll P (parr A B :: l)
| top_r l : ll P (top :: l)
| plus_r1 A B l : ll P (A :: l) -> ll P (aplus A B :: l)
| plus_r2 A B l : ll P (A :: l) -> ll P (aplus B A :: l)
| with_r A B l : ll P (A :: l) -> ll P (B :: l) -> ll P (awith A B :: l)
| oc_r A l : ll P (A :: map wn l) -> ll P (oc A :: map wn l)
| de_r A l : ll P (A :: l) -> ll P (wn A :: l)
| wk_r A l : ll P l -> ll P (wn A :: l)
| co_r A l : ll P (wn A :: wn A :: l) -> ll P (wn A :: l)
| cut_r A (f : pcut P A = true) l1 l2 : ll P (dual A :: l1) -> ll P (A :: l2) -> ll P (l2 ++ l1)
| gax_r a : ll P (projT2 (pgax P) a).
#[global] Arguments ax_r [P] _.
#[global] Arguments ex_r [P] _ _ _ _.
#[global] Arguments ex_wn_r [P] _ _ _ _ _ _.
#[global] Arguments one_r {P}.
#[global] Arguments top_r [P] _.
#[global] Arguments oc_r [P A l] _.
#[global] Arguments cut_r [P] _ f [l1 l2] _ _.
#[global] Arguments gax_r [P] _.

Definition mix'_r P L : is_true (pmix P (length L)) -> ll P (flat_map (@projT1 _ (ll P)) L).
Proof.
intros Hmix. rewrite flat_map_concat_map. apply mix_r.
- rewrite length_map. assumption.
- apply list_to_Forall.
Defined.

Section ll_ind.

  Context {P : pfrag}.

  Definition Forall_Proofs (Pred : forall l, ll P l -> Type) L (piL : Forall_inf (ll P) L) :=
    Dependent_Forall_inf Pred piL.

  Lemma Forall_Proofs_to_Forall_inf (Pred : forall l, ll P l -> Type) L (piL : Forall_inf (ll P) L) :
    Forall_Proofs Pred piL -> 
    Forall_inf (fun x => Pred (projT1 x) (projT2 x)) (Forall_to_list piL).
  Proof. intros PpiL. induction PpiL; constructor; assumption. Qed.

  Fixpoint pre_ll_nested_ind l (pi : ll P l) : forall (Pred : forall l, ll P l -> Type),
    (forall X, Pred (covar X :: var X :: nil) (ax_r X)) ->
    (forall l1 l2 pi p, Pred l1 pi -> Pred l2 (ex_r l1 l2 pi p)) ->
    (forall l1 lw lw' l2 pi p, Pred (l1 ++ map wn lw ++ l2) pi ->
       Pred (l1 ++ map wn lw' ++ l2) (ex_wn_r l1 lw lw' l2 pi p)) ->
    (forall L eqpmix PL, Forall_Proofs Pred PL -> Pred (concat L) (mix_r eqpmix PL)) ->
    Pred (one :: nil) one_r ->
    (forall l pi, Pred l pi -> Pred (bot :: l) (bot_r pi)) ->
    (forall A B l1 l2 pi1 pi2, Pred (A :: l1) pi1 -> Pred (B :: l2) pi2 ->
       Pred (tens A B :: l2 ++ l1) (tens_r pi1 pi2)) ->
    (forall A B l pi, Pred (A :: B :: l) pi -> Pred (parr A B :: l) (parr_r pi)) ->
    (forall l, Pred (top :: l) (top_r l)) ->
    (forall A B l pi, Pred (A :: l) pi -> Pred (aplus A B :: l) (plus_r1 B pi)) ->
    (forall A B l pi, Pred (A :: l) pi -> Pred (aplus B A :: l) (plus_r2 B pi)) ->
    (forall A B l pi1 pi2, Pred (A :: l) pi1 -> Pred (B :: l) pi2 -> Pred (awith A B :: l) (with_r pi1 pi2)) ->
    (forall A l pi, Pred (A :: map wn l) pi -> Pred (oc A :: map wn l) (oc_r pi)) ->
    (forall A l pi, Pred (A :: l) pi -> Pred (wn A :: l) (de_r pi)) ->
    (forall A l pi, Pred l pi -> Pred (wn A :: l) (wk_r A pi)) ->
    (forall A l pi, Pred (wn A :: wn A :: l) pi -> Pred (wn A :: l) (co_r pi)) ->
    (forall A f l1 l2 pi1 pi2, Pred (dual A :: l1) pi1 -> Pred (A :: l2) pi2 ->
       Pred (l2 ++ l1) (@cut_r P A f l1 l2 pi1 pi2)) ->
    (forall a, Pred (projT2 (pgax P) a) (gax_r a)) ->
    Pred l pi :=
      fun Pred ax_case ex_case ex_wn_case mix_case one_case bot_case tens_case parr_case
               top_case plus_case1 plus_case2 with_case oc_case de_case wk_case co_case cut_case gax_case =>
      let rec_call {l : list formula} (pi : ll P l) :=
        (pre_ll_nested_ind pi ax_case ex_case ex_wn_case mix_case one_case bot_case tens_case parr_case
                              top_case plus_case1 plus_case2 with_case oc_case de_case wk_case co_case
                              cut_case gax_case) in
    match pi with
    | ax_r X => ax_case X
    | ex_r l1 l2 pi p => ex_case l1 l2 pi p (rec_call pi)
    | ex_wn_r l1 lw lw' l2 pi p => ex_wn_case l1 lw lw' l2 pi p (rec_call pi)
    | @mix_r _ L eqpmix PL => mix_case L eqpmix PL (
                (fix ll_nested_ind_aux (L : list (list formula))
                                       (PL : Forall_inf (ll P) L) : Forall_Proofs Pred PL :=
                   match PL with
                   | Forall_inf_nil _ => Dependent_Forall_inf_nil _ Pred
                   | @Forall_inf_cons _ _ l L Pil PiL => Dependent_Forall_inf_cons _ Pil (rec_call Pil)
                                                            (ll_nested_ind_aux L PiL)
                   end) L PL)
    | one_r => one_case
    | @bot_r _ l pi => bot_case l pi (rec_call pi)
    | @tens_r _ A B l1 l2 pi1 pi2 => tens_case A B l1 l2 pi1 pi2 (rec_call pi1) (rec_call pi2)
    | @parr_r _ A B l pi => parr_case A B l pi (rec_call pi)
    | @top_r _ l => top_case l
    | @plus_r1 _ A B l pi => plus_case1 A B l pi (rec_call pi)
    | @plus_r2 _ A B l pi => plus_case2 A B l pi (rec_call pi)
    | @with_r _ A B l pi1 pi2 => with_case A B l pi1 pi2 (rec_call pi1) (rec_call pi2)
    | @oc_r _ A l pi => oc_case A l pi (rec_call pi)
    | @de_r _ A l pi => de_case A l pi (rec_call pi)
    | @wk_r _ A l pi => wk_case A l pi (rec_call pi)
    | @co_r _ A l pi => co_case A l pi (rec_call pi)
    | @cut_r _ A f l1 l2 pi1 pi2 => cut_case A f l1 l2 pi1 pi2 (rec_call pi1) (rec_call pi2)
    | @gax_r _ a => gax_case a
    end.

  Lemma ll_nested_ind' : forall (Pred : forall l, ll P l -> Type),
    (forall X, Pred (covar X :: var X :: nil) (ax_r X)) ->
    (forall l1 l2 pi p, Pred l1 pi -> Pred l2 (ex_r l1 l2 pi p)) ->
    (forall l1 lw lw' l2 pi p, Pred (l1 ++ map wn lw ++ l2) pi ->
       Pred (l1 ++ map wn lw' ++ l2) (ex_wn_r l1 lw lw' l2 pi p)) ->
    (forall L eqpmix, Forall_inf (fun x => Pred (projT1 x) (projT2 x)) L ->
       Pred _ (mix'_r L eqpmix)) ->
    Pred (one :: nil) one_r ->
    (forall l pi, Pred l pi -> Pred (bot :: l) (bot_r pi)) ->
    (forall A B l1 l2 pi1 pi2, Pred (A :: l1) pi1 -> Pred (B :: l2) pi2 ->
       Pred (tens A B :: l2 ++ l1) (tens_r pi1 pi2)) ->
    (forall A B l pi, Pred (A :: B :: l) pi -> Pred (parr A B :: l) (parr_r pi)) ->
    (forall l, Pred (top :: l) (top_r l)) ->
    (forall A B l pi, Pred (A :: l) pi -> Pred (aplus A B :: l) (plus_r1 B pi)) ->
    (forall A B l pi, Pred (A :: l) pi -> Pred (aplus B A :: l) (plus_r2 B pi)) ->
    (forall A B l pi1 pi2, Pred (A :: l) pi1 -> Pred (B :: l) pi2 ->
       Pred (awith A B :: l) (with_r pi1 pi2)) ->
    (forall A l pi, Pred (A :: map wn l) pi -> Pred (oc A :: map wn l) (oc_r pi)) ->
    (forall A l pi, Pred (A :: l) pi -> Pred (wn A :: l) (de_r pi)) ->
    (forall A l pi, Pred l pi -> Pred (wn A :: l) (wk_r A pi)) ->
    (forall A l pi, Pred (wn A :: wn A :: l) pi -> Pred (wn A :: l) (co_r pi)) ->
    (forall A f l1 l2 pi1 pi2, Pred (dual A :: l1) pi1 -> Pred (A :: l2) pi2 ->
       Pred (l2 ++ l1) (@cut_r P A f l1 l2 pi1 pi2)) ->
    (forall a, Pred (projT2 (pgax P) a) (gax_r a)) ->
    forall l (pi : ll P l), Pred l pi.
  Proof.
  intros.
  apply pre_ll_nested_ind; try assumption.
  intros L e f HP.
  assert (Pred (flat_map (projT1 (P:=ll P)) (Forall_to_list f))
               (rew <- [fun l => ll P l] flat_map_concat_map (projT1 (P:=ll P)) (Forall_to_list f) in
                  @mix_r _ (map (projT1 (P:=ll P)) (Forall_to_list f))
                           (eq_ind_r (fun n => pmix P n = true)
                           (eq_ind_r (fun n => pmix P n = true) e (Forall_to_list_length f))
                           (length_map (projT1 (P:=ll P)) (Forall_to_list f)))
                        (list_to_Forall (Forall_to_list f)))) as HL
    by (apply X2; clear e; induction HP; cbn; constructor; assumption).
  clear - HL.
  rewrite (flat_map_concat_map (@projT1 _ (ll P)) (Forall_to_list f)) in HL. unfold eq_rect_r in HL. cbn in HL.
  rewrite <- (Forall_to_list_to_Forall f).
  replace e with
      (rew [fun n : nat => pmix P n = true] f_equal (length (A:=list formula))
                                                    (Forall_to_list_support f) in
          eq_ind_r (fun n => pmix P n = true)
                   (eq_ind_r (fun n => pmix P n = true) e (Forall_to_list_length f))
                   (length_map (projT1 (P:=ll P)) (Forall_to_list f)))
    by apply (Eqdep_dec.UIP_dec Bool.bool_dec).
  rewrite <- (Forall_to_list_support f). assumption.
  Defined.

End ll_ind.

Definition ll_nested_ind P := fun Pred ax_case ex_case ex_wn_case mix_case one_case bot_case tens_case parr_case
               top_case plus_case1 plus_case2 with_case oc_case de_case wk_case co_case cut_case gax_case l pi =>
 @pre_ll_nested_ind P l pi Pred ax_case ex_case ex_wn_case mix_case one_case bot_case tens_case parr_case
               top_case plus_case1 plus_case2 with_case oc_case de_case wk_case co_case cut_case gax_case.
#[global] Arguments ll_nested_ind [P] Pred.
#[global] Arguments ll_nested_ind' [P] Pred.

#[export] Instance ll_perm P : Proper ((@PCPermutation_Type _ (pperm P)) ==> arrow) (ll P) | 100.
Proof. intros l1 l2 HP pi. exact (ex_r _ _ pi HP). Qed.

(* Unused
Lemma same_pfrag P Q : eq_pfrag P Q -> forall l, ll P l -> ll Q l.
Proof.
intros Heq l pi.
induction pi using ll_nested_ind'; try now constructor.
- apply (ex_r l1 _ IHpi).
  destruct Heq as (_ & _ & _  & Hp).
  unfold PCPermutation_Type in *.
  destruct (pperm P), (pperm Q); cbn in Hp; try inversion Hp; try assumption.
- apply (ex_wn_r l1 lw); assumption.
- assert ({L' & (map (@projT1 _ (ll Q)) L') = (map (@projT1 _ (ll P)) L)}) as [L' eqL'].
  { destruct eqpmix.
    induction L.
    - split with nil; reflexivity.
    - inversion X; subst.
      destruct (IHL X1) as [L' eq].
      split with (existT (ll Q) (projT1 a) X0 :: L').
      cbn; rewrite eq; reflexivity. }
  rewrite flat_map_concat_map, <- eqL', <- flat_map_concat_map.
  apply mix'_r.
  destruct Heq as (_ & _ & Hpmix & _).
  specialize Hpmix with (length L).
  rewrite <- length_map with _ _ (@projT1 _ (ll Q)) L', eqL', length_map.
  case_eq (pmix Q (length L)); intros eq; [ reflexivity | exfalso ].
  rewrite eq, eqpmix in Hpmix.
  inversion Hpmix.
- destruct Heq as [Hcut _].
  rewrite f in Hcut; symmetry in Hcut.
  apply (@cut_r _ Hcut A); assumption.
- destruct Heq as (_ & Hgax & _).
  destruct (fst Hgax a) as [b ->].
  apply gax_r.
Qed.
*)

Lemma stronger_pfrag P Q (Hle : le_pfrag P Q) l : ll P l -> ll Q l.
Proof.
intro pi. induction pi using ll_nested_ind; try (constructor; assumption).
- refine (ex_r _ _ IHpi _).
  apply (PCPermutation_Type_monot (pperm P)), p.
  apply Hle.
- exact (ex_wn_r _ _ _ _ IHpi p).
- apply mix_r.
  + destruct Hle as (_ & _ & Hmix & _).
    eapply implb_true_iff, eqpmix. apply le_implb, (Hmix (length L)).
  + clear eqpmix. induction L as [|l L IHL]; constructor; inversion X; subst.
    * apply X0.
    * eapply IHL, X1.
- refine (cut_r _ _ IHpi1 IHpi2).
  destruct Hle as (Hcut & _ & _ & _).
  eapply implb_true_iff, f. apply le_implb, Hcut.
- destruct Hle as (_ & Hgax & _ & _), (Hgax a) as [b ->]. apply gax_r.
Defined.
#[global] Arguments stronger_pfrag : clear implicits.


(** Proofs with sequent satisfying a given predicate *)

Fixpoint Forall_sequent P PS l (pi : ll P l) : Type :=
match pi with
| ax_r _ | gax_r _ => PS l
| ex_r _ _ pi1 _ | ex_wn_r _ _ _ _ pi1 _ => Forall_sequent PS pi1 * PS l
| mix_r _ PL => ((fix Forall_sequent_Forall P L (PL : Forall_inf (ll P) L) {struct PL} : Type :=
       match PL with
       | Forall_inf_nil _ => unit
       | Forall_inf_cons _ Pl PL => (Forall_sequent PS Pl * Forall_sequent_Forall _ _ PL)%type
       end) _ _ PL) * PS l
| one_r | top_r _ => PS l
| bot_r pi1 | parr_r pi1 => Forall_sequent PS pi1 * PS l
| tens_r pi1 pi2 | cut_r _ _ pi1 pi2 => Forall_sequent PS pi1 * Forall_sequent PS pi2 * PS l
| plus_r1 _ pi1 | plus_r2 _ pi1 => Forall_sequent PS pi1 * PS l
| with_r pi1 pi2 => Forall_sequent PS pi1 * Forall_sequent PS pi2 * PS l
| oc_r pi1 | de_r pi1 | wk_r _ pi1 | co_r pi1 => Forall_sequent PS pi1 * PS l
end.

Definition Forall_formula P FS := @Forall_sequent P (Forall_inf FS).

Lemma Forall_sequent_is P PS l (pi : ll P l) : Forall_sequent PS pi -> PS l.
Proof. destruct pi; cbn; tauto. Qed.

Lemma Forall_sequent_impl P PS QS (HPQ : forall x, PS x -> QS x) l (pi : ll P l) :
  Forall_sequent PS pi -> Forall_sequent QS pi.
Proof.
induction pi using ll_nested_ind;
  try (apply HPQ; assumption);
  try (intros [IH H]; split; auto; fail);
  try (intros [[IH1 IH2] H]; split; auto; fail).
cbn. clear eqpmix. intros [HFS HPS].
split; [ clear HPS | exact (HPQ _ HPS) ].
induction PL; [ constructor | ].
unfold Forall_Proofs in X. Dependent_Forall_inversion_formula X. tauto.
Qed.

Lemma Forall_sequent_stronger_pfrag P Q (Hfrag : le_pfrag P Q) PS l (pi : ll P l) :
  Forall_sequent PS pi -> Forall_sequent PS (stronger_pfrag _ _ Hfrag _ pi).
Proof.
induction pi using ll_nested_ind; intros HFS; try (cbn in HFS; cbn; tauto).
- cbn in HFS. cbn. clear eqpmix. destruct HFS as [HFS HPS].
  split; [ clear HPS | exact HPS ].
  induction PL in X, HFS |- *.
  + exact HFS.
  + unfold Forall_Proofs in X. Dependent_Forall_inversion_formula X.
    destruct HFS as [Hp HFS]. split.
    * exact (X1 Hp).
    * exact (IHPL X2 HFS).
- cbn. cbn in HFS. destruct Hfrag as (_ & ? & _ & _), (s a) as [b H].
  rewrite ? H in *. assumption.
Qed.


(** Size of proofs *)

Fixpoint psize P l (pi : ll P l) :=
match pi with
| ax_r _ | gax_r _ => 1
| ex_r _ _ pi0 _ | ex_wn_r _ _ _ _ pi0 _ => S (psize pi0)
| mix_r _ PL => S ((fix psize_Forall P L (PL : Forall_inf (ll P) L) {struct PL} :=
       match PL with
       | Forall_inf_nil _ => 0
       | Forall_inf_cons _ Pl PL => (psize Pl) + (psize_Forall _ _ PL)
       end) _ _ PL)
| one_r | top_r _ => 1
| bot_r pi0 | parr_r pi0 | plus_r1 _ pi0 | plus_r2 _ pi0 => S (psize pi0)
| tens_r pi1 pi2 | cut_r _ _ pi1 pi2 => S (psize pi1 + psize pi2)
| with_r pi1 pi2 => S (max (psize pi1) (psize pi2))
| oc_r pi0 | de_r pi0 | wk_r _ pi0 | co_r pi0 => S (psize pi0)
end.

Lemma psize_pos P l (pi : @ll P l) : 0 < psize pi.
Proof. destruct pi; cbn; lia. Qed.

Lemma psize_mix P L eq (FL : Forall_inf (ll P) L) :
  psize (mix_r eq FL) = S (Forall_inf_sum (fun _ pi => psize pi) FL).
Proof. cbn. clear eq. induction FL; [ | cbn; rewrite <- 2 Nat.add_succ_r, IHFL ]; reflexivity. Qed.

Lemma psize_inf_mix P L eq (FL : Forall_inf (ll P) L) l (pi : ll P l) :
  In_Forall_inf _ pi FL -> psize pi < psize (mix_r eq FL).
Proof.
intros Hin. cbn. clear eq. induction FL; inversion Hin.
- injection H as [= -> H'].
  apply inj_pair2_eq_dec in H' as ->; [ lia | apply (list_eq_dec (@eqb formulas_dectype)); apply eqb_eq ].
- specialize (IHFL X). lia.
Qed.


(** *** Variants of rules *)

(** Weakening on a list of formulas *)
Lemma wk_list_r P l l' : ll P l' -> ll P (map wn l ++ l').
Proof. induction l as [|a l IHl] in l' |- *; intros pi; [ | apply wk_r, IHl ]; assumption. Qed.

(** Contraction on a list of formulas *)
Lemma co_list_r P l l' : ll P (map wn l ++ map wn l ++ l') -> ll P (map wn l ++ l').
Proof.
induction l in l' |- *; intros pi; [ assumption | ].
rewrite <- app_nil_l.
apply (ex_wn_r _ (l ++ a :: nil)); [ | symmetry; apply Permutation_Type_cons_append ].
list_simpl. apply IHl.
replace (map wn l ++ map wn l ++ wn a :: l')
  with (nil ++ map wn (l ++ l ++ a :: nil) ++ l')
  by (list_simpl; reflexivity).
apply (ex_wn_r _ (a :: l ++ l)); [ | rewrite app_assoc; apply Permutation_Type_cons_append ].
list_simpl. apply co_r.
replace (wn a :: wn a :: map wn l ++ map wn l ++ l')
   with (nil ++ map wn (a :: a :: l ++ l) ++ l')
  by (list_simpl; reflexivity).
apply ex_wn_r with ((a :: l) ++ a :: l); [ list_simpl; list_simpl in pi; assumption | ].
rewrite (app_comm_cons _ l). symmetry. apply Permutation_Type_middle.
Qed.

Lemma co_const_list_r P n A l : ll P (repeat (wn A) n ++ l) -> ll P ((wn A) :: l).
Proof.
induction n as [|n IHn] in l |- *; intros pi.
- apply wk_r. assumption.
- apply co_r, IHn.
  change (repeat (wn A) (S n) ++ l) with ((wn A :: repeat (wn A) n) ++ l) in pi.
  rewrite repeat_cons, <- app_assoc in pi. assumption.
Qed.

(** Special rules regarding the concat operator *)
Lemma co_list_gen_perm_r P (P_perm : pperm P = true) L l0 l :
  ll P (l ++ flat_map (app (map wn l0)) L) -> ll P (l ++ (map wn l0) ++ concat L).
Proof.
induction L in l0, l |- *; intros pi.
- apply ex_r with (map wn l0 ++ l ++ concat nil).
  + apply wk_list_r. assumption.
  + rewrite P_perm. cbn. rewrite 2 app_nil_r. apply Permutation_Type_app_swap.
- apply ex_r with (map wn l0 ++ l ++ concat (a :: L));
    [ | rewrite P_perm; cbn; rewrite 2 (app_assoc _ _ (a ++ _));
        apply Permutation_Type_app_tail, Permutation_Type_app_swap ].
  apply co_list_r.
  apply ex_r with ((l ++ (map wn l0 ++ a)) ++ map wn l0 ++ concat L).
  + apply IHL.
    rewrite <- app_assoc. assumption.
  + rewrite P_perm. cbn. rewrite ? app_assoc. apply Permutation_Type_app_tail.
    etransitivity; [ apply Permutation_Type_app_comm | ].
    rewrite <- ? app_assoc. apply Permutation_Type_app_head.
    rewrite ? app_assoc. apply Permutation_Type_app_tail, Permutation_Type_app_comm.
Qed.

Lemma ex_concat_r P (P_perm : pperm P = true) l A L :
  ll P (l ++ flat_map (cons A) L) -> ll P (l ++ repeat A (length L) ++ concat L).
Proof.
induction L in l |- *; intros pi; [ assumption | ].
apply ex_r with ((A :: l ++ a) ++ repeat A (length L) ++ concat L).
- apply IHL.
  now apply ex_r with (l ++ (A :: a) ++ flat_map (cons A) L);
    [ | rewrite P_perm; cbn; symmetry; apply Permutation_Type_cons_app; rewrite app_assoc ].
- rewrite P_perm. cbn. cons2app. rewrite ? app_assoc. apply Permutation_Type_app_tail.
  list_simpl. etransitivity; [ apply Permutation_Type_middle | ].
  apply Permutation_Type_app_head, Permutation_Type_cons, Permutation_Type_app_comm. reflexivity.
Qed.


(** n-ary versions of tens and parr rules *)
Lemma tens_n_r P L A : Forall_inf (ll P) (map (cons A) L) -> ll P (tens_n (length L) A :: concat L).
Proof.
induction L as [|l L IHL]; intros FL.
- apply one_r.
- destruct L; list_simpl; inversion FL; [ assumption | subst ].
  apply tens_r; [ apply IHL | ]; assumption.
Qed.

Lemma parr_n_r P l n A : ll P (repeat A n ++ l) -> ll P (parr_n n A :: l).
Proof.
induction n in l |- *; intros pi.
- apply bot_r. assumption.
- destruct n; [ assumption | ].
  apply parr_r.
  apply ex_r with (parr_n (S n) A :: (l ++ (A :: nil)));
     [ | symmetry; rewrite PCPermutation_Type_cons_append; reflexivity ].
  apply IHn, (ex_r _ _ pi).
  rewrite app_assoc. apply PCPermutation_Type_cons_append.
Qed.

(** Permutation on mix *)
Lemma ex_mix_r P L L' (eq : is_true (pmix P (length L))) (p : Permutation_Type L L') :
  Forall_inf (ll P) L -> ll P (concat L').
Proof.
intros FL.
apply mix_r.
- replace (length L') with (length L); [ assumption | ].
  apply Permutation_Type_length. assumption.
- apply forall_Forall_inf. intros l Hin.
  apply (@Forall_inf_forall (list formula) (ll P) L); [ assumption | ].
  apply Permutation_Type_in_inf with L'; [ | assumption ].
  symmetry. assumption.
Qed.

(** *** Some tactics for manipulating rules *)
Ltac ll_swap :=
  match goal with
  | |- ll ?P (?a1 :: ?a2 :: nil) => eapply ex_r; [ | apply PCPermutation_Type_swap ]
  end.
Ltac ll_swap_hyp H :=
  match goal with
  | H : ll ?P (?a1 :: ?a2 :: nil) |- _ =>
        eapply ex_r in H; [ | apply PCPermutation_Type_swap ]
  end.
Tactic Notation "ll_swap" "in" hyp(H) := ll_swap_hyp H.


(** ** Reversibility statements *)

Lemma bot_rev P (Hgax : gax_excludes P bot) l1 l2 : ll P (l1 ++ bot :: l2) -> ll P (l1 ++ l2).
Proof.
intro pi. remember (l1 ++ bot :: l2) as l eqn:Heql.
induction pi using ll_nested_ind in l1, l2, Heql |- *;
  try (destruct l1; destr_eq Heql; subst; (try assumption);
       list_simpl; constructor; rewrite ? app_comm_cons;
       (apply IHpi + apply IHpi1 + apply IHpi2); reflexivity);
  (try now do 3 (destruct l1 as [|? l1]; inversion Heql));
  subst.
- apply PCPermutation_Type_vs_elt_subst in p as [(l3, l4) HP' ->].
  specialize (HP' nil). symmetry in HP'.
  refine (ex_r _ _ _ HP').
  apply IHpi. reflexivity.
- dichot_elt_app_inf_exec Heql; subst.
  + rewrite app_assoc. apply (ex_wn_r _ lw); [ | assumption ].
    list_simpl. apply IHpi. list_simpl. reflexivity.
  + dichot_elt_app_inf_exec Heql1; subst.
    * exfalso. decomp_map Heql0 eqn:Hwb. discriminate Hwb.
    * list_simpl. apply (ex_wn_r _ lw); [ | assumption ].
      rewrite 2 app_assoc. apply IHpi. list_simpl. reflexivity.
- apply concat_vs_elt in Heql as ([[[L1 L2] l1'] l2'] & -> & -> & ->).
  apply Dependent_Forall_inf_app_inv in X as ((l1'' & Fl1) & (l2'' & Fl2)).
  inversion_clear Fl2.
  replace ((concat L1 ++ l1') ++ l2' ++ concat L2) with (concat (L1 ++ (l1' ++ l2') :: L2));
    [ | rewrite concat_app; cbn; rewrite 3 app_assoc; reflexivity].
  apply mix_r.
  + rewrite length_app. rewrite length_app in eqpmix. assumption.
  + apply Forall_inf_app; [ assumption | ].
    apply Forall_inf_cons; [ | assumption ].
    apply (X _ _ eq_refl).
- rewrite app_comm_cons in Heql. dichot_elt_app_inf_exec Heql; subst.
  + destruct l1; destr_eq Heql0. subst.
    rewrite app_assoc. apply tens_r; [ assumption | ].
    rewrite app_comm_cons. apply IHpi2. reflexivity.
  + list_simpl. apply tens_r; [ | assumption ].
    rewrite app_comm_cons. apply IHpi1. reflexivity.
- exfalso.
  destruct l1; injection Heql as [= [=] Heq]. decomp_map Heq. discriminate.
- dichot_elt_app_inf_exec Heql; subst.
  + rewrite app_assoc. apply (@cut_r _ A f); [ assumption | ].
    rewrite app_comm_cons. apply IHpi2. reflexivity.
  + rewrite <- app_assoc. apply (@cut_r _ A f); [ | assumption ].
    rewrite app_comm_cons. apply IHpi1. reflexivity.
- contradiction (Hgax a). rewrite Heql. apply in_inf_elt.
Qed.

Lemma parr_rev P A B (Hgax : gax_excludes P (parr A B)) l1 l2 :
  ll P (l1 ++ parr A B :: l2) -> ll P (l1 ++ A :: B :: l2).
Proof.
intro pi. remember (l1 ++ parr A B :: l2) as l eqn:Heql.
induction pi using ll_nested_ind in l1, l2, Heql |- *;
  try (destruct l1; destr_eq Heql; subst; (try assumption);
       list_simpl; constructor; rewrite ? app_comm_cons;
       (apply IHpi + apply IHpi1 + apply IHpi2); reflexivity);
  (try now do 3 (destruct l1 as [|? l1]; inversion Heql));
  subst.
- apply PCPermutation_Type_vs_elt_subst in p as [(l3, l4) HP' ->].
  specialize (HP' (A :: B :: nil)). symmetry in HP'.
  refine (ex_r _ _ _ HP').
  apply IHpi. reflexivity.
- dichot_elt_app_inf_exec Heql; subst.
  + rewrite 2 app_comm_cons, app_assoc.
    apply (ex_wn_r _ lw); [ | assumption ].
    list_simpl. apply IHpi. list_simpl. reflexivity.
  + dichot_elt_app_inf_exec Heql1; subst.
    * exfalso. decomp_map Heql0 eqn:Hwp. discriminate Hwp.
    * list_simpl. apply (ex_wn_r _ lw); [ | assumption ].
      rewrite 2 app_assoc. apply IHpi. list_simpl. reflexivity.
- apply concat_vs_elt in Heql as ([[[L1 L2] l1'] l2'] & -> & -> & ->).
  apply Dependent_Forall_inf_app_inv in X as ((l1'' & Fl1) & (l2'' & Fl2)).
  inversion_clear Fl2.
  replace ((concat L1 ++ l1') ++ A :: B :: l2' ++ concat L2) with (concat (L1 ++ (l1' ++ A :: B :: l2') :: L2));
    [ |rewrite concat_app; cbn; rewrite ? app_comm_cons, ? app_assoc; reflexivity].
  apply mix_r.
  + rewrite length_app. rewrite length_app in eqpmix. assumption.
  + apply Forall_inf_app; [ assumption | ].
    apply Forall_inf_cons; [ | assumption ].
    apply (X _ _ eq_refl).
- rewrite app_comm_cons in Heql. dichot_elt_app_inf_exec Heql; subst.
  + destruct l1; destr_eq Heql0. subst.
    rewrite 2 app_comm_cons, app_assoc. apply tens_r; [ assumption | ].
    rewrite app_comm_cons. apply IHpi2. reflexivity.
  + list_simpl. apply tens_r; [ | assumption ].
    rewrite app_comm_cons. apply IHpi1. reflexivity.
- exfalso.
  destruct l1; injection Heql as [= [=] Heq]. decomp_map Heq. discriminate.
- dichot_elt_app_inf_exec Heql; subst.
  + rewrite 2 app_comm_cons, app_assoc. apply (cut_r A0 f); [ assumption | ].
    rewrite app_comm_cons. apply IHpi2. reflexivity.
  + rewrite <- app_assoc. apply (cut_r A0 f); [ | assumption ].
    rewrite app_comm_cons. apply IHpi1. reflexivity.
- contradiction (Hgax a). rewrite Heql. apply in_inf_elt.
Qed.

Lemma with_rev1 P A B (Hgax : gax_excludes P (awith A B)) l1 l2 :
  ll P (l1 ++ awith A B :: l2) -> ll P (l1 ++ A :: l2).
Proof.
intro pi. remember (l1 ++ awith A B :: l2) as l eqn:Heql.
induction pi using ll_nested_ind in l1, l2, Heql |- *;
  try (destruct l1; destr_eq Heql; subst; (try assumption);
       list_simpl; constructor; rewrite ? app_comm_cons;
       (apply IHpi + apply IHpi1 + apply IHpi2); reflexivity);
  (try now do 3 (destruct l1 as [|? l1]; inversion Heql));
  subst.
- apply PCPermutation_Type_vs_elt_subst in p as [(l3, l4) HP' ->].
  specialize (HP' (A :: nil)). symmetry in HP'. refine (ex_r _ _ _ HP').
  apply IHpi. reflexivity.
- dichot_elt_app_inf_exec Heql; subst.
  + rewrite app_comm_cons, app_assoc.
    apply (ex_wn_r _ lw); [ | assumption ].
    list_simpl. apply IHpi. list_simpl. reflexivity.
  + dichot_elt_app_inf_exec Heql1; subst.
    * exfalso. decomp_map Heql0 eqn:Hww. discriminate Hww.
    * list_simpl. apply (ex_wn_r _ lw); [ | assumption ].
      rewrite 2 app_assoc. apply IHpi. list_simpl. reflexivity.
- apply concat_vs_elt in Heql as ([[[L1 L2] l1'] l2'] & -> & -> & ->).
  apply Dependent_Forall_inf_app_inv in X as ((l1'' & Fl1) & (l2'' & Fl2)).
  inversion_clear Fl2.
  replace ((concat L1 ++ l1') ++ A :: l2' ++ concat L2) with (concat (L1 ++ (l1' ++ A :: l2') :: L2));
    [ |rewrite concat_app; cbn; rewrite ? app_comm_cons, ? app_assoc; reflexivity].
  apply mix_r.
  + rewrite length_app. rewrite length_app in eqpmix. assumption.
  + apply Forall_inf_app; [ assumption | ].
    apply Forall_inf_cons; [ | assumption ].
    apply (X _ _ eq_refl).
- rewrite app_comm_cons in Heql. dichot_elt_app_inf_exec Heql; subst.
  + destruct l1; destr_eq Heql0. subst.
    rewrite app_comm_cons, app_assoc. apply tens_r; [ assumption | ].
    rewrite app_comm_cons. apply IHpi2. reflexivity.
  + list_simpl. apply tens_r; [ | assumption ].
    rewrite app_comm_cons. apply IHpi1. reflexivity.
- exfalso.
  destruct l1; injection Heql as [= [=] Heq]. decomp_map Heq. discriminate.
- dichot_elt_app_inf_exec Heql; subst.
  + rewrite app_comm_cons, app_assoc. apply (cut_r A0 f); [ assumption | ].
    rewrite app_comm_cons. apply IHpi2. reflexivity.
  + rewrite <- app_assoc. apply (cut_r A0 f); [ | assumption ].
    rewrite app_comm_cons. apply IHpi1. reflexivity.
- contradiction (Hgax a). rewrite Heql. apply in_inf_elt.
Qed.

Lemma with_rev2 P A B (Hgax : gax_excludes P (awith B A)) l1 l2 :
  ll P (l1 ++ awith B A :: l2) -> ll P (l1 ++ A :: l2).
Proof.
intro pi. remember (l1 ++ awith B A :: l2) as l eqn:Heql.
induction pi using ll_nested_ind in l1, l2, Heql |- *;
  try (destruct l1; destr_eq Heql; subst; (try assumption);
       list_simpl; constructor; rewrite ? app_comm_cons;
       (apply IHpi + apply IHpi1 + apply IHpi2); reflexivity);
  (try now do 3 (destruct l1 as [|? l1]; inversion Heql));
  subst.
- apply PCPermutation_Type_vs_elt_subst in p as [(l3, l4) HP' ->].
  specialize (HP' (A :: nil)). symmetry in HP'. refine (ex_r _ _ _ HP').
  apply IHpi. reflexivity.
- dichot_elt_app_inf_exec Heql; subst.
  + rewrite app_comm_cons, app_assoc.
    apply (ex_wn_r _ lw); [ | assumption ].
    list_simpl. apply IHpi. list_simpl. reflexivity.
  + dichot_elt_app_inf_exec Heql1; subst.
    * exfalso. decomp_map Heql0 eqn:Hww. discriminate Hww.
    * list_simpl. apply (ex_wn_r _ lw); [ | assumption ].
      rewrite 2 app_assoc. apply IHpi. list_simpl. reflexivity.
- apply concat_vs_elt in Heql as ([[[L1 L2] l1'] l2'] & -> & -> & ->).
  apply Dependent_Forall_inf_app_inv in X as ((l1'' & Fl1) & (l2'' & Fl2)).
  inversion_clear Fl2.
  replace ((concat L1 ++ l1') ++ A :: l2' ++ concat L2) with (concat (L1 ++ (l1' ++ A :: l2') :: L2));
    [ |rewrite concat_app; cbn; rewrite ? app_comm_cons, ? app_assoc; reflexivity].
  apply mix_r.
  + rewrite length_app. rewrite length_app in eqpmix. assumption.
  + apply Forall_inf_app; [ assumption | ].
    apply Forall_inf_cons; [ | assumption ].
    apply (X _ _ eq_refl).
- rewrite app_comm_cons in Heql. dichot_elt_app_inf_exec Heql; subst.
  + destruct l1; destr_eq Heql0. subst.
    rewrite app_comm_cons, app_assoc. apply tens_r; [ assumption | ].
    rewrite app_comm_cons. apply IHpi2. reflexivity.
  + list_simpl. apply tens_r; [ | assumption ].
    rewrite app_comm_cons. apply IHpi1. reflexivity.
- exfalso.
  destruct l1; injection Heql as [= [=] Heq]. decomp_map Heq. discriminate.
- dichot_elt_app_inf_exec Heql; subst.
  + rewrite app_comm_cons, app_assoc. apply (cut_r A0 f); [ assumption | ].
    rewrite app_comm_cons. apply IHpi2. reflexivity.
  + rewrite <- app_assoc. apply (cut_r A0 f); [ | assumption ].
    rewrite app_comm_cons. apply IHpi1. reflexivity.
- contradiction (Hgax a). rewrite Heql. apply in_inf_elt.
Qed.

Lemma oc_rev P A (Hgax : gax_excludes P (oc A)) l1 l2 : ll P (l1 ++ oc A :: l2) -> ll P (l1 ++ A :: l2).
Proof.
intro pi. remember (l1 ++ oc A :: l2) as l eqn:Heql.
induction pi using ll_nested_ind in l1, l2, Heql |- *;
  try (destruct l1; destr_eq Heql; subst; (try assumption);
       list_simpl; constructor; rewrite ? app_comm_cons;
       (apply IHpi + apply IHpi1 + apply IHpi2); reflexivity);
  (try now do 3 (destruct l1 as [|? l1]; inversion Heql));
  subst.
- apply PCPermutation_Type_vs_elt_subst in p as [(l3, l4) HP' ->].
  specialize (HP' (A :: nil)). symmetry in HP'. refine (ex_r _ _ _ HP').
  apply IHpi. reflexivity.
- dichot_elt_app_inf_exec Heql; subst.
  + rewrite app_comm_cons, app_assoc.
    apply (ex_wn_r _ lw); [ | assumption ].
    list_simpl. apply IHpi. list_simpl. reflexivity.
  + dichot_elt_app_inf_exec Heql1; subst.
    * exfalso. decomp_map Heql0 eqn:Hwo. discriminate Hwo.
    * list_simpl. apply (ex_wn_r _ lw); [ | assumption ].
      rewrite 2 app_assoc. apply IHpi. list_simpl. reflexivity.
- apply concat_vs_elt in Heql as ([[[L1 L2] l1'] l2'] & -> & -> & ->).
  apply Dependent_Forall_inf_app_inv in X as ((l1'' & Fl1) & (l2'' & Fl2)).
  inversion_clear Fl2.
  replace ((concat L1 ++ l1') ++ A :: l2' ++ concat L2) with (concat (L1 ++ (l1' ++ A :: l2') :: L2));
    [ |rewrite concat_app; cbn; rewrite ? app_comm_cons, ? app_assoc; reflexivity].
  apply mix_r.
  + rewrite length_app. rewrite length_app in eqpmix. assumption.
  + apply Forall_inf_app; [ assumption | ].
    apply Forall_inf_cons; [ | assumption ].
    apply (X _ _ eq_refl).
- rewrite app_comm_cons in Heql. dichot_elt_app_inf_exec Heql; subst.
  + destruct l1; destr_eq Heql0. subst.
    rewrite app_comm_cons, app_assoc. apply tens_r; [ assumption | ].
    rewrite app_comm_cons. apply IHpi2. reflexivity.
  + list_simpl. apply tens_r; [ | assumption ].
    rewrite app_comm_cons. apply IHpi1. reflexivity.
- destruct l1; injection Heql as [= [= <-] Heq].
  + rewrite <- Heq. exact pi.
  + exfalso. decomp_map Heq. discriminate.
- dichot_elt_app_inf_exec Heql; subst.
  + rewrite app_comm_cons, app_assoc. apply (cut_r A0 f); [ assumption | ].
    rewrite app_comm_cons. apply IHpi2. reflexivity.
  + rewrite <- app_assoc. apply (cut_r A0 f); [ | assumption ].
    rewrite app_comm_cons. apply IHpi1. reflexivity.
- contradiction (Hgax a). rewrite Heql. apply in_inf_elt.
Qed.

Lemma one_rev P (Hgax : gax_excludes P one) l1 l2 :
  ll P (l1 ++ one :: l2) -> forall l0, ll P l0 -> ll P (l1 ++ l0 ++ l2).
Proof.
intros pi l0 pi0. remember (l1 ++ one :: l2) as l eqn:Heql.
induction pi in l1, l2, Heql |- * using ll_nested_ind;
  try (destruct l1; destr_eq Heql; subst; (try assumption);
       list_simpl; constructor; rewrite ? app_comm_cons;
       (apply IHpi + apply IHpi1 + apply IHpi2); reflexivity);
  (try now do 3 (destruct l1 as [|? l1]; inversion Heql));
  subst.
- apply PCPermutation_Type_vs_elt_subst in p as [(l1', l2') HP' ->].
  specialize (HP' l0). symmetry in HP'. refine (ex_r _ _ _ HP').
  apply IHpi. reflexivity.
- dichot_elt_app_inf_exec Heql; subst.
  + rewrite 2 app_assoc. eapply ex_wn_r; [ | eassumption ]. list_simpl.
    apply IHpi. list_simpl. reflexivity.
  + dichot_elt_app_inf_exec Heql1; subst.
    * exfalso. decomp_map Heql0 eqn:Hwo. discriminate Hwo.
    * list_simpl. eapply ex_wn_r; [ | eassumption ].
      rewrite 2 app_assoc. apply IHpi. list_simpl. reflexivity.
- apply concat_vs_elt in Heql as ([[[L1 L2] l1'] l2'] & -> & -> & ->).
  replace ((concat L1 ++ l1') ++ l0 ++ l2' ++ concat L2) with (concat (L1 ++ (l1' ++ l0 ++ l2') :: L2))
    by (rewrite concat_app; cbn; rewrite ? app_comm_cons, ? app_assoc; reflexivity).
  apply mix_r.
  + rewrite length_app. rewrite length_app in eqpmix. assumption.
  + assert (Fl1 := Forall_inf_app_l _ _ PL).
    assert (Fl2 := Forall_inf_app_r _ _ PL).
    apply Forall_inf_app; [ assumption | ].
    inversion Fl2. subst.
    apply Forall_inf_cons; [ | assumption ].
    destruct (In_Forall_inf_elt _ _ _ PL).
    refine (Dependent_Forall_inf_forall_formula _ _ X i _ _ eq_refl).
- destruct l1; destr_eq Heql; subst.
  + list_simpl. assumption.
  + destruct l1; discriminate H.
- rewrite app_comm_cons in Heql. dichot_elt_app_inf_exec Heql; subst.
  + destruct l1; destr_eq Heql0; subst.
    rewrite <- app_comm_cons, 2 app_assoc. apply tens_r; [ assumption | ].
    list_simpl. rewrite app_comm_cons. apply IHpi2. reflexivity.
  + rewrite <- app_assoc. apply tens_r; [ | assumption ].
    rewrite app_comm_cons. apply IHpi1. reflexivity.
- exfalso. destruct l1; destr_eq Heql. decomp_map H eqn:Hwo. discriminate Hwo.
- dichot_elt_app_inf_exec Heql; subst.
  + rewrite 2 app_assoc. eapply cut_r; [ eassumption | assumption | ].
    list_simpl. rewrite app_comm_cons. apply IHpi2. reflexivity.
  + rewrite <- app_assoc. eapply cut_r; [ eassumption | | assumption ].
    rewrite app_comm_cons. apply IHpi1. reflexivity.
- contradiction (Hgax a). rewrite Heql. apply in_inf_elt.
Qed.

Lemma zero_rev P (Hgax : gax_excludes P zero) l1 l2 :
  ll P (l1 ++ zero :: l2) -> forall l0, ll P (l1 ++ l0 ++ l2).
Proof.
intro pi. remember (l1 ++ zero :: l2) as l eqn:Heql. intro l'.
induction pi in l1, l2, Heql |- * using ll_nested_ind;
  try (destruct l1; destr_eq Heql; subst; (try assumption);
       list_simpl; constructor; rewrite ? app_comm_cons;
       (apply IHpi + apply IHpi1 + apply IHpi2); reflexivity);
  (try now do 3 (destruct l1 as [|? l1]; inversion Heql));
  subst.
- apply PCPermutation_Type_vs_elt_subst in p as [(l1', l2') HP' ->].
  specialize (HP' l'). symmetry in HP'. refine (ex_r _ _ _ HP').
  apply IHpi. reflexivity.
- dichot_elt_app_inf_exec Heql; subst.
  + rewrite 2 app_assoc. eapply ex_wn_r; [ | eassumption ]. list_simpl.
    apply IHpi. list_simpl. reflexivity.
  + dichot_elt_app_inf_exec Heql1; subst.
    * exfalso. decomp_map Heql0 eqn:Hwz. discriminate Hwz.
    * list_simpl. eapply ex_wn_r; [ | eassumption ].
      rewrite 2 app_assoc. apply IHpi. list_simpl. reflexivity.
- apply concat_vs_elt in Heql as ([[[L1 L2] l1'] l2'] & -> & -> & ->).
  replace ((concat L1 ++ l1') ++ l' ++ l2' ++ concat L2) with (concat (L1 ++ (l1' ++ l' ++ l2') :: L2))
    by (rewrite concat_app; cbn; rewrite ? app_comm_cons, ? app_assoc; reflexivity).
  apply mix_r.
  + rewrite length_app. rewrite length_app in eqpmix. assumption.
  + assert (Fl1 := Forall_inf_app_l _ _ PL).
    assert (Fl2 := Forall_inf_app_r _ _ PL).
    apply Forall_inf_app; [ assumption | ].
    inversion Fl2. subst.
    apply Forall_inf_cons; [ | assumption ].
    destruct (In_Forall_inf_elt _ _ _ PL).
    refine (Dependent_Forall_inf_forall_formula _ _ X i _ _ eq_refl).
- rewrite app_comm_cons in Heql. dichot_elt_app_inf_exec Heql; subst.
  + destruct l1; destr_eq Heql0; subst.
    rewrite <- app_comm_cons, 2 app_assoc. apply tens_r; [ assumption | ].
    list_simpl. rewrite app_comm_cons. apply IHpi2. reflexivity.
  + rewrite <- app_assoc. apply tens_r; [ | assumption ].
    rewrite app_comm_cons. apply IHpi1. reflexivity.
- exfalso. destruct l1; destr_eq Heql. decomp_map H eqn:Hwz. discriminate Hwz.
- dichot_elt_app_inf_exec Heql; subst.
  + rewrite 2 app_assoc. eapply cut_r; [ eassumption | assumption | ].
    list_simpl. rewrite app_comm_cons. apply IHpi2. reflexivity.
  + rewrite <- app_assoc. eapply cut_r; [ eassumption | | assumption ].
    rewrite app_comm_cons. apply IHpi1. reflexivity.
- contradiction (Hgax a). rewrite Heql. apply in_inf_elt.
Qed.

Lemma tens_one_rev P A (Hgax1 : gax_excludes P one) (Hgax2 : gax_excludes P (tens one A)) l1 l2 :
  ll P (l1 ++ tens one A :: l2) -> ll P (l1 ++ A :: l2).
Proof.
intros pi. remember (l1 ++ tens one A :: l2) as l eqn:Heql.
induction pi in l1, l2, Heql |- * using ll_nested_ind;
  try (destruct l1; destr_eq Heql; subst; (try assumption);
       list_simpl; constructor; rewrite ? app_comm_cons;
       (apply IHpi + apply IHpi1 + apply IHpi2); reflexivity);
  (try now do 3 (destruct l1 as [|? l1]; inversion Heql));
  subst.
- apply PCPermutation_Type_vs_elt_subst in p as [(l1', l2') HP' ->].
  specialize (HP' (A :: nil)). symmetry in HP'. refine (ex_r _ _ _ HP').
  apply IHpi. reflexivity.
- dichot_elt_app_inf_exec Heql; subst.
  + rewrite app_comm_cons, app_assoc. eapply ex_wn_r; [ | eassumption ]. list_simpl.
    apply IHpi. list_simpl. reflexivity.
  + dichot_elt_app_inf_exec Heql1; subst.
    * exfalso. decomp_map Heql0 eqn:Hwt. discriminate Hwt.
    * list_simpl. eapply ex_wn_r; [ | eassumption ].
      rewrite 2 app_assoc. apply IHpi. list_simpl. reflexivity.
- apply concat_vs_elt in Heql as ([[[L1 L2] l1'] l2'] & -> & -> & ->).
  replace ((concat L1 ++ l1') ++ A :: l2' ++ concat L2) with (concat (L1 ++ (l1' ++ A :: l2') :: L2))
    by (rewrite concat_app; cbn; rewrite ? app_comm_cons, ? app_assoc; reflexivity).
  apply mix_r.
  + rewrite length_app. rewrite length_app in eqpmix. assumption.
  + assert (Fl1 := Forall_inf_app_l _ _ PL).
    assert (Fl2 := Forall_inf_app_r _ _ PL).
    apply Forall_inf_app; [ assumption | ].
    inversion Fl2. subst.
    apply Forall_inf_cons; [ | assumption ].
    destruct (In_Forall_inf_elt _ _ _ PL).
    refine (Dependent_Forall_inf_forall_formula _ _ X i _ _ eq_refl).
- rewrite app_comm_cons in Heql. dichot_elt_app_inf_exec Heql; subst.
  + destruct l1; destr_eq Heql0; subst.
    * rewrite <- (app_nil_l _) in pi1. apply (one_rev Hgax1 _ _ pi1 pi2).
    * rewrite <- app_comm_cons, (app_comm_cons l), app_assoc. apply tens_r; [ assumption | ].
      rewrite app_comm_cons. apply IHpi2. reflexivity.
  + rewrite <- app_assoc. apply tens_r; [ | assumption ].
    rewrite app_comm_cons. apply IHpi1. reflexivity.
- exfalso. destruct l1; destr_eq Heql. decomp_map H eqn:Hwt. discriminate Hwt.
- dichot_elt_app_inf_exec Heql; subst.
  + rewrite app_comm_cons, app_assoc. apply cut_r with A0; [ assumption | assumption | ].
    list_simpl. rewrite app_comm_cons. apply IHpi2. reflexivity.
  + rewrite <- app_assoc. apply cut_r with A0; [ assumption | | assumption ].
    rewrite app_comm_cons. apply IHpi1. reflexivity.
- contradiction (Hgax2 a). rewrite Heql. apply in_inf_elt.
Qed.

Lemma tens_rev P A B (Hgax : forall a, notT (projT2 (pgax P) a = tens A B :: nil)) (Hcut : no_cut P) :
  ll P (tens A B :: nil) -> (ll P (A :: nil)) * (ll P (B :: nil)).
Proof.
intros pi. remember (tens A B :: nil) as l eqn:Heq. rewrite Heq in Hgax.
induction pi in Heq |- * using ll_nested_ind; subst; try (now inversion Heq).
- symmetry in p. apply PCPermutation_Type_length_1_inv in p as ->.
  apply IHpi. reflexivity.
- destruct l1; inversion Heq; subst.
  + destruct lw'; destr_eq H0. list_simpl in H0.
    symmetry in p. apply Permutation_Type_nil in p as ->.
    apply IHpi. assumption.
  + apply app_eq_nil in H1 as [-> [->%map_eq_nil ->]%app_eq_nil].
    symmetry in p. apply Permutation_Type_nil in p as ->.
    apply IHpi. list_simpl. reflexivity.
- change (tens A B :: nil) with (nil ++ tens A B :: nil) in Heq.
  apply concat_vs_elt in Heq as ([[[L1 L2] l1'] l2'] & eqb & eqt & ->).
  destruct l1'.
  + destruct l2'; [ | discriminate eqt ].
    destruct (Dependent_Forall_inf_app_inv _ _ X) as ((FL1 & PL1) & (FL2 & PL2)).
    inversion_clear PL2. exact (X0 eq_refl).
  + exfalso. exact (app_cons_not_nil (concat L1) l1' f eqb).
- injection Heq as [= -> -> [-> ->]%app_eq_nil].
  split; assumption.
- rewrite Hcut in f. discriminate f.
- contradiction (Hgax a Heq).
Qed.

Lemma plus_rev P A B (Hgax : forall a, notT (projT2 (pgax P) a = aplus A B :: nil)) (Hcut : no_cut P) :
  ll P (aplus A B :: nil) -> (ll P (A :: nil)) + (ll P (B :: nil)).
Proof.
intro pi. remember (aplus A B :: nil) as l eqn:Heq. rewrite Heq in Hgax.
induction pi in Heq |- * using ll_nested_ind; subst; try (now inversion Heq).
- symmetry in p. apply PCPermutation_Type_length_1_inv in p as ->.
  apply IHpi. reflexivity.
- destruct l1; inversion Heq; subst.
  + destruct lw'; destr_eq H0. list_simpl in H0.
    symmetry in p. apply Permutation_Type_nil in p as ->.
    apply IHpi. assumption.
  + apply app_eq_nil in H1 as [-> [->%map_eq_nil ->]%app_eq_nil].
    symmetry in p. apply Permutation_Type_nil in p as ->.
    apply IHpi. list_simpl. reflexivity.
- change (aplus A B :: nil) with (nil ++ aplus A B :: nil) in Heq.
  apply concat_vs_elt in Heq as ([[[L1 L2] l1'] l2'] & eqb & eqt & ->).
  destruct l1'.
  + destruct l2'; [ | discriminate eqt ].
    destruct (Dependent_Forall_inf_app_inv _ _ X) as ((FL1 & PL1) & (FL2 & PL2)).
    inversion_clear PL2. exact (X0 eq_refl).
  + exfalso. exact (app_cons_not_nil (concat L1) l1' f eqb).
- injection Heq as [= -> -> ->]. left. assumption.
- injection Heq as [= -> -> ->]. right. assumption.
- rewrite Hcut in f. discriminate f.
- contradiction (Hgax a Heq).
Qed.

Lemma wn_n_rev P A n (Hgax : forall a k, notT (projT2 (pgax P) a = repeat (wn A) k)) (Hcut : no_cut P) :
  ll P (repeat (wn A) n) -> (ll P (A :: wn A :: nil)) + (pmix P 0 = true).
Proof.
intro pi. remember (repeat (wn A) n) as l eqn:Heql.
induction pi in n, Heql |- * using ll_nested_ind; (try now destruct n; destr_eq Heql); subst.
- assert (l1 = (repeat (wn A) n)) as ->
    by eapply Permutation.Permutation_repeat, Permutation_Type_Permutation, PCPermutation_Permutation_Type, p.
  apply (IHpi _ eq_refl).
- symmetry in Heql. apply repeat_eq_app in Heql as [Heq1 [Hw Heq2]%repeat_eq_app].
  apply (IHpi (length l1 + (length lw' + length l2))).
  assert (lw' = repeat A (length lw')) as Hlw'.
  { clear - Hw. rewrite length_map in Hw.
    induction lw' as [|a l IHl]; [ reflexivity | cbn ].
    cbn in Hw. injection Hw as [= -> Hl].
    f_equal. apply IHl, Hl. }
  rewrite Hlw' in p.
  apply Permutation_Type_Permutation, Permutation.Permutation_repeat in p.
  rewrite <- Heq1 at 1. rewrite <- Heq2 at 1. rewrite p.
  rewrite map_repeat, ? repeat_app. reflexivity.
- destruct L.
  + right. rewrite eqpmix. reflexivity.
  + cbn in Heql. symmetry in Heql. apply repeat_eq_app in Heql as [Hl _]. symmetry in Hl.
    inversion_clear X. exact (X0 _ Hl).
- destruct n; destr_eq Heql. subst. left.
  ll_swap. eapply ex_r in pi; [ | apply PCPermutation_Type_cons_append ].
  clear - pi. induction n as [|[|n] IHn].
  + apply wk_r, pi.
  + exact pi.
  + apply IHn, co_r, pi.
- destruct n; destr_eq Heql. subst.
  apply (IHpi _ eq_refl).
- destruct n; destr_eq Heql. subst.
  exact (IHpi (S (S n)) eq_refl).
- rewrite Hcut in f. discriminate f.
- contradiction (Hgax a _ Heql).
Qed.

Lemma wn_rev P A (Hgax : forall a k, notT (projT2 (pgax P) a = repeat (wn A) k)) (Hcut : no_cut P) :
  ll P (wn A :: nil) -> (ll P (A :: wn A :: nil)) + (pmix P 0 = true).
Proof. intro pi. apply (wn_n_rev _ 1); assumption. Qed.


(** *** Tensor-One Par-Bottom simplifications *)

Inductive munit_smp : formula -> formula -> Type :=
| musmp_var X : munit_smp (var X) (var X)
| musmp_covar X : munit_smp (covar X) (covar X)
| musmp_one : munit_smp one one
| musmp_bot : munit_smp bot bot
| musmp_tens A1 A2 B1 B2 : munit_smp A1 B1 -> munit_smp A2 B2 -> munit_smp (tens A1 A2) (tens B1 B2)
| musmp_parr A1 A2 B1 B2 : munit_smp A1 B1 -> munit_smp A2 B2 -> munit_smp (parr A1 A2) (parr B1 B2)
| musmp_zero : munit_smp zero zero
| musmp_top : munit_smp top top
| musmp_plus A1 A2 B1 B2 : munit_smp A1 B1 -> munit_smp A2 B2 -> munit_smp (aplus A1 A2) (aplus B1 B2)
| musmp_with A1 A2 B1 B2 : munit_smp A1 B1 -> munit_smp A2 B2 -> munit_smp (awith A1 A2) (awith B1 B2)
| musmp_oc A B : munit_smp A B -> munit_smp (oc A) (oc B)
| musmp_wn A B : munit_smp A B -> munit_smp (wn A) (wn B)
| musmp_to A B : munit_smp A B -> munit_smp (tens one A) B
| musmp_pb A B : munit_smp A B -> munit_smp (parr A bot) B.

Lemma munit_smp_id A : munit_smp A A.
Proof. induction A; constructor; assumption. Qed.

Lemma munit_smp_map_wn l1 l2 : Forall2_inf munit_smp (map wn l1) l2 ->
  { l & l2 = map wn l & Forall2_inf munit_smp l1 l }.
Proof.
induction l1 in l2 |- *; intros HF; inversion HF; subst.
- exists nil; constructor.
- inversion X. subst.
  apply IHl1 in X0 as [ l'' -> HF' ].
  exists (B :: l''); constructor; assumption.
Qed.

Lemma munit_elim P (Hgax : atomic_ax P) l1 : ll P l1 -> forall l2, Forall2_inf munit_smp l1 l2 -> ll P l2.
Proof.
intros pi. induction pi using ll_nested_ind; intros l2' HF;
  try now (inversion HF as [ | ? ? ? ? Hm HF' ];
           inversion Hm; subst;
           constructor; apply IHpi; try eassumption;
           constructor; eassumption).
- inversion HF as [ | C D lc ld Hc' HF']. subst.
  inversion HF' as [ | C' D' lc' ld' Hc'' HF'']; subst.
  inversion HF''; subst.
  inversion Hc'; subst.
  inversion Hc''; subst.
  apply ax_r.
- symmetry in p.
  eapply PCPermutation_Type_Forall2_inf in p as [la HP]; [ | eassumption ].
  symmetry in HP.
  eapply ex_r; [ | apply HP ].
  apply IHpi. assumption.
- apply Forall2_inf_app_inv_l in HF as [(l'1, l'2) [HF1 HF2] ->].
  apply Forall2_inf_app_inv_l in HF2 as [(l''1, l''2) [HF2 HF3] ->].
  assert (HF4 := HF2).
  apply munit_smp_map_wn in HF2 as [ l''' -> HF2 ].
  symmetry in p.
  apply (Permutation_Type_map wn) in p.
  eapply Permutation_Type_Forall2_inf in p as [la HP]; [ | eassumption ].
  symmetry in HP.
  apply Permutation_Type_map_inv in HP as [lb -> HP].
  symmetry in HP.
  eapply ex_wn_r; [ | apply HP ].
  apply IHpi.
  repeat apply Forall2_inf_app; assumption.
- destruct (@concat_Forall2_inf formula) with formula L l2' munit_smp as [L' eq HF']; [ assumption | ].
  rewrite <- eq.
  apply mix_r.
  + replace (length L') with (length L); [ assumption | ].
    apply Forall2_inf_length with (Forall2_inf munit_smp); assumption.
  + apply forall_Forall_inf. intros l' Hin.
    apply Forall2_inf_in_r with (b := l') in HF'; [ | assumption ].
    destruct HF' as [l Hinl Rll'].
    apply (In_Forall_inf_in _ PL) in Hinl as (pi' & Hinl).
    refine (Dependent_Forall_inf_forall_formula _ _ X Hinl _ Rll').
- inversion_clear HF as [ | ? ? ? ? Hm HF' ].
  inversion_clear Hm; inversion_clear HF'.
  constructor.
- inversion_clear HF as [ | ? ? ? ? Hm HF' ].
  apply Forall2_inf_app_inv_l in HF' as [(l2'', l1'') [HF2 HF1] Heq]; subst.
  inversion Hm; subst.
  + constructor; [ apply IHpi1 | apply IHpi2 ]; constructor; assumption.
  + apply (Forall2_inf_cons one one) in HF1; [ | constructor ].
    apply IHpi1 in HF1.
    apply (Forall2_inf_cons B y) in HF2; [ | assumption ].
    apply IHpi2 in HF2.
    assert (forall a, notT (In_inf one (projT2 (pgax P) a))) as Hgax1.
    { intros a Hone.
      eapply Forall_inf_forall in Hone; [ | apply Hgax].
      inversion Hone. }
    rewrite <- (app_nil_l _) in HF1. apply (one_rev Hgax1 _ _ HF1 HF2).
- inversion_clear HF as [ | ? ? ? ? Hm HF' ].
  inversion Hm; subst.
  + constructor; apply IHpi; constructor; try constructor; assumption.
  + apply (Forall2_inf_cons bot bot) in HF'; [ | constructor ].
    apply (Forall2_inf_cons A y) in HF'; [ | assumption ].
    apply IHpi in HF'.
    rewrite <- (app_nil_l l'), app_comm_cons.
    eapply bot_rev; [ | assumption ].
    intros a Hbot.
    eapply Forall_inf_forall in Hbot; [ | apply Hgax].
    inversion Hbot.
- inversion_clear HF as [ | ? ? ? ? Hm HF' ]. inversion_clear Hm.
  constructor; [ apply IHpi1 | apply IHpi2 ]; constructor; assumption.
- inversion_clear HF as [ | ? ? ? ? Hm HF' ].
  inversion_clear Hm.
  destruct (munit_smp_map_wn _ HF') as [ l'' Heq HF'' ]; subst.
  constructor; apply IHpi; constructor; assumption.
- apply Forall2_inf_app_inv_l in HF as [(l', l'') [HF2 HF1] ->].
  eapply cut_r; [ eassumption | apply IHpi1 | apply IHpi2 ];
    (apply Forall2_inf_cons; [ apply munit_smp_id | ]); assumption.
- assert (Hat := Hgax a).
  assert (projT2 (pgax P) a = l2') as <-.
  { remember (projT2 (pgax P) a) as l.
    revert l2' Hat HF. clear.
    induction l; intros l2 Hat HF; inversion_clear HF as [ | ? ? ? ? Hm ]; f_equal.
    - inversion_clear Hat as [ | ? ? Hat' ].
      destruct a; inversion Hat'; inversion_clear Hm; reflexivity.
    - inversion_clear Hat.
      apply IHl; assumption. }
  apply gax_r.
Qed.


(** ** Properties on axioms *)

(** Axiom expansion *)
Lemma ax_exp P A : ll P (A :: dual A :: nil).
Proof.
induction A; cbn.
- ll_swap. apply ax_r.
- apply ax_r.
- ll_swap. apply bot_r, one_r.
- apply bot_r, one_r.
- ll_swap. apply parr_r.
  cons2app. eapply ex_r; [ | apply PCPermutation_Type_app_rot ].
  rewrite app_assoc. apply tens_r; assumption.
- apply parr_r.
  ll_swap in IHA1. ll_swap in IHA2.
  cons2app. eapply ex_r; [ | apply PCPermutation_Type_app_rot ].
  rewrite app_assoc. apply tens_r; assumption.
- ll_swap. apply top_r.
- apply top_r.
- eapply plus_r1 in IHA1. ll_swap in IHA1.
  eapply plus_r2 in IHA2. ll_swap in IHA2.
  ll_swap. apply with_r; eassumption.
- apply with_r; ll_swap; [ apply plus_r1 | apply plus_r2 ]; ll_swap; assumption.
- ll_swap in IHA.
  change (oc A :: wn (dual A) :: nil) with (oc A :: map wn (dual A :: nil)).
  apply oc_r.
  list_simpl. ll_swap. apply de_r. assumption.
- apply de_r in IHA. ll_swap in IHA. ll_swap.
  change (oc (dual A) :: wn A :: nil) with (oc (dual A) :: map wn (A :: nil)).
  apply oc_r. assumption.
Qed.
#[global] Arguments ax_exp [P].

Lemma ax_gen P Q l (Hperm : Bool.le (pperm P) (pperm Q)) (Hmix : forall n, Bool.le (pmix P n) (pmix Q n))
  (Hcut : forall A, Bool.le (pcut P A) (pcut Q A)) (Hgax : forall a, ll Q (projT2 (pgax P) a)) :
  ll P l -> ll Q l.
Proof.
intro pi.
induction pi using ll_nested_ind; cbn;
  try (assert (Hgax1 := Forall_inf_app_l _ _ Hgax));
  try (assert (Hgax2 := Forall_inf_app_r _ _ Hgax));
  try (apply IHpi1 in Hgax1);
  try (apply IHpi2 in Hgax2);
  try (now constructor; auto).
- eapply ex_r; [ eassumption | ].
  apply (PCPermutation_Type_monot _ _ Hperm). assumption.
- eapply ex_wn_r; eassumption.
- apply mix_r.
  + specialize Hmix with (length L).
    rewrite eqpmix in Hmix.
    destruct (pmix Q (length L)); assumption.
  + apply forall_Forall_inf.
    intros l' Hin. clear eqpmix. induction PL; inversion Hin.
    * subst.
      unfold Forall_Proofs in X. Dependent_Forall_inversion_formula X. assumption.
    * unfold Forall_Proofs in X. Dependent_Forall_inversion_formula X.
      apply IHPL; assumption.
- eapply cut_r; [ | eassumption | eassumption ].
  specialize (Hcut A). eapply implb_true_iff, f. apply le_implb, Hcut.
- exact (Hgax a).
Qed.

Lemma ax_exp_frag P l P' : ll P' l ->
  le_pfrag P' (axext_pfrag P (fun A => A :: dual A :: nil)) ->
  ll P l.
Proof.
intros pi Hlf.
apply (@ax_gen (axext_pfrag P (fun A => A :: dual A :: nil))); try reflexivity.
- cbn. intros [|]; [ apply gax_r | apply ax_exp ].
- eapply stronger_pfrag; eassumption.
Qed.


(* Unused
(** *** Extracting finite theory *)

(** List of the elements of [pgax P] used in [pi] *)
Fixpoint gax_elts P l (pi : ll P l) :=
match pi with
| ax_r _ => nil
| ex_r _ _ pi0 _ | ex_wn_r _ _ _ _ pi0 _ => gax_elts pi0
| mix_r _ PL => (fix gax_elts_Forall P L (PL : Forall_inf (ll P) L) {struct PL} :=
       match PL with
       | Forall_inf_nil _ => nil
       | Forall_inf_cons _ Pl PL => (gax_elts Pl) ++ (gax_elts_Forall _ _ PL)
       end) _ _ PL
| one_r | top_r _ => nil
| bot_r pi0 | parr_r pi0 | plus_r1 _ pi0 | plus_r2 _ pi0 => gax_elts pi0
| tens_r pi1 pi2 | with_r pi1 pi2 | cut_r _ _ pi1 pi2 => gax_elts pi1 ++ gax_elts pi2
| oc_r pi0 | de_r pi0 | wk_r _ pi0 | co_r pi0 => gax_elts pi0
| gax_r a => a :: nil
end.

Lemma gax_elts_mix P L eq (FL : Forall_inf (ll P) L) l (pi : ll P l) : In_Forall_inf _ pi FL ->
  forall ax, In_inf ax (gax_elts pi) -> In_inf ax (gax_elts (mix_r eq FL)).
Proof.
cbn. clear eq. induction FL in l, pi |- *; intros Hin; inversion Hin.
- inversion H. subst.
  apply inj_pair2_eq_dec in H2; [ | apply (list_eq_dec (@eqb formulas_dectype)); apply eqb_eq ]; subst.
  intros ax Hin_ax. apply in_inf_or_app. left. assumption.
- intros ax Hin_ax. apply in_inf_or_app. right.
  apply IHFL with l pi; assumption.
Qed.

Lemma ax_gen_loc P Q l (Hperm : Bool.le (pperm P) (pperm Q)) (Hmix : forall n, Bool.le (pmix P n) (pmix Q n))
  (Hcut : forall A, Bool.le (pcut P A) (pcut Q A)) (pi : ll P l) :
  Forall_inf (fun a => ll Q (projT2 (pgax P) a)) (gax_elts pi) -> ll Q l.
Proof.
induction pi using ll_nested_ind; cbn; intros Hgax;
  try (assert (Hgax1 := Forall_inf_app_l _ _ Hgax));
  try (assert (Hgax2 := Forall_inf_app_r _ _ Hgax));
  try (apply IHpi1 in Hgax1);
  try (apply IHpi2 in Hgax2);
  try (now constructor; auto).
- apply IHpi in Hgax.
  eapply ex_r; [ eassumption | ].
  apply (PCPermutation_Type_monot _ _ Hperm). assumption.
- apply IHpi in Hgax.
  eapply ex_wn_r; eassumption.
- apply mix_r.
  + specialize Hmix with (length L).
    rewrite eqpmix in Hmix.
    destruct (pmix Q (length L)); assumption.
  + apply forall_Forall_inf.
    intros l' Hin. clear eqpmix. induction PL; inversion Hin.
    * subst.
      unfold Forall_Proofs in X. Dependent_Forall_inversion_formula X.
      apply X1.
      now apply Forall_inf_app_l in Hgax.
    * unfold Forall_Proofs in X. Dependent_Forall_inversion_formula X.
      apply Forall_inf_app_r in Hgax.
      apply IHPL; assumption.
- eapply cut_r; [ | eassumption | eassumption ].
  specialize (Hcut A). eapply implb_true_iff, f. apply le_implb, Hcut.
- inversion_clear Hgax. assumption.
Qed.

Lemma ax_loc P l (pi : ll P l) :
  ll (axupd_pfrag P (existT (fun x => x -> _) _
                            (fun n => projT2 (pgax P) (Vector.nth (Vector.of_list (gax_elts pi)) n)))) l.
Proof.
refine (ax_gen_loc _ _ _ pi _); try reflexivity.
destruct (gax_elts pi) as [|d l0]; [ constructor | remember (d :: l0) as l1 ]. clear - d.
apply forall_Forall_inf. intros a [n Hn <-]%(In_inf_nth _ _ d).
enough (projT2 (pgax P) (nth n l1 d)
      = projT2 (pgax (axupd_pfrag P (existT (fun x => x -> _) _
                                            (fun n => projT2 (pgax P) (Vector.nth (Vector.of_list l1) n)))))
                        (Fin.of_nat_lt Hn))
  as -> by apply gax_r.
assert (Hnth := Vector.to_list_nth_order _ _ (Vector.of_list l1) _ Hn d).
unfold Vector.nth_order in Hnth. cbn. rewrite Hnth, Vector.to_list_of_list_opp. reflexivity.
Qed.
*)


(** ** Extending sequents with a [wn] context *)

Lemma ext_wn_param P Q (Q_perm : pperm Q = true) (Hcut: forall A, Bool.le (pcut P A) (pcut Q A)) l0
  (Hgax : forall a, ll Q (projT2 (pgax P) a ++ map wn l0))
  (Hmix : forall L, pmix P (length L) = true -> pmix Q (length L) = false ->
     forall (FL : Forall_inf (ll Q) (map (fun l => l ++ (map wn l0)) L)), ll Q (concat L ++ map wn l0)) l :
  ll P l -> ll Q (l ++ map wn l0).
Proof.
intros pi.
induction pi using ll_nested_ind; try (now constructor).
- eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  apply wk_list_r, ax_r.
- eapply ex_r; [ eassumption | ].
  apply PCPermutation_Permutation_Type in p.
  rewrite Q_perm.
  apply Permutation_Type_app_tail; assumption.
- list_simpl.
  eapply ex_wn_r; [ | eassumption ].
  rewrite app_assoc in IHpi. rewrite 2 app_assoc. assumption.
- destruct (pmix Q (length L)) eqn:Q_mix.
  + apply ex_r with (map wn l0 ++ concat L); [ | apply PCPermutation_Type_app_comm ].
    rewrite <- (app_nil_l _). apply co_list_gen_perm_r; [ assumption | ].
    rewrite app_nil_l, flat_map_concat_map. apply mix_r.
    * rewrite length_map. assumption.
    * apply forall_Forall_inf.
      intros l' [l1 <- [pil1 Hin]%(In_Forall_inf_in _ PL)]%in_inf_map_inv.
      apply (Dependent_Forall_inf_forall_formula _ _ X) in Hin as pi.
      eapply ex_r; [ exact pi | apply PCPermutation_Type_app_comm ].
  + apply Hmix; [ assumption | assumption | ].
    apply forall_Forall_inf.
    intros l' [l1 <- [pil1 Hin]%(In_Forall_inf_in _ PL)]%in_inf_map_inv.
    apply (Dependent_Forall_inf_forall_formula _ _ X Hin).
- eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  apply wk_list_r, one_r.
- eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  apply co_list_r.
  apply ex_r with (tens A B :: (l2 ++ map wn l0) ++ l1 ++ map wn l0);
    [ apply tens_r; assumption | rewrite Q_perm; cbn ].
  list_simpl. rewrite ? app_comm_cons. remember (tens A B :: l2) as l2'.
  symmetry. etransitivity; [ apply Permutation_Type_app_comm | ].
  rewrite ? app_assoc. apply Permutation_Type_app_tail, Permutation_Type_app_tail, Permutation_Type_app_comm.
- rewrite <- app_comm_cons, <- map_app in IHpi.
  rewrite <- app_comm_cons, <- map_app.
  apply oc_r, IHpi.
- eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  apply co_list_r.
  apply (ex_r ((l2 ++ map wn l0) ++ l1 ++ map wn l0));
    [ | rewrite Q_perm, <- app_assoc;
        symmetry; apply Permutation_Type_app_middle, Permutation_Type_app_rot ].
  refine (cut_r A _ IHpi1 IHpi2).
  eapply implb_true_iff, f. apply le_implb, Hcut.
- apply Hgax.
Qed.

(** By extending axioms of [P] with [map wn l0],
one can turn any proof of [l] in [P] into a proof of [l ++ map wn l0]. *)
Lemma ext_wn P (P_perm : pperm P = true) l l0 : ll P l ->
  ll (axmodif_pfrag P (fun l => l ++ map wn l0)) (l ++ map wn l0).
Proof.
intro pi. refine (ext_wn_param _ _ _ _ _ pi).
- assumption.
- intro. reflexivity.
- intro a.
  assert ({ b | projT2 (pgax P) a ++ map wn l0
              = projT2 (pgax (axmodif_pfrag P (fun l => l ++ map wn l0))) b}) as [b ->]
    by (subst; exists a; reflexivity).
  apply gax_r.
- intros L P_mix Q_mix. cbn in Q_mix. rewrite P_mix in Q_mix. discriminate Q_mix.
Qed.


(** ** Consistency properties *)

Lemma weak_consistency_no_dual_proofs_ll P (Hcut : full_cut P) :
  iffT (ll P nil) { A & ll P (A :: nil) & ll P (dual A :: nil) }.
Proof.
split.
- intros pi. exists one; constructor. exact pi.
- intros [A pi1 pi2]. rewrite <- app_nil_r. exact (cut_r _ (Hcut A) pi2 pi1).
Qed.

Lemma strong_contradition_general_contradiction_ll P (Hcut : pcut P zero = true) :
  ll P (zero :: nil) -> forall l, ll P l.
Proof. intros pi l. refine (cut_r _ Hcut _ pi). apply top_r. Qed.

End Atoms.

Arguments ll_nested_ind : clear implicits.
Arguments ll_nested_ind' : clear implicits.

Notation Dependent_Forall_inf_forall_formula :=
  (Dependent_Forall_inf_forall (list_eq_dec (@eqb formulas_dectype) (fun x y => proj1 (eqb_eq x y))
                                                                    (fun x y => proj2 (eqb_eq x y)))).

Ltac destruct_ll H f X l Hl Hr HP FL a :=
  match type of H with
  | ll _ _ => destruct H as [ X
                            | l ? Hl HP
                            | l ? ? ? Hl HP
                            | ? f FL
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
                            | ? f ? ? Hl Hr
                            | a ]; subst
  end.

Ltac ll_swap :=
  match goal with
  | |- ll ?P (?a1 :: ?a2 :: nil) => eapply ex_r; [ | apply PCPermutation_Type_swap ]
  end.
Ltac ll_swap_hyp H :=
  match goal with
  | H : ll ?P (?a1 :: ?a2 :: nil) |- _ =>
        eapply ex_r in H; [ | apply PCPermutation_Type_swap ]
  end.
Tactic Notation "ll_swap" "in" hyp(H) := ll_swap_hyp H.
