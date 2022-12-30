(** * Andreoli's triadic system for focusing *)

From Coq Require Import Bool Logic Wf_nat Lia.
From OLlibs Require Import infinite List_more Permutation_Type_more.
From Yalla Require Import ll_fragments llfoc.

Set Implicit Arguments.


(* TODO move to Permutation_Type and add Prop version in stdlib
  and other places of stdlib *)
Lemma reflect_neg P b : reflect P b -> reflect (not P) (negb b).
Proof. now intros H; inversion H; constructor. Qed.

Inductive reflectT (P : Type) : bool -> Type :=
  | ReflectTT : P -> reflectT P true
  | ReflectTF : notT P -> reflectT P false.
#[global] Hint Constructors reflectT : bool.

Lemma reflectT_iffT : forall P b, reflectT P b -> (CRelationClasses.iffT P (b = true)).
Proof. now destruct 1; split; [ | | | discriminate ]. Qed.

Lemma reflectT_neg P b : reflectT P b -> reflectT (notT P) (negb b).
Proof. now intros H; inversion H; constructor. Qed.

Lemma filter_idem A f (l : list A) : filter f (filter f l) = filter f l.
Proof.
induction l as [|a l IHl]; cbn.
- reflexivity.
- case_eq (f a); cbn; intros Hfa; rewrite ? Hfa, IHl; reflexivity.
Qed.

Lemma filter_negb_filter A f (l : list A) : filter (fun x => negb (f x)) (filter f l) = nil.
Proof.
induction l as [|a l IHl]; cbn.
- reflexivity.
- case_eq (f a); cbn; intros Hfa; rewrite ? Hfa, IHl; reflexivity.
Qed.

Lemma filter_filter_comm A f g (l : list A) : filter f (filter g l) = filter g (filter f l).
Proof.
induction l as [|a l IHl]; cbn; [ reflexivity | ].
case_eq (f a); case_eq (g a); intros Hg Hf; cbn; rewrite ? Hf, ? Hg, IHl; reflexivity.
Qed.

Lemma forallb_filter A f (l : list A) : forallb f (filter f l) = true.
Proof.
induction l as [|a l IHl]; cbn; [ reflexivity | ].
case_eq (f a); intros Hfa; cbn; [ rewrite Hfa | ]; assumption.
Qed.

Lemma forallb_filter_id A f (l : list A) : forallb f l = true -> filter f l = l.
Proof.
induction l; cbn; intros Hb.
- reflexivity.
- apply andb_prop in Hb as [-> Hb].
  rewrite (IHl Hb); reflexivity.
Qed.

Lemma Forall_filter A f P (l : list A) : (forall a, reflect (P a) (f a)) -> Forall P (filter f l).
Proof.
intros Hspec.
induction l as [|a l IHl]; cbn; [ constructor | ].
now destruct (Hspec a); try constructor.
Qed.

Lemma Forall_inf_filter A f P (l : list A) :
  (forall a, reflectT (P a) (f a)) -> Forall_inf P (filter f l).
Proof.
intros Hspec.
induction l as [|a l IHl]; cbn; [ constructor | ].
now destruct (Hspec a); try constructor.
Qed.

Lemma partition_filter A f (l : list A) :
  partition f l = (filter f l, filter (fun x => negb (f x)) l).
Proof.
induction l as [|a l IHl]; cbn.
- reflexivity.
- destruct (f a); destruct (partition f l); cbn;
  inversion IHl; subst; reflexivity.
Qed.

Lemma fst_partition_incl A f (l : list A) : incl (fst (partition f l)) l.
Proof. rewrite partition_filter; cbn; apply incl_filter. Qed.

Lemma snd_partition_incl A f (l : list A) : incl (snd (partition f l)) l.
Proof. rewrite partition_filter; cbn; apply incl_filter. Qed.

Lemma fst_partition_incl_inf A f (l : list A) : incl_inf (fst (partition f l)) l.
Proof. rewrite partition_filter; cbn; apply incl_inf_filter. Qed.

Lemma snd_partition_incl_inf A f (l : list A) : incl_inf (snd (partition f l)) l.
Proof. rewrite partition_filter; cbn; apply incl_inf_filter. Qed.

Definition prod_map A B (f : A -> B) p :=
  match p with
  | (a1, a2) => (f a1, f a2)
  end.

Definition prod_map2 A B C (f : A -> B -> C) p1 p2 :=
  match p1, p2 with
  | (a1, a2), (b1, b2) => (f a1 b1, f a2 b2)
  end.

Lemma partition_app A f (l1 l2 : list A) :
  partition f (l1 ++ l2) = prod_map2 (@app A) (partition f l1) (partition f l2).
Proof.
induction l1 as [|a l1 IHl1]; cbn.
- destruct (partition f l2); reflexivity.
- destruct (f a); rewrite IHl1; destruct (partition f l1), (partition f l2); reflexivity.
Qed.

Lemma partition_Permutation_Type A f (l l1 l2 : list A) :
  (l1, l2) = partition f l -> Permutation_Type (l1 ++ l2) l.
Proof.
induction l as [|a l IHl] in l1, l2 |- *; cbn; intros Hp.
- inversion Hp; subst; reflexivity.
- destruct (partition f l), (f a); inversion Hp; subst.
  + cbn; apply Permutation_Type_cons; [ reflexivity | ].
    apply IHl; reflexivity.
  + symmetry; apply Permutation_Type_cons_app; symmetry.
    apply IHl; reflexivity.
Qed.

Lemma Permutation_Type_partition A f (l l' l1 l2 l1' l2' : list A) :
  Permutation_Type l l' -> (l1, l2) = partition f l -> (l1', l2') = partition f l' ->
  Permutation_Type l1 l1' * Permutation_Type l2 l2'.
Proof.
intros HP; induction HP as [ | x l l' HP IHHP | x y l
                           | l l' l'' HP1 IHHP1 HP2 IHHP2 ] in l1, l2, l1', l2' |- *;
  cbn; intros Hp1 Hp2.
- inversion Hp1; inversion Hp2; subst.
  split; reflexivity.
- destruct (partition f l) as [l3 l4], (partition f l') as [l3' l4'], (f x);
    inversion Hp1; inversion Hp2; subst;
    destruct (IHHP l3 l4 l3' l4' eq_refl eq_refl); split; try assumption.
  + apply Permutation_Type_cons; [ reflexivity | assumption ].
  + apply Permutation_Type_cons; [ reflexivity | assumption ].
- destruct (partition f l) as [l3 l4], (f x), (f y);
    inversion Hp1; inversion Hp2; subst; split; try reflexivity.
  + apply Permutation_Type_swap.
  + apply Permutation_Type_swap.
- destruct (partition f l) as [l3 l4], (partition f l') as [l3' l4'],
           (partition f l'') as [l3'' l4''];
     inversion Hp1; inversion Hp2; subst;
     destruct (IHHP1 l3 l4 l3' l4' eq_refl eq_refl);
     destruct (IHHP2 l3' l4' l3'' l4'' eq_refl eq_refl); split; try assumption.
  + transitivity l3'; assumption.
  + transitivity l4'; assumption.
Qed.


Section Atoms.

Context { atom : InfDecType }.
Notation formula := (@formula atom).
Notation aformula := (@aformula atom).
Notation sformula := (@sformula atom).

(* TODO integrate *_formula in llfoc.v and get Foc from ttFoc (and rename ttFoc) *)
Lemma wk_list_Fr (lw l : list formula) : llFoc l None -> Forall_inf Foc l ->
  llFoc (map wn lw ++ l) None.
Proof.
induction lw as [|A lw IHlw] in l |- *; cbn; intros pi HF; [ assumption | ].
apply wk_Fr; [ apply IHlw; assumption | ].
apply Forall_inf_app; [ | assumption ].
clear; induction lw as [|A lw IHlw]; cbn; constructor; [ | assumption ].
right; exists A; reflexivity.
Qed.

Lemma wk_gen_list_Fr (lw l : list formula) : llFoc l None -> llFoc (map wn lw ++ l) None.
Proof.
induction lw as [|A lw IHlw] in l |- *; cbn; intros pi; [ assumption | ].
apply wk_gen_Fr, IHlw; assumption.
Qed.

(*
Variant is_var : formula -> Type := isvar : forall X, is_var (var X).
*)
Variant covar_formula : formula -> Type := iscovar : forall X, covar_formula (covar X).
Variant wn_formula : formula -> Type := iswn : forall A, wn_formula (wn A).

Definition ttFoc x := (sformula x + covar_formula x)%type.

Definition is_covar (A : formula) :=
  match A with
  | covar _ => true
  | _ => false
  end.

Lemma covar_spec A : reflectT (covar_formula A) (is_covar A).
Proof. destruct A; cbn; constructor; try (intros H; inversion H); constructor. Qed.

Definition is_wn (A : formula) :=
  match A with
  | wn _ => true
  | _ => false
  end.

Lemma wn_spec A : reflectT (wn_formula A) (is_wn A).
Proof.
destruct A; cbn; constructor; try (intros H; inversion H); constructor.
Qed.

Definition is_ttFoc (A : formula) :=
  match A with
  | covar _ | var _ | one | tens _ _ | zero | aplus _ _ | oc _ => true
  | _ => false
  end.

Lemma ttFoc_spec A : reflectT (ttFoc A) (is_ttFoc A).
Proof.
destruct A; cbn; constructor; try (now repeat constructor); intros H; inversion H; inversion X.
Qed.

Lemma Foc_not_wn_ttFoc A : Foc A -> notT (wn_formula A) -> ttFoc A.
Proof.
intros [[Hs|[X ->]]|[B ->]] Hwn.
- left; assumption.
- right; constructor.
- exfalso; apply Hwn; constructor.
Qed.

Lemma ttFoc_Foc A : ttFoc A -> Foc A.
Proof. now intros [Hs|[X]]; left; [left|right; exists X]. Qed.

Lemma ttFoc_not_wn A : ttFoc A -> wn_formula A -> False.
Proof.
intros Hf Hwn; destruct A; inversion Hwn.
inversion Hf as [Hf'|Hf']; inversion Hf'.
Qed.


Inductive atrifoc : list formula -> list formula -> list formula -> Type :=
| foc_tfr : forall A lw ls1 ls2, sformula A ->
              strifoc lw (ls1 ++ ls2) A -> atrifoc lw (ls1 ++ A :: ls2) nil
| focd_tfr : forall A lw1 lw2 ls, strifoc (lw1 ++ A :: lw2) ls A -> atrifoc (lw1 ++ A :: lw2) ls nil
| bot_tfr : forall lw ls l, atrifoc lw ls l -> atrifoc lw ls (bot :: l)
| parr_tfr : forall A B lw ls l,
                    atrifoc lw ls (A :: B :: l) -> atrifoc lw ls (parr A B :: l)
| top_tfr : forall lw ls l, Forall_inf ttFoc ls -> atrifoc lw ls (top :: l)
| with_tfr : forall A B lw ls l, atrifoc lw ls (A :: l) -> atrifoc lw ls (B :: l) ->
                    atrifoc lw ls (awith A B :: l)
| wn_tfr : forall A lw ls l, atrifoc (A :: lw) ls l -> atrifoc lw ls (wn A :: l)
| as_tfr : forall A lw ls l, ttFoc A -> atrifoc lw (A :: ls) l -> atrifoc lw ls (A :: l)
with strifoc : list formula -> list formula -> formula -> Type :=
| ax_tfr : forall X lw, strifoc lw (covar X :: nil) (var X)
| axd_tfr : forall X lw1 lw2, strifoc (lw1 ++ covar X :: lw2) nil (var X)
| exs_tfr : forall A lw ls1 ls2, strifoc lw ls1 A -> Permutation_Type ls1 ls2 -> strifoc lw ls2 A
  (* some shuffle is necessary below the tens_tfr rule *)
| one_tfr : forall lw, strifoc lw nil one
| tens_tfr : forall A B lw ls1 ls2,
                    strifoc lw ls1 A -> strifoc lw ls2 B -> strifoc lw (ls1 ++ ls2) (tens A B)
| plus_tfr1 : forall A B lw ls, strifoc lw ls A -> strifoc lw ls (aplus A B)
| plus_tfr2 : forall A B lw ls, strifoc lw ls A -> strifoc lw ls (aplus B A)
| oc_tfr : forall A lw, atrifoc lw nil (A :: nil) -> strifoc lw nil (oc A)
| unfoc_tfr : forall A lw ls, aformula A -> atrifoc lw ls (A :: nil) -> strifoc lw ls A.

Scheme astrifoc_rect := Induction for atrifoc Sort Type
  with satrifoc_rect := Induction for strifoc Sort Type.
Combined Scheme trifoc_rect from astrifoc_rect, satrifoc_rect.

Lemma tsync_context :
  (forall lw ls l, atrifoc lw ls l -> Forall_inf ttFoc ls)
* (forall lw ls A, strifoc lw ls A -> Forall_inf ttFoc ls).
Proof.
apply trifoc_rect; try now intuition constructor.
- intros A lw ls1 ls2 Hs pi HF.
  apply (inl : _ -> ttFoc _) in Hs.
  apply Forall_inf_app; [ | constructor; [ assumption | ] ].
  + now apply Forall_inf_app_l in HF.
  + now apply Forall_inf_app_r in HF.
- intros A lw ls1 ls2 _ _ HF.
  now inversion HF.
- intros X _.
  constructor; [ | constructor ].
  right; constructor.
- intros A lw ls1 ls2 pi HF HP.
  eapply Permutation_Type_Forall_inf; eassumption.
- intros A B lw ls1 ls2 pi1 HF1 pi2 HF2.
  apply Forall_inf_app; assumption.
Qed.

Lemma wk_list_tfr lw0 :
  (forall lw ls l, atrifoc lw ls l -> atrifoc (lw ++ lw0) ls l)
* (forall lw ls A, strifoc lw ls A -> strifoc (lw ++ lw0) ls A).
Proof. apply trifoc_rect; try intuition (list_simpl; econstructor; eassumption). Qed.

Lemma exw_tfr :
  (forall lw ls l, atrifoc lw ls l -> forall lw0, Permutation_Type lw lw0 -> atrifoc lw0 ls l)
* (forall lw ls A, strifoc lw ls A -> forall lw0, Permutation_Type lw lw0 -> strifoc lw0 ls A).
Proof.
apply trifoc_rect;
  try now (intros; try specialize (X lw0); try (intuition (list_simpl; constructor; assumption))).
- intros A lw1 lw2 ls pi IHpi lw0 HP.
  symmetry in HP; destruct (Permutation_Type_vs_elt_inv _ _ _ HP) as [(l1, l2) ->].
  apply focd_tfr, IHpi.
  symmetry; assumption.
- intros A B lw ls l pi1 IHpi1 pi2 IHpi2 lw0 HP.
  apply with_tfr; [ apply IHpi1 | apply IHpi2 ]; assumption.
- intros A lw ls l pi IHpi lw0 HP.
  apply wn_tfr, IHpi, Permutation_Type_cons; [ reflexivity | assumption ].
- intros X lw1 lw2 lw0 HP.
  symmetry in HP; destruct (Permutation_Type_vs_elt_inv _ _ _ HP) as [(l1, l2) ->].
  apply axd_tfr.
- intros A lw ls1 ls2 pi IHpi HP' lw0 HP.
  eapply exs_tfr; [ | eassumption ].
  apply IHpi, HP.
- intros A B lw ls1 ls2 pi1 IHpi1 pi2 IHpi2 lw0 HP.
  apply tens_tfr; [ apply IHpi1 | apply IHpi2 ]; apply HP.
Qed.

Lemma ex_tfr :
  (forall lw ls l, atrifoc lw ls l -> forall ls0, Permutation_Type ls ls0 -> atrifoc lw ls0 l)
* (forall lw ls A, strifoc lw ls A -> forall ls0, Permutation_Type ls ls0 -> strifoc lw ls0 A).
Proof.
apply trifoc_rect; try now (intros; constructor; auto).
- intros A lw ls1 ls2 Hs pi IHpi ls0 HP.
  symmetry in HP; destruct (Permutation_Type_vs_elt_inv _ _ _ HP) as [(l1, l2) ->].
  apply foc_tfr, IHpi; try assumption.
  symmetry in HP; apply Permutation_Type_app_inv in HP; assumption.
- intros lw ls l HF ls0 HP.
  apply top_tfr.
  apply Permutation_Type_Forall_inf with ls; assumption.
- intros X lw ls0 HP.
  apply Permutation_Type_length_1_inv in HP; subst.
  apply ax_tfr.
- intros X lw1 lw2 ls0 HP.
  apply Permutation_Type_nil in HP; subst.
  apply axd_tfr.
- intros A lw ls1 ls2 pi IHpi HP' ls0 HP.
  apply IHpi.
  transitivity ls2; assumption.
- intros lw ls0 HP.
  apply Permutation_Type_nil in HP; subst.
  apply one_tfr.
- intros A B lw ls1 ls2 pi1 IHpi1 pi2 IHpi2 lw0 HP.
  eapply exs_tfr; [ | eassumption ].
  apply tens_tfr; auto.
- intros A lw pi IHpi ls0 HP.
  apply Permutation_Type_nil in HP; subst.
  apply oc_tfr; auto.
Qed.

Lemma bot_gen_tfr lw ls l1 l2 :
  atrifoc lw ls (l1 ++ l2) -> atrifoc lw ls (l1 ++ bot :: l2).
Proof.
remember (list_sum (map fsize l1)) as n; revert lw ls l1 Heqn; induction n using lt_wf_rect;
  intros lw ls l1 -> pi; subst.
destruct l1.
- apply bot_tfr; assumption.
- list_simpl; destruct f;
    try (inversion pi; subst; apply as_tfr; [ left; constructor | ];
         apply X with (list_sum (map fsize l1)); simpl; try lia; assumption).
  + inversion pi; subst.
    apply as_tfr; [ right; constructor | ].
    apply X with (list_sum (map fsize l1)); simpl; try lia; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply bot_tfr.
    apply X with (list_sum (map fsize l1)); simpl; try lia; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply parr_tfr; rewrite 2 app_comm_cons.
    apply X with (list_sum (map fsize (f1 :: f2 :: l1))); simpl; try lia; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply top_tfr; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply with_tfr; rewrite app_comm_cons.
    * apply X with (list_sum (map fsize (f1 :: l1))); simpl; try lia; assumption.
    * apply X with (list_sum (map fsize (f2 :: l1))); simpl; try lia; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply wn_tfr.
    apply X with (list_sum (map fsize l1)); simpl; try lia; assumption.
Qed.

Lemma parr_gen_tfr A B lw ls l1 l2 :
  atrifoc lw ls (l1 ++ A :: B :: l2) -> atrifoc lw ls (l1 ++ parr A B :: l2).
Proof.
remember (list_sum (map fsize l1)) as n; revert lw ls l1 Heqn; induction n using lt_wf_rect;
  intros lw ls l1 -> pi; subst.
destruct l1.
- apply parr_tfr; assumption.
- list_simpl; destruct f;
    try (inversion pi; subst; apply as_tfr; [ left; constructor | ];
         apply X with (list_sum (map fsize l1)); simpl; try lia; assumption).
  + inversion pi; subst.
    apply as_tfr; [ right; constructor | ].
    apply X with (list_sum (map fsize l1)); simpl; try lia; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply bot_tfr.
    apply X with (list_sum (map fsize l1)); simpl; try lia; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply parr_tfr; rewrite 2 app_comm_cons.
    apply X with (list_sum (map fsize (f1 :: f2 :: l1))); simpl; try lia; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply top_tfr; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply with_tfr; rewrite app_comm_cons.
    * apply X with (list_sum (map fsize (f1 :: l1))); simpl; try lia; assumption.
    * apply X with (list_sum (map fsize (f2 :: l1))); simpl; try lia; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply wn_tfr.
    apply X with (list_sum (map fsize l1)); simpl; try lia; assumption.
Qed.

Lemma top_gen_tfr lw ls l1 l2 : Forall_inf ttFoc ls ->
  atrifoc lw ls (l1 ++ top :: l2).
Proof.
remember (list_sum (map fsize l1)) as n; revert lw ls l1 Heqn; induction n using lt_wf_rect;
  intros lw ls l1 -> HF; subst.
destruct l1.
- apply top_tfr; assumption.
- list_simpl; destruct f;
    try (apply as_tfr; [ left; constructor | ];
    apply X with (list_sum (map fsize l1)); simpl; try lia;
    constructor; [ left; constructor | assumption ]).
  + apply as_tfr; [ right; constructor | ].
    apply X with (list_sum (map fsize l1)); simpl; try lia.
    constructor; [ right; constructor | assumption ].
  + apply bot_tfr.
    apply X with (list_sum (map fsize l1)); simpl; try lia; assumption.
  + apply parr_tfr; rewrite 2 app_comm_cons.
    apply X with (list_sum (map fsize (f1 :: f2 :: l1))); simpl; try lia; assumption.
  + apply top_tfr; assumption.
  + apply with_tfr; rewrite app_comm_cons.
    * apply X with (list_sum (map fsize (f1 :: l1))); simpl; try lia; assumption.
    * apply X with (list_sum (map fsize (f2 :: l1))); simpl; try lia; assumption.
  + apply wn_tfr.
    apply X with (list_sum (map fsize l1)); simpl; try lia; assumption.
Qed.

Lemma with_gen_tfr A B lw ls l1 l2 :
  atrifoc lw ls (l1 ++ A :: l2) -> atrifoc lw ls (l1 ++ B :: l2) ->
  atrifoc lw ls (l1 ++ awith A B :: l2).
Proof.
remember (list_sum (map fsize l1)) as n; revert lw ls l1 Heqn; induction n using lt_wf_rect;
  intros lw ls l1 -> pi1 pi2; subst.
destruct l1.
- apply with_tfr; assumption.
- list_simpl; destruct f;
    try (inversion pi1; inversion pi2; subst; apply as_tfr; [ left; constructor | ];
         apply X with (list_sum (map fsize l1)); simpl; try lia; assumption).
  + inversion pi1; inversion pi2; subst.
    apply as_tfr; [ right; constructor | ].
    apply X with (list_sum (map fsize l1)); simpl; try lia; assumption.
  + inversion pi1; subst; [ | inversion X0; inversion X2; inversion H ].
    inversion pi2; subst; [ | inversion X1; inversion X3; inversion H ].
    apply bot_tfr.
    apply X with (list_sum (map fsize l1)); simpl; try lia; assumption.
  + inversion pi1; subst; [ | inversion X0; inversion X2; inversion H ].
    inversion pi2; subst; [ | inversion X1; inversion X3; inversion H ].
    apply parr_tfr; rewrite 2 app_comm_cons.
    apply X with (list_sum (map fsize (f1 :: f2 :: l1))); simpl; try lia; assumption.
  + inversion pi1; subst; [ | inversion X0; inversion X2; inversion H ].
    inversion pi2; subst; [ | inversion X1; inversion X3; inversion H ].
    apply top_tfr; assumption.
  + inversion pi1; subst; [ | inversion X0; inversion X2; inversion H ].
    inversion pi2; subst; [ | inversion X2; inversion X4; inversion H ].
    apply with_tfr; rewrite app_comm_cons.
    * apply X with (list_sum (map fsize (f1 :: l1))); simpl; try lia; assumption.
    * apply X with (list_sum (map fsize (f2 :: l1))); simpl; try lia; assumption.
  + inversion pi1; subst; [ | inversion X0; inversion X2; inversion H ].
    inversion pi2; subst; [ | inversion X1; inversion X3; inversion H ].
    apply wn_tfr.
    apply X with (list_sum (map fsize l1)); simpl; try lia; assumption.
Qed.

Lemma wn_gen_tfr A lw ls l1 l2 :
  atrifoc (A :: lw) ls (l1 ++ l2) -> atrifoc lw ls (l1 ++ wn A :: l2).
Proof.
remember (list_sum (map fsize l1)) as n; revert lw ls l1 Heqn; induction n using lt_wf_rect;
  intros lw ls l1 -> pi; subst.
destruct l1.
- apply wn_tfr; assumption.
- list_simpl; destruct f;
    try (inversion pi; subst; apply as_tfr; [ left; constructor | ];
         apply X with (list_sum (map fsize l1)); simpl; try lia; assumption).
  + inversion pi; subst.
    apply as_tfr; [ right; constructor | ].
    apply X with (list_sum (map fsize l1)); simpl; try lia; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply bot_tfr.
    apply X with (list_sum (map fsize l1)); simpl; try lia; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply parr_tfr; rewrite 2 app_comm_cons.
    apply X with (list_sum (map fsize (f1 :: f2 :: l1))); simpl; try lia; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply top_tfr; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply with_tfr; rewrite app_comm_cons.
    * apply X with (list_sum (map fsize (f1 :: l1))); simpl; try lia; assumption.
    * apply X with (list_sum (map fsize (f2 :: l1))); simpl; try lia; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply wn_tfr.
    apply X with (list_sum (map fsize l1)); simpl; try lia.
    apply exw_tfr with (f :: A :: lw); [ assumption | apply Permutation_Type_swap ].
Qed.

Lemma unfoc_gen_tfr A lw ls l1 l2 : ttFoc A ->
  atrifoc lw (A :: ls) (l1 ++ l2) -> atrifoc lw ls (l1 ++ A :: l2).
Proof.
remember (list_sum (map fsize l1)) as n; revert lw ls l1 Heqn; induction n using lt_wf_rect;
  intros lw ls l1 -> HF pi; subst.
destruct l1.
- apply as_tfr; assumption.
- list_simpl; destruct f;
    try (inversion pi; subst; apply as_tfr; [ left; constructor | ];
         apply X with (list_sum (map fsize l1)); simpl; try lia; [ assumption | ];
         eapply ex_tfr; [ eassumption | apply Permutation_Type_swap ]).
  + inversion pi; subst.
    apply as_tfr; [ right; constructor | ].
    apply X with (list_sum (map fsize l1)); simpl; try lia; [ assumption | ].
    eapply ex_tfr; [ eassumption | apply Permutation_Type_swap ].
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply bot_tfr.
    apply X with (list_sum (map fsize l1)); simpl; try lia; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply parr_tfr; rewrite 2 app_comm_cons.
    apply X with (list_sum (map fsize (f1 :: f2 :: l1))); simpl; try lia; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply top_tfr.
    inversion X0; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply with_tfr; rewrite app_comm_cons.
    * apply X with (list_sum (map fsize (f1 :: l1))); simpl; try lia; assumption.
    * apply X with (list_sum (map fsize (f2 :: l1))); simpl; try lia; assumption.
  + inversion pi; subst; [ | inversion X0; inversion X2; inversion H ].
    apply wn_tfr.
    apply X with (list_sum (map fsize l1)); simpl; try lia; assumption.
Qed.

Lemma exa_tfr : forall lw ls l,
  atrifoc lw ls l -> forall l0, Permutation_Type l l0 -> atrifoc lw ls l0.
Proof.
apply (astrifoc_rect (fun lw ls l _ => forall l0, Permutation_Type l l0 -> atrifoc lw ls l0)
                     (fun _ _ _ _ => unit));
  try now intuition constructor.
- intros A lw ls1 ls2 Hs pi _ l0 HP.
  apply Permutation_Type_nil in HP; subst.
  apply foc_tfr, pi; assumption.
- intros A lw1 lw2 ls pi _ ls0 HP.
  apply Permutation_Type_nil in HP; subst.
  apply focd_tfr, pi.
- intros lw ls l pi IHpi l0 HP.
  symmetry in HP; destruct (Permutation_Type_vs_cons_inv HP) as [(l1, l2) ->].
  symmetry in HP; apply Permutation_Type_cons_app_inv in HP.
  apply bot_gen_tfr, IHpi; assumption.
- intros A B lw ls l pi IHpi l0 HP.
  symmetry in HP; destruct (Permutation_Type_vs_cons_inv HP) as [(l1, l2) ->].
  symmetry in HP; apply Permutation_Type_cons_app_inv in HP.
  apply parr_gen_tfr, IHpi.
  do 2 apply Permutation_Type_cons_app; assumption.
- intros lw ls l HF l0 HP.
  symmetry in HP; destruct (Permutation_Type_vs_cons_inv HP) as [(l1, l2) ->].
  symmetry in HP; apply Permutation_Type_cons_app_inv in HP.
  apply top_gen_tfr; assumption.
- intros A B lw ls l pi1 IHpi1 pi2 IHpi2 l0 HP.
  symmetry in HP; destruct (Permutation_Type_vs_cons_inv HP) as [(l1, l2) ->].
  symmetry in HP; apply Permutation_Type_cons_app_inv in HP.
  apply with_gen_tfr; [ apply IHpi1 | apply IHpi2]; apply Permutation_Type_cons_app; assumption.
- intros A lw ls l pi IHpi l0 HP.
  symmetry in HP; destruct (Permutation_Type_vs_cons_inv HP) as [(l1, l2) ->].
  symmetry in HP; apply Permutation_Type_cons_app_inv in HP.
  apply wn_gen_tfr, IHpi; assumption.
- intros A lw ls l Hf pi IHpi ls0 HP.
  symmetry in HP; destruct (Permutation_Type_vs_cons_inv HP) as [(l1, l2) ->].
  symmetry in HP; apply Permutation_Type_cons_app_inv in HP.
  apply unfoc_gen_tfr, IHpi; assumption.
Qed.

Lemma unfoc_tfr_rev A lw ls : aformula A -> strifoc lw ls A -> atrifoc lw ls (A :: nil).
Proof.
intros Ha pi; induction pi; (try now inversion Ha); [ apply (fst ex_tfr _ ls1) | ]; auto.
Qed.

Lemma trifoc_set:
  (forall lw ls l, atrifoc lw ls l -> atrifoc (nodup (@eq_dt_dec formulas_dectype) lw) ls l)
* (forall lw ls A, strifoc lw ls A -> strifoc (nodup (@eq_dt_dec formulas_dectype) lw) ls A).
Proof.
apply trifoc_rect; try (now intuition constructor); try (now econstructor; eassumption).
- intros A lw1 lw2 ls pi IHpi.
  assert (In_inf A (nodup (@eq_dt_dec formulas_dectype) (lw1 ++ A :: lw2))) as Hin
    by apply (in_in_inf (@eq_dt_dec formulas_dectype)), nodup_In, in_elt.
  apply in_inf_split in Hin as [(l1, l2) Hin]; rewrite_all Hin.
  apply focd_tfr; assumption.
- intros A lw ls l pi IHpi.
  apply wn_tfr.
  cbn in IHpi; destruct (in_dec _ A lw) as [Hin|Hnin]; [ | assumption ].
  eapply exw_tfr; [ | symmetry; apply Permutation_Type_cons_append ].
  apply wk_list_tfr; assumption.
- intros X lw1 lw2.
  assert (In_inf (covar X) (nodup (@eq_dt_dec formulas_dectype) (lw1 ++ covar X :: lw2))) as Hin
    by apply (in_in_inf (@eq_dt_dec formulas_dectype)), nodup_In, in_elt.
  apply in_inf_split in Hin as [(l1, l2) Hin]; rewrite_all Hin.
  apply axd_tfr.
Qed.

End Atoms.
