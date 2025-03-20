 (* ill_prop library for yalla *)

(** * Intuitionistic Linear Logic *)
(* Properties depending on cut admissibility *)

From Stdlib Require Import Bool.
Require Import List_more.
Require Import Permutation_Type_more.
Require Import GPermutation_Type.

Require Export ill_cut.


(** ** Reversibility statements *)
(** axiom-free cases *)

Lemma ione_rev_noax {P} : (projT1 (ipgax P) -> False) ->
  forall l1 l2 C, ill P (l1 ++ ione :: l2) C -> ill P (l1 ++ l2) C.
Proof.
intros Hgax l1 l2 C pi.
rewrite <- (app_nil_l l2).
eapply cut_ir_axfree ; try eassumption.
apply one_irr.
Qed.

Lemma itens_rev_noax {P} : (projT1 (ipgax P) -> False) ->
  forall l1 l2 A B C, ill P (l1 ++ itens A B :: l2) C -> ill P (l1 ++ A :: B :: l2) C.
Proof.
intros Hgax l1 l2 A B C pi.
assert (ill P (A :: B :: nil) (itens A B)) as Hax.
{ cons2app.
  apply tens_irr ;apply ax_exp_ill. }
rewrite <- (app_nil_l l2) ; rewrite 2 app_comm_cons.
eapply cut_ir_axfree ; eassumption.
Qed.

Lemma lpam_rev_noax {P} : (projT1 (ipgax P) -> False) ->
  forall l A B, ill P l (ilpam A B) -> ill P (l ++ A :: nil) B.
Proof.
intros Hgax l A B pi.
assert (ill P (ilpam A B :: A :: nil) B) as Hax.
{ rewrite <- (app_nil_r _) ; rewrite <- app_comm_cons ; rewrite <- (app_nil_l _).
  apply lpam_ilr ; apply ax_exp_ill. }
rewrite <- (app_nil_l _).
eapply cut_ir_axfree ; eassumption.
Qed.

Lemma gen_rev_noax {P} : (projT1 (ipgax P) -> False) ->
  forall l A, ill P l (igen A) -> ill P (l ++ A :: nil) N.
Proof.
intros Hgax l A pi.
assert (ill P (igen A :: A :: nil) N) as Hax.
{ apply gen_ilr ; apply ax_exp_ill. }
rewrite <- (app_nil_l _).
eapply cut_ir_axfree ; eassumption.
Qed.

Lemma lmap_rev_noax {P} : (projT1 (ipgax P) -> False) ->
  forall l A B, ill P l (ilmap A B) -> ill P (A :: l) B.
Proof.
intros Hgax l A B pi.
assert (ill P (A :: ilmap A B :: nil) B) as Hax.
{ cons2app.
  rewrite <- (app_nil_l (A :: _)) ; rewrite <- app_assoc.
  apply lmap_ilr ; apply ax_exp_ill. }
rewrite <- (app_nil_r _).
rewrite <- (app_nil_l l) ; rewrite app_comm_cons ; rewrite <- app_assoc.
eapply cut_ir_axfree ; eassumption.
Qed.

Lemma neg_rev_noax {P} : (projT1 (ipgax P) -> False) ->
  forall l A, ill P l (ineg A) -> ill P (A :: l) N.
Proof.
intros Hgax l A pi.
assert (ill P (A :: ineg A :: nil) N) as Hax.
{ cons2app.
  apply neg_ilr ; apply ax_exp_ill. }
rewrite <- (app_nil_r _).
rewrite <- (app_nil_l l) ; rewrite app_comm_cons ; rewrite <- app_assoc.
eapply cut_ir_axfree ; eassumption.
Qed.

Lemma iwith_rev1_noax {P} : (projT1 (ipgax P) -> False) ->
  forall l A B, ill P l (iwith A B) -> ill P l A.
Proof.
intros Hgax l A B pi.
assert (ill P (iwith A B :: nil) A) as Hax.
{ rewrite <- (app_nil_l _).
  apply with_ilr1 ; apply ax_exp_ill. }
rewrite <- (app_nil_r _).
rewrite <- (app_nil_l _).
eapply cut_ir_axfree ; eassumption.
Qed.

Lemma iwith_rev2_noax {P} : (projT1 (ipgax P) -> False) ->
  forall l A B, ill P l (iwith B A) -> ill P l A.
Proof.
intros Hgax l A B pi.
assert (ill P (iwith B A :: nil) A) as Hax.
{ rewrite <- (app_nil_l _).
  apply with_ilr2 ; apply ax_exp_ill. }
rewrite <- (app_nil_r _).
rewrite <- (app_nil_l _).
eapply cut_ir_axfree ; eassumption.
Qed.

Lemma iplus_rev1_noax {P} : (projT1 (ipgax P) -> False) ->
  forall l1 l2 A B C, ill P (l1 ++ iplus A B :: l2) C -> ill P (l1 ++ A :: l2) C.
Proof.
intros Hgax l1 l2 A B C pi.
assert (ill P (A :: nil) (iplus A B)) as Hax.
{ apply plus_irr1 ;apply ax_exp_ill. }
rewrite <- (app_nil_l l2) ; rewrite app_comm_cons.
eapply cut_ir_axfree ; eassumption.
Qed.

Lemma iplus_rev2_noax {P} : (projT1 (ipgax P) -> False) ->
  forall l1 l2 A B C, ill P (l1 ++ iplus B A :: l2) C -> ill P (l1 ++ A :: l2) C.
Proof.
intros Hgax l1 l2 A B C pi.
assert (ill P (A :: nil) (iplus B A)) as Hax.
{ apply plus_irr2 ;apply ax_exp_ill. }
rewrite <- (app_nil_l l2) ; rewrite app_comm_cons.
eapply cut_ir_axfree ; eassumption.
Qed.

Lemma ioc_rev_noax {P} : (projT1 (ipgax P) -> False) ->
  forall l A, ill P l (ioc A) -> ill P l A.
Proof.
intros Hgax l A pi.
assert (ill P (ioc A :: nil) A) as Hax.
{ rewrite <- (app_nil_l _).
  apply de_ilr ; apply ax_exp_ill. }
rewrite <- (app_nil_r _).
rewrite <- (app_nil_l _).
eapply cut_ir_axfree ; eassumption.
Qed.


(** ** Fragments of [ill] *)

Section Fragments.

(** Version of [ill] with a predicate parameter for constraining sequents inside proofs. *)
Inductive ill_ps P PS : list iformula -> iformula -> Type :=
| ax_ps_ir : forall X, is_true (PS (ivar X :: nil) (ivar X)) ->
                ill_ps P PS (ivar X :: nil) (ivar X)
| ex_ps_ir : forall l1 l2 A, is_true (PS l2 A) -> ill_ps P PS l1 A ->
                 PEPermutation_Type (ipperm P) l1 l2 -> ill_ps P PS l2 A
| ex_oc_ps_ir : forall l1 lw lw' l2 A, is_true (PS (l1 ++ map ioc lw' ++ l2) A) ->
               ill_ps P PS (l1 ++ map ioc lw ++ l2) A ->
               Permutation_Type lw lw' -> ill_ps P PS (l1 ++ map ioc lw' ++ l2) A
| one_ps_irr : is_true (PS nil ione) -> ill_ps P PS nil ione
| one_ps_ilr : forall l1 l2 A, is_true (PS (l1 ++ ione :: l2) A) ->
                              ill_ps P PS (l1 ++ l2) A ->
                              ill_ps P PS (l1 ++ ione :: l2) A
| tens_ps_irr : forall A B l1 l2, is_true (PS (l1 ++ l2) (itens A B)) ->
                    ill_ps P PS l1 A -> ill_ps P PS l2 B ->
                    ill_ps P PS (l1 ++ l2) (itens A B)
| tens_ps_ilr : forall A B l1 l2 C, is_true (PS (l1 ++ itens A B :: l2) C) ->
                    ill_ps P PS (l1 ++ A :: B :: l2) C ->
                    ill_ps P PS (l1 ++ itens A B :: l2) C
| lpam_ps_irr : forall A B l, is_true (PS l (ilpam A B)) ->
                    ill_ps P PS (l ++ A :: nil) B ->
                    ill_ps P PS l (ilpam A B)
| lpam_ps_ilr : forall A B l0 l1 l2 C, is_true (PS (l1 ++ ilpam A B :: l0 ++ l2) C) ->
                    ill_ps P PS l0 A -> ill_ps P PS (l1 ++ B :: l2) C ->
                    ill_ps P PS (l1 ++ ilpam A B :: l0 ++ l2) C
| gen_ps_irr : forall A l, is_true (PS l (igen A)) -> ill_ps P PS (l ++ A :: nil) N ->
                          ill_ps P PS l (igen A)
| gen_ps_ilr : forall A l, is_true (PS (igen A :: l) N) -> ill_ps P PS l A ->
                          ill_ps P PS (igen A :: l) N
| lmap_ps_irr : forall A B l, is_true (PS l (ilmap A B)) ->
                    ill_ps P PS (A :: l) B ->
                    ill_ps P PS l (ilmap A B)
| lmap_ps_ilr : forall A B l0 l1 l2 C, is_true (PS (l1 ++ l0 ++ ilmap A B :: l2) C) ->
                    ill_ps P PS l0 A -> ill_ps P PS (l1 ++ B :: l2) C ->
                    ill_ps P PS (l1 ++ l0 ++ ilmap A B :: l2) C
| neg_ps_irr : forall A l, is_true (PS l (ineg A)) -> ill_ps P PS (A :: l) N ->
                          ill_ps P PS l (ineg A)
| neg_ps_ilr : forall A l, is_true (PS (l ++ ineg A :: nil) N) -> ill_ps P PS l A ->
                          ill_ps P PS (l ++ ineg A :: nil) N
| top_ps_irr : forall l, is_true (PS l itop) -> ill_ps P PS l itop
| with_ps_irr : forall A B l, is_true (PS l (iwith A B)) ->
                    ill_ps P PS l A -> ill_ps P PS l B ->
                    ill_ps P PS l (iwith A B)
| with_ps_ilr1 : forall A B l1 l2 C, is_true (PS (l1 ++ iwith A B :: l2) C) ->
                           ill_ps P PS (l1 ++ A :: l2) C ->
                           ill_ps P PS (l1 ++ iwith A B :: l2) C
| with_ps_ilr2 : forall A B l1 l2 C, is_true (PS (l1 ++ iwith B A :: l2) C) ->
                           ill_ps P PS (l1 ++ A :: l2) C ->
                           ill_ps P PS (l1 ++ iwith B A :: l2) C
| zero_ps_ilr : forall l1 l2 C, is_true (PS (l1 ++ izero :: l2) C) ->
                                         ill_ps P PS (l1 ++ izero :: l2) C
| plus_ps_irr1 : forall A B l, is_true (PS l (iplus A B)) ->
                               ill_ps P PS l A ->
                               ill_ps P PS l (iplus A B)
| plus_ps_irr2 : forall A B l, is_true (PS l (iplus B A)) ->
                               ill_ps P PS l A ->
                               ill_ps P PS l (iplus B A)
| plus_ps_ilr : forall A B l1 l2 C, is_true (PS (l1 ++ iplus A B :: l2) C) ->
                        ill_ps P PS (l1 ++ A :: l2) C ->
                        ill_ps P PS (l1 ++ B :: l2) C ->
                        ill_ps P PS (l1 ++ iplus A B :: l2) C
| oc_ps_irr : forall A l, is_true (PS (map ioc l) (ioc A)) ->
                          ill_ps P PS (map ioc l) A ->
                          ill_ps P PS (map ioc l) (ioc A)
| de_ps_ilr : forall A l1 l2 C, is_true (PS (l1 ++ ioc A :: l2) C) ->
                        ill_ps P PS (l1 ++ A :: l2) C ->
                        ill_ps P PS (l1 ++ ioc A :: l2) C
| wk_ps_ilr : forall A l1 l2 C, is_true (PS (l1 ++ ioc A :: l2) C) ->
                        ill_ps P PS (l1 ++ l2) C ->
                        ill_ps P PS (l1 ++ ioc A :: l2) C
| co_ps_ilr : forall A l1 l2 C, is_true (PS (l1 ++ ioc A :: l2) C) ->
                        ill_ps P PS (l1 ++ ioc A :: ioc A :: l2) C ->
                        ill_ps P PS (l1 ++ ioc A :: l2) C
| cut_ps_ir {f : ipcut P = true} : forall A l0 l1 l2 C,
                               is_true (PS (l1 ++ l0 ++ l2) C) ->
                               ill_ps P PS l0 A -> ill_ps P PS (l1 ++ A :: l2) C ->
                               ill_ps P PS (l1 ++ l0 ++ l2) C
| gax_ps_ir : forall a, is_true (PS (fst (projT2 (ipgax P) a)) (snd (projT2 (ipgax P) a))) ->
           ill_ps P PS (fst (projT2 (ipgax P) a)) (snd (projT2 (ipgax P) a)).

Lemma stronger_ps_ipfrag P Q : le_ipfrag P Q ->
  forall PS l A, ill_ps P PS l A -> ill_ps Q PS l A.
Proof with myeeasy.
intros Hle PS l A H.
induction H ; try now constructor.
- apply (ex_ps_ir _ _ l1)...
  inversion Hle.
  destruct X as (_ & Hp).
  unfold PEPermutation_Type in p.
  unfold PEPermutation_Type.
  destruct (ipperm P) ; destruct (ipperm Q) ;
    simpl in Hp ; try inversion Hp ; subst...
- eapply ex_oc_ps_ir...
- inversion Hle.
  rewrite f in H1 ; simpl in H1.
  eapply (@cut_ps_ir _ _ H1)...
- destruct (fst (snd Hle) a) as [b Heq] ; rewrite_all Heq.
  apply gax_ps_ir...
Qed.

Lemma ill_ps_stronger {P} : forall PS QS l A,
  ill_ps P PS l A -> (forall x y, Bool.le (PS x y) (QS x y)) -> ill_ps P QS l A.
Proof with try eassumption.
intros PS QS l A pi Hsb.
assert (forall x y, is_true (PS x y) -> is_true (QS x y)) as Hs.
{ intros x y HP.
  specialize Hsb with x y.
  rewrite HP in Hsb... }
induction pi ;
  try (econstructor ; try apply Hs ; eassumption ; fail).
Qed.

Lemma ill_ps_is_ps {P} : forall l A PS, ill_ps P PS l A -> is_true (PS l A).
Proof.
intros l A PS pi.
inversion pi ; try assumption.
Qed.

Lemma ill_ps_is_ill {P} : forall l A PS, ill_ps P PS l A -> ill P l A.
Proof with try eassumption.
intros l A PS pi.
induction pi ; try now constructor.
- eapply ex_ir...
- eapply ex_oc_ir...
- eapply (@cut_ir _ f)...
Qed.

Lemma ill_is_ill_ps {P} : forall l A, ill P l A -> ill_ps P (fun _ _ => true) l A.
Proof with myeeasy.
intros l A pi.
induction pi ; try now constructor.
- eapply ex_ps_ir...
- eapply ex_oc_ps_ir...
- eapply (@cut_ps_ir _ _ f)...
Qed.

(** A fragment is a subset stable under sub-formula *)
Definition ifragment FS :=
  forall A, is_true (FS A) -> forall B, isubform B A -> is_true (FS B).

(** Conservativity over fragments *)
Lemma iconservativity {P} : ipcut P = false -> forall FS, ifragment FS ->
  forall l A, ill_ps P (fun _ _ => true) l A -> is_true (forallb FS (A :: l)) ->
    ill_ps P (fun l0 A0 => forallb FS (A0 :: l0)) l A.
Proof with try eassumption ; try reflexivity.
intros P_cutfree FS HFS l A pi.
induction pi; intros HFrag;
  inversion HFrag; simpl in HFrag; apply andb_true_iff in HFrag as [Hhd HFrag]; subst.
- apply ax_ps_ir...
- apply (ex_ps_ir _ _ l1)...
  apply IHpi...
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  constructor...
  symmetry in p.
  eapply PEPermutation_Type_Forall in p.
  apply p in HFrag...
- eapply ex_oc_ps_ir...
  apply IHpi...
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  apply Forall_app in HFrag as [HF1 HF2].
  apply Forall_app in HF2 as [HF2 HF3].
  constructor...
  apply Forall_app; split...
  apply Forall_app; split...
  apply (Permutation_Type_map ioc) in p.
  symmetry in p ; eapply Permutation_Type_Forall...
- apply one_ps_irr...
- apply one_ps_ilr...
  apply IHpi...
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  constructor...
  apply Forall_app in HFrag as [ HFhd HFtl ].
  inversion HFtl ; apply Forall_app; split...
- rewrite forallb_forall in HFrag; apply Forall_forall, Forall_app in HFrag.
  destruct HFrag.
  apply tens_ps_irr...
  + apply IHpi1...
    apply forallb_forall, Forall_forall.
    constructor...
    eapply HFS...
    apply isub_tens_l...
  + apply IHpi2...
    apply forallb_forall, Forall_forall.
    constructor...
    eapply HFS...
    apply isub_tens_r...
- apply tens_ps_ilr...
  apply IHpi.
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  constructor...
  apply Forall_app in HFrag as [ HFhd HFtl ].
  inversion HFtl ; apply Forall_app; split...
  constructor ; [ | constructor ]...
  + eapply HFS...
    apply isub_tens_l...
  + eapply HFS...
    apply isub_tens_r...
- apply lpam_ps_irr...
  apply IHpi.
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  constructor...
  + eapply HFS...
    apply isub_lpam_r...
  + apply Forall_app; split...
    constructor ; [ | constructor ]...
    eapply HFS...
    apply isub_lpam_l...
- apply lpam_ps_ilr...
  + apply IHpi1...
    apply forallb_forall, Forall_forall.
    rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
    apply Forall_app in HFrag as [ HFhd HFtl ].
    inversion HFtl.
    apply Forall_app in H3; destruct H3.
    constructor...
    eapply HFS...
    apply isub_lpam_l...
  + apply IHpi2...
    apply forallb_forall, Forall_forall.
    rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
    apply Forall_app in HFrag as [ HFhd HFtl ].
    inversion HFtl.
    apply Forall_app in H3; destruct H3.
    constructor...
    apply Forall_app; split...
    constructor...
    eapply HFS...
    apply isub_lpam_r...
- apply gen_ps_irr...
  apply IHpi.
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  constructor...
  + eapply HFS...
    apply isub_gen_N.
  + apply Forall_app; split...
    constructor ; [ | constructor ].
    eapply HFS...
    apply isub_gen...
- apply gen_ps_ilr...
  apply IHpi...
  apply forallb_forall, Forall_forall.
  apply andb_true_iff in HFrag as [ HFhd HFtl ].
  rewrite forallb_forall in HFtl; apply Forall_forall in HFtl.
  constructor...
  eapply HFS...
  apply isub_gen...
- apply lmap_ps_irr...
  apply IHpi.
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  constructor...
  + eapply HFS...
    apply isub_lmap_r...
  + constructor...
    eapply HFS...
    apply isub_lmap_l...
- apply lmap_ps_ilr...
  + apply IHpi1...
    apply forallb_forall, Forall_forall.
    rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
    apply Forall_app in HFrag as [ HFhd HFtl ].
    apply Forall_app in HFtl; destruct HFtl.
    inversion H1.
    constructor...
    eapply HFS...
    apply isub_lmap_l...
  + apply IHpi2...
    apply forallb_forall, Forall_forall.
    rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
    apply Forall_app in HFrag as [ HFhd HFtl ].
    apply Forall_app in HFtl; destruct HFtl.
    inversion H1.
    constructor...
    apply Forall_app; split...
    constructor...
    eapply HFS...
    apply isub_lmap_r...
- apply neg_ps_irr...
  apply IHpi.
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  constructor...
  + eapply HFS...
    apply isub_neg_N.
  + constructor...
    eapply HFS...
    constructor...
- apply neg_ps_ilr...
  apply IHpi...
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  apply Forall_app in HFrag as [ HFhd HFtl ].
  inversion HFtl ; subst.
  constructor...
  eapply HFS...
  apply isub_neg...
- apply top_ps_irr...
- apply with_ps_irr...
  + apply IHpi1...
    apply forallb_forall, Forall_forall.
    rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
    constructor...
    eapply HFS...
    apply isub_with_l...
  + apply IHpi2...
    apply forallb_forall, Forall_forall.
    rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
    constructor...
    eapply HFS...
    apply isub_with_r...
- apply with_ps_ilr1...
  apply IHpi.
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  constructor...
  apply Forall_app in HFrag as [ HFhd HFtl ].
  inversion HFtl; apply Forall_app; split...
  constructor...
  eapply HFS...
  apply isub_with_l...
- apply with_ps_ilr2...
  apply IHpi.
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  constructor...
  apply Forall_app in HFrag as [ HFhd HFtl ].
  inversion HFtl ; apply Forall_app; split...
  constructor...
  eapply HFS...
  apply isub_with_r...
- apply zero_ps_ilr...
- apply plus_ps_irr1...
  apply IHpi.
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  constructor...
  eapply HFS...
  apply isub_plus_l...
- apply plus_ps_irr2...
  apply IHpi.
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  constructor...
  eapply HFS...
  apply isub_plus_r...
- apply plus_ps_ilr...
  + apply IHpi1...
    apply forallb_forall, Forall_forall.
    rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
    constructor...
    apply Forall_app in HFrag as [ HFhd HFtl ].
    inversion HFtl ; apply Forall_app; split...
    constructor...
    eapply HFS...
    apply isub_plus_l...
  + apply IHpi2...
    apply forallb_forall, Forall_forall.
    rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
    constructor...
    apply Forall_app in HFrag as [ HFhd HFtl ].
    inversion HFtl; apply Forall_app; split...
    constructor...
    eapply HFS...
    apply isub_plus_r...
- apply oc_ps_irr...
  apply IHpi.
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  constructor...
  eapply HFS...
  apply isub_oc...
- apply de_ps_ilr...
  apply IHpi.
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  constructor...
  apply Forall_app in HFrag as [ HFhd HFtl ].
  inversion HFtl; apply Forall_app; split...
  constructor...
  eapply HFS...
  apply isub_oc...
- apply wk_ps_ilr...
  apply IHpi...
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  constructor...
  apply Forall_app in HFrag as [ HFhd HFtl ].
  inversion HFtl; apply Forall_app; split...
- apply co_ps_ilr...
  apply IHpi.
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  constructor...
  apply Forall_app in HFrag as [ HFhd HFtl ].
  apply Forall_app; split...
  inversion HFtl ; subst.
  constructor...
- rewrite P_cutfree in f.
  inversion f.
- apply gax_ps_ir...
Qed.

(** Sub-formula property *)
Proposition isubformula {P} : ipcut P = false -> forall l A,
  ill P l A -> ill_ps P (fun l' C => isubformb_list (C :: l') (A :: l)) l A.
Proof with try eassumption ; try reflexivity.
intros P_cutfree l A pi.
apply ill_is_ill_ps in pi.
apply iconservativity...
- intros C Hf B Hs.
  remember (A :: l) as l'.
  revert Hf ; clear - Hs ; induction l' ; intro Hf ; inversion Hf ; subst.
  simpl ; apply orb_true_iff.
  apply orb_true_iff in H0.
  destruct H0.
  + left.
    eapply isubb_trans...
    apply isubb_isub...
  + right.
    apply IHl'...
- apply (isubb_id_list (A :: l) nil).
Qed.

Lemma cut_admissible_ifragment_axfree {P} : (projT1 (ipgax P) -> False) ->
forall FS, ifragment FS -> forall l A,
  ill_ps P (fun l A => forallb FS (A :: l)) l A ->
  ill_ps (cutrm_ipfrag P) (fun l A => forallb FS (A :: l)) l A.
Proof with myeeasy.
intros P_axfree FS HFS l A pi.
assert (is_true (forallb FS (A :: l))) as HFSl by (destruct pi ; myeeasy).
apply ill_ps_is_ill in pi.
eapply cut_admissible_ill_axfree in pi...
apply ill_is_ill_ps in pi.
apply iconservativity...
Qed.

Lemma iconservativity_axfree {P} : (projT1 (ipgax P) -> False) ->
forall FS, ifragment FS ->
  forall l A, ill P l A -> is_true (forallb FS (A :: l)) ->
    ill_ps P (fun l A => forallb FS (A :: l)) l A.
Proof with try eassumption ; try reflexivity.
intros P_axfree FS Hf l A pi HFS.
eapply cut_admissible_ill_axfree in pi...
apply ill_is_ill_ps in pi.
eapply iconservativity in pi...
clear - P_axfree pi ; induction pi ; try now econstructor.
- eapply ex_ps_ir...
- eapply ex_oc_ps_ir...
Qed.

End Fragments.
