 (* ill_prop library for yalla *)


(** * Intuitionistic Linear Logic *)
(* Properties depending on cut admissibility *)

From Coq Require Import Bool.
From OLlibs Require Import dectype List_more Permutation_Type_more GPermutation_Type.
From Yalla Require Export ill_cut.

Set Implicit Arguments.


Section Atoms.

Context { preiatom : DecType }.
Notation iformula := (@iformula preiatom).
Notation ill := (@ill preiatom).

(** Consistency *)

Lemma strong_consistency_ill_axfree P : (projT1 (ipgax P) -> False) ->
  ill P nil izero -> False.
Proof.
intros Hgax pi.
apply cut_admissible_ill_axfree in pi ; try assumption.
remember nil as l ; remember izero as C ; revert Heql HeqC ; induction pi ;
  intros Heql HeqC ; inversion Heql ; inversion HeqC ; subst ;
  try now (destruct l1 ; inversion Heql).
- apply IHpi ; try reflexivity.
  symmetry in p.
  apply (PEPermutation_Type_nil _ _ p).
- apply IHpi ; try reflexivity.
  destruct l1 ; destruct lw' ; destruct l2 ; inversion Heql.
  symmetry in p ; apply Permutation_Type_nil in p ; subst ; reflexivity.
- destruct l1 ; destruct l0 ; inversion Heql.
- apply (Hgax a).
Qed.


(** ** Relating negation and implication *)

Lemma ilmap_to_ineg P A : ill P (ilmap A N :: nil) (ineg A).
Proof.
apply neg_irr.
cons2app; rewrite <- (app_nil_l _).
apply lmap_ilr; apply ax_exp_ill.
Qed.

Lemma ineg_to_ilmap P A : ill P (ineg A :: nil) (ilmap A N).
Proof.
apply lmap_irr.
cons2app.
apply neg_ilr, ax_exp_ill.
Qed.

Lemma neg_map_rule P : (forall a, notT (In_inf N (fst (projT2 (ipgax P) a)))) ->
  forall l0 l1 l2 C D, ill P l0 C -> ill P (l1 ++ N :: l2) D -> ill P (l1 ++ l0 ++ ineg C :: l2) D.
Proof.
intros Hgax l0 l1 l2 C D pi0 pi.
replace (l1 ++ l0 ++ ineg C :: l2) with (l1 ++ (l0 ++ ineg C :: nil) ++ l2)
  by (list_simpl; reflexivity).
apply cut_at_ir_gaxat with atN; [ | | apply neg_ilr | ]; try assumption.
intros b l l' Heq.
exfalso.
apply (Hgax b).
rewrite Heq.
apply in_inf_elt.
Qed.

Lemma ilpam_to_igen P A : ill P (ilpam A N :: nil) (igen A).
Proof.
apply gen_irr; list_simpl.
rewrite <- (app_nil_l _), <- (app_nil_r (A :: nil)).
apply lpam_ilr; apply ax_exp_ill.
Qed.

Lemma igen_to_ilpam P A : ill P (igen A :: nil) (ilpam A N).
Proof. apply lpam_irr, gen_ilr, ax_exp_ill. Qed.

Lemma gen_pam_rule P : (forall a, notT (In_inf N (fst (projT2 (ipgax P) a)))) ->
  forall l0 l1 l2 C D, ill P l0 C -> ill P (l1 ++ N :: l2) D -> ill P (l1 ++ igen C :: l0 ++ l2) D.
Proof.
intros Hgax l0 l1 l2 C D pi0 pi.
rewrite app_comm_cons.
apply cut_at_ir_gaxat with atN; [ | | apply gen_ilr | ]; try assumption.
intros b l l' Heq.
exfalso.
apply (Hgax b).
rewrite Heq.
apply in_inf_elt.
Qed.


(** ** Reversibility statements *)
(** axiom-free cases *)

Lemma ione_rev_noax P : (projT1 (ipgax P) -> False) ->
  forall l1 l2 C, ill P (l1 ++ ione :: l2) C -> ill P (l1 ++ l2) C.
Proof.
intros Hgax l1 l2 C pi.
rewrite <- (app_nil_l l2).
eapply cut_ir_axfree ; try eassumption.
apply one_irr.
Qed.

Lemma itens_rev_noax P : (projT1 (ipgax P) -> False) ->
  forall l1 l2 A B C, ill P (l1 ++ itens A B :: l2) C -> ill P (l1 ++ A :: B :: l2) C.
Proof.
intros Hgax l1 l2 A B C pi.
assert (ill P (A :: B :: nil) (itens A B)) as Hax.
{ cons2app.
  apply tens_irr ;apply ax_exp_ill. }
rewrite <- (app_nil_l l2) ; rewrite 2 app_comm_cons.
eapply cut_ir_axfree ; eassumption.
Qed.

Lemma ilpam_rev_noax P : (projT1 (ipgax P) -> False) ->
  forall l A B, ill P l (ilpam A B) -> ill P (l ++ A :: nil) B.
Proof.
intros Hgax l A B pi.
assert (ill P (ilpam A B :: A :: nil) B) as Hax.
{ rewrite <- (app_nil_r _) ; rewrite <- app_comm_cons ; rewrite <- (app_nil_l _).
  apply lpam_ilr ; apply ax_exp_ill. }
rewrite <- (app_nil_l _).
eapply cut_ir_axfree ; eassumption.
Qed.

Lemma igen_rev_noax P : (projT1 (ipgax P) -> False) ->
  forall l A, ill P l (igen A) -> ill P (l ++ A :: nil) N.
Proof.
intros Hgax l A pi.
assert (ill P (igen A :: A :: nil) N) as Hax.
{ apply gen_ilr ; apply ax_exp_ill. }
rewrite <- (app_nil_l _).
eapply cut_ir_axfree ; eassumption.
Qed.

Lemma ilmap_rev_noax P : (projT1 (ipgax P) -> False) ->
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

Lemma ineg_rev_noax P : (projT1 (ipgax P) -> False) ->
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

Lemma iwith_rev1_noax P : (projT1 (ipgax P) -> False) ->
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

Lemma iwith_rev2_noax P : (projT1 (ipgax P) -> False) ->
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

Lemma iplus_rev1_noax P : (projT1 (ipgax P) -> False) ->
  forall l1 l2 A B C, ill P (l1 ++ iplus A B :: l2) C -> ill P (l1 ++ A :: l2) C.
Proof.
intros Hgax l1 l2 A B C pi.
assert (ill P (A :: nil) (iplus A B)) as Hax.
{ apply plus_irr1 ;apply ax_exp_ill. }
rewrite <- (app_nil_l l2) ; rewrite app_comm_cons.
eapply cut_ir_axfree ; eassumption.
Qed.

Lemma iplus_rev2_noax P : (projT1 (ipgax P) -> False) ->
  forall l1 l2 A B C, ill P (l1 ++ iplus B A :: l2) C -> ill P (l1 ++ A :: l2) C.
Proof.
intros Hgax l1 l2 A B C pi.
assert (ill P (A :: nil) (iplus B A)) as Hax.
{ apply plus_irr2 ;apply ax_exp_ill. }
rewrite <- (app_nil_l l2) ; rewrite app_comm_cons.
eapply cut_ir_axfree ; eassumption.
Qed.

Lemma ioc_rev_noax P : (projT1 (ipgax P) -> False) ->
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
Proof.
intros Hle PS l A H.
induction H; try now constructor.
- apply ex_ps_ir with l1; try assumption.
  inversion Hle.
  destruct X as (_ & Hp).
  unfold PEPermutation_Type in *.
  now destruct (ipperm P); destruct (ipperm Q);
    cbn in Hp; try inversion Hp; subst.
- apply ex_oc_ps_ir with lw; assumption.
- inversion Hle.
  rewrite f in H1; cbn in H1.
  apply (@cut_ps_ir _ _ H1 A); assumption.
- destruct (fst (snd Hle) a) as [b Heq]; rewrite_all Heq.
  apply gax_ps_ir; assumption.
Qed.

Lemma ill_ps_stronger P PS QS l A :
  ill_ps P PS l A -> (forall x y, Bool.le (PS x y) (QS x y)) -> ill_ps P QS l A.
Proof.
intros pi Hsb.
assert (forall x y, is_true (PS x y) -> is_true (QS x y)) as Hs.
{ intros x y HP.
  specialize Hsb with x y.
  rewrite HP in Hsb; assumption. }
induction pi;
  try (econstructor; try apply Hs; eassumption). (* TODO bug??? removing [try] make it very long *)
Qed.

Lemma ill_ps_is_ps P l A PS : ill_ps P PS l A -> is_true (PS l A).
Proof. intros pi; inversion pi; assumption. Qed.

Lemma ill_ps_is_ill P l A PS : ill_ps P PS l A -> ill P l A.
Proof.
intros pi; induction pi; try now constructor.
- eapply ex_ir; eassumption.
- eapply ex_oc_ir; eassumption.
- apply (@cut_ir _ _ f A); assumption.
Qed.

Lemma ill_is_ill_ps P l A : ill P l A -> ill_ps P (fun _ _ => true) l A.
Proof.
intros pi; induction pi; try now constructor.
- now eapply ex_ps_ir; try eassumption.
- now eapply ex_oc_ps_ir; try eassumption.
- now apply (@cut_ps_ir _ _ f A).
Qed.

(** A fragment is a subset stable under sub-formula *)
Definition ifragment FS :=
  forall A : iformula, FS A -> forall B, isubform B A -> FS B.

Definition ifragmentb FS := ifragment (fun A => is_true (FS A)).

(** Conservativity over fragments *)
Lemma iconservativity P : ipcut P = false -> forall FS, ifragmentb FS ->
  forall l A, ill_ps P (fun _ _ => true) l A -> is_true (forallb FS (A :: l)) ->
    ill_ps P (fun l0 A0 => forallb FS (A0 :: l0)) l A.
Proof.
intros P_cutfree FS HFS l A pi.
induction pi; cbn; intros HFrag;
  inversion HFrag; apply andb_true_iff in HFrag; destruct HFrag as [Hhd HFrag]; subst.
- apply ax_ps_ir; assumption.
- apply ex_ps_ir with l1; trivial.
  apply IHpi.
  apply forallb_forall, Forall_forall.
  unfold is_true in HFrag; rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  constructor; [ assumption | ].
  symmetry in p.
  eapply PEPermutation_Type_Forall in p.
  apply p in HFrag; assumption.
- eapply ex_oc_ps_ir; try eassumption.
  apply IHpi.
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  apply Forall_app in HFrag as [HF1 HF2].
  apply Forall_app in HF2 as [HF2 HF3].
  constructor; [ assumption | ].
  apply Forall_app; split; [ assumption | ].
  apply Forall_app; split; [ | assumption ].
  apply (Permutation_Type_map ioc) in p.
  symmetry in p; eapply Permutation_Type_Forall; eassumption.
- apply one_ps_irr; assumption.
- apply one_ps_ilr; [ assumption | ].
  apply IHpi.
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  constructor; [ assumption | ].
  apply Forall_app in HFrag as [ HFhd HFtl ].
  inversion HFtl ; apply Forall_app; split; assumption.
- rewrite forallb_forall in HFrag; apply Forall_forall, Forall_app in HFrag as [H H1].
  apply tens_ps_irr; [ assumption | | ].
  + apply IHpi1.
    apply forallb_forall, Forall_forall.
    constructor; [ | assumption ].
    eapply HFS; [ eassumption | ].
    apply isub_tens_l; reflexivity.
  + apply IHpi2.
    apply forallb_forall, Forall_forall.
    constructor; [ | assumption ].
    eapply HFS; [ eassumption | ].
    apply isub_tens_r; reflexivity.
- apply tens_ps_ilr; [ assumption | ].
  apply IHpi.
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  constructor; [ assumption | ].
  apply Forall_app in HFrag as [ HFhd HFtl ].
  inversion HFtl; apply Forall_app; split; [ assumption | ].
  constructor ; [ | constructor ]; [ | | assumption ].
  + eapply HFS; [ eassumption | ].
    apply isub_tens_l; reflexivity.
  + eapply HFS; [ eassumption | ].
    apply isub_tens_r; reflexivity.
- apply lpam_ps_irr; [ assumption | ].
  apply IHpi.
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  constructor.
  + eapply HFS; [ eassumption | ].
    apply isub_lpam_r; reflexivity.
  + apply Forall_app; split; [ assumption | ].
    constructor ; [ | constructor ].
    eapply HFS; [ eassumption | ].
    apply isub_lpam_l; reflexivity.
- apply lpam_ps_ilr; [ assumption | | ].
  + apply IHpi1.
    apply forallb_forall, Forall_forall.
    rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
    apply Forall_app in HFrag as [ HFhd HFtl ].
    inversion HFtl.
    apply Forall_app in H3; destruct H3.
    constructor; [ | assumption ].
    eapply HFS; [ eassumption | ].
    apply isub_lpam_l; reflexivity.
  + apply IHpi2.
    apply forallb_forall, Forall_forall.
    rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
    apply Forall_app in HFrag as [ HFhd HFtl ].
    inversion HFtl.
    apply Forall_app in H3; destruct H3.
    constructor; [ assumption | ].
    apply Forall_app; split; [ assumption | ].
    constructor; [ | assumption ].
    eapply HFS; [ eassumption | ].
    apply isub_lpam_r; reflexivity.
- apply gen_ps_irr; [ assumption | ].
  apply IHpi.
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  constructor.
  + eapply HFS; [ eassumption | ].
    apply isub_gen_N.
  + apply Forall_app; split; [ assumption | ].
    constructor ; [ | constructor ].
    eapply HFS; [ eassumption | ].
    apply isub_gen; reflexivity.
- apply gen_ps_ilr; [ assumption | ].
  apply IHpi.
  apply forallb_forall, Forall_forall.
  apply andb_true_iff in HFrag as [ HFhd HFtl ].
  rewrite forallb_forall in HFtl; apply Forall_forall in HFtl.
  constructor; [ | assumption ].
  eapply HFS; [ eassumption | ].
  apply isub_gen; reflexivity.
- apply lmap_ps_irr; [ assumption | ].
  apply IHpi.
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  constructor.
  + eapply HFS; [ eassumption | ].
    apply isub_lmap_r; reflexivity.
  + constructor; [ | assumption ].
    eapply HFS; [ eassumption | ].
    apply isub_lmap_l; reflexivity.
- apply lmap_ps_ilr; [ assumption | | ].
  + apply IHpi1.
    apply forallb_forall, Forall_forall.
    rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
    apply Forall_app in HFrag as [ HFhd HFtl ].
    apply Forall_app in HFtl; destruct HFtl.
    inversion H1.
    constructor; [ | assumption ].
    eapply HFS; [ eassumption | ].
    apply isub_lmap_l; reflexivity.
  + apply IHpi2.
    apply forallb_forall, Forall_forall.
    rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
    apply Forall_app in HFrag as [ HFhd HFtl ].
    apply Forall_app in HFtl; destruct HFtl.
    inversion H1.
    constructor; [ assumption | ].
    apply Forall_app; split; [ assumption | ].
    constructor; [ | assumption ].
    eapply HFS; [ eassumption | ].
    apply isub_lmap_r; reflexivity.
- apply neg_ps_irr; [ assumption | ].
  apply IHpi.
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  constructor.
  + eapply HFS; [ eassumption | ].
    apply isub_neg_N.
  + constructor; [ | assumption ].
    eapply HFS; [ eassumption | ].
    constructor; reflexivity.
- apply neg_ps_ilr; [ assumption | ].
  apply IHpi.
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  apply Forall_app in HFrag as [ HFhd HFtl ].
  inversion HFtl ; subst.
  constructor; [ | assumption ].
  eapply HFS; [ eassumption | ].
  apply isub_neg; reflexivity.
- apply top_ps_irr; assumption.
- apply with_ps_irr; [ assumption | | ].
  + apply IHpi1.
    apply forallb_forall, Forall_forall.
    rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
    constructor; [ | assumption ].
    eapply HFS; [ eassumption | ].
    apply isub_with_l; reflexivity.
  + apply IHpi2.
    apply forallb_forall, Forall_forall.
    rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
    constructor; [ | assumption ].
    eapply HFS; [ eassumption | ].
    apply isub_with_r; reflexivity.
- apply with_ps_ilr1; [ assumption | ].
  apply IHpi.
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  constructor; [ assumption | ].
  apply Forall_app in HFrag as [ HFhd HFtl ].
  inversion HFtl; apply Forall_app; split; [ assumption | ].
  constructor; [ | assumption ].
  eapply HFS; [ eassumption | ].
  apply isub_with_l; reflexivity.
- apply with_ps_ilr2; [ assumption | ].
  apply IHpi.
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  constructor; [ assumption | ].
  apply Forall_app in HFrag as [ HFhd HFtl ].
  inversion HFtl ; apply Forall_app; split; [ assumption | ].
  constructor; [ | assumption ].
  eapply HFS; [ eassumption | ].
  apply isub_with_r; reflexivity.
- apply zero_ps_ilr; assumption.
- apply plus_ps_irr1; [ assumption | ].
  apply IHpi.
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  constructor; [ | assumption ].
  eapply HFS; [ eassumption | ].
  apply isub_plus_l; reflexivity.
- apply plus_ps_irr2; [ assumption | ].
  apply IHpi.
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  constructor; [ | assumption ].
  eapply HFS; [ eassumption | ].
  apply isub_plus_r; reflexivity.
- apply plus_ps_ilr; [ assumption | | ].
  + apply IHpi1.
    apply forallb_forall, Forall_forall.
    rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
    constructor; [ assumption | ].
    apply Forall_app in HFrag as [ HFhd HFtl ].
    inversion HFtl ; apply Forall_app; split; [ assumption | ].
    constructor; [ | assumption ].
    eapply HFS; [ eassumption | ].
    apply isub_plus_l; reflexivity.
  + apply IHpi2.
    apply forallb_forall, Forall_forall.
    rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
    constructor; [ assumption | ].
    apply Forall_app in HFrag as [ HFhd HFtl ].
    inversion HFtl; apply Forall_app; split; [ assumption | ].
    constructor; [ | assumption ].
    eapply HFS; [ eassumption | ].
    apply isub_plus_r; reflexivity.
- apply oc_ps_irr; [ assumption | ].
  apply IHpi.
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  constructor; [ | assumption ].
  eapply HFS; [ eassumption | ].
  apply isub_oc; reflexivity.
- apply de_ps_ilr; [ assumption | ].
  apply IHpi.
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  constructor; [ assumption | ].
  apply Forall_app in HFrag as [ HFhd HFtl ].
  inversion HFtl; apply Forall_app; split; [ assumption | ].
  constructor; [ | assumption ].
  eapply HFS; [ eassumption | ].
  apply isub_oc; reflexivity.
- apply wk_ps_ilr; [ assumption | ].
  apply IHpi.
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  constructor; [ assumption | ].
  apply Forall_app in HFrag as [ HFhd HFtl ].
  inversion HFtl; apply Forall_app; split; assumption.
- apply co_ps_ilr; [ assumption | ].
  apply IHpi.
  apply forallb_forall, Forall_forall.
  rewrite forallb_forall in HFrag; apply Forall_forall in HFrag.
  constructor; [ assumption | ].
  apply Forall_app in HFrag as [ HFhd HFtl ].
  apply Forall_app; split; [ assumption | ].
  inversion HFtl; subst.
  constructor; assumption.
- rewrite P_cutfree in f.
  inversion f.
- apply gax_ps_ir; assumption.
Qed.

(** Sub-formula property *)
Proposition isubformula P : ipcut P = false -> forall l A,
  ill P l A -> ill_ps P (fun l' C => isubformb_list (C :: l') (A :: l)) l A.
Proof.
intros P_cutfree l A pi.
apply ill_is_ill_ps in pi.
apply iconservativity; trivial.
- intros C Hf B Hs.
  remember (A :: l) as l'.
  revert Hf; clear - Hs; induction l'; intro Hf; inversion Hf; subst.
  cbn; apply orb_true_iff.
  apply orb_true_iff in H0.
  destruct H0.
  + left.
    apply (isubb_trans _ C); [ | assumption ].
    apply isubb_isub; assumption.
  + right.
    apply IHl'; assumption.
- apply (isubb_id_list (A :: l) nil).
Qed.

Lemma cut_admissible_ifragment_axfree P : (projT1 (ipgax P) -> False) ->
  forall FS, ifragmentb FS -> forall l A,
  ill_ps P (fun l A => forallb FS (A :: l)) l A ->
  ill_ps (cutrm_ipfrag P) (fun l A => forallb FS (A :: l)) l A.
Proof.
intros P_axfree FS HFS l A pi.
assert (is_true (forallb FS (A :: l))) as HFSl by now destruct pi.
apply ill_ps_is_ill in pi.
apply cut_admissible_ill_axfree in pi; [ | assumption ].
apply ill_is_ill_ps in pi.
now apply iconservativity.
Qed.

Lemma iconservativity_axfree P : (projT1 (ipgax P) -> False) ->
  forall FS, ifragmentb FS ->
  forall l A, ill P l A -> is_true (forallb FS (A :: l)) ->
    ill_ps P (fun l A => forallb FS (A :: l)) l A.
Proof.
intros P_axfree FS Hf l A pi HFS.
apply cut_admissible_ill_axfree in pi; [ | assumption ].
apply ill_is_ill_ps in pi.
eapply iconservativity in pi; try eassumption; try reflexivity.
clear - P_axfree pi; induction pi;
  (try now constructor); try (econstructor; eassumption); now econstructor.
Qed.

End Fragments.

End Atoms.
