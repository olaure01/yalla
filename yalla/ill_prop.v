(** * Properties of Intuitionistic Linear Logic *)
(* Properties depending on cut admissibility *)

From Coq Require Import Bool.
From OLlibs Require Import dectype List_more Permutation_Type_more GPermutation_Type.
From Yalla Require Export ill_cut.

Set Implicit Arguments.


Section Atoms.

Context {preiatom : DecType}.
Notation iformula := (@iformula preiatom).
Notation ill := (@ill preiatom).

(** Consistency *)

Lemma strong_consistency_ill_axfree P (Hgax : no_iax P) : notT (ill P nil izero).
Proof.
intros pi%cut_admissible_ill_axfree; [ | assumption ].
remember nil as l eqn:Heql. remember izero as C eqn:HeqC.
induction pi in Heql, HeqC |- *; inversion Heql; inversion HeqC; subst;
  try now (destruct l1; destr_eq Heql).
- symmetry in p. apply PEPermutation_Type_nil in p as ->.
  apply IHpi; reflexivity.
- apply app_eq_nil in Heql as [-> [->%map_eq_nil ->]%app_eq_nil].
  symmetry in p. apply Permutation_Type_nil in p as ->.
  apply IHpi; reflexivity.
- rewrite app_assoc in Heql. symmetry in Heql. nil_vs_elt_inv Heql.
- contradiction (Hgax a).
Qed.


(** ** Relating negation and implication *)

Lemma cut_N_ir P (Hgax : noN_iax P) l0 l1 l2 C :
  ill P l0 N -> ill P (l1 ++ N :: l2) C -> ill P (l1 ++ l0 ++ l2) C.
Proof.
intros pi1 pi2. refine (cut_at_ir_gax Hgax _ _ _ pi1 pi2).
intros b l l' Heq. contradiction (Hgax b). rewrite Heq. apply in_inf_elt.
Qed.

Lemma ilmap_to_ineg P A : ill P (ilmap A N :: nil) (ineg A).
Proof. apply neg_irr. cons2app. rewrite <- (app_nil_l _). apply lmap_ilr; apply ax_exp_ill. Qed.

Lemma ineg_to_ilmap P A : ill P (ineg A :: nil) (ilmap A N).
Proof. apply lmap_irr. cons2app. apply neg_ilr, ax_exp_ill. Qed.

Lemma neg_map_rule P (Hgax : noN_iax P) l0 l1 l2 C D :
  ill P l0 C -> ill P (l1 ++ N :: l2) D -> ill P (l1 ++ l0 ++ ineg C :: l2) D.
Proof. intros pi0%neg_ilr pi. cons2app. rewrite (app_assoc l0). apply cut_N_ir; assumption. Qed.

Lemma ilpam_to_igen P A : ill P (ilpam A N :: nil) (igen A).
Proof.
apply gen_irr. list_simpl. rewrite <- (app_nil_l _), <- (app_nil_r (A :: nil)).
apply lpam_ilr; apply ax_exp_ill.
Qed.

Lemma igen_to_ilpam P A : ill P (igen A :: nil) (ilpam A N).
Proof. apply lpam_irr, gen_ilr, ax_exp_ill. Qed.

Lemma gen_pam_rule P (Hgax : noN_iax P) l0 l1 l2 C D :
  ill P l0 C -> ill P (l1 ++ N :: l2) D -> ill P (l1 ++ igen C :: l0 ++ l2) D.
Proof. intros pi0%gen_ilr pi. rewrite app_comm_cons. apply cut_N_ir; assumption. Qed.


(** ** Reversibility statements *)
(** axiom-free cases *)

Lemma ione_rev_noax P (Hgax : no_iax P) l1 l2 C : ill P (l1 ++ ione :: l2) C -> ill P (l1 ++ l2) C.
Proof. intro pi. rewrite <- (app_nil_l l2). apply cut_ir_axfree with ione; (assumption + apply one_irr). Qed.

Lemma itens_rev_noax P (Hgax : no_iax P) l1 l2 A B C :
  ill P (l1 ++ itens A B :: l2) C -> ill P (l1 ++ A :: B :: l2) C.
Proof.
intro pi.
assert (ill P (A :: B :: nil) (itens A B)) as Hax by (cons2app; apply tens_irr; apply ax_exp_ill).
rewrite <- (app_nil_l l2), 2 app_comm_cons. eapply cut_ir_axfree; eassumption.
Qed.

Lemma ilpam_rev_noax P (Hgax : no_iax P) l A B : ill P l (ilpam A B) -> ill P (l ++ A :: nil) B.
Proof.
intro pi.
assert (ill P (ilpam A B :: A :: nil) B) as Hax
  by (rewrite <- (app_nil_r _), <- app_comm_cons, <- (app_nil_l _); apply lpam_ilr; apply ax_exp_ill).
rewrite <- (app_nil_l _). eapply cut_ir_axfree; eassumption.
Qed.

Lemma igen_rev_noax P (Hgax : no_iax P) l A : ill P l (igen A) -> ill P (l ++ A :: nil) N.
Proof.
intro pi.
assert (ill P (igen A :: A :: nil) N) as Hax by apply gen_ilr, ax_exp_ill.
rewrite <- (app_nil_l _). eapply cut_ir_axfree; eassumption.
Qed.

Lemma ilmap_rev_noax P (Hgax : no_iax P) l A B : ill P l (ilmap A B) -> ill P (A :: l) B.
Proof.
intro pi.
assert (ill P (A :: ilmap A B :: nil) B) as Hax
  by (cons2app; rewrite <- (app_nil_l (A :: _)), <- app_assoc; apply lmap_ilr; apply ax_exp_ill).
rewrite <- (app_nil_r _), <- (app_nil_l l), app_comm_cons, <- app_assoc. eapply cut_ir_axfree; eassumption.
Qed.

Lemma ineg_rev_noax P (Hgax : no_iax P) l A : ill P l (ineg A) -> ill P (A :: l) N.
Proof.
intro pi.
assert (ill P (A :: ineg A :: nil) N) as Hax by (cons2app; apply neg_ilr, ax_exp_ill).
rewrite <- (app_nil_r _), <- (app_nil_l l), app_comm_cons, <- app_assoc. eapply cut_ir_axfree; eassumption.
Qed.

Lemma iwith_rev1_noax P (Hgax : no_iax P) l A B : ill P l (iwith A B) -> ill P l A.
Proof.
intro pi.
assert (ill P (iwith A B :: nil) A) as Hax by (rewrite <- (app_nil_l _); apply with_ilr1, ax_exp_ill).
rewrite <- (app_nil_r _), <- (app_nil_l _). eapply cut_ir_axfree; eassumption.
Qed.

Lemma iwith_rev2_noax P (Hgax : no_iax P) l A B : ill P l (iwith B A) -> ill P l A.
Proof.
intro pi.
assert (ill P (iwith B A :: nil) A) as Hax by (rewrite <- (app_nil_l _); apply with_ilr2, ax_exp_ill).
rewrite <- (app_nil_r _), <- (app_nil_l _). eapply cut_ir_axfree; eassumption.
Qed.

Lemma iplus_rev1_noax P (Hgax : no_iax P) l1 l2 A B C :
  ill P (l1 ++ iplus A B :: l2) C -> ill P (l1 ++ A :: l2) C.
Proof.
intro pi.
assert (ill P (A :: nil) (iplus A B)) as Hax by apply plus_irr1, ax_exp_ill.
rewrite <- (app_nil_l l2), app_comm_cons. eapply cut_ir_axfree; eassumption.
Qed.

Lemma iplus_rev2_noax P (Hgax : no_iax P) l1 l2 A B C :
  ill P (l1 ++ iplus B A :: l2) C -> ill P (l1 ++ A :: l2) C.
Proof.
intro pi.
assert (ill P (A :: nil) (iplus B A)) as Hax by apply plus_irr2, ax_exp_ill.
rewrite <- (app_nil_l l2), app_comm_cons. eapply cut_ir_axfree; eassumption.
Qed.

Lemma ioc_rev_noax P (Hgax : no_iax P) l A : ill P l (ioc A) -> ill P l A.
Proof.
intro pi.
assert (ill P (ioc A :: nil) A) as Hax by (rewrite <- (app_nil_l _); apply de_ilr, ax_exp_ill).
rewrite <- (app_nil_r _), <- (app_nil_l _). eapply cut_ir_axfree; eassumption.
Qed.


(** ** Fragments of [ill] *)

(** A fragment is a subset stable under sub-formula *)
Definition ifragment FS := forall A : iformula, FS A -> forall B, isubform B A -> FS B.

(** Conservativity over fragments *)
Lemma iconservativity P (P_cutfree : no_icut P) FS (Hfrag : ifragment FS) l A (pi : ill P l A) :
  Forall_inf FS (A :: l) -> Forall_iformula FS pi.
Proof.
induction pi; cbn; intros HFS; inversion HFS as [|D l' Hhd Htl]; subst; repeat split; try assumption;
  try (apply IHpi; constructor; [ eapply Hfrag; [ apply Hhd | now repeat constructor ] | ]);
  try (apply IHpi1; constructor; [ eapply Hfrag; [ apply Hhd | now repeat constructor ] | ]);
  try (apply IHpi2; constructor; [ eapply Hfrag; [ apply Hhd | now repeat constructor ] | ]);
  try apply IHpi; try apply IHpi1; try apply IHpi2;
  try Forall_inf_solve;
  try (Forall_inf_simpl_hyp; subst; Forall_inf_solve_rec;
       repeat constructor; try assumption;
       eapply Hfrag; [ eassumption | now repeat constructor ]).
- symmetry in p. exact (PEPermutation_Type_Forall_inf _ _ p Htl).
- refine (Permutation_Type_Forall_inf _ Htl).
  symmetry in p. apply Permutation_Type_app_head, Permutation_Type_app_tail, Permutation_Type_map, p.
- Forall_inf_simpl_hyp. subst. Forall_inf_solve_rec.
  constructor; [ | constructor; [ | assumption ] ].
  + eapply Hfrag; [ eassumption | now repeat constructor ].
  + eapply Hfrag; [ eassumption | now repeat constructor ].
- rewrite P_cutfree in f. discriminate f.
- rewrite P_cutfree in f. discriminate f.
Qed.

(** Sub-formula property *)
Lemma isubformula_cutfree P (P_cutfree : no_icut P) l A (pi : ill P l A) :
  Forall_iformula (fun x => Exists (isubform x) (A :: l)) pi.
Proof.
apply (iconservativity P_cutfree).
- intros C Hf B Hs.
  eapply Exists_impl, Hf.
  intros D HCD. transitivity C; assumption.
- remember (A :: l) as l0. clear. induction l0 as [|A l IHl]; repeat constructor.
  eapply Forall_inf_arrow, IHl.
  intros B Hl. right. exact Hl.
Qed.

Lemma iconservativity_axfree P (P_axfree : no_iax P) FS (Hfrag : ifragment FS) l A (pi : ill P l A) :
  Forall_inf FS (A :: l) -> { pi' : ill P l A & Forall_iformula FS pi' }.
Proof.
intro HFS.
apply cut_admissible_ill_axfree in pi; [ | assumption ].
exists (stronger_ipfrag (cutrm_ipfrag_le P) pi).
apply Forall_isequent_stronger_ipfrag, iconservativity; [ | assumption .. ].
apply noicut_cutrm.
Qed.

Lemma cut_admissible_ifragment_axfree P (P_axfree : no_iax P) FS (Hfrag : ifragment FS) l A (pi : ill P l A) :
  Forall_iformula FS pi -> { pi' : ill (cutrm_ipfrag P) l A & Forall_iformula FS pi'}.
Proof.
intro HFS.
apply iconservativity_axfree; [ assumption .. | | ].
- apply cut_admissible_ill_axfree; assumption.
- exact (Forall_isequent_is _ _ HFS).
Qed.

Lemma isubformula P (P_axfree : no_iax P) l A (pi : ill P l A) :
  { pi': ill P l A & Forall_iformula (fun x => Exists (isubform x) (A :: l)) pi' }.
Proof.
refine (iconservativity_axfree P_axfree _ pi _).
- intros C Hf B Hs.
  eapply Exists_impl, Hf.
  intros D HCD. transitivity C; assumption.
- remember (A :: l) as l0. clear. induction l0 as [|A l IHl]; repeat constructor.
  eapply Forall_inf_arrow, IHl.
  intros B Hl. right. exact Hl.
Qed.

End Atoms.
