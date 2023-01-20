(** * Substitutions in Intuitionistic Linear Logic formulas and proofs *)

From OLlibs Require Import infinite List_more Permutation_Type GPermutation_Type.
From Yalla Require Export ill_def.

Set Implicit Arguments.


Section Atoms.

Context { preiatom : InfDecType }.

Notation atN := (@atN preiatom).
Definition iateq := @eqb (option_dectype preiatom).
Definition iateq_eq := @eqb_eq (option_dectype preiatom).

(** ** Substitutions *)

(** basic operation for substitution of atoms *)
Definition repl_iat x y A := if iateq x y then A else ivar x.

Lemma repl_iat_eq x y A : x = y -> repl_iat x y A = A.
Proof. intros ->. unfold repl_iat. rewrite (proj2 (iateq_eq _ _) (eq_refl _)). reflexivity. Qed.

Lemma repl_iat_neq x y A : x <> y -> repl_iat x y A = ivar x.
Proof.
intros Hneq. unfold repl_iat.
destruct (iateq x y) eqn:Heqb; [ | reflexivity ].
exfalso. rewrite iateq_eq in Heqb. contradiction Heqb.
Qed.

(** Substitution in [iformula]: substitutes [x] by [C] in [A] *)
Fixpoint isubs C x A :=
match A with
| ivar y    => repl_iat y x C
| ione      => ione
| itens A B => itens (isubs C x A) (isubs C x B)
| ilpam A B => ilpam (isubs C x A) (isubs C x B)
| igen A => igen (isubs C x A)
| ilmap A B => ilmap (isubs C x A) (isubs C x B)
| ineg A => ineg (isubs C x A)
| izero => izero
| itop => itop
| iplus A B => iplus (isubs C x A) (isubs C x B)
| iwith A B => iwith (isubs C x A) (isubs C x B)
| ioc A     => ioc (isubs C x A)
end.

(** Substitution in proofs *)
Lemma subs_ill P A x l C (HN : x <> atN) (Hcut : forall D, Bool.le (ipcut P D) (ipcut P (isubs A x D))) :
  ill P l C ->
  ill (axupd_ipfrag P (existT (fun x => x -> list iformula * iformula) _
                              (fun a => (map (isubs A x) (fst (projT2 (ipgax P) a)),
                                             isubs A x (snd (projT2 (ipgax P) a))))))
      (map (isubs A x) l) (isubs A x C).
Proof.
apply <- (@eqb_neq (option_dectype preiatom)) in HN. rewrite eqb_sym in HN. fold iateq in HN.
intros pi.
assert (forall l, map (isubs A x) (map ioc l) = map ioc (map (isubs A x) l)) as Hmapioc
  by (clear; induction l as [|a l IHl]; [ | cbn; rewrite IHl ]; reflexivity).
induction pi; cbn; rewrite ? map_app;
  try (cbn in IHpi; rewrite ? map_app in IHpi);
  try (cbn in IHpi1; rewrite ? map_app in IHpi1);
  try (cbn in IHpi2; rewrite ? map_app in IHpi2);
  try (constructor; assumption).
- apply ax_exp_ill.
- eapply PEPermutation_Type_map in p.
  eapply ex_ir; eassumption.
- rewrite ? map_app, Hmapioc in IHpi. rewrite Hmapioc.
  eapply Permutation_Type_map in p.
  eapply ex_oc_ir; eassumption.
- list_simpl. apply lpam_ilr; assumption.
- unfold repl_iat in IHpi. rewrite HN in IHpi. apply gen_irr. assumption.
- unfold repl_iat. rewrite HN. apply gen_ilr. assumption.
- unfold repl_iat in IHpi. rewrite HN in IHpi. apply neg_irr. assumption.
- unfold repl_iat. rewrite HN. apply neg_ilr. assumption.
- specialize Hmapioc with l.
  rewrite Hmapioc. apply oc_irr. rewrite <- Hmapioc. assumption.
- refine (cut_ir (isubs A x A0) _ IHpi1 IHpi2).
  specialize (Hcut A0).
  eapply Bool.implb_true_iff, f. apply Bool.le_implb, Hcut.
- refine (gax_ir _).
Qed.

Lemma subs_ill_axfree P (P_axfree : notT (projT1 (ipgax P))) A x
  (Hcut : forall D, Bool.le (ipcut P D) (ipcut P (isubs A x D))) l C (HN : x <> atN) :
  ill P l C -> ill P (map (isubs A x) l) (isubs A x C).
Proof.
intros pi.
apply (subs_ill A HN) in pi; [ | assumption ].
eapply stronger_ipfrag; [ | eassumption ].
repeat split; [ reflexivity | | reflexivity ].
intro. contradiction P_axfree.
Qed.

(** Substitution of axioms *)
Lemma subs_ill_axioms P (gax : { _ &  _ }) l C
  (Hgax : forall a, ill P (fst (projT2 gax a)) (snd (projT2 gax a))) :
  ill (axupd_ipfrag P gax) l C -> @ill preiatom P l C.
Proof. intros pi. induction pi; try (econstructor; eassumption). apply Hgax. Qed.


(** ** Fresh atoms and associated properties *)

(** Provide an [Atom] which is fresh for [A] *)
Definition ifresh_of A := @fresh (option_infdectype preiatom) (iatom_list A).

Lemma subs_ifresh_incl C lat A :
  incl (iatom_list A) lat -> isubs C (@fresh (option_infdectype preiatom) lat) A = A.
Proof.
induction A; cbn; intros Hincl;
  change (proj1_sig (nat_injective_choice (option_dectype preiatom)
            (nat_injective_option infinite_nat_injective)) lat)
    with (@fresh (option_infdectype preiatom) lat);
  rewrite ? IHA, ? IHA1, ? IHA2; cbn; trivial;
  try (now apply incl_app_inv in Hincl); try now apply incl_cons_inv in Hincl.
rewrite repl_iat_neq; [ reflexivity | ].
intros ->.
apply (@fresh_prop (option_infdectype preiatom) lat), (Hincl (@fresh (option_infdectype preiatom) lat)).
left. reflexivity.
Qed.

Lemma subs_ifresh C A : isubs C (ifresh_of A) A = A.
Proof. apply subs_ifresh_incl. intro. exact id. Qed.

(** Provide an [Atom] which is fresh for all elements of [l] *)
Definition ifresh_of_list l := @fresh (option_infdectype preiatom) (flat_map iatom_list l).

Lemma subs_ifresh_list_incl C lat l :
  incl (flat_map iatom_list l) lat -> map (isubs C (@fresh (option_infdectype preiatom) lat)) l = l.
Proof.
induction l; cbn; intros Hincl; auto.
apply incl_app_inv in Hincl.
change (proj1_sig (nat_injective_choice (option_dectype preiatom)
                  (nat_injective_option infinite_nat_injective)) lat)
  with (@fresh (option_infdectype preiatom) lat).
now rewrite subs_ifresh_incl; [ rewrite IHl | ].
Qed.

Lemma subs_ifresh_list C l : map (isubs C (ifresh_of_list l)) l = l.
Proof. apply subs_ifresh_list_incl. intro. exact id. Qed.

End Atoms.
