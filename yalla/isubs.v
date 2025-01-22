(** * Substitutions in Intuitionistic Linear Logic formulas and proofs *)

From OLlibs Require Import infinite List_more Permutation_Type GPermutation_Type.
From Yalla Require Export ill_def.

Set Implicit Arguments.


Section Atoms.

Context {preiatom : InfDecType}.
Notation atN := (@atN preiatom).

(** ** Substitutions *)

(** basic operation for substitution of atoms *)
Definition repl_iat x y A := if (@eq_dt_dec (option_dectype preiatom) x y) then A else ivar x.

Lemma repl_iat_eq x A : repl_iat x x A = A.
Proof. unfold repl_iat. rewrite if_eq_dt_dec_refl. reflexivity. Qed.

Lemma repl_iat_neq x y A : x <> y -> repl_iat x y A = ivar x.
Proof. intro Hneq. unfold repl_iat. rewrite (if_eq_dt_dec_neq _ Hneq). reflexivity. Qed.

(** Substitution in [iformula]: substitutes [x] by [C] in [A] *)
Fixpoint isubs C x A :=
match A with
| ivar y    => repl_iat y x C
| ione      => ione
| itens A B => itens (isubs C x A) (isubs C x B)
| ilpam A B => ilpam (isubs C x A) (isubs C x B)
| igen A    => igen (isubs C x A)
| ilmap A B => ilmap (isubs C x A) (isubs C x B)
| ineg A    => ineg (isubs C x A)
| izero     => izero
| itop      => itop
| iplus A B => iplus (isubs C x A) (isubs C x B)
| iwith A B => iwith (isubs C x A) (isubs C x B)
| ioc A     => ioc (isubs C x A)
end.

Lemma isubs_ioc A x l : map (isubs A x) (map ioc l) = map ioc (map (isubs A x) l).
Proof. induction l as [|a l IHl]; [ | cbn; rewrite IHl ]; reflexivity. Qed.

(** Substitution in proofs *)
Lemma subs_ill P A x l C (HN : atN <> x) (Hcut : forall D, Bool.le (ipcut P D) (ipcut P (isubs A x D))) :
  ill P l C ->
  ill (axmodif_ipfrag P (fun '(l, D) => (map (isubs A x) l, isubs A x D))) (map (isubs A x) l) (isubs A x C).
Proof.
intro pi. induction pi; cbn; rewrite ? map_app;
  try (cbn in IHpi; rewrite ? map_app in IHpi);
  try (cbn in IHpi1; rewrite ? map_app in IHpi1);
  try (cbn in IHpi2; rewrite ? map_app in IHpi2);
  try (constructor; assumption).
- apply ax_exp_ill.
- eapply PEPermutation_Type_map in p.
  eapply ex_ir; eassumption.
- rewrite isubs_ioc in *.
  eapply Permutation_Type_map in p.
  eapply ex_oc_ir; eassumption.
- list_simpl. apply lpam_ilr; assumption.
- unfold repl_iat in IHpi. rewrite if_eq_dt_dec_neq in IHpi by exact HN. apply gen_irr, IHpi.
- unfold repl_iat. rewrite if_eq_dt_dec_neq by exact HN. apply gen_ilr, IHpi.
- unfold repl_iat in IHpi. rewrite if_eq_dt_dec_neq in IHpi by exact HN. apply neg_irr, IHpi.
- unfold repl_iat. rewrite if_eq_dt_dec_neq by exact HN. apply neg_ilr, IHpi.
- rewrite isubs_ioc in *. apply oc_irr. assumption.
- refine (cut_ir (isubs A x A0) _ IHpi1 IHpi2).
  eapply Bool.implb_true_iff, f. apply Bool.le_implb, Hcut.
- assert ({ b | isubs A x (snd (projT2 (ipgax P) a))
              = snd (projT2 (ipgax (axmodif_ipfrag P (fun '(l, D) => (map (isubs A x) l, isubs A x D)))) b)
              & (map (isubs A x) (fst (projT2 (ipgax P) a)))
              = fst (projT2 (ipgax (axmodif_ipfrag P (fun '(l, D) => (map (isubs A x) l, isubs A x D)))) b) })
      as [b -> ->]
      by (exists a; cbn; destruct (projT2 (ipgax P) a); reflexivity).
  apply gax_ir.
Qed.

Lemma subs_ill_axfree P (P_axfree : no_iax P) A x
  (Hcut : forall D, Bool.le (ipcut P D) (ipcut P (isubs A x D))) l C (HN : atN <> x) :
  ill P l C -> ill P (map (isubs A x) l) (isubs A x C).
Proof.
intros pi%(subs_ill A HN); [ | assumption ].
eapply stronger_ipfrag; [ | eassumption ].
repeat split; [ reflexivity | | reflexivity ].
intro. contradiction P_axfree.
Qed.

(** Substitution of axioms *)
Lemma subs_ill_axioms P (gax : { _ &  _ }) l C
  (Hgax : forall a, ill P (fst (projT2 gax a)) (snd (projT2 gax a))) :
  ill (axupd_ipfrag P gax) l C -> @ill preiatom P l C.
Proof. intro pi. induction pi; try (econstructor; eassumption). apply Hgax. Qed.

End Atoms.


(** ** Fresh atoms and associated properties *)

Section InfAtoms.

Context {preiatom : InfDecType}.

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
apply (@fresh_spec (option_infdectype preiatom) lat), (Hincl (@fresh (option_infdectype preiatom) lat)), in_eq.
Qed.

Lemma subs_ifresh C A : isubs C (ifresh_of A) A = A.
Proof. apply subs_ifresh_incl. intro. exact id. Qed.

(** Provide an [Atom] which is fresh for all elements of [l] *)
Definition ifresh_of_list l := @fresh (option_infdectype preiatom) (flat_map iatom_list l).

Lemma subs_ifresh_list_incl C lat l :
  incl (flat_map iatom_list l) lat -> map (isubs C (@fresh (option_infdectype preiatom) lat)) l = l.
Proof.
induction l as [|a l IHl]; [ reflexivity | cbn; intros Hincl%incl_app_inv ].
change (proj1_sig (nat_injective_choice (option_dectype preiatom)
                  (nat_injective_option infinite_nat_injective)) lat)
  with (@fresh (option_infdectype preiatom) lat).
now rewrite subs_ifresh_incl, IHl.
Qed.

Lemma subs_ifresh_list C l : map (isubs C (ifresh_of_list l)) l = l.
Proof. apply subs_ifresh_list_incl. intro. exact id. Qed.

End InfAtoms.
