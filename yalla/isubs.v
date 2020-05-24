(* isubs library for yalla *)


(** * Substitutions in Intuitionistic Linear Logic formulas and proofs *)

From OLlibs Require Import infinite List_more Permutation_Type GPermutation_Type.
From Yalla Require Export ill_def.


Section Atoms.

Context { preiatom : InfDecType }.

Notation atN := (@atN preiatom).
Definition iateq := @eqb (option_dectype preiatom).
Definition iateq_eq := @eqb_eq (option_dectype preiatom).

(** ** Substitutions *)

(** basic operation for substitution of atoms *)
Definition repl_iat x y A := if iateq x y then A else ivar x.

Lemma repl_iat_eq : forall x y A, x = y -> repl_iat x y A = A.
Proof.
intros ; subst.
unfold repl_iat.
rewrite (proj2 (iateq_eq _ _) (eq_refl _)).
reflexivity.
Qed.

Lemma repl_iat_neq : forall x y A, x <> y -> repl_iat x y A = ivar x.
Proof.
intros x y A Hneq.
unfold repl_iat.
case_eq (iateq x y) ; intros Heqb ; try reflexivity.
exfalso.
rewrite iateq_eq in Heqb.
apply Hneq ; assumption.
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
Lemma subs_ill {P} : forall A x l C, iateq atN x = false ->
  ill P l C ->
    ill (axupd_ipfrag P (existT (fun x => x -> list iformula * iformula) _
            (fun a => (map (isubs A x) (fst (projT2 (ipgax P) a)),
                       isubs A x (snd (projT2 (ipgax P) a))))))
        (map (isubs A x) l) (isubs A x C).
Proof with myeeasy.
intros A x l C HN pi.
assert
  (forall l, map (isubs A x) (map ioc l)
           = map ioc (map (isubs A x) l))
  as Hmapioc.
{ clear.
  induction l...
  simpl ; rewrite IHl... }
induction pi ; list_simpl ;
  try (list_simpl in IHpi) ;
  try (list_simpl in IHpi1) ;
  try (list_simpl in IHpi2) ;
  try now (constructor ; myeeasy).
- apply ax_exp_ill.
- eapply PEPermutation_Type_map in p.
  eapply ex_ir...
- rewrite ? map_app in IHpi ; rewrite Hmapioc in IHpi ; rewrite Hmapioc.
  eapply Permutation_Type_map in p.
  eapply ex_oc_ir...
- unfold repl_iat in IHpi.
  rewrite HN in IHpi.
  constructor...
- unfold repl_iat.
  rewrite HN.
  constructor...
- unfold repl_iat in IHpi.
  rewrite HN in IHpi.
  constructor...
- unfold repl_iat.
  rewrite HN.
  constructor...
- specialize Hmapioc with l.
  rewrite Hmapioc.
  apply oc_irr.
  rewrite <- Hmapioc...
- eapply (cut_ir _ (isubs A x A0))...
- apply (gax_ir ((axupd_ipfrag P (existT (fun x => x -> list iformula * iformula) _
            (fun a => (map (isubs A x) (fst (projT2 (ipgax P) a)),
                       isubs A x (snd (projT2 (ipgax P) a))))))) a).
Unshelve. simpl...
Qed.

Lemma subs_ill_axfree {P} : (projT1 (ipgax P) -> False) -> forall A x l C,
iateq atN x = false -> ill P l C ->
  ill P (map (isubs A x) l) (isubs A x C).
Proof with myeeasy.
intros P_axfree A x l C HN pi.
apply (subs_ill A x) in pi...
eapply stronger_ipfrag...
nsplit 3...
intuition.
Qed.

(** Substitution of axioms *)
Lemma subs_ill_axioms {P} :
 forall (gax : { iptypgax : Type & iptypgax -> list iformula * iformula }) l C,
  (forall a, ill P (fst (projT2 gax a)) (snd (projT2 gax a))) ->
  ill (axupd_ipfrag P gax) l C -> @ill preiatom P l C.
Proof with myeeasy.
intros gax l C Hgax pi.
induction pi ; try now constructor.
- simpl in p.
  eapply ex_ir ; [ apply IHpi | ]...
- eapply ex_oc_ir...
- simpl in f.
  eapply (@cut_ir _ _ f)...
- apply Hgax...
Qed.


(** ** Fresh atoms and associated properties *)

Fixpoint iatom_list A : list iatom :=
match A with
| ivar x    => x :: nil
| ione      => nil
| itens B C => iatom_list B ++ iatom_list C
| ilpam B C => iatom_list B ++ iatom_list C
| igen B => atN :: iatom_list B
| ilmap B C => iatom_list B ++ iatom_list C
| ineg B => atN :: iatom_list B
| izero     => nil
| itop      => nil
| iplus B C => iatom_list B ++ iatom_list C
| iwith B C => iatom_list B ++ iatom_list C
| ioc B     => iatom_list B
end.

(** Provide an [Atom] which is fresh for [A] *)
Definition ifresh_of A := @fresh (option_infdectype preiatom) (iatom_list A).

Lemma subs_ifresh_incl : forall C lat A,
  incl (iatom_list A) lat -> isubs C (@fresh (option_infdectype preiatom) lat) A = A.
Proof.
intros C lat A; induction A; simpl; intros Hincl;
  change (proj1_sig (nat_injective_choice (option_dectype preiatom)
            (nat_injective_option infinite_nat_injective)) lat)
  with (@fresh (option_infdectype preiatom) lat);
  try rewrite IHA;
  try (rewrite IHA2 ; [ rewrite IHA1 | ]);
  simpl; intuition;
  (try now apply incl_app_inv in Hincl);
  try now apply incl_cons_inv in Hincl.
rewrite repl_iat_neq; auto.
intros ->.
apply (@fresh_prop (option_infdectype preiatom) lat),
      (Hincl (@fresh (option_infdectype preiatom) lat)); intuition.
Qed.

Lemma subs_ifresh : forall C A, isubs C (ifresh_of A) A = A.
Proof. now intros; apply subs_ifresh_incl. Qed.

(** Provide an [Atom] which is fresh for all elements of [l] *)
Definition ifresh_of_list l := @fresh (option_infdectype preiatom) (flat_map iatom_list l).

Lemma subs_ifresh_list_incl : forall C lat l,
  incl (flat_map iatom_list l) lat -> map (isubs C (@fresh (option_infdectype preiatom) lat)) l = l.
Proof.
intros C lat l; induction l; simpl; intros Hincl; auto.
apply incl_app_inv in Hincl.
change (proj1_sig (nat_injective_choice (option_dectype preiatom)
            (nat_injective_option infinite_nat_injective)) lat)
  with (@fresh (option_infdectype preiatom) lat).
rewrite subs_ifresh_incl; [ rewrite IHl | ]; intuition.
Qed.

Lemma subs_ifresh_list : forall C l, map (isubs C (ifresh_of_list l)) l = l.
Proof. now intros; apply subs_ifresh_list_incl. Qed.

End Atoms.
