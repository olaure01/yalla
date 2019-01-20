(* isubs library for yalla *)

(* output in Type *)


(** * Substitutions in Intuitionistic Linear Logic formulas and proofs *)

Require Import List_more.
Require Import Permutation_Type.
Require Import genperm_Type.

Require Export ill_def.


(** ** Decidable equality on [IAtom], through value into [bool] *)
Definition iateq := yalla_ax.iateq.
Definition iateq_eq := yalla_ax.iateq_eq.


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
- eapply PEperm_Type_map in p.
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
  ill (axupd_ipfrag P gax) l C -> ill P l C.
Proof with myeeasy.
intros gax l C Hgax pi.
induction pi ; try now constructor.
- simpl in p.
  eapply ex_ir ; [ apply IHpi | ]...
- eapply ex_oc_ir...
- simpl in f.
  eapply (@cut_ir _ f)...
- apply Hgax...
Qed.


(** ** Fresh variables and associated properties *)
Section Fresh.

(** Embedding of [nat] into [Atom] *)
Variable i2n : IAtom -> nat.
Variable n2i : nat -> IAtom.
Hypothesis n2n : forall n, i2n (n2i n) = n.

Lemma i2n_is_n2i : forall a n, a = n2i n -> n = i2n a.
Proof.
intros a n Ha.
rewrite Ha.
rewrite n2n.
reflexivity.
Qed.

(** [nat] bigger than all [nat] associated with [IAtom] in [A] *)
Fixpoint inat_fresh_of A :=
match A with
| ivar x    => S (i2n x)
| ione      => 0
| itens B C => inat_fresh_of B + inat_fresh_of C
| ilpam B C => inat_fresh_of B + inat_fresh_of C
| igen B => inat_fresh_of B + S (i2n atN)
| ilmap B C => inat_fresh_of B + inat_fresh_of C
| ineg B => inat_fresh_of B + S (i2n atN)
| izero     => 0
| itop      => 0
| iplus B C => inat_fresh_of B + inat_fresh_of C
| iwith B C => inat_fresh_of B + inat_fresh_of C
| ioc B     => inat_fresh_of B
end.

(** Provide an [IAtom] which is fresh for [A] *)
Definition ifresh_of A := n2i (inat_fresh_of A).

Lemma subs_ifresh_le : forall C A n, inat_fresh_of A <= n -> isubs C (n2i n) A = A.
Proof with myeasy.
intros C A n Hle.
induction A ; simpl in Hle ; simpl ;
  try rewrite IHA ;
  try (rewrite IHA2 ; [ rewrite IHA1 | ]) ;
  simpl...
rewrite repl_iat_neq...
intro Heq.
apply i2n_is_n2i in Heq ; subst.
inversion Hle...
Qed.

Lemma subs_ifresh : forall C A, isubs C (ifresh_of A) A = A.
Proof.
intros.
apply subs_ifresh_le.
reflexivity.
Qed.

Definition inat_fresh_of_list l := list_max (map inat_fresh_of l).

(** Provide an [IAtom] which is fresh for all elements of [l] *)
Definition ifresh_of_list l := n2i (inat_fresh_of_list l).

Lemma subs_ifresh_list_le : forall C l n,
  inat_fresh_of_list l <= n -> map (isubs C (n2i n)) l = l.
Proof with myeasy.
unfold inat_fresh_of_list.
intros C l n Hle.
induction l...
simpl in Hle ; simpl.
rewrite subs_ifresh_le ; [ rewrite IHl | ]...
Qed.

Lemma subs_ifresh_list : forall C l, map (isubs C (ifresh_of_list l)) l = l.
Proof.
intros.
apply subs_ifresh_list_le.
reflexivity.
Qed.

End Fresh.


