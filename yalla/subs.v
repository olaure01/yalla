(* subs library for yalla *)


(** * Substitutions in Linear Logic formulas and proofs *)

From OLlibs Require Import List_more Permutation_Type GPermutation_Type
                           Dependent_Forall_Type.
Require Export ll_def.

(** ** Decidable equality on [Atom], through value into [bool] *)
Definition ateq := yalla_ax.ateq.
Definition ateq_eq := yalla_ax.ateq_eq.


(** ** Substitutions *)

(** basic operation for substitution of atoms *)
Definition repl_at x y A := if ateq x y then A else var x.

Lemma repl_at_eq : forall x y A, x = y -> repl_at x y A = A.
Proof.
intros ; subst.
unfold repl_at.
rewrite (proj2 (ateq_eq _ _) (eq_refl _)).
reflexivity.
Qed.

Lemma repl_at_neq : forall x y A, x <> y -> repl_at x y A = var x.
Proof.
intros x y A Hneq.
unfold repl_at.
case_eq (ateq x y) ; intros Heqb ; try reflexivity.
exfalso.
rewrite ateq_eq in Heqb.
apply Hneq ; assumption.
Qed.

(** Substitution in [formula]: substitutes [x] by [C] in [A] *)
Fixpoint subs C x A :=
match A with
| var y     => repl_at y x C
| covar y   => dual (repl_at y x C)
| one       => one
| bot       => bot
| tens A B  => tens (subs C x A) (subs C x B)
| parr A B  => parr (subs C x A) (subs C x B)
| zero      => zero
| top       => top
| aplus A B => aplus (subs C x A) (subs C x B)
| awith A B => awith (subs C x A) (subs C x B)
| oc A      => oc (subs C x A)
| wn A      => wn (subs C x A)
end.

Lemma subs_dual : forall A C x, subs C x (dual A) = dual (subs C x A).
Proof with myeasy.
intros A C x.
induction A ; simpl ; rewrite ?bidual ; simpl ;
  try (rewrite IHA ; myeasy ; fail) ;
  try (rewrite IHA1 ; rewrite IHA2 ; myeasy ; fail)...
Qed.

(** Substitution in proofs *)

Lemma subs_ll {P} : forall A x l,
  ll P l ->
    ll (axupd_pfrag P (existT (fun x => x -> list formula) _
                            (fun a => map (subs A x) (projT2 (pgax P) a))))
       (map (subs A x) l).
Proof with myeeasy.
intros A x l pi.
assert
  (forall l, map (subs A x) (map wn l)
           = map wn (map (subs A x) l))
  as Hmapwn.
{ clear.
  induction l...
  simpl ; rewrite IHl... }
induction pi using ll_nested_ind ; list_simpl ; try (now constructor).
- eapply ex_r ; [ apply ax_exp | apply PCPermutation_Type_swap ].
- eapply PCPermutation_Type_map in p.
  eapply ex_r...
- rewrite ? map_app in IHpi ; rewrite Hmapwn in IHpi ; rewrite Hmapwn.
  eapply Permutation_Type_map in p.
  eapply ex_wn_r...
- rewrite concat_map.
  apply mix_r.
  + simpl.
    rewrite map_length...
  + apply forall_Forall_inf.
    intros l' Hin.
    destruct (in_inf_map_inv (map (subs A x)) L l' Hin) as [l0 <- Hin'].
    apply (In_Forall_inf_in _ PL) in Hin' as [pi' Hin'].
    refine (Dependent_Forall_inf_forall_formula _ _ X Hin').
- specialize Hmapwn with l0.
  rewrite Hmapwn.
  apply oc_r.
  rewrite <- Hmapwn...
- eapply (cut_r _ (subs A x A0))...
  rewrite <- subs_dual...
- apply (gax_r (axupd_pfrag P (existT (fun x => x -> list formula) _
                      (fun a => map (subs A x) (projT2 (pgax P) a)))) a).
Unshelve. simpl...
Qed.

Lemma subs_ll_axfree {P} : (projT1 (pgax P) -> False) -> forall A x l,
  ll P l -> ll P (map (subs A x) l).
Proof with myeeasy.
intros P_axfree A x l pi.
apply (subs_ll A x) in pi.
eapply stronger_pfrag...
nsplit 4...
simpl ; intros a.
contradiction P_axfree.
Qed.


(** ** Fresh variables and associated properties *)
Section Fresh.

(** Embedding of [nat] into [Atom] *)
Variable a2n : Atom -> nat.
Variable n2a : nat -> Atom.
Hypothesis n2n : forall n, a2n (n2a n) = n.

Lemma a2n_is_n2a : forall a n, a = n2a n -> n = a2n a.
Proof.
intros a n Ha.
rewrite Ha.
rewrite n2n.
reflexivity.
Qed.

(** [nat] bigger than all [nat] associated with [Atom] in [A] *)
Fixpoint nat_fresh_of A :=
match A with
| var x     => S (a2n x)
| covar x   => S (a2n x)
| one       => 0
| bot       => 0
| tens B C  => nat_fresh_of B + nat_fresh_of C
| parr B C  => nat_fresh_of B + nat_fresh_of C
| zero      => 0
| top       => 0
| aplus B C => nat_fresh_of B + nat_fresh_of C
| awith B C => nat_fresh_of B + nat_fresh_of C
| oc B      => nat_fresh_of B
| wn B      => nat_fresh_of B
end.

(** Provide an [Atom] which is fresh for [A] *)
Definition fresh_of A := n2a (nat_fresh_of A).

Lemma subs_fresh_le : forall C A n, nat_fresh_of A <= n -> subs C (n2a n) A = A.
Proof with myeasy.
intros C A n Hle.
induction A ; simpl in Hle ; simpl ;
  try rewrite IHA ;
  try (rewrite IHA2 ; [ rewrite IHA1 | ]) ;
  simpl...
- rewrite repl_at_neq...
  intro Heq.
  apply a2n_is_n2a in Heq ; subst.
  inversion Hle...
- rewrite repl_at_neq...
  intro Heq.
  apply a2n_is_n2a in Heq ; subst.
  inversion Hle...
Qed.

Lemma subs_fresh : forall C A, subs C (fresh_of A) A = A.
Proof.
intros.
apply subs_fresh_le.
reflexivity.
Qed.

Definition nat_fresh_of_list l := list_max (map nat_fresh_of l).

Lemma nat_fresh_of_list_fresh : forall l,
  Forall (fun x => nat_fresh_of x <= nat_fresh_of_list l) l.
Proof with myeasy.
unfold nat_fresh_of_list.
induction l ; constructor ; simpl...
remember (map nat_fresh_of l) as k.
revert IHl ; clear ; induction l ;
  intros IHl' ; inversion IHl' ; subst ; constructor...
intuition.
Qed.

(** Provide an [Atom] which is fresh for all elements of [l] *)
Definition fresh_of_list l := n2a (nat_fresh_of_list l).

Lemma subs_fresh_list_le : forall C l n,
  nat_fresh_of_list l <= n -> map (subs C (n2a n)) l = l.
Proof with myeasy.
unfold nat_fresh_of_list.
intros C l n Hle.
induction l...
simpl in Hle ; simpl.
rewrite subs_fresh_le ; [ rewrite IHl | ]...
Qed.

Lemma subs_fresh_list : forall C l, map (subs C (fresh_of_list l)) l = l.
Proof.
intros.
apply subs_fresh_list_le.
reflexivity.
Qed.

End Fresh.
