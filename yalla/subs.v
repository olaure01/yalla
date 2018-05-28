(* subs library for yalla *)
(* Coq 8.6 *)
(* v 1.0   Olivier Laurent *)


(** * Substitutions in Linear Logic formulas and proofs *)

Require Import List.
Require Import Permutation.
Require Import genperm.

Require Export ll.


(** ** Decidable equality on [Atom], through value into [bool] *)
Parameter ateq : Atom -> Atom -> bool.
Axiom ateq_eq : forall x y, ateq x y = true <-> x = y.


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
| var y      => repl_at y x C
| covar y    => dual (repl_at y x C)
| one        => one
| bot        => bot
| tens A B   => tens (subs C x A) (subs C x B)
| parr A B   => parr (subs C x A) (subs C x B)
| zero       => zero
| top        => top
| aplus A B  => aplus (subs C x A) (subs C x B)
| awith A B  => awith (subs C x A) (subs C x B)
| oc A       => oc (subs C x A)
| wn A       => wn (subs C x A)
end.

Lemma subs_dual : forall A C x, subs C x (dual A) = dual (subs C x A).
Proof with myeasy.
intros A C x.
induction A ; simpl ; rewrite ?bidual ; simpl ;
  try (rewrite IHA ; myeasy ; fail) ;
  try (rewrite IHA1 ; rewrite IHA2 ; myeasy ; fail)...
Qed.

(** Substitution in proofs *)
Lemma subs_ll {P} : forall A x l s,
  ll P l s -> exists s',
    ll (axupd_pfrag P (fun l => exists l', pgax P l' /\ l = map (subs A x) l'))
       (map (subs A x) l) s'.
Proof with myeeasy.
intros A x l s pi.
assert
  (forall l, map (subs A x) (map wn l)
           = map wn (map (subs A x) l))
  as Hmapwn.
{ clear.
  induction l...
  simpl ; rewrite IHl... }
induction pi ; simpl ;
  try (destruct IHpi as [s' IHpi]) ;
  try (destruct IHpi1 as [s1' IHpi1]) ;
  try (destruct IHpi2 as [s2' IHpi2]).
- rewrite <- (bidual (repl_at _ _ _)).
  rewrite bidual.
  apply ax_exp.
- eexists.
  simpl in H.
  eapply PCperm_map in H.
  eapply ex_r...
- eexists.
  assert (pmix0 (axupd_pfrag P
     (fun l => exists l', pgax P l' /\ l = map (subs A x) l')) = true)
    as f' by (simpl ; myeasy).
  apply (@mix0_r _ f')...
- eexists.
  rewrite map_app.
  assert (pmix2 (axupd_pfrag P
     (fun l => exists l', pgax P l' /\ l = map (subs A x) l')) = true)
    as f' by (simpl ; myeasy).
  apply (@mix2_r _ f')...
- eexists.
  apply one_r.
- eexists.
  apply bot_r...
- eexists.
  rewrite map_app.
  apply tens_r...
- eexists.
  apply parr_r...
- eexists.
  apply top_r.
- eexists.
  apply plus_r1...
- eexists.
  apply plus_r2...
- eexists.
  apply with_r...
- eexists.
  specialize Hmapwn with l.
  rewrite Hmapwn.
  apply oc_r...
  rewrite <- Hmapwn...
- eexists.
  apply de_r...
- eexists.
  apply wk_r...
- eexists.
  rewrite map_app.
  specialize Hmapwn with lw.
  simpl in IHpi.
  rewrite map_app in IHpi.
  rewrite Hmapwn.
  apply co_r...
  rewrite <- Hmapwn...
- eexists.
  rewrite map_app.
  assert (pcut (axupd_pfrag P
     (fun l => exists l', pgax P l' /\ l = map (subs A x) l')) = true)
    as f' by (simpl ; myeasy).
  eapply (@cut_r _ f' (subs A x A0))...
  rewrite <- subs_dual...
- eexists.
  apply gax_r.
  eexists ; split...
Qed.

Lemma subs_ll_axfree {P} : (forall l, ~ pgax P l) -> forall A x l s,
  ll P l s -> exists s', ll P (map (subs A x) l) s'.
Proof with myeeasy.
intros P_axfree A x l s pi.
apply (subs_ll A x) in pi.
clear s ; destruct pi as [s pi].
eexists.
eapply stronger_pfrag...
nsplit 5...
intros f (l' & Hax & _).
apply P_axfree in Hax...
Qed.

(** Substitution of axioms *)
Lemma subs_ll_axioms {P} : forall (gax : _ -> Prop) l s,
  (forall l, gax l -> exists s0, ll P l s0) ->
  ll (axupd_pfrag P gax) l s -> exists s', ll P l s'.
Proof with myeeasy.
intros gax l s Hgax pi.
induction pi ;
  try destruct IHpi as [s' IHpi] ;
  try destruct IHpi1 as [s1' IHpi1] ;
  try destruct IHpi2 as [s2' IHpi2] ;
  try (now (eexists ; constructor ; myeeasy)).
- eexists.
  simpl in H.
  eapply ex_r ; [ apply IHpi | ]...
- eexists.
  simpl in f.
  eapply (@cut_r _ f)...
- apply Hgax...
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
- simpl in Hle.
  rewrite repl_at_neq...
  intro Heq.
  apply a2n_is_n2a in Heq ; subst.
  inversion Hle...
- simpl in Hle.
  rewrite repl_at_neq...
  intro Heq.
  apply a2n_is_n2a in Heq ; subst.
  inversion Hle...
Qed.

Lemma subs_fresh : forall C A, subs C (fresh_of A) A = A.
Proof.
intros.
apply subs_fresh_le.
myeasy.
Qed.

Definition nat_fresh_of_list l := fold_right (fun x y => nat_fresh_of x + y) 0 l.

(** Provide an [Atom] which is fresh for all elements of [l] *)
Definition fresh_of_list l := n2a (nat_fresh_of_list l).

Lemma subs_fresh_list_le : forall C l n,
  nat_fresh_of_list l <= n -> map (subs C (n2a n)) l = l.
Proof with myeasy.
intros C l n Hle.
induction l...
simpl in Hle ; simpl.
rewrite subs_fresh_le ; [ rewrite IHl | ]...
Qed.

Lemma subs_fresh_list : forall C l, map (subs C (fresh_of_list l)) l = l.
Proof.
intros.
apply subs_fresh_list_le.
myeasy.
Qed.

End Fresh.


