(* Infinite Types *)

Require Import Bool Lia.
Require Import List_more List_Type funtheory dectype.

Set Implicit Arguments.


(* a pigeonhole principle *)
Definition pigeon X := forall (l1 l2 : list X),
  NoDup l1 -> length l2 < length l1 -> { x | In x l1 & ~ In x l2 }.


(* The following results are proved in the case of a DecType:
     bijection with nat => section with nat => non-surjective self injection => injection from nat
     injection from nat <=> choice out of finite subsets
*)


(* we start with results true for an arbitrary Type:
     bijection with nat => section with nat => choice out of finite subsets => injection from nat
     bijection with nat => non-surjective self injection
*)
Section Infinite.

Variable X : Type.

(* bijection with nat *)
Definition nat_bijective := { f : nat -> X & bijective f }.
(* section with nat *)
Definition nat_section := {'(i,s) : (nat -> X) * (X -> nat) | retract s i }.
(* non-surjective self injection *)
Definition self_injective := { f : X -> X & injective f & { x | forall y, x <> f y } }.
(* injection from nat *)
Definition nat_injective := { f : nat -> X | injective f }.
(* choice out of finite subsets *)
Definition choice_out_finite := { f : list X -> X | forall l, ~ In (f l) l }.

Lemma nat_bijective_section : nat_bijective -> nat_section.
Proof.
intros [i Hbij].
destruct (bijective_inverse _ Hbij) as [s _ Hsec].
now exists (i, s).
Qed.

Lemma section_choice : nat_section -> choice_out_finite.
Proof.
intros [(i,s) Hsec].
remember (fix h l :=
  match l with
  | nil => i 0
  | x :: tl => i (S (max (s x) (s (h tl))))
  end) as c; exists c.
enough (forall l, Forall (fun x => s x < s (c l)) l) as Hlt.
{ intros l Hin; specialize Hlt with l.
  apply Forall_forall with (x:= c l) in Hlt; [ lia | assumption ]. }
induction l; simpl; intuition; constructor.
- rewrite Heqc, Hsec; lia.
- apply Forall_forall; intros b Hb; apply Forall_forall with (x:= b) in IHl; [ | assumption ].
  subst; rewrite Hsec; lia.
Qed.

Lemma choice_nat_injective : choice_out_finite -> nat_injective.
Proof.
intros [c Hc].
remember (fix h n := (* a non-empty list of iterated choices *)
  match n with
  | 0 => c nil :: nil
  | S k => c (h k) :: h k
  end) as ih.
exists (fun n => hd (c nil) (ih n)).
assert(forall n x, In (hd (c nil) (ih x)) (ih (n + x))) as HC.
{ induction n; simpl; intros x.
  - subst; destruct x; intuition.
  - subst; apply in_cons; intuition. }
enough (forall x y, x < y -> hd (c nil) (ih x) = hd (c nil) (ih y) -> x = y) as Hlt.
{ intros x y Heq.
  destruct (Compare_dec.lt_eq_lt_dec x y) as [C | C]; [ destruct C as [C | C] | ].
  - now apply Hlt; [ lia | ].
  - assumption.
  - symmetry; now apply Hlt; [ lia | ]. }
intros x y Hlt Heq; exfalso.
specialize HC with (y - S x) x.
replace (y - S x + x) with (pred y) in HC by lia.
rewrite Heq in HC.
replace y with (S (pred y)) in HC at 1 by lia.
now apply (Hc (ih (pred y))); subst.
Qed.

Lemma nat_bijective_self : nat_bijective -> self_injective.
Proof.
intros [i Hbij].
destruct (bijective_inverse _ Hbij) as [s Hsec1 Hsec2].
exists (fun x => i (S (s x))).
- apply compose_injective; [ apply compose_injective | ].
  + now apply section_injective with i.
  + intros x y; lia.
  + now apply section_injective with s.
- exists (i 0); intros x Heq.
  apply section_injective in Hsec2.
  apply Hsec2 in Heq; inversion Heq.
Qed.

End Infinite.


(* Implications requiring a DecType
     section with nat => non-surjective self injection => injection from nat
     injection from nat => choice out of finite subset
*)
Section InfiniteDec.

Context { X : DecType }.

Lemma section_self_injective : nat_section X -> self_injective X.
Proof.
intros [(i, s) Hs].
assert (Hinj := section_injective _ _ Hs).
assert (forall x z, x = i z -> x = i (s x)) as Hsi
  by (now intros x z Heq; rewrite Heq at 2; rewrite Hs); clear Hs.
exists (fun x => if eqb x (i (s x)) then i (S (s x)) else x).
- intros x y.
  repeat case_analysis; intros Heqh; intuition.
  + rewrite Heq, Heq0; f_equal.
    apply Hinj in Heqh.
    now inversion Heqh.
  + exfalso; apply Heq0.
    symmetry in Heqh.
    eapply Hsi; eassumption.
  + exfalso; apply Heq.
    eapply Hsi; eassumption.
- exists (i 0); intros x.
  case_analysis; intros Heqi.
  + apply Hinj in Heqi; inversion Heqi.
  + apply Heq.
    symmetry in Heqi.
    eapply Hsi; eassumption.
Qed.

Lemma pigeon_dectype : pigeon X.
Proof.
intros l1; induction l1; simpl; intros l2 Hnd Hl; [ exfalso; lia | ].
destruct (in_dec eq_dt_dec a l2).
- apply NoDup_NoDup_Type in Hnd.
  inversion_clear Hnd as [ | ? ? Hnin Hnd2 ].
  apply NoDup_Type_NoDup in Hnd2.
  apply notin_Type_notin in Hnin.
  apply IHl1 with (remove eq_dt_dec a l2) in Hnd2.
  + destruct Hnd2 as [b Hb Hnb].
    exists b.
    * now apply in_cons.
    * intros Hin; apply Hnb.
      apply in_in_remove; [ | assumption ].
      intros Heq; subst; intuition.
  + apply remove_length with (Hdec:= eq_dt_dec) in i; lia.
- exists a; intuition.
Qed.

Lemma injective_enum : forall (f : nat -> X), injective f ->
  forall l, { n | ~ In (f n) l }.
Proof.
intros f Hinj l.
destruct pigeon_dectype with (map f (seq 0 (S (length l)))) l as [x Hin Hnin].
- now apply injective_NoDup, seq_NoDup.
- rewrite map_length, seq_length; lia.
- remember (S (length l)) as k; clear Heqk.
  remember 0 as s; clear Heqs.
  revert s Hin Hnin; induction k; simpl; intros s Hin Hnin; [ easy | ].
  case (eq_dt_reflect (f s) x); intros Heq; subst.
  + now exists s.
  + apply IHk with (S s); [ | assumption ].
    now destruct Hin.
Qed.

Lemma nat_injective_choice : nat_injective X -> choice_out_finite X.
Proof.
intros [i Hi].
exists (fun l => i (proj1_sig (injective_enum Hi l))).
intros l Hin; destruct (injective_enum Hi l) ; intuition.
Qed.

Lemma self_injective_minus : forall (pi : self_injective X),
  self_injective (minus (proj1_sig (projT3 pi))).
Proof.
intros [f Hinj [i Hi]]; simpl.
assert (forall x, eqb i x = false -> eqb i (f x) = false) as Hif
  by (intros x _; now apply eqb_neq).
split with (fun a => exist _ (f (proj1_sig a)) (Hif (proj1_sig a) (proj2_sig a))).
- intros [x Hx] [y Hy] Heq.
  inversion Heq as [ Heq2 ].
  apply Hinj in Heq2; subst.
  now rewrite ((Eqdep_dec.UIP_dec bool_dec) _ _ Hx Hy).
- assert (eqb i (f i) = false) as Hj by now apply eqb_neq.
  split with (exist _ (f i) Hj).
  intros [y Hy]; simpl; intros Heq.
  inversion Heq as [Heq2].
  now apply Hinj, eqb_neq in Heq2.
Qed.

End InfiniteDec.

Definition nat_of_self (X : DecType) (pi : self_injective X) (n : nat) :
   { x : X | x = Nat.iter n (projT1 (sigT_of_sigT2 pi)) (proj1_sig (projT3 pi)) }
 * { Y : DecType & self_injective Y }.
Proof.
remember pi as HX; destruct pi as [f Hinj [i Hi]].
induction n.
- split.
  + exists i; simpl; now subst.
  + exists (minus (proj1_sig (projT3 HX))).
    apply (self_injective_minus HX).
- destruct IHn as [y Y]; split.
  + destruct y as [y Hy].
    exists (f y); simpl; now subst.
  + destruct Y as [Y HY].
    exists (minus (proj1_sig (projT3 HY))).
    apply (self_injective_minus HY).
Defined.

Lemma self_injective_nat (X : DecType) : self_injective X -> nat_injective X.
Proof.
intros HX.
exists (fun n => proj1_sig (fst (nat_of_self X HX n))).
intros x y Heq.
destruct (fst (nat_of_self X HX x)) as [n Hn]; subst.
destruct (fst (nat_of_self X HX y)) as [m Hm]; subst; simpl in Heq.
destruct HX as [f Hinj [i Hi]]; simpl in Heq.
revert x y Heq.
enough (forall x y, x < y -> Nat.iter x f i = Nat.iter y f i -> x = y) as Hlt.
{ intros x y Heq.
  destruct (Compare_dec.lt_eq_lt_dec x y) as [C | C]; [ destruct C as [C | C] | ].
  - now apply Hlt; [ lia | ].
  - assumption.
  - symmetry; now apply Hlt; [ lia | ]. }
intros x y Hlt Heq; exfalso.
remember (pred (y - x)) as n.
replace y with (S n + x) in Heq by lia; clear Heqn.
revert Heq; induction x; simpl; intros Heq.
- now apply Hi in Heq.
- replace (S n + x) with (n + S x) in IHx by lia.
  now apply IHx, Hinj; [ lia | ].
Qed.


(** * Infinite Decidable Types *)
(* (infinite) decidable types with freshness function *)

Record InfDecType := {
  infcar :> DecType;
  fresh : list infcar -> infcar;
  fresh_prop : forall l, ~ In (fresh l) l
}.
Arguments fresh {_}.
Arguments fresh_prop {_}.

(* [nat] instance of [InfDecType] *)
Definition nat_infdectype := {|
  infcar := nat_dectype;
  fresh := (proj1_sig (section_choice (nat_bijective_section (existT _ id (id_bijective)))));
  fresh_prop := (proj2_sig (section_choice (nat_bijective_section (existT _ id (id_bijective)))));
|}.
(* alternative direct construction *)
Definition nat_fresh l := S (fold_right max 0 l).
Lemma nat_fresh_prop : forall l, ~ In (nat_fresh l) l.
Proof.
enough (forall l n h, ~ In (n + nat_fresh (h ++ l)) l) as Hh
  by (intros l; rewrite <- (app_nil_l l) at 1; apply (Hh _ 0)).
induction l; unfold nat_fresh; simpl; intros n h Hin; auto.
destruct Hin as [Hin|Hin].
- enough (a < n + S (fold_right Init.Nat.max 0 (h ++ a :: l))) by lia.
  clear; induction h; simpl; lia.
- apply IHl with n (h ++ a :: nil).
  now rewrite <- app_assoc.
Qed.
(*
Definition nat_infdectype := {|
  infcar := nat_dectype;
  fresh := nat_fresh;
  fresh_prop := nat_fresh_prop
|}.
*)


Section InfDecTypes.

Context { X : InfDecType }.

Lemma infinite_nat_injective : nat_injective X.
Proof.
apply choice_nat_injective.
exists fresh.
apply fresh_prop.
Qed.

End InfDecTypes.

