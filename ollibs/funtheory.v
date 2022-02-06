(** Properties of functions *)

From Coq Require Export Program.Basics.
From Coq Require Import Relation_Definitions RelationClasses List.

Set Implicit Arguments.

(** * Functions on constructors *)
Definition Empty_fun {A} : Empty_set -> A := fun o => match o with end.

Definition option_eval_default A B default (f : A -> B) o :=
match o with
| Some a => f a
| None => default
end.

Definition option_map A B (f : A -> B) := option_eval_default None (fun x => Some (f x)).


(** * Retraction pairs *)

Definition retract A B (s : B -> A) (i : A -> B) := forall x, s (i x) = x.

Lemma id_retract A : retract (@id A) id.
Proof. intros x; reflexivity. Qed.

Lemma compose_retract A B C : forall (s1 : B -> A) (s2 : C -> B) i1 i2,
  retract s1 i1 -> retract s2 i2 -> retract (compose s1 s2) (compose i2 i1).
Proof. intros s1 s2 i1 i2 Hr1 Hr2 x; unfold compose; rewrite Hr2, Hr1; reflexivity. Qed.

Definition embedding A B := {'(s,i) : _ * (A -> B) | retract s i }.

Lemma id_embedding A : embedding A A.
Proof. now exists (id, id). Qed.


Section Function.

  Variable A B : Type.
  Variable f : A -> B.

  (** ** Injective functions *)

  (** Same definition as in standard library [Coq.Sets.Image] *)
  Definition injective := forall x y, f x = f y -> x = y.

  Lemma section_injective : forall g, retract g f -> injective.
  Proof. intros g Hsec x y Hf; rewrite <- Hsec, Hf; intuition. Qed.

  Lemma injective_NoDup : injective -> forall l, NoDup l -> NoDup (map f l).
  Proof.
  (* from Logic.FinFun
  intros Ij. induction 1 as [|x l X N IH]; cbn; constructor; trivial.
  rewrite in_map_iff. intros (y & E & Y). apply Ij in E. now subst.
  *)
  intros Hinj l; induction l as [|a l IHl]; cbn; intros Hnd.
  - constructor.
  - inversion Hnd as [|a' l' Hnin Hnd']; constructor; subst.
    + intros Hin; apply Hnin.
      apply in_map_iff in Hin.
      destruct Hin as [x [Heq Hin]].
      now apply Hinj in Heq; subst.
    + now apply IHl.
  Qed.

  (** ** Surjective functions *)

  Definition surjective := forall y, { x | y = f x }.

  Lemma retract_surjective : forall g, retract f g -> surjective.
  Proof. intros g Hr y; exists (g y); rewrite Hr; reflexivity. Qed.

  Lemma surjective_retract : forall (Hs : surjective),
    retract f (fun y => proj1_sig (Hs y)).
  Proof.
  intros Hs y.
  symmetry; apply (proj2_sig (Hs y)).
  Qed.

  (** ** Bijective functions *)

  Definition bijective :=
    forall y, { x | y = f x & forall x', y = f x' -> x = x' }.

  Lemma bijective_inverse : bijective -> { g : B -> A | retract f g & retract g f }.
  Proof.
  intros Hbij.
  exists (fun x => proj1_sig (sig_of_sig2 (Hbij x))).
  - intros x; cbn; destruct (Hbij x) as [y Heq _]; auto.
  - intros x; cbn; destruct (Hbij (f x)) as [y _ Heq]; auto.
  Qed.

  Lemma bijective_injective : bijective -> injective.
  Proof.
  intros Hbij.
  destruct (bijective_inverse Hbij) as [g _ Hsec].
  now apply section_injective with g.
  Qed.

  Lemma bijective_surjective : bijective -> surjective.
  Proof. intros Hbij y; destruct (Hbij y) as [x Hx _]; exists x; assumption. Qed.

  Lemma injective_surjective_bijective : injective -> surjective -> bijective.
  Proof.
  intros Hinj Hsurj y.
  destruct (Hsurj y) as [x Heq].
  exists x; [ assumption | ].
  intros x' Heq2; apply Hinj; subst; assumption.
  Qed.

  Lemma biretract_bijective : forall g, retract f g -> retract g f -> bijective.
  Proof.
  intros g Hfg Hgf.
  apply injective_surjective_bijective.
  - now apply section_injective with g.
  - now apply retract_surjective with g.
  Qed.

End Function.


(** * More Properties of Injective Functions *)

Lemma id_injective A : injective (@id A).
Proof. intros x y Heq; unfold id in Heq; assumption. Qed.

Lemma compose_injective A B C (f : A -> B) (g : B -> C) :
  injective f -> injective g -> injective (compose g f) .
Proof. unfold injective; intuition. Qed.

Lemma map_injective A B (f : A -> B) : injective f -> injective (map f).
Proof.
intros Hf l1; induction l1 as [|a l1 IHl1]; intros l2 Hmap; destruct l2; auto;
  inversion Hmap as [ [Hhd Htl] ].
apply Hf in Hhd.
apply IHl1 in Htl.
subst; reflexivity.
Qed.

Lemma map_injective_in A B (f : A -> B) l1 l2 :
  (forall x y, In x l1 -> In y l2 -> f x = f y -> x = y) ->
    map f l1 = map f l2 -> l1 = l2.
Proof.
revert l2; induction l1 as [|a l1 IHl1]; intros l2 Hi Hmap; destruct l2; auto;
  inversion Hmap as [ [Hhd Htl] ].
apply Hi in Hhd; try now apply in_eq.
apply IHl1 in Htl; subst; auto.
intros; apply Hi; auto; now apply in_cons.
Qed.

(** ** Inverse image of a relation by an injective function *)

Section Relation_injective.

  Variable A B : Type.
  Variable f : A -> B.
  Hypothesis f_inj : injective f.

  Variable R : relation B.

  Definition f_R := fun x y => R (f x) (f y).

  Lemma PreOrder_injective : PreOrder R -> PreOrder f_R.
  Proof.
  intros [Hrefl Htrans]; split; unfold f_R.
  - intros x; apply Hrefl.
  - intros x y z H1 H2; eapply Htrans; eassumption.
  Qed.

  Lemma Equivalence_injective : Equivalence R -> Equivalence f_R.
  Proof.
  intros [Hrefl Hsym Htrans]; split; unfold f_R.
  - intros x; apply Hrefl.
  - intros x y HR; apply Hsym; assumption.
  - intros x y z HR1 HR2; eapply Htrans; eassumption.
  Qed.

  Lemma PartialOrder_injective : forall Ro,
    @PartialOrder _ eq _ _ Ro -> @PartialOrder _ eq _ _ (PreOrder_injective Ro).
  Proof.
  intros Ro Rp x y ; split.
  - intros Heq; subst; split; clear Rp; apply PreOrder_injective in Ro; reflexivity.
  - intros [Hr Hs].
    destruct Rp with (f x) (f y) as [_ Hf].
    apply f_inj, Hf; split; assumption.
  Qed.

End Relation_injective.


(** * More Properties of Surjective Functions *)

Lemma id_surjective A : surjective (@id A).
Proof. intros x; exists x; reflexivity. Qed.

Lemma compose_surjective A B C : forall (f : A -> B) (g : B -> C),
  surjective f -> surjective g -> surjective (compose g f).
Proof.
intros f g Hf Hg z.
destruct (Hg z) as [y Heq]; subst.
destruct (Hf y) as [x Heq]; subst.
exists x; reflexivity.
Qed.

Lemma map_surjective A B (f : A -> B) : surjective f -> surjective (map f).
Proof.
intros Hf l1; induction l1 as [| a l1 IHl1].
- exists nil; reflexivity.
- destruct (Hf a) as [b Heq] ; subst.
  destruct IHl1 as [l Heq] ; subst.
  exists (b :: l); reflexivity.
Qed.


(** * More Properties of Bijective Functions *)

Lemma id_bijective A : bijective (@id A).
Proof. intros x; exists x; unfold id; cbn; intuition. Qed.
Arguments id_bijective {_}.

Lemma compose_bijective A B C : forall (f : A -> B) (g : B -> C),
  bijective f -> bijective g -> bijective (compose g f).
Proof.
intros f g Hf Hg z.
destruct (Hg z) as [y Heq Hinjf] ; subst.
destruct (Hf y) as [x Heq Hinjg] ; subst.
exists x; [ reflexivity | ].
intros x' Heq; apply Hinjg, Hinjf; assumption.
Qed.


(** * Additional definitions *)

(* Binary functions *)
Definition injective2 A B C (f : A -> B -> C) :=
  forall x y x' y', f x y = f x' y' -> x = x' /\ y = y'.

Definition surjective2 A B C (f : A -> B -> C) :=
  forall z, {'(x, y) | z = f x y }.
