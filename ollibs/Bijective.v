(* Bijective Library *)

Require Import Injective Surjective.

(** * Some properties of bijective functions *)

Definition bijective {A B} (f : A -> B) :=
  forall y, { x : _ & y = f x & forall x', y = f x' -> x = x' }.

Lemma id_bijective {A} : bijective (@id A).
Proof. intros x; exists x; unfold id; simpl; intuition. Qed.

Lemma comp_bijectiv {A B C} : forall (f : B -> C) (g : A -> B),
  bijective f -> bijective g -> bijective (fun x => f (g x)).
Proof.
intros f g Hf Hg z.
destruct (Hf z) as [y Heq Hinjf] ; subst.
destruct (Hg y) as [x Heq Hinjg] ; subst.
exists x; [ reflexivity | ].
intros x' Heq; apply Hinjg, Hinjf; assumption.
Qed.

Lemma bijective_inverse {A B} : forall f : A -> B, bijective f ->
  { g : B -> A & retract f g & retract g f }.
Proof.
intros f Hbij.
exists (fun x => projT1 (sigT_of_sigT2 (Hbij x))).
- intros x; simpl; destruct (Hbij x) as [y Heq _]; auto.
- intros x; simpl; destruct (Hbij (f x)) as [y _ Heq]; auto.
Qed.

Lemma bijective_injective {A B} : forall f : A -> B, bijective f -> injective f.
Proof.
intros f Hbij.
destruct (bijective_inverse _ Hbij) as [g _ Hsec].
now apply section_inj with g.
Qed.

Lemma bijective_surjective {A B} : forall f : A -> B, bijective f -> surjective f.
Proof. intros f Hbij y; destruct (Hbij y) as [x Hx _]; exists x; assumption. Qed.

Lemma inj_surj_bijective {A B} : forall f : A -> B,
  injective f -> surjective f -> bijective f.
Proof.
intros f Hinj Hsurj y.
destruct (Hsurj y) as [x Heq].
exists x; [ assumption | ].
intros x' Heq2; apply Hinj; subst; assumption.
Qed.

