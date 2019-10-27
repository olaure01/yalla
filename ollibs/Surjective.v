(* Surjective Library *)

(** * Some properties of surjective functions *)

Require Import List.

Definition surjective {A B} (f : A -> B) := forall y, exists x, y = f x.

Definition surjective2 {A B C} (f : A -> B -> C) := forall z, exists x y, z = f x y.

(** * Basic properties of surjective functions *)

Lemma comp_surj {A B C} : forall (f : B -> C) (g : A -> B),
  surjective f -> surjective g -> surjective (fun x => f (g x)).
Proof.
intros f g Hf Hg z.
destruct (Hf z) as [y Heq] ; subst.
destruct (Hg y) as [x Heq] ; subst.
exists x ; reflexivity.
Qed.

Lemma retract_surj {A B} : forall (f : A -> B) g,
  (forall x, f (g x) = x) -> surjective f.
Proof.
intros f g Hret y.
exists (g y).
rewrite Hret.
reflexivity.
Qed.

Lemma map_surj {A B} : forall f : A -> B, surjective f -> surjective (map f).
Proof.
intros f Hf l1.
induction l1.
- exists nil.
  reflexivity.
- destruct (Hf a) as [b Heq] ; subst.
  destruct IHl1 as [l Heq] ; subst.
  exists (b :: l).
  reflexivity.
Qed.

