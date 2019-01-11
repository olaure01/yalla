(* Injective Library *)
(* v0   Olivier Laurent *)


(** * Some properties of injective functions *)

Require Import Relations.
Require Import RelationClasses.
Require Import List_more.

(** Same definition as in standard library [Coq.Sets.Image] *)
Definition injective {A B} (f : A -> B) := forall x y, f x = f y -> x = y.

Definition injective2 {A B C} (f : A -> B -> C) :=
  forall x y x' y', f x y = f x' y' -> x = x' /\ y = y'.

(** * Basic properties of injective functions *)

Lemma comp_inj {A B C} : forall (f : B -> C) (g : A -> B),
  injective f -> injective g -> injective (fun x => f (g x)).
Proof.
intros f g Hf Hg x y Hc.
apply Hg.
apply Hf.
assumption.
Qed.

Lemma section_inj {A B} : forall (f : A -> B) g,
  (forall x, g (f x) = x) -> injective f.
Proof.
intros f g Hsec x y Hf.
rewrite <- Hsec.
rewrite <- Hf.
rewrite Hsec.
reflexivity.
Qed.

Lemma map_inj {A B} : forall f : A -> B, injective f -> injective (map f).
Proof.
intros f Hf l1.
induction l1 ; intros l2 Hmap.
- destruct l2.
  + reflexivity.
  + inversion Hmap.
- destruct l2.
  + inversion Hmap.
  + simpl in Hmap.
    injection Hmap ; intros Htl Hhd.
    apply Hf in Hhd.
    apply IHl1 in Htl.
    subst.
    reflexivity.
Qed.

Lemma map_inj_local {A B} : forall f : A -> B, forall l1 l2,
  (forall x y, In x l1 -> In y l2 -> f x = f y -> x = y) ->
    map f l1 = map f l2 -> l1 = l2.
Proof with try assumption ; try reflexivity.
induction l1 ; intros l2 Hi Hmap.
- destruct l2...
  inversion Hmap.
- destruct l2.
  + inversion Hmap.
  + simpl in Hmap.
    injection Hmap ; intros Htl Hhd.
    apply Hi in Hhd ; try (apply in_eq ; fail).
    apply IHl1 in Htl ; subst...
    intros.
    apply Hi...
    * apply in_cons...
    * apply in_cons...
Qed.


(** * Inverse image of a relation by an injective function *)

Section Relation_inj.

Variable A B : Type.
Variable f : A -> B.
Hypothesis f_inj : injective f.

Variable R : relation B.

Definition f_R := fun x y => R (f x) (f y).

Lemma PreOrder_inj : PreOrder R -> PreOrder f_R.
Proof.
intros Hp.
destruct Hp.
split ; unfold f_R.
- intros x.
  apply PreOrder_Reflexive.
- intros x y z H1 H2.
  eapply PreOrder_Transitive ; eassumption.
Qed.

Lemma Equivalence_inj : Equivalence R -> Equivalence f_R.
Proof.
intros He.
destruct He.
split ; unfold f_R.
- intros x.
  apply Equivalence_Reflexive.
- intros x y H.
  apply Equivalence_Symmetric ; assumption.
- intros x y z H1 H2.
  eapply Equivalence_Transitive ; eassumption.
Qed.

Lemma PartialOrder_inj : forall Ro,
  @PartialOrder _ eq _ _ Ro -> @PartialOrder _ eq _ _ (PreOrder_inj Ro).
Proof.
intros Ro Rp x y ; split ; intros H.
- subst ; split.
  + clear Rp ; apply PreOrder_inj in Ro.
    reflexivity.
  + clear Rp ; apply PreOrder_inj in Ro.
    reflexivity.
- destruct H as [Hr Hs].
  destruct Rp with (f x) (f y) as [_ Hf].
  apply f_inj.
  apply Hf.
  split.
  + apply Hr.
  + apply Hs.
Qed.

End Relation_inj.




