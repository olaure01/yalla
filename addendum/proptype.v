Set Implicit Arguments.

Section PropType.

Variable formula : Set.
Variable lv : list formula.
Variable fv: formula.
Variable c : formula -> formula -> formula.

Inductive proofP : list formula -> Prop :=
| zruleP : proofP (fv :: fv :: lv)
| uruleP l A B : proofP (A :: B :: l) -> proofP (c A B :: l)
| bruleP l1 l2 A B : proofP (A :: l1) -> proofP (B :: l2) -> proofP (c A B :: l1 ++ l2).

Inductive proofT : list formula -> Type :=
| zruleT : proofT (fv :: fv :: lv)
| uruleT l A B : proofT (A :: B :: l) -> proofT (c A B :: l)
| bruleT l1 l2 A B : proofT (A :: l1) -> proofT (B :: l2) -> proofT (c A B :: l1 ++ l2).

Fixpoint sizeT l (pi : proofT l) :=
match pi with
| zruleT => 1
| uruleT pi1 => S (sizeT pi1)
| bruleT pi1 pi2 => S (sizeT pi1 + sizeT pi2)
end.

Goal (sizeT (bruleT (uruleT zruleT) zruleT)) = 4.
Proof. reflexivity. Qed.

Fail Fixpoint sizeP l (pi : proofP l) :=
match pi with
| zruleP => 1
| uruleP pi1 => S (sizeP pi1)
| bruleP pi1 pi2 => S (sizeP pi1 + sizeP pi2)
end.
(* Elimination of an inductive object of sort Prop is not allowed on a predicate in sort Set *)

(* proof of size [n] *)
Inductive proofP_size : nat -> list formula -> Prop :=
| zruleP_size : proofP_size 1 (fv :: fv :: lv)
| uruleP_size n l A B : proofP_size n (A :: B :: l) -> proofP_size (S n) (c A B :: l)
| bruleP_size n1 n2 l1 l2 A B :
    proofP_size n1 (A :: l1) -> proofP_size n2 (B :: l2) -> proofP_size (S (n1 + n2)) (c A B :: l1 ++ l2).

Lemma proofP_size_proofP n l : proofP_size n l -> proofP l.
Proof. intro pi. induction pi; now constructor. Qed.

Lemma proofP_proofP_size l : proofP l -> exists n, proofP_size n l.
Proof.
intro pi. induction pi.
- exists 1. constructor.
- destruct IHpi as [n IHpi].
  exists (S n). now constructor.
- destruct IHpi1 as [n1 IHpi1]. destruct IHpi2 as [n2 IHpi2].
  exists (S (n1 + n2)). now constructor.
Qed.

Lemma proofP_size_ProofP_equiv l : (exists n, proofP_size n l) <-> proofP l.
Proof. split; [ intros [n pi]; exact (proofP_size_proofP pi) | intros pi; exact (proofP_proofP_size pi) ]. Qed.

End PropType.
