(** * Order structure and finite multiset structure on intuitionistic formulas *)

From OLlibs Require Import funtheory dectype nattree fmsetlist_Type BOrders.
From Yalla Require Export iformulas.

Set Implicit Arguments.


Section Atoms.

Context {preiatom : DecType} {IAtoms : IAtomType_into_nat preiatom}.

(** ** Encoding of [iformula] into [nat]-labelled trees for ordering *)

(** Embedding of [IAtom] into [nat] *)
Notation i2n := (snd (proj1_sig IAtom_into_nat)).
Notation n2i := (fst (proj1_sig IAtom_into_nat)).
Definition i2i_n : retract n2i i2n :=
  eq_rect _ _ (proj2_sig IAtom_into_nat) _ (surjective_pairing (proj1_sig IAtom_into_nat)).

(** Embedding of [iformula] into [nattree] *)
Fixpoint iform2nattree A :=
match A with
| ivar X => Bnt 1 (Bnt (i2n X) Lnt Lnt) Lnt
| ione => Bnt 2 Lnt Lnt
| itens A B => Bnt 3 (iform2nattree A) (iform2nattree B)
| ilpam A B => Bnt 4 (iform2nattree A) (iform2nattree B)
| igen A => Bnt 5 (iform2nattree A) Lnt
| ilmap A B => Bnt 6 (iform2nattree A) (iform2nattree B)
| ineg A => Bnt 7 (iform2nattree A) Lnt
| itop => Bnt 8 Lnt Lnt
| iwith A B => Bnt 9 (iform2nattree A) (iform2nattree B)
| izero => Bnt 10 Lnt Lnt
| iplus A B => Bnt 11 (iform2nattree A) (iform2nattree B)
| ioc A => Bnt 12 (iform2nattree A) Lnt
end.

Fixpoint nattree2iform t :=
match t with
| Bnt 1 (Bnt k Lnt Lnt) Lnt => ivar (n2i k)
| Bnt 2 Lnt Lnt => ione
| Bnt 3 t1 t2 => itens (nattree2iform t1) (nattree2iform t2)
| Bnt 4 t1 t2 => ilpam (nattree2iform t1) (nattree2iform t2)
| Bnt 5 t1 Lnt => igen (nattree2iform t1)
| Bnt 6 t1 t2 => ilmap (nattree2iform t1) (nattree2iform t2)
| Bnt 7 t1 Lnt => ineg (nattree2iform t1)
| Bnt 8 Lnt Lnt => itop
| Bnt 9 t1 t2 => iwith (nattree2iform t1) (nattree2iform t2)
| Bnt 10 Lnt Lnt => izero
| Bnt 11 t1 t2 => iplus (nattree2iform t1) (nattree2iform t2)
| Bnt 12 t1 Lnt => ioc (nattree2iform t1)
| _ => ione
end.

Lemma iform_nattree_section : retract nattree2iform iform2nattree.
Proof. intros A. induction A; cbn; rewrite ? IHA, ? IHA1, ? IHA2, ? i2i_n; reflexivity. Qed.


(** ** [BOrder] structure (total order with value into [bool]) *)

#[export] Instance border_iformula : BOrder | 50.
Proof.
eapply border_inj, compose_injective.
- eapply section_injective. intro. apply iform_nattree_section.
- apply nattree2nat_inj.
Defined.


(** ** Finite multi-sets over [iformula] *)

#[export] Instance fmset_iformula : FinMultiset (SortedList border_iformula) iformula | 50
  := FMConstr_slist border_iformula.

End Atoms.
