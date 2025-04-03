(** * Order structure and finite multiset structure on formulas *)

From OLlibs Require Import funtheory infinite nattree fmsetlistT BOrders.
From Yalla Require Export formulas.

Set Implicit Arguments.


Section Atoms.

Context {atom : DecType} {Atoms : AtomType_into_nat atom}.

(** ** Encoding of [formula] into [nat]-labelled trees for ordering *)

(** Embedding of [Atom] into [nat] *)
Notation a2n := (snd (proj1_sig Atom_into_nat)).
Notation n2a := (fst (proj1_sig Atom_into_nat)).
Definition a2a_n : retract n2a a2n :=
  eq_rect _ _ (proj2_sig Atom_into_nat) _ (surjective_pairing (proj1_sig Atom_into_nat)).

(** Embedding of [formula] into [nattree] *)
Fixpoint form2nattree A :=
match A with
| var X => Bnt 1 (Bnt (a2n X) Lnt Lnt) Lnt
| covar X => Bnt 2 (Bnt (a2n X) Lnt Lnt) Lnt
| one => Bnt 3 Lnt Lnt
| bot => Bnt 4 Lnt Lnt
| tens A B => Bnt 5 (form2nattree A) (form2nattree B)
| parr A B => Bnt 6 (form2nattree A) (form2nattree B)
| zero => Bnt 7 Lnt Lnt
| top => Bnt 8 Lnt Lnt
| aplus A B => Bnt 9 (form2nattree A) (form2nattree B)
| awith A B => Bnt 10 (form2nattree A) (form2nattree B)
| oc A => Bnt 11 (form2nattree A) Lnt
| wn A => Bnt 12 (form2nattree A) Lnt
end.

Fixpoint nattree2form t :=
match t with
| Bnt 1 (Bnt k Lnt Lnt) Lnt => var (n2a k)
| Bnt 2 (Bnt k Lnt Lnt) Lnt => covar (n2a k)
| Bnt 3 Lnt Lnt => one
| Bnt 4 Lnt Lnt => bot
| Bnt 5 t1 t2 => tens (nattree2form t1) (nattree2form t2)
| Bnt 6 t1 t2 => parr (nattree2form t1) (nattree2form t2)
| Bnt 7 Lnt Lnt => zero
| Bnt 8 Lnt Lnt => top
| Bnt 9 t1 t2 => aplus (nattree2form t1) (nattree2form t2)
| Bnt 10 t1 t2 => awith (nattree2form t1) (nattree2form t2)
| Bnt 11 t1 Lnt => oc (nattree2form t1)
| Bnt 12 t1 Lnt => wn (nattree2form t1)
| _ => one
end.

Lemma form_nattree_section : retract nattree2form form2nattree.
Proof. intro A. induction A; cbn; rewrite ?IHA1, ?IHA2, ?IHA, ?a2a_n; reflexivity. Qed.


(** ** [BOrder] structure (total order with value into [bool]) *)

#[export] Instance border_formula : BOrder | 50.
Proof.
eapply border_inj, compose_injective.
- eapply section_injective. exact form_nattree_section.
- exact nattree2nat_inj.
Defined.


(** ** Finite multi-sets over [formula] *)

#[export] Instance fmset_formula : FinMultiset (SortedList border_formula) formula | 50
  := FMConstr_slist border_formula.

End Atoms.
