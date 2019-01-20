(* fmformulas library for yalla *)

(* output in Type *)


(** * Order structure and finite multiset structure on intuitionistic formulas *)

Require Import Injective.
Require Import nattree.
Require Import fmsetlist_Type.

Require Export iformulas.


(** ** Encoding of [iformula] into [nat]-labelled trees for ordering *)

(** Embedding of [IAtom] into [nat] *)
Definition i2n := yalla_ax.i2n.
Definition n2i := yalla_ax.n2i.
Definition i2i_n := yalla_ax.i2i_n.

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

Lemma iform_nattree_section : forall A, nattree2iform (iform2nattree A) = A.
Proof.
induction A ; simpl ;
  try rewrite IHA1 ; try rewrite IHA2 ;
  try rewrite IHA ;
  try rewrite i2i_n ; try reflexivity.
Qed.


(** ** [BOrder] structure (total order with value into [bool]) *)

Instance border_iformula : BOrder.
Proof.
eapply border_inj.
eapply comp_inj.
- apply nattree2nat_inj.
- eapply section_inj.
  apply iform_nattree_section.
Defined.


(** ** Finite multi-sets over [iformula] *)

Instance fmset_iformula :
  FinMultiset (SortedList border_iformula) iformula
  := FMConstr_slist border_iformula.


