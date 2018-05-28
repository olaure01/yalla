(* fmformulas library for yalla *)
(* Coq 8.6 *)
(* v 1.0   Olivier Laurent *)


(** * Order structure and finite multiset structure on intuitionistic formulas *)

Require Import Injective.
Require Import nattree.
Require Import fmsetlist.

Require Export iformulas.


(** ** Encoding of [iformula] into [nat]-labelled trees for ordering *)

(** Embedding of [IAtom] into [nat] *)
Parameter i2n : IAtom -> nat.
Parameter n2i : nat -> IAtom.
Axiom i2i : forall X, n2i (i2n X) = X.

(** Embedding of [iformula] into [nattree] *)
Fixpoint iform2nattree A :=
match A with
| ivar X => Bnt 1 (Bnt (i2n X) Lnt Lnt) Lnt
| ione => Bnt 2 Lnt Lnt
| itens A B => Bnt 3 (iform2nattree A) (iform2nattree B)
| ilmap A B => Bnt 4 (iform2nattree A) (iform2nattree B)
| ilpam A B => Bnt 5 (iform2nattree A) (iform2nattree B)
| itop => Bnt 6 Lnt Lnt
| iwith A B => Bnt 7 (iform2nattree A) (iform2nattree B)
| izero => Bnt 8 Lnt Lnt
| iplus A B => Bnt 9 (iform2nattree A) (iform2nattree B)
| ioc A => Bnt 10 (iform2nattree A) Lnt
end.

Fixpoint nattree2iform (ft : iftop = true) (fz : ifzer = true) t :=
match t with
| Bnt 1 (Bnt k Lnt Lnt) Lnt => ivar (n2i k)
| Bnt 2 Lnt Lnt => ione
| Bnt 3 t1 t2 => itens (nattree2iform ft fz t1) (nattree2iform ft fz t2)
| Bnt 4 t1 t2 => ilmap (nattree2iform ft fz t1) (nattree2iform ft fz t2)
| Bnt 5 t1 t2 => ilpam (nattree2iform ft fz t1) (nattree2iform ft fz t2)
| Bnt 6 Lnt Lnt => @itop ft
| Bnt 7 t1 t2 => iwith (nattree2iform ft fz t1) (nattree2iform ft fz t2)
| Bnt 8 Lnt Lnt => @izero fz
| Bnt 9 t1 t2 => iplus (nattree2iform ft fz t1) (nattree2iform ft fz t2)
| Bnt 10 t1 Lnt => ioc (nattree2iform ft fz t1)
| _ => ione
end.

Lemma iform_nattree_section : forall ft fz A,
  nattree2iform ft fz (iform2nattree A) = A.
Proof.
induction A ; simpl ;
  try rewrite IHA1 ; try rewrite IHA2 ;
  try rewrite IHA ;
  try rewrite i2i ; try reflexivity.
- apply uniq_itop.
- apply uniq_izero.
Qed.


(** ** [BOrder] structure (total order with value into [bool]) *)

Instance border_iformula (ft : iftop = true) (fz : ifzer = true) : BOrder.
Proof.
eapply border_inj.
eapply comp_inj.
- apply nattree2nat_inj.
- eapply section_inj.
  apply (iform_nattree_section ft fz).
Defined.


(** ** Finite multi-sets over [iformula] *)

Instance fmset_iformula ft fz :
  FinMultiset (SortedList (border_iformula ft fz)) iformula
  := FMConstr_slist (border_iformula ft fz).


