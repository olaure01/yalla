(* microyalla library for intuitionistic linear logic *)
(*   Olivier Laurent *)

Open Scope list_scope.

Require List.
(* only List.map from module List is used:
Fixpoint map {A B : Type} (f: A -> B) l :=
    match l with
      | nil => nil
      | a :: t => (f a) :: (map f t)
    end.
*)

(* Transpose elements of index n and n+1 in l *)
Fixpoint transp {A} n (l : list A) :=
match n, l with
| 0, x :: y :: r => y :: x :: r
| S n, x :: r => x :: transp n r
| _, r => r
end.


(* Adapted from yalla/iformulas.v *)

(** A set of atoms for building formulas *)
Definition IAtom := nat.

(** Intuitionistic formulas *)
Inductive iformula : Set :=
| ivar  : IAtom -> iformula
| ione  : iformula
| itens : iformula -> iformula -> iformula
| ilmap : iformula -> iformula -> iformula
| itop  : iformula
| iwith : iformula -> iformula -> iformula
| izero : iformula
| iplus : iformula -> iformula -> iformula
| ioc   : iformula -> iformula.


(* Adapted from yalla/ill_def.v *)

(** Rules *)
Inductive ill : list iformula -> iformula -> Type :=
| ax_ir : forall X, ill (ivar X :: nil) (ivar X)
| ex_t_ir : forall n l A, ill l A -> ill (transp n l) A
| one_irr : ill nil ione
| one_ilr : forall l A, ill l A -> ill (ione :: l) A
| tens_irr : forall A B l1 l2, ill l1 A -> ill l2 B -> ill (l1 ++ l2) (itens A B)
| tens_ilr : forall A B l C, ill (A :: B :: l) C -> ill (itens A B :: l) C
| lmap_irr : forall A B l, ill (A :: l) B -> ill l (ilmap A B)
| lmap_ilr : forall A B l1 l2 C, ill l1 A -> ill (B :: l2) C -> ill (ilmap A B :: l1 ++ l2) C
| top_irr : forall l, ill l itop
| with_irr : forall A B l, ill l A -> ill l B -> ill l (iwith A B)
| with_ilr1 : forall A B l C, ill (A :: l) C -> ill (iwith A B :: l) C
| with_ilr2 : forall A B l C, ill (A :: l) C -> ill (iwith B A :: l) C
| zero_ilr : forall l C, ill (izero :: l) C
| plus_irr1 : forall A B l, ill l A -> ill l (iplus A B)
| plus_irr2 : forall A B l, ill l A -> ill l (iplus B A)
| plus_ilr : forall A B l C, ill (A :: l) C -> ill (B :: l) C -> ill (iplus A B :: l) C
| oc_irr : forall A l, ill (List.map ioc l) A -> ill (List.map ioc l) (ioc A)
| de_ilr : forall A l C, ill (A :: l) C -> ill (ioc A :: l) C
| wk_ilr : forall A l C, ill l C -> ill (ioc A :: l) C
| co_ilr : forall A l C, ill (ioc A :: ioc A :: l) C -> ill (ioc A :: l) C.


