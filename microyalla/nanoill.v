(* nanoyalla library for intuitionistic linear logic *)

Open Scope list_scope.

(* Same definition as [List.map] *)
Definition map [A B : Type] (f : A -> B) :=
  fix map l := match l with
               | nil => nil
               | a :: t => f a :: map t
               end.


(* Adapted from yalla/iformulas.v *)

(** A set of atoms for building formulas *)
Definition IAtom := nat.

(** Intuitionistic formulas *)
Inductive iformula :=
| ivar (_ : IAtom)
| ione | itens (_ _ : iformula) | ilmap (_ _ : iformula)
| itop | iwith (_ _ : iformula) | izero | iplus (_ _ : iformula)
| ioc (_ : iformula).


(* Adapted from yalla/ill_def.v *)

(** Rules *)
Inductive ill : list iformula -> iformula -> Type :=
| ax_ir X : ill (ivar X :: nil) (ivar X)
| ex_t_ir l1 l2 A B C : ill (l1 ++ A :: B :: l2) C -> ill (l1 ++ B :: A :: l2) C
| one_irr : ill nil ione
| one_ilr l A : ill l A -> ill (ione :: l) A
| tens_irr A B l1 l2 : ill l1 A -> ill l2 B -> ill (l1 ++ l2) (itens A B)
| tens_ilr A B l C : ill (A :: B :: l) C -> ill (itens A B :: l) C
| lmap_irr A B l : ill (A :: l) B -> ill l (ilmap A B)
| lmap_ilr A B l1 l2 C : ill l1 A -> ill (B :: l2) C -> ill (ilmap A B :: l1 ++ l2) C
| top_irr l : ill l itop
| with_irr A B l : ill l A -> ill l B -> ill l (iwith A B)
| with_ilr1 A B l C : ill (A :: l) C -> ill (iwith A B :: l) C
| with_ilr2 A B l C : ill (A :: l) C -> ill (iwith B A :: l) C
| zero_ilr l C : ill (izero :: l) C
| plus_irr1 A B l : ill l A -> ill l (iplus A B)
| plus_irr2 A B l : ill l A -> ill l (iplus B A)
| plus_ilr A B l C : ill (A :: l) C -> ill (B :: l) C -> ill (iplus A B :: l) C
| oc_irr A l : ill (map ioc l) A -> ill (map ioc l) (ioc A)
| de_ilr A l C : ill (A :: l) C -> ill (ioc A :: l) C
| wk_ilr A l C : ill l C -> ill (ioc A :: l) C
| co_ilr A l C : ill (ioc A :: ioc A :: l) C -> ill (ioc A :: l) C.
