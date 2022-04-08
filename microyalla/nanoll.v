(* nanoyalla library for linear logic *)

Open Scope list_scope.

(* Same definition as [List.map] *)
Definition map [A B : Type] (f : A -> B) :=
  fix map l := match l with
               | nil => nil
               | a :: t => f a :: map t
               end.


(* Adapted from yalla/formulas.v *)

(** A set of atoms for building formulas *)
Definition Atom := nat.

(** Formulas *)
Inductive formula :=
| var (_ : Atom) | covar (_ : Atom)
| one | bot
| tens (_ _ : formula) | parr (_ _ : formula)
| zero | top
| aplus (_ _ : formula) | awith (_ _ : formula)
| oc (_ : formula) | wn (_ : formula).


(* Adapted from yalla/ll_def.v *)

(** Rules *)
Inductive ll : list formula -> Type :=
| ax_r X : ll (covar X :: var X :: nil)
| ex_t_r l1 l2 A B : ll (l1 ++ A :: B :: l2) -> ll (l1 ++ B :: A :: l2)
| one_r : ll (one :: nil)
| bot_r l : ll l -> ll (bot :: l)
| tens_r A B l1 l2 : ll (A :: l1) -> ll (B :: l2) -> ll (tens A B :: l1 ++ l2)
| parr_r A B l : ll (A :: B :: l) -> ll (parr A B :: l)
| top_r l : ll (top :: l)
| plus_r1 A B l : ll (A :: l) -> ll (aplus A B :: l)
| plus_r2 A B l : ll (A :: l) -> ll (aplus B A :: l)
| with_r A B l : ll (A :: l) -> ll (B :: l) -> ll (awith A B :: l)
| oc_r A l : ll (A :: map wn l) -> ll (oc A :: map wn l)
| de_r A l : ll (A :: l) -> ll (wn A :: l)
| wk_r A l : ll l -> ll (wn A :: l)
| co_r A l : ll (wn A :: wn A :: l) -> ll (wn A :: l).
