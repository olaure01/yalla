Set Mangle Names.
Set Mangle Names Light.
Set Implicit Arguments.

Definition iffT (A B : Type) := ((A -> B) * (B -> A))%type.

Definition prod_map A B (f : A -> B) p :=
  match p with
  | (a1, a2) => (f a1, f a2)
  end.

Definition prod_map2 A B C (f : A -> B -> C) p1 p2 :=
  match p1, p2 with
  | (a1, a2), (b1, b2) => (f a1 b1, f a2 b2)
  end.
