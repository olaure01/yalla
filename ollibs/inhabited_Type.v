(** Types with inhabitant declared in Type *)

Set Implicit Arguments.

(** * Inhabitation *)

Variant inhabited_inf A : Type := | inhabits_inf : A -> inhabited_inf A.

Definition inhabitant_inf A (Hinh : inhabited_inf A) := match Hinh with inhabits_inf a => a end.

Lemma inhabited_inf_unit : inhabited_inf unit.
Proof. exact (inhabits_inf tt). Qed.

Lemma inhabited_inf_bool : inhabited_inf bool.
Proof. exact (inhabits_inf false). Qed.

Lemma inhabited_inf_nat : inhabited_inf nat.
Proof. exact (inhabits_inf 0). Qed.

Lemma inhabited_inf_option A : inhabited_inf (option A).
Proof. exact (inhabits_inf None). Qed.

Lemma inhabited_inf_suml A B : inhabited_inf A -> inhabited_inf (sum A B).
Proof. exact (fun Hinh => inhabits_inf (inl (inhabitant_inf Hinh))). Qed.
Arguments inhabited_inf_suml [_] {_} _.

Lemma inhabited_inf_sumr A B : inhabited_inf B -> inhabited_inf (sum A B).
Proof. exact (fun Hinh => inhabits_inf (inr (inhabitant_inf Hinh))). Qed.
Arguments inhabited_inf_sumr {_} [_] _.

Lemma inhabited_inf_prod A B : inhabited_inf A -> inhabited_inf B -> inhabited_inf (prod A B).
Proof. exact (fun HinhA HinhB => inhabits_inf (inhabitant_inf HinhA, inhabitant_inf HinhB)). Qed.

Lemma inhabited_inf_list A : inhabited_inf (list A).
Proof. exact (inhabits_inf nil). Qed.

Lemma inhabited_inf_fun A B (f : A -> B) : inhabited_inf A -> inhabited_inf B.
Proof. exact (fun Hinh => inhabits_inf (f (inhabitant_inf Hinh))). Qed.

Lemma inhabited_inf_img A B : inhabited_inf B -> inhabited_inf (A -> B).
Proof. exact (fun Hinh => inhabits_inf (fun _ => (inhabitant_inf Hinh))). Qed.

Lemma inhabited_inf_id A : inhabited_inf (A -> A).
Proof. exact (inhabits_inf (@id _)). Qed.
