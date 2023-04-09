(** Well-founded order on products of [nat] *)

From Coq Require Import Relation_Operators Lexicographic_Product Lia.
From Coq Require Export Wf_nat.

Set Implicit Arguments.


(** * Well founded order on pairs of [nat] *)

Definition lt_nat_nat := slexprod _ _ lt lt.
Definition wf_nat_nat := wf_slexprod _ _ _ _ lt_wf lt_wf.

Ltac lt_nat_nat_solve :=
  match goal with
  | |- lt_nat_nat _ _ => try (left; cbn; lia);
                         try (right; cbn; lia);
                         fail
  | |- slexprod _ _ lt lt _ _ => try (left; cbn; lia);
                                 try (right; cbn; lia);
                                 fail
  end.

(** * Well founded order on triples of [nat] *)

Definition lt_nat_nat_nat := slexprod _ _ lt lt_nat_nat.
Definition wf_nat_nat_nat := wf_slexprod _ _ _ _ lt_wf wf_nat_nat.

Ltac lt_nat_nat_nat_solve :=
  match goal with
  | |- lt_nat_nat_nat _ _ =>
    try (left; cbn; lia);
    try (right; left; cbn; lia);
    try (right; right; cbn; lia);
    fail
  | |- slexprod _ _ lt lt_nat_nat _ _ =>
    try (left; cbn; lia);
    try (right; left; cbn; lia);
    try (right; right; cbn; lia);
    fail
  | |- slexprod _ _ lt (slexprod _ _ lt lt) _ _ =>
    try (left; cbn; lia);
    try (right; left; cbn; lia);
    try (right; right; cbn; lia);
    fail
  end.
