(** Infinite Types *)

From Coq Require Import Bool PeanoNat Lia List.
From Yalla.OLlibs Require Import funtheory List_Type.
From Yalla.OLlibs Require Export inhabited_Type dectype.

Set Implicit Arguments.
Set Default Proof Using "Type".


(** a pigeonhole principle *)
Definition pigeon X := forall (l1 l2 : list X),
  NoDup l1 -> length l2 < length l1 -> { x | In x l1 & ~ In x l2 }.


(** * Definitions and implications *)

(* The following results are proved in the case of a DecType:
     bijection with nat => section with nat => non-surjective self injection => injection from nat
     injection from nat <=> choice out of finite subsets
*)


(* we start with results true for an arbitrary Type:
     bijection with nat => section with nat => choice out of finite subsets => injection from nat
     bijection with nat => non-surjective self injection
*)
Section Infinite.

  Variable X : Type.

  (* bijection with nat *)
  Definition nat_bijective := { f : nat -> X & bijective f }.
  (* section with nat *)
  Definition nat_section := {'(i, s) : (nat -> X) * (X -> nat) | retract s i }.
  (* non-surjective self injection *)
  Definition self_injective := { f : X -> X & injective f & { x | forall y, x <> f y } }.
  (* injection from nat *)
  Definition nat_injective := { f : nat -> X | injective f }.
  (* choice out of finite subsets *)
  Definition choice_out_finite := { f : list X -> X | forall l, ~ In (f l) l }.

  Lemma nat_bijective_section : nat_bijective -> nat_section.
  Proof.
  intros [i Hbij].
  destruct (bijective_inverse Hbij) as [s _ Hsec].
  exists (i, s). exact Hsec.
  Qed.

  Lemma section_choice : nat_section -> choice_out_finite.
  Proof.
  intros [(i,s) Hsec].
  remember (fix h l :=
    match l with
    | nil => i 0
    | x :: tl => i (S (max (s x) (s (h tl))))
    end) as c.
  exists c.
  enough (forall l, Forall (fun x => s x < s (c l)) l) as Hlt.
  { intros l Hin. specialize Hlt with l.
    apply (proj1 (Forall_forall _ _) Hlt (c l)) in Hin. lia. }
  induction l; cbn; constructor.
  - rewrite Heqc, Hsec. lia.
  - apply Forall_forall. intros b Hb. apply Forall_forall with (x:= b) in IHl; [ | assumption ].
    subst c. rewrite Hsec. lia.
  Qed.

  Lemma choice_nat_injective : choice_out_finite -> nat_injective.
  Proof.
  intros [c Hc].
  remember (fix h n := (* a non-empty list of iterated choices *)
    match n with
    | 0 => c nil :: nil
    | S k => c (h k) :: h k
    end) as ih.
  exists (fun n => hd (c nil) (ih n)).
  assert(forall n x, In (hd (c nil) (ih x)) (ih (n + x))) as HC.
  { intros n x. induction n; cbn; subst.
    - destruct x; left; reflexivity.
    - right. exact IHn. }
  enough (forall x y, x < y -> hd (c nil) (ih x) = hd (c nil) (ih y) -> x = y) as Hlt.
  { intros x y Heq.
    case (Nat.compare_spec x y); intros Ho; [ exact Ho | | ].
    - apply Hlt, Heq. exact Ho.
    - symmetry. apply Hlt; [ | symmetry ]; assumption. }
  intros x y Hlt Heq. exfalso.
  specialize HC with (y - S x) x.
  replace (y - S x + x) with (pred y) in HC by lia.
  rewrite Heq in HC.
  replace y with (S (pred y)) in HC at 1 by lia.
  apply (Hc (ih (pred y))). subst ih. assumption.
  Qed.

  Lemma nat_bijective_self : nat_bijective -> self_injective.
  Proof.
  intros [i Hbij].
  destruct (bijective_inverse Hbij) as [s Hsec1 Hsec2].
  exists (fun x => i (S (s x))).
  - apply compose_injective; [ apply compose_injective | ].
    + apply section_injective with i, Hsec1.
    + intros x y. lia.
    + apply section_injective with s, Hsec2.
  - exists (i 0). intros x Heq.
    apply section_injective in Hsec2.
    apply Hsec2 in Heq. discriminate Heq.
  Qed.

End Infinite.

(** [DecType] case *)

(* Implications requiring a DecType
     section with nat => non-surjective self injection => injection from nat
     injection from nat => choice out of finite subset
*)
Section InfiniteDec.

  Variable X : DecType.

  Lemma section_self_injective : nat_section X -> self_injective X.
  Proof.
  intros [(i, s) Hs].
  assert (Hinj := section_injective Hs).
  assert (forall x z, x = i z -> x = i (s x)) as Hsi
    by (now intros x z Heq; rewrite Heq at 2; rewrite Hs). clear Hs.
  exists (fun x => if eqb x (i (s x)) then i (S (s x)) else x).
  - intros x y.
    repeat case_analysis; intros Heqh; [ | | | exact Heqh ].
    + rewrite Heq, Heq0. f_equal.
      apply Hinj in Heqh.
      injection Heqh as [= ->]. reflexivity.
    + exfalso. symmetry in Heqh.
      apply Heq0, (Hsi _ _ Heqh).
    + exfalso.
      apply Heq, (Hsi _ _ Heqh).
  - exists (i 0). intros x.
    case_analysis; intros Heqi.
    + apply Hinj in Heqi. discriminate Heqi.
    + symmetry in Heqi.
      apply Heq, (Hsi _ _ Heqi).
  Qed.

  Lemma pigeon_dectype : pigeon X.
  Proof.
  intros l1. induction l1; cbn; intros l2 Hnd Hl; [ exfalso; lia | ].
  destruct (in_dec eq_dt_dec a l2).
  - apply NoDup_NoDup_inf in Hnd.
    inversion_clear Hnd as [ | ? ? Hnin%notin_inf_notin Hnd2%NoDup_inf_NoDup ].
    apply IHl1 with (remove eq_dt_dec a l2) in Hnd2 as [b Hb Hnb].
    + exists b.
      * right. assumption.
      * intros Hin. apply Hnb.
        apply in_in_remove; [ | assumption ].
        intros ->. exact (Hnin Hb).
    + apply remove_length_lt with (eq_dec:= eq_dt_dec) in i. lia.
  - now exists a; [ left | ].
  Qed.

  Lemma injective_enum (f : nat -> X) : injective f -> forall l, { n | ~ In (f n) l }.
  Proof.
  intros Hinj l.
  destruct pigeon_dectype with (map f (seq 0 (S (length l)))) l as [x Hin Hnin].
  - apply injective_NoDup, seq_NoDup. assumption.
  - rewrite map_length, seq_length. lia.
  - remember (S (length l)) as k. clear Heqk.
    remember 0 as s. clear Heqs.
    induction k in s, Hin, Hnin |-*; cbn; [ easy | ].
    case (eq_dt_reflect (f s) x); intros Heq; subst.
    + exists s. assumption.
    + apply IHk with (S s); [ | assumption ].
      now destruct Hin.
  Qed.

  Lemma nat_injective_choice : nat_injective X -> choice_out_finite X.
  Proof.
  intros [i Hi].
  exists (fun l => i (proj1_sig (injective_enum Hi l))).
  intros l Hin. destruct (injective_enum Hi l) as [n Hnin]. exact (Hnin Hin).
  Qed.

  Lemma self_injective_minus (pi : self_injective X) : self_injective (minus (proj1_sig (projT3 pi))).
  Proof.
  destruct pi as [f Hinj [i Hi]]. cbn.
  assert (forall x, eqb i x = false -> eqb i (f x) = false) as Hif
    by (intros x _; apply eqb_neq, Hi).
  split with (fun a => exist _ (f (proj1_sig a)) (Hif (proj1_sig a) (proj2_sig a))).
  - intros [x Hx] [y Hy] Heq.
    inversion Heq as [Heq2].
    apply Hinj in Heq2 as ->.
    rewrite ((Eqdep_dec.UIP_dec bool_dec) _ _ Hx Hy). reflexivity.
  - assert (eqb i (f i) = false) as Hj by apply eqb_neq, Hi.
    split with (exist _ (f i) Hj).
    intros [y Hy]. cbn. intros Heq.
    inversion Heq as [Heq2].
    apply Hinj, eqb_neq in Heq2; assumption.
  Qed.

End InfiniteDec.

Arguments self_injective_minus {_} _.

Definition nat_of_self (X : DecType) (pi : self_injective X) n :
   { x | x = Nat.iter n (projT1 (sigT_of_sigT2 pi)) (proj1_sig (projT3 pi)) }
 * { Y : DecType & self_injective Y }.
Proof.
remember pi as HX. destruct pi as [f Hinj [i Hi]].
induction n as [|n IHn].
- split.
  + exists i. subst HX. reflexivity.
  + exists (minus (proj1_sig (projT3 HX))).
    apply (self_injective_minus HX).
- destruct IHn as [[y Hy] [Y HY]]. split.
  + exists (f y). subst y HX. reflexivity.
  + exists (minus (proj1_sig (projT3 HY))).
    apply (self_injective_minus HY).
Defined.

Lemma self_injective_nat (X : DecType) : self_injective X -> nat_injective X.
Proof.
intros HX.
exists (fun n => proj1_sig (fst (nat_of_self X HX n))).
intros x y Heq.
destruct (fst (nat_of_self X HX x)) as [n ->].
destruct (fst (nat_of_self X HX y)) as [m ->]. cbn in Heq.
destruct HX as [f Hinj [i Hi]]. cbn in Heq.
enough (forall x y, x < y -> Nat.iter x f i = Nat.iter y f i -> x = y) as Hlt.
{ case (Nat.compare_spec x y); intros Ho; [ exact Ho | | ].
  - apply Hlt; assumption.
  - symmetry. symmetry in Heq. apply Hlt; assumption. }
clear - Hinj Hi. intros x y Hlt Heq. exfalso.
remember (pred (y - x)) as n.
replace y with (S n + x) in Heq by lia. clear Heqn.
induction x in Hlt, Heq |- *.
- apply Hi in Heq as [].
- replace (S n + x) with (n + S x) in IHx by lia.
  apply IHx, Hinj; [ lia | assumption ].
Qed.


(** * Infinite Decidable Types
  (infinite) decidable types with freshness function *)

Record InfDecType := {
  infcar :> DecType;
  fresh : list infcar -> infcar;
  fresh_spec : forall l, ~ In (fresh l) l }.
Arguments fresh {_}.
Arguments fresh_spec {_}.

Section InfDecTypes.

  Variable X : InfDecType.

  Lemma infinite_nat_injective : nat_injective X.
  Proof. apply choice_nat_injective. exists fresh. apply fresh_spec. Qed.

  (* A list (of length [n]+1) of distinct fresh elements (not in [l]) *)
  Fixpoint freshlist_of_list (l : list X)  n :=
    match n with
    | 0 => fresh l :: nil
    | S k => let lv := freshlist_of_list l k in fresh (lv ++ l) :: lv
    end.

  Definition freshlist l n := hd (fresh l) (freshlist_of_list l n).

  Lemma freshlist_of_list_fresh l n x : In x (freshlist_of_list l n) -> ~ In x l.
  Proof.
  induction n; cbn; intros [Hin1 | Hin2] Hinl; subst.
  - exact (fresh_spec _ Hinl).
  - assumption.
  - apply fresh_spec with (freshlist_of_list l n ++ l).
    apply in_or_app. right. assumption.
  - exact (IHn Hin2 Hinl).
  Qed.

  Lemma freshlist_of_list_prefix l n m : n < m -> exists l',
    l' <> nil /\ freshlist_of_list l m = l' ++ freshlist_of_list l n.
  Proof.
  induction m as [|m IHm]; intros Hlt; [ lia | ].
  destruct (Nat.eq_dec n m); subst.
  - now exists (fresh (freshlist_of_list l m ++ l) :: nil).
  - assert (n < m) as [ l' [_ Heq] ]%IHm by lia.
    exists (fresh (freshlist_of_list l m ++ l) :: l').
    split ; [ | rewrite <- app_comm_cons, <- Heq; reflexivity ].
    intros [=].
  Qed.

  Lemma freshlist_of_list_NoDup l n : NoDup (freshlist_of_list l n).
  Proof.
  induction n; cbn; constructor; [ intros [] | constructor | | assumption ].
  intros Hin. apply fresh_spec with (freshlist_of_list l n ++ l).
  apply in_or_app. left. assumption.
  Qed.

  Lemma freshlist_fresh l n : ~ In (freshlist l n) l.
  Proof.
  intros Hin.
  assert (In (freshlist l n) (freshlist_of_list l n)) as Hin2
    by (destruct n; left; reflexivity).
  exact (freshlist_of_list_fresh _ _ _ Hin2 Hin).
  Qed.

  Lemma freshlist_inj l n m : freshlist l n = freshlist l m -> n = m.
  Proof.
  enough (forall n m, n < m -> freshlist l n = freshlist l m -> n = m) as Hlt.
  { intros Heq.
    case (Nat.compare_spec n m); intros Ho; [ exact Ho | | ].
    - apply Hlt, Heq. exact Ho.
    - symmetry. symmetry in Heq. apply Hlt; assumption. }
  clear. intros n m Hlt Heq. exfalso.
  apply freshlist_of_list_prefix with (l:= l) in Hlt as [ l' [Hnil Hprf] ].
  unfold freshlist in Heq. rewrite Hprf in Heq.
  destruct l'; [ apply Hnil; reflexivity | ]. cbn in Heq.
  destruct n; cbn in Heq, Hprf; rewrite Heq in Hprf.
  - assert (In c ((c :: l') ++ nil)) as Hin by (left; reflexivity).
    revert Hin. apply NoDup_remove_2. rewrite <- app_comm_cons, <- Hprf.
    apply (freshlist_of_list_NoDup l m).
  - assert (In c ((c :: l') ++ freshlist_of_list l n)) as Hin by (left; reflexivity).
    revert Hin. apply NoDup_remove_2. rewrite <- app_comm_cons, <- Hprf.
    apply (freshlist_of_list_NoDup l m).
  Qed.

  Definition Inh_of_InfDecType := {|
    inhcar := X;
    inh_dt := inhabits_inf (fresh nil) |}.

End InfDecTypes.

Arguments infinite_nat_injective {_}.
Arguments freshlist {_} _ _.
Arguments Inh_of_InfDecType _ : clear implicits.


(** [nat] instance of [InfDecType] *)
Definition nat_infdectype := {|
  infcar := nat_dectype;
  fresh := (proj1_sig (section_choice (nat_bijective_section (existT _ id (id_bijective)))));
  fresh_spec := (proj2_sig (section_choice (nat_bijective_section (existT _ id (id_bijective))))) |}.
(* alternative direct construction *)
Definition nat_fresh l := S (list_max l).
Lemma nat_fresh_spec l : ~ In (nat_fresh l) l.
Proof.
enough (forall n h, ~ In (n + nat_fresh (h ++ l)) l) as Hh
  by (rewrite <- (app_nil_l l) at 1; apply (Hh 0)).
induction l as [|a l IHl]; unfold nat_fresh; cbn; intros n h Hin; [ destruct Hin | ].
destruct Hin as [Hin|Hin].
- enough (a < n + S (list_max (h ++ a :: l))) by lia.
  clear. induction h; simpl; lia.
- apply IHl with n (h ++ a :: nil).
  rewrite <- app_assoc. exact Hin.
Qed.
(*
Definition nat_infdectype := {|
  infcar := nat_dectype;
  fresh := nat_fresh;
  fresh_spec := nat_fresh_spec |}.
*)

(** [option] construction of [InfDecType] *)
Lemma nat_injective_option (T : Type) : nat_injective T -> nat_injective (option T).
Proof.
intros [i Hi].
exists (fun n => Some (i n)).
intros n m [= Heq]. apply Hi, Heq.
Qed.

Definition option_infdectype (D : InfDecType) := {|
  infcar := option_dectype D;
  fresh := (proj1_sig (@nat_injective_choice (option_dectype D)
                      (nat_injective_option infinite_nat_injective)));
  fresh_spec := (proj2_sig (@nat_injective_choice (option_dectype D)
                           (nat_injective_option infinite_nat_injective))) |}.
(* alternative definition could use: fresh := fun L => Some (fresh (SomeDown L))
                               with: SomeDown := nil => nil
                                               | None :: r => SomeDown r
                                               | Some x :: r => x :: SomeDown r *)

(** [sum] constructions of [InfDecType] *)
Lemma nat_injective_suml (T1 T2 : Type) : nat_injective T1 -> nat_injective (sum T1 T2).
Proof.
intros [i Hi].
exists (fun n => inl (i n)).
intros n m [= Heq]. apply Hi, Heq.
Qed.

Definition suml_infdectype (D1 : InfDecType) (D2 : DecType) := {|
  infcar := sum_dectype D1 D2;
  fresh := (proj1_sig (@nat_injective_choice (sum_dectype D1 D2)
                      (nat_injective_suml _ infinite_nat_injective)));
  fresh_spec := (proj2_sig (@nat_injective_choice (sum_dectype D1 D2)
                           (nat_injective_suml _ infinite_nat_injective))) |}.
(* alternative definition could use direct definition of fresh *)

Lemma nat_injective_sumr (T1 T2 : Type) : nat_injective T2 -> nat_injective (sum T1 T2).
Proof.
intros [i Hi].
exists (fun n => inr (i n)).
intros n m [= Heq]. apply Hi, Heq.
Qed.

Definition sumr_infdectype (D1 : DecType) (D2 : InfDecType) := {|
  infcar := sum_dectype D1 D2;
  fresh := (proj1_sig (@nat_injective_choice (sum_dectype D1 D2)
                      (nat_injective_sumr _ infinite_nat_injective)));
  fresh_spec := (proj2_sig (@nat_injective_choice (sum_dectype D1 D2)
                (nat_injective_sumr _ infinite_nat_injective))) |}.
(* alternative definition could use direct definition of fresh *)

(** [prod] constructions of [InfDecType] *)
Section Prod.

  Variable (ID : InfDecType) (D : InhDecType).

  Definition prodl_fresh (l : list (prod ID D)) : prod ID D := (fresh (map fst l), inhabitant_inf inh_dt).

  Lemma notin_prodl_fresh l : ~ In (prodl_fresh l) l.
  Proof. intros Hin%(in_map fst). apply (fresh_spec _ Hin). Qed.

  Definition prodl_infdectype := {|
    infcar := prod_dectype ID D;
    fresh := prodl_fresh;
    fresh_spec := notin_prodl_fresh |}.

  Definition prodr_fresh (l : list (prod D ID)) : prod D ID := (inhabitant_inf inh_dt, fresh (map snd l)).

  Lemma notin_prodr_fresh l : ~ In (prodr_fresh l) l.
  Proof. intros Hin%(in_map snd). apply (fresh_spec _ Hin). Qed.

  Definition prodr_infdectype := {|
    infcar := prod_dectype D ID;
    fresh := prodr_fresh;
    fresh_spec := notin_prodr_fresh |}.

End Prod.

Definition prod_infdectype (ID1 ID2 : InfDecType) := prodl_infdectype ID1 (Inh_of_InfDecType ID2).

(** [list] construction of [InfDecType] *)
Lemma nat_injective_list (T : Type) : inhabited_inf T -> nat_injective (list T).
Proof.
intros [x]. exists (repeat x). intros n.
induction n as [|n IHn]; cbn; intros [|m] Heq; inversion Heq; [ reflexivity | ].
f_equal. apply IHn. assumption.
Qed.

Definition list_infdectype (D : InhDecType) := {|
  infcar := list_dectype D;
  fresh := (proj1_sig (@nat_injective_choice (list_dectype D) (nat_injective_list inh_dt)));
  fresh_spec := (proj2_sig (@nat_injective_choice (list_dectype D) (nat_injective_list inh_dt))) |}.
(* alternative definition could use: (x : D) : fresh := fun L => x :: concat L *)
