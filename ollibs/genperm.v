(* genperm Library *)

(** * Factorized statements for different notions of permutation *)

Require Import List Morphisms.
Require Import List_more Permutation_more funtheory Permutation_solve CyclicPerm CPermutation_solve.


(** ** Definitions
 parametrized by a boolean. *)

(** Permutation or cyclic permutation *)
Definition PCperm {A} (b : bool) :=
  if b then @Permutation A else @CPermutation A.

(** Permutation or equality *)
Definition PEperm {A} (b : bool) :=
  if b then @Permutation A else @eq (list A).


(** ** Permutation or cyclic permutation *)

(** unfolding into [Permutation] or [CPermutation] *)
Ltac hyps_PCperm_unfold :=
  match goal with
  | H : PCperm _ _ _ |- _ => unfold PCperm in H ; hyps_PCperm_unfold
  | _ => idtac
  end.

(** automatic solving *)
Ltac PCperm_solve :=
  hyps_PCperm_unfold ;
  simpl ;
  match goal with
  | |- PCperm ?b _ _ => unfold PCperm ; destruct b ;
                        simpl ; PCperm_solve
  | |- Permutation _ _  => perm_solve
  | |- CPermutation _ _  => cperm_solve
  end.

(** *** Properties *)

Instance PCperm_perm {A} b : Proper (PCperm b ==> (@Permutation A)) id.
Proof with try assumption.
destruct b ; intros l l' HP...
apply cperm_perm...
Qed.

Instance cperm_PCperm {A} b : Proper (CPermutation ==> PCperm b) (@id (list A)).
Proof with try assumption.
destruct b ; intros l l' HC...
apply cperm_perm...
Qed.

Lemma PCperm_monot {A} : forall b1 b2, Bool.leb b1 b2 ->
  forall l1 l2 : list A, PCperm b1 l1 l2 -> PCperm b2 l1 l2.
Proof.
intros b1 b2 Hleb l1 l2.
destruct b1; destruct b2; try (now inversion Hleb).
apply cperm_perm.
Qed.

Instance PCperm_refl {A} b : Reflexive (@PCperm A b).
Proof.
destruct b ; intros l ; reflexivity.
Qed.

Instance PCperm_sym {A} b : Symmetric (@PCperm A b).
Proof.
destruct b ; intros l l' ; symmetry ; assumption.
Qed.

Instance PCperm_trans {A} b : Transitive (@PCperm A b).
Proof.
destruct b ; intros l l' l'' ; etransitivity ; eassumption.
Qed.

Instance PCperm_equiv {A} b : Equivalence (@PCperm A b).
Proof.
split.
- apply PCperm_refl.
- apply PCperm_sym.
- apply PCperm_trans.
Qed.

Lemma PCperm_swap {A} b : forall (a1 : A) a2,
  PCperm b (a1 :: a2 :: nil) (a2 :: a1 :: nil).
Proof.
destruct b ; intros.
- apply perm_swap.
- apply cperm_swap.
Qed.

Lemma PCperm_last {A} b : forall (a : A) l, PCperm b (a :: l) (l ++ a :: nil).
Proof.
destruct b ; intros ;
  rewrite <- (app_nil_l l) ; rewrite app_comm_cons.
- apply Permutation_cons_append.
- apply cperm_last.
Qed.

Lemma PCperm_app_comm {A} b : forall l l', @PCperm A b (l ++ l') (l' ++ l).
Proof.
destruct b ; intros.
- apply Permutation_app_comm.
- apply cperm.
Qed.

Lemma PCperm_app_rot {A} b : forall l1 l2 l3,
  @PCperm A b  (l1 ++ l2 ++ l3) (l2 ++ l3 ++ l1).
Proof.
destruct b ; intros.
- apply Permutation_app_rot.
- apply cperm_app_rot.
Qed.

Lemma PCperm_nil {A} b : forall l, @PCperm A b nil l -> l = nil.
Proof with try assumption.
destruct b ; intros.
- apply Permutation_nil...
- apply cperm_nil...
Qed.

Lemma PCperm_nil_cons {A} b : forall l (a : A), ~ PCperm b nil (a :: l).
Proof with try assumption.
destruct b ; intros.
- apply Permutation_nil_cons...
- apply cperm_nil_cons...
Qed.

Lemma PCperm_length_1_inv {A} b : forall (a : A) l,
  PCperm b (a :: nil) l -> l = a :: nil.
Proof with try assumption.
destruct b ; intros.
- apply Permutation_length_1_inv...
- apply cperm_one_inv...
Qed.

Lemma PCperm_length_2_inv {A} b : forall (a1 : A) a2 l,
  PCperm b (a1 :: a2 :: nil) l -> l = a1 :: a2 :: nil \/ l = a2 :: a1 :: nil.
Proof with try assumption.
destruct b ; intros.
- apply Permutation_length_2_inv...
- apply cperm_two_inv...
Qed.

Lemma PCperm_vs_elt_inv {A} b : forall (a : A) l l1 l2,
  PCperm b l (l1 ++ a :: l2) ->  exists l' l'',
    PEperm b (l2 ++ l1) (l'' ++ l') /\ l = l' ++ a :: l''.
Proof with try reflexivity.
destruct b ; intros a l l1 l2 HC.
- assert (Heq := HC).
  apply Permutation_vs_elt_inv in Heq.
  destruct Heq as (l' & l'' & Heq) ; subst.
  exists l' ; exists l'' ; split...
  apply Permutation_app_inv in HC.
  symmetry in HC.
  etransitivity ; [ eapply Permutation_app_comm | ].
  etransitivity ; [ eassumption | ].
  apply Permutation_app_comm.
- apply cperm_vs_elt_inv in HC.
  destruct HC as (l' & l'' & Heq1 & Heq2) ; subst.
  exists l' ; exists l'' ; split...
  rewrite Heq1...
Qed.

Lemma PCperm_vs_cons_inv {A} b : forall (a : A) l l1,
  PCperm b l (a :: l1) -> exists l' l'',
    PEperm b l1 (l'' ++ l') /\ l = l' ++ a :: l''.
Proof.
intros a l l1 HP.
rewrite <- app_nil_l in HP.
apply PCperm_vs_elt_inv in HP.
destruct HP as (l' & l'' & HP & Heq) ; subst.
exists l' ; exists l'' ; split.
- rewrite app_nil_r in HP.
  apply HP.
- reflexivity.
Qed.

Lemma PCperm_cons_cons_inv {A} b : forall (a : A) l l1, ~ In a l -> ~ In a l1 ->
  PCperm b (a :: l) (a :: l1) -> PEperm b l l1.
Proof.
intros a l l1 Hin1 Hin2 HP.
destruct b.
- now apply Permutation_cons_inv with a.
- assert (HP' := HP).
  rewrite <- app_nil_l in HP; apply PCperm_vs_elt_inv in HP; rewrite app_nil_r in HP.
  destruct HP as (l' & l'' & HP & Heq) ; subst.
  rewrite HP; simpl.
  destruct l'; inversion Heq; subst.
  + symmetry; apply app_nil_r.
  + exfalso; apply Hin1.
    apply in_elt.
Qed.

Instance PCperm_map {A B} (f : A -> B) b :
  Proper (PCperm b ==> PCperm b) (map f).
Proof with try assumption.
destruct b ; intros l1 l2 HC.
- apply Permutation_map...
- apply cperm_map...
Qed.

Lemma PCperm_map_inv {A B} b : forall (f : A -> B) l1 l2,
  PCperm b l1 (map f l2) -> exists l3, l1 = map f l3 /\ PCperm b l2 l3.
Proof.
destruct b ; intros.
- eapply Permutation_map_inv ; eassumption.
- eapply cperm_map_inv ; eassumption.
Qed.

Instance PCperm_in {A} b (a : A) : Proper (PCperm b ==> Basics.impl) (In a).
Proof with try eassumption.
destruct b ; intros l l' HP HIn.
- eapply Permutation_in...
- eapply cperm_in...
Qed.

Instance PCperm_Forall {A} b (P : A -> Prop) :
  Proper (PCperm b ==> Basics.impl) (Forall P).
Proof with try eassumption.
destruct b ; intros l1 l2 HP HF.
- eapply Permutation_Forall...
- eapply cperm_Forall...
Qed.

Instance PCperm_Exists {A} b (P : A -> Prop) :
  Proper (PCperm b ==> Basics.impl) (Exists P).
Proof with try eassumption.
destruct b ; intros l1 l2 HP HE.
- eapply Permutation_Exists...
- eapply cperm_Exists...
Qed.

Lemma PCperm_Forall2 {A B} b (P : A -> B -> Prop) :
  forall l1 l1' l2, PCperm b l1 l1' -> Forall2 P l1 l2 -> exists l2',
    PCperm b l2 l2' /\ Forall2 P l1' l2'.
Proof.
destruct b ; [ apply Permutation_Forall2 | apply cperm_Forall2 ].
Qed.

Lemma PCperm_image {A B} b : forall (f : A -> B) a l l',
  PCperm b (a :: l) (map f l') -> exists a', a = f a'.
Proof with try eassumption.
destruct b ; intros.
- eapply Permutation_image...
- eapply cperm_image...
Qed.


(** ** Permutation or equality *)

(** unfolding into [Permutation] or [eq] and automatic solving *)
Ltac hyps_PEperm_unfold :=
  match goal with
  | H : PEperm _ _ _ |- _ => unfold PEperm in H ; hyps_PEperm_unfold
  | _ => idtac
  end.

(** automatic solving *)
Ltac PEperm_solve :=
  hyps_PEperm_unfold ;
  simpl ;
  match goal with
  | |- PEperm ?b _ _ => unfold PEperm ; destruct b ;
                        simpl ; PEperm_solve
  | |- Permutation _ _  => perm_solve
  | |- eq _ _  => reflexivity
  end.

(** *** Properties *)

Instance PEperm_perm {A} b : Proper (PEperm b ==> (@Permutation A)) id.
Proof.
destruct b ; intros l l' HP ; simpl in HP ; now subst.
Qed.

Lemma PEperm_monot {A} : forall b1 b2, Bool.leb b1 b2 ->
  forall l1 l2 : list A, PEperm b1 l1 l2 -> PEperm b2 l1 l2.
Proof.
intros b1 b2 Hleb l1 l2.
destruct b1; destruct b2; try (now inversion Hleb).
simpl; intros HP; subst; reflexivity.
Qed.

Instance PEperm_refl {A} b : Reflexive (@PEperm A b).
Proof.
destruct b ; intros l ; reflexivity.
Qed.

Instance PEperm_sym {A} b : Symmetric (@PEperm A b).
Proof.
destruct b ; intros l l' ; symmetry ; assumption.
Qed.

Instance PEperm_trans {A} b : Transitive (@PEperm A b).
Proof.
destruct b ; intros l l' l'' ; etransitivity ; eassumption.
Qed.

Instance PEperm_equiv {A} b : Equivalence (@PEperm A b).
Proof.
split.
- apply PEperm_refl.
- apply PEperm_sym.
- apply PEperm_trans.
Qed.

Instance eq_PEperm {A} b : Proper (eq ==> PEperm b) (@id (list A)).
Proof.
intros l l' Heq ; subst ; reflexivity.
Qed.

Instance PEperm_cons {A} b :
  Proper (eq ==> PEperm b ==> PEperm b) (@cons A).
Proof.
destruct b ; intros x y Heq l1 l2 HP ; subst.
- now apply Permutation_cons.
- now rewrite HP.
Qed.

Instance PEperm_app {A} b : Proper (PEperm b ==> PEperm b ==> PEperm b) (@app A).
Proof.
destruct b ; simpl ; intros l m HP1 l' m' HP2.
- now apply Permutation_app.
- now subst.
Qed.

Lemma PEperm_app_tail {A} b : forall l l' tl,
  @PEperm A b l l' -> PEperm b (l ++ tl) (l' ++ tl).
Proof.
destruct b ; simpl ; intros l l' tl HP.
- now apply Permutation_app_tail.
- now subst.
Qed.

Lemma PEperm_app_head {A} b : forall l tl tl',
  @PEperm A b tl tl' -> PEperm b (l ++ tl) (l ++ tl').
Proof.
destruct b ; simpl ; intros l tl tl' HP.
- now apply Permutation_app_head.
- now subst.
Qed.

Lemma PEperm_add_inside {A} b : forall (a : A) l l' tl tl',
  PEperm b l l' -> PEperm b tl tl' -> PEperm b (l ++ a :: tl) (l' ++ a :: tl').
Proof.
destruct b ; simpl ; intros a l l' tl tl' HP1 HP2.
- now apply Permutation_add_inside.
- now subst.
Qed.

Lemma PEperm_nil {A} b : forall l, @PEperm A b nil l -> l = nil.
Proof with try assumption.
destruct b ; intros.
- apply Permutation_nil...
- symmetry...
Qed.

Lemma PEperm_nil_cons {A} b : forall l (a : A), ~ PEperm b nil (a :: l).
Proof with try assumption.
destruct b ; intros.
- apply Permutation_nil_cons...
- intro Heq ; inversion Heq.
Qed.

Lemma PEperm_length_1_inv {A} b : forall (a : A) l,
  PEperm b (a :: nil) l -> l = a :: nil.
Proof with try assumption.
destruct b ; intros.
- apply Permutation_length_1_inv...
- symmetry...
Qed.

Lemma PEperm_length_2_inv {A} b : forall (a1 : A) a2 l,
  PEperm b (a1 :: a2 :: nil) l -> l = a1 :: a2 :: nil \/ l = a2 :: a1 :: nil.
Proof with try assumption.
destruct b ; intros.
- apply Permutation_length_2_inv...
- left ; symmetry...
Qed.

Lemma PEperm_vs_elt_inv {A} b : forall (a : A) l l1 l2,
  PEperm b l (l1 ++ a :: l2) -> exists l3 l4,
    PEperm b (l1 ++ l2) (l3 ++ l4) /\ l = l3 ++ a :: l4.
Proof.
destruct b ; intros a l l1 l2 HP.
- assert (HP' := HP).
  apply Permutation_vs_elt_inv in HP'.
  destruct HP' as (l' & l'' & Heq) ; subst.
  apply Permutation_app_inv in HP.
  symmetry in HP.
  eexists ; eexists ; split.
  + eassumption.
  + reflexivity.
- exists l1 ; exists l2.
  rewrite HP.
  split ; reflexivity.
Qed.

Lemma PEperm_vs_cons_inv {A} b : forall (a : A) l l1,
  PEperm b l (a :: l1) -> exists l2 l3,
    PEperm b l1 (l2 ++ l3) /\ l = l2 ++ a :: l3.
Proof.
intros a l l1 HP.
rewrite <- (app_nil_l l1).
eapply PEperm_vs_elt_inv.
assumption.
Qed.

Instance PEperm_in {A} b (a : A) : Proper (PEperm b ==> Basics.impl) (In a).
Proof with try eassumption.
destruct b ; simpl ; intros l l' HP HIn.
- eapply Permutation_in...
- subst...
Qed.

Instance PEperm_Forall {A} b (P : A -> Prop) :
  Proper (PEperm b ==> Basics.impl) (Forall P).
Proof with try eassumption.
destruct b ; simpl ; intros l1 l2 HP HF.
- eapply Permutation_Forall...
- subst...
Qed.

Instance PEperm_Exists {A} b (P : A -> Prop) :
  Proper (PEperm b ==> Basics.impl) (Exists P).
Proof with try eassumption.
destruct b ; simpl ; intros l1 l2 HP HF.
- eapply Permutation_Exists...
- subst...
Qed.

Lemma PEperm_Forall2 {A B} b (P : A -> B -> Prop) :
  forall l1 l1' l2, PEperm b l1 l1' -> Forall2 P l1 l2 -> exists l2',
    PCperm b l2 l2' /\ Forall2 P l1' l2'.
Proof.
destruct b ; [ apply Permutation_Forall2 | ].
intros l1 l1' l2 HE HF ; simpl in HE ; subst.
exists l2 ; split ; [ reflexivity | assumption ].
Qed.

Instance PEperm_map {A B} (f : A -> B) b :
  Proper (PEperm b ==> PEperm b) (map f).
Proof.
destruct b ; intros l l' HP.
- apply Permutation_map.
  assumption.
- simpl in HP ; subst.
  reflexivity.
Qed.

Lemma PEperm_map_inv {A B} b : forall (f : A -> B) l1 l2,
  PEperm b l1 (map f l2) -> exists l3, l1 = map f l3 /\ PEperm b l2 l3.
Proof.
destruct b ; simpl ; intros f l1 l2 HP.
- eapply Permutation_map_inv ; eassumption.
- subst.
  exists l2 ; split ; reflexivity.
Qed.

Instance PEperm_rev {A} b : Proper (PEperm b ==> PEperm b) (@rev A).
Proof.
destruct b ; intros l1 l2 HP.
- now apply Permutation_rev'.
- now (simpl in HP ; subst).
Qed.

Lemma PEperm_map_inv_inj {A B} b : forall f : A -> B, injective f ->
  forall l1 l2, PEperm b (map f l1) (map f l2) -> PEperm b l1 l2.
Proof with try assumption.
destruct b ; intros f Hi l1 l2 HP.
- apply Permutation_map_inv_inj in HP...
- apply map_injective in HP...
Qed.

Lemma PEperm_image {A B} b : forall (f : A -> B) a l l',
  PEperm b (a :: l) (map f l') -> exists a', a = f a'.
Proof.
destruct b ; intros.
- eapply Permutation_image ; eassumption.
- destruct l' ; inversion H ; subst.
  exists a0 ; reflexivity.
Qed.


(** ** From PEperm to PCperm *)

Instance PEperm_PCperm {A} b : Proper (PEperm b ==> PCperm b) (@id (list A)).
Proof.
destruct b ; simpl ; intros l l' HP ; now subst.
Qed.

Instance PEperm_PCperm_cons {A} b :
  Proper (eq ==> PEperm b ==> PCperm b) (@cons A).
Proof.
intros x y Heq l1 l2 HP ; subst.
apply PEperm_PCperm.
rewrite HP.
reflexivity.
Qed.

Instance PEperm_PCperm_app {A} b :
  Proper (PEperm b ==> PEperm b ==> PCperm b) (@app A).
Proof.
intros l1 l1' HPhd l2 l2' HPtl.
apply PEperm_PCperm.
rewrite HPhd.
rewrite HPtl.
reflexivity.
Qed.

