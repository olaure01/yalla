(* List_Type_ Library *)

(** * Copy of some List library with parameters with Type output *)


Require Export List.

Set Implicit Arguments.


Section In.

Variable A:Type.

Fixpoint In_Type (a:A) (l:list A) : Type :=
    match l with
      | nil => False
      | b :: m => sum (b = a) (In_Type a m)
    end.

  Lemma in_Type_in : forall (a : A) l, In_Type a l -> In a l.
  Proof.
  induction l; intros Hin; inversion Hin; try now constructor.
  right; intuition.
  Qed.

  Lemma notin_Type_notin : forall (a : A) l, (In_Type a l -> False) -> ~ In a l.
  Proof.
  induction l; intros Hnin Hin; inversion Hin; subst.
  - apply Hnin; constructor; reflexivity.
  - apply IHl; [ | assumption ].
    intros Hin2; apply Hnin.
    right; assumption.
  Qed.

  (** Characterization of [In] *)

  Theorem in_Type_eq : forall (a:A) (l:list A), In_Type a (a :: l).
  Proof.
    simpl; auto.
  Qed.

  Theorem in_Type_cons : forall (a b:A) (l:list A), In_Type b l -> In_Type b (a :: l).
  Proof.
    simpl; auto.
  Qed.

  Theorem not_in_Type_cons (x a : A) (l : list A):
    (In_Type x (a::l) -> False) -> (x<>a) * (In_Type x l -> False).
  Proof.
    simpl. intuition.
  Qed.

  Theorem cons_not_in_Type (x a : A) (l : list A):
    x<>a -> (In_Type x l -> False) -> In_Type x (a::l) -> False.
  Proof.
    simpl. intuition.
  Qed.

  Theorem in_Type_nil : forall a:A, In_Type a nil -> False.
  Proof.
    unfold not; intros a H; inversion_clear H.
  Qed.

  Theorem in_Type_split : forall x (l:list A), In_Type x l ->
    { '(l1,l2) | l = l1 ++  x:: l2 }.
  Proof.
  induction l; simpl; destruct 1.
  subst a; auto.
  exists (nil, l) ; auto.
  destruct (IHl i) as ((l1,l2),H0).
  exists (a::l1, l2); simpl. apply f_equal. auto.
  Qed.

  (** Inversion *)
  Lemma in_Type_inv : forall (a b:A) (l:list A), In_Type b (a :: l) ->
    sum (a = b) (In_Type b l).
  Proof.
    intros a b l H; inversion_clear H; auto.
  Qed.

  (** Decidability of [In] *)
  Theorem in_Type_dec :
    (forall x y:A, {x = y} + {x <> y}) ->
    forall (a:A) (l:list A), (In_Type a l) + (In_Type a l -> False).
  Proof.
    intro H; induction l as [| a0 l IHl].
    right; apply in_Type_nil.
    destruct (H a0 a); simpl; auto.
    destruct IHl; simpl; auto.
    right; unfold not; intros [Hc1| Hc2]; auto.
  Defined.

  (** Compatibility with other operations *)
  Lemma in_Type_app_or : forall (l m:list A) (a:A), In_Type a (l ++ m) ->
    In_Type a l + In_Type a m.
  Proof.
    intros l m a.
    elim l; simpl; auto.
    intros a0 y H H0.
    now_show (sum (sum (a0 = a) (In_Type a y)) (In_Type a m)).
    elim H0; auto.
    intro H1.
    now_show (sum (sum (a0 = a) (In_Type a y)) (In_Type a m)).
    elim (H H1); auto.
  Qed.

  Lemma in_Type_or_app : forall (l m:list A) (a:A),
    sum (In_Type a l) (In_Type a m) -> In_Type a (l ++ m).
  Proof.
    intros l m a.
    elim l; simpl; intro H.
    now_show (In_Type a m).
    elim H; auto; intro H0.
    now_show (In_Type a m).
    elim H0. (* subProof completed *)
    intros y H0 H1.
    destruct H1 ; intuition.
  Qed.

End In.

Hint Resolve in_Type_eq in_Type_cons in_Type_inv in_Type_nil in_Type_app_or
  in_Type_or_app: datatypes.


  (**************************)
  (** Facts about [app] *)
  (**************************)

Section App.


  Variable A : Type.

  (** Facts deduced from the result of a concatenation *)

  Theorem app_eq_nil_Type : forall l l':list A, l ++ l' = nil -> (l = nil) * (l' = nil).
  Proof.
    destruct l as [| x l]; destruct l' as [| y l']; simpl; auto.
    intro; discriminate.
    intros H; discriminate H.
  Qed.

  Theorem app_eq_unit_Type :
    forall (x y:list A) (a:A),
      x ++ y = a::nil -> ((x = nil) * (y = a::nil)) + ((x = a::nil) * (y = nil)).
  Proof.
    destruct x as [| a l]; [ destruct y as [| a l] | destruct y as [| a0 l0] ];
      simpl.
    intros a H; discriminate H.
    left; split; auto.
    right; split; auto.
    generalize H.
    generalize (app_nil_r l); intros E.
    rewrite -> E; auto.
    intros.
    injection H as H H0.
    assert (nil = l ++ a0 :: l0) by auto.
    apply app_cons_not_nil in H1 as [].
  Qed.

End App.

(*******************************************)
(** * Operations on the elements of a list *)
(*******************************************)

Section Elts.

  Variable A : Type.

  (*****************)
  (** ** Remove    *)
  (*****************)

  Hypothesis eq_dec : forall x y : A, {x = y}+{x <> y}.

  Theorem remove_In_Type : forall (l : list A) (x : A), In_Type x (remove eq_dec x l) -> False.
  Proof.
    induction l as [|x l]; auto.
    intro y; simpl; destruct (eq_dec y x) as [yeqx | yneqx].
    apply IHl.
    unfold not; intro HF; simpl in HF; destruct HF; auto.
    apply (IHl y); assumption.
  Qed.

End Elts.


(*********************************************)
(** Reverse Induction Principle on Lists  *)
(*********************************************)

  Section Reverse_Induction.

  Variable A : Type.

    Lemma rev_list_ind_Type :
      forall P:list A-> Type,
	P nil ->
	(forall (a:A) (l:list A), P (rev l) -> P (rev (a :: l))) ->
	forall l:list A, P (rev l).
    Proof.
      induction l; auto.
    Qed.

    Theorem rev_ind_Type :
      forall P:list A -> Type,
	P nil ->
	(forall (x:A) (l:list A), P l -> P (l ++ x :: nil)) -> forall l:list A, P l.
    Proof.
      intros.
      generalize (rev_involutive l).
      intros E; rewrite <- E.
      apply (rev_list_ind_Type P).
      - auto.
      - simpl.
        intros.
        apply (X0 a (rev l0)).
        auto.
    Qed.

  End Reverse_Induction.


(***************************************************)
(** * Applying functions to the elements of a list *)
(***************************************************)

(************)
(** ** Map  *)
(************)

Section Map.
  Variables (A : Type) (B : Type).
  Variable f : A -> B.

  Lemma in_Type_map :
    forall (l:list A) (x:A), In_Type x l -> In_Type (f x) (map f l).
  Proof.
    induction l; firstorder (subst; auto).
  Qed. 

  Lemma in_Type_map_inv : forall l y, In_Type y (map f l) ->
    { x & prod (f x = y) (In_Type x l) }.
  Proof.
    induction l; firstorder (subst; auto).
  Qed.

  Lemma in_Type_flat_map : forall (f:A->list B)(l:list A)(y:B),
    In_Type y (flat_map f l) -> { x & prod (In_Type x l) (In_Type y (f x)) }.
  Proof using A B.
    induction l; simpl; intros.
    contradiction.
    destruct (in_Type_app_or _ _ _ X).
    - exists a; auto.
    - destruct (IHl y i) as (x,(H1,H2)).
      exists x; auto.
  Qed.

  Lemma flat_map_in_Type : forall (f:A->list B)(l:list A)(y:B),
    { x & prod (In_Type x l) (In_Type y (f x)) } -> In_Type y (flat_map f l).
  Proof using A B.
    induction l; simpl; intros.
    destruct X as (x,(X,_)); contradiction.
    apply in_Type_or_app.
    destruct X as (x,(H0,H1)); destruct H0.
    - subst; auto.
    - right ; apply (IHl y (existT _ x (i,H1))).
  Qed.

End Map.

Lemma map_ext_in_Type :
  forall (A B : Type)(f g:A->B) l, (forall a, In_Type a l -> f a = g a) -> map f l = map g l.
Proof.
  induction l; simpl; auto.
  intros; rewrite H by intuition; rewrite IHl; auto.
Qed.

Lemma ext_in_Type_map :
  forall (A B : Type)(f g:A->B) l, map f l = map g l -> forall a, In_Type a l -> f a = g a.
Proof. induction l; intros [=] ? []; subst; auto. Qed.

Arguments ext_in_Type_map [A B f g l].


(******************************)
(** ** Set inclusion on list  *)
(******************************)

Section SetIncl.

  Variable A : Type.

  Definition incl_Type (l m:list A) := forall a:A, In_Type a l -> In_Type a m.
  Hint Unfold incl_Type : core.

  Lemma incl_Type_refl : forall l:list A, incl_Type l l.
  Proof.
    auto.
  Qed.
  Hint Resolve incl_Type_refl : core.

  Lemma incl_Type_tl : forall (a:A) (l m:list A), incl_Type l m -> incl_Type l (a :: m).
  Proof.
    unfold incl_Type ; intros.
    simpl ; intuition.
  Qed.
  Hint Immediate incl_Type_tl : core.

  Lemma incl_Type_tran : forall l m n:list A, incl_Type l m -> incl_Type m n -> incl_Type l n.
  Proof.
    auto.
  Qed.

  Lemma incl_Type_appl : forall l m n:list A, incl_Type l n -> incl_Type l (n ++ m).
  Proof.
    auto with datatypes.
  Qed.
  Hint Immediate incl_Type_appl : core.

  Lemma incl_Type_appr : forall l m n:list A, incl_Type l n -> incl_Type l (m ++ n).
  Proof.
    auto with datatypes.
  Qed.
  Hint Immediate incl_Type_appr : core.

  Lemma incl_Type_cons :
    forall (a:A) (l m:list A), In_Type a m -> incl_Type l m -> incl_Type (a :: l) m.
  Proof.
    unfold incl_Type; simpl; intros a l m H H0 a0 H1.
    now_show (In_Type a0 m).
    elim H1.
    now_show (a = a0 -> In_Type a0 m).
    elim H1; auto; intro H2.
    now_show (a = a0 -> In_Type a0 m).
    elim H2; auto. (* solves subgoal *)
    now_show (In_Type a0 l -> In_Type a0 m).
    auto.
  Qed.
  Hint Resolve incl_Type_cons : core.

  Lemma incl_Type_app : forall l m n:list A, incl_Type l n -> incl_Type m n ->
    incl_Type (l ++ m) n.
  Proof.
    unfold incl_Type; simpl; intros l m n H H0 a H1.
    now_show (In_Type a n).
    elim (in_Type_app_or _ _ _ H1); auto.
  Qed.
  Hint Resolve incl_Type_app : core.

End SetIncl.

Hint Resolve incl_Type_refl incl_Type_tl incl_Type_tran incl_Type_appl incl_Type_appr
  incl_Type_cons incl_Type_app: datatypes.


(********************************)
(** ** Lists without redundancy *)
(********************************)

Section ReDun.

  Variable A : Type.

  Inductive NoDup_Type : list A -> Type :=
    | NoDup_Type_nil : NoDup_Type nil
    | NoDup_Type_cons : forall x l, (In_Type x l -> False) -> NoDup_Type l -> NoDup_Type (x::l).

  Lemma NoDup_NoDup_Type : forall l : list A, NoDup l -> NoDup_Type l.
  Proof.
  induction l; intros Hnd; constructor.
  - intros Hnin.
    apply in_Type_in in Hnin.
    inversion Hnd; intuition.
  - apply IHl; now inversion Hnd.
  Qed.

  Lemma NoDup_Type_NoDup : forall l : list A, NoDup_Type l -> NoDup l.
  Proof.
  induction l; intros Hnd; constructor.
  - apply notin_Type_notin; intros Hnin.
    inversion Hnd; intuition.
  - apply IHl; now inversion Hnd.
  Qed.

  Theorem NoDup_Type_cons_imp a l:
    NoDup_Type (a::l) -> (In_Type a l -> False) * NoDup_Type l.
  Proof.
    intros Hd; inversion Hd; subst; split; assumption.
  Qed.

End ReDun.

(** NoDup and map *)

(** NB: the reciprocal result holds only for injective functions,
    see FinFun.v *)

Lemma NoDup_Type_map_inv A B (f:A->B) l : NoDup_Type (map f l) -> NoDup_Type l.
Proof.
 induction l; simpl; inversion_clear 1; subst; constructor; auto.
 intro Hin. now apply (in_Type_map f) in Hin.
Qed.

(***********************************)
(** ** Sequence of natural numbers *)
(***********************************)

Section NatSeq.

  (** [seq] computes the sequence of [len] contiguous integers
      that starts at [start]. For instance, [seq 2 3] is [2::3::4::nil]. *)

  Lemma in_Type_seq len start n :
    In_Type n (seq start len) -> start <= n < start+len.
  Proof.
   revert start. induction len; simpl; intros.
   - inversion H.
   - rewrite <- plus_n_Sm.
     destruct X; subst.
     + intuition auto with arith.
     + apply IHlen in i.
       intuition auto with arith.
  Qed.

  Lemma seq_in_Type len start n :
    start <= n < start+len -> In n (seq start len).
  Proof.
   revert start. induction len; simpl; intros.
   - inversion_clear H.
     rewrite <- plus_n_O in H1.
     apply (Lt.lt_irrefl _ (Lt.le_lt_trans _ _ _ H0 H1)).
   - destruct H.
     destruct (Lt.le_lt_or_eq _ _ H); intuition.
     right; apply IHlen.
     rewrite <- plus_n_Sm in H0.
     intuition auto with arith.
  Qed.

  Lemma seq_NoDup_Type len start : NoDup_Type (seq start len).
  Proof.
   revert start; induction len; simpl; constructor; trivial.
   intros Hin; apply in_Type_seq in Hin.
   destruct Hin as [H _].
   apply (Lt.lt_irrefl _ H).
  Qed.

End NatSeq.

Section Exists_Forall.

  (** * Existential and universal predicates over lists *)

  Variable A:Type.

  Section One_predicate.

    Variable P:A->Type.

    Inductive Exists_Type : list A -> Type :=
      | Exists_Type_cons_hd : forall x l, P x -> Exists_Type (x::l)
      | Exists_Type_cons_tl : forall x l, Exists_Type l -> Exists_Type (x::l).

    Hint Constructors Exists_Type : core.

    Lemma Exists_Type_nil : Exists_Type nil -> False.
    Proof. inversion 1. Qed.

    Lemma Exists_Type_cons x l:
      Exists_Type (x::l) -> P x + Exists_Type l.
    Proof. inversion 1; auto. Qed.

    Lemma Exists_Type_dec l:
      (forall x:A, P x + (P x -> False)) ->
      Exists_Type l + (Exists_Type l -> False).
    Proof.
      intro Pdec. induction l as [|a l' Hrec].
      - right. now apply Exists_Type_nil.
      - destruct Hrec as [Hl'|Hl'].
        * left. now apply Exists_Type_cons_tl.
        * destruct (Pdec a) as [Ha|Ha].
          + left. now apply Exists_Type_cons_hd.
          + right. now inversion_clear 1.
    Qed.

    Inductive Forall_Type : list A -> Type :=
      | Forall_Type_nil : Forall_Type nil
      | Forall_Type_cons : forall x l, P x -> Forall_Type l -> Forall_Type (x::l).

    Hint Constructors Forall_Type : core.

    Lemma Forall_Type_forall (l:list A):
      Forall_Type l -> forall x, In_Type x l -> P x.
    Proof.
      induction 1; firstorder; subst; auto.
    Qed.

    Lemma forall_Forall_Type (l:list A):
      (forall x, In_Type x l -> P x) -> Forall_Type l.
    Proof.
      induction l; firstorder.
    Qed.

    Lemma Forall_Type_inv : forall (a:A) l, Forall_Type (a :: l) -> P a.
    Proof.
      intros ? ? H ; inversion H ; trivial.
    Qed.

    Lemma Forall_Type_dec :
      (forall x:A, P x + (P x -> False)) ->
      forall l:list A, Forall_Type l + (Forall_Type l -> False).
    Proof.
      intro Pdec. induction l as [|a l' Hrec].
      - left. apply Forall_Type_nil.
      - destruct Hrec as [Hl'|Hl'].
        + destruct (Pdec a) as [Ha|Ha].
          * left. now apply Forall_Type_cons.
          * right. abstract now inversion 1.
        + right. abstract now inversion 1.
    Defined.

  End One_predicate.

  Lemma Forall_Exists_neg_Type (P:A->Type)(l:list A) :
   Forall_Type (fun x => P x -> False) l -> Exists_Type P l -> False.
  Proof.
   induction l ; intros HF HE ; inversion HE ; inversion HF ; subst ; auto.
  Qed.

  Lemma Exists_neg_Forall_Type (P:A->Type)(l:list A) :
   (Exists_Type P l -> False) -> Forall_Type (fun x => P x -> False) l.
  Proof.
   induction l ; intros HE ; constructor.
   - intros Ha ; apply HE.
     now constructor.
   - apply IHl ; intros HF ; apply HE.
     now constructor.
  Qed.

  Lemma Exists_Forall_neg_Type (P:A->Type)(l:list A) :
    Exists_Type (fun x => P x -> False) l -> Forall_Type P l -> False.
  Proof.
   induction l ; intros HE HF ; inversion HE ; inversion HF ; subst ; auto.
  Qed.

  Lemma Forall_neg_Exists_Type (P:A->Type)(l:list A) :
    (forall x, P x + (P x -> False)) ->
    (Forall_Type P l -> False) -> Exists_Type (fun x => P x -> False) l.
  Proof.
   intro Dec.
   induction l ; intros HF.
   - contradiction HF. constructor.
   - destruct (Dec a) as [ Ha | Hna ].
     + apply Exists_Type_cons_tl.
       apply IHl.
       intros HFl.
       apply HF ; now constructor.
     + now apply Exists_Type_cons_hd.
  Qed.

  Lemma neg_Forall_Exists_neg_Type (P:A->Type) (l:list A) :
    (forall x:A, P x + (P x -> False)) ->
    (Forall_Type P l -> False) ->
    Exists_Type (fun x => (P x -> False)) l.
  Proof.
    intro Dec.
    apply Forall_neg_Exists_Type; intros.
    destruct (Dec x); auto.
  Qed.

  Lemma Forall_Exists_Type_dec (P:A->Type) :
    (forall x:A, P x + (P x -> False)) ->
    forall l:list A,
    Forall_Type P l + Exists_Type (fun x => P x -> False) l.
  Proof.
    intros Pdec l.
    destruct (Forall_Type_dec P Pdec l); [left|right]; trivial.
    now apply neg_Forall_Exists_neg_Type.
  Defined.

  Lemma Forall_Type_arrow : forall (P Q : A -> Type), (forall a, P a -> Q a) ->
    forall l, Forall_Type P l -> Forall_Type Q l.
  Proof.
    induction l ; intros H ; inversion H ; constructor ; auto.
  Qed.

End Exists_Forall.

Hint Constructors Exists_Type : core.
Hint Constructors Forall_Type : core.

Section Forall2.

  (** [Forall2]: stating that elements of two lists are pairwise related. *)

  Variables A B : Type.
  Variable R : A -> B -> Type.

  Inductive Forall2_Type : list A -> list B -> Type :=
    | Forall2_Type_nil : Forall2_Type nil nil
    | Forall2_Type_cons : forall x y l l',
      R x y -> Forall2_Type l l' -> Forall2_Type (x::l) (y::l').

  Hint Constructors Forall2_Type : core.

  Theorem Forall2_Type_refl : Forall2_Type nil nil.
  Proof. intros; apply Forall2_Type_nil. Qed.

  Theorem Forall2_Type_app_inv_l : forall l1 l2 l0,
    Forall2_Type (l1 ++ l2) l0 ->
    {'(l1', l2') : _ & prod (Forall2_Type l1 l1') (Forall2_Type l2 l2') & l0 = l1' ++ l2' }.
  Proof.
    induction l1; intros.
    - assert (Forall2_Type nil nil) as HF1 by auto.
      assert (Forall2_Type l2 l0) as HF2 by auto.
      exists (nil,l0); [ split; assumption | reflexivity ].
    - simpl in X; inversion X; subst; clear X.
      apply IHl1 in X1 as [(l1',l2') [HF1 HF2] Heq]; subst.
      assert (Forall2_Type (a :: l1) (y :: l1')) as HF3 by auto.
      exists (y :: l1', l2'); [ split; assumption | reflexivity ].
  Qed.

  Theorem Forall2_Type_app_inv_r : forall l1 l2 l0,
    Forall2_Type l0 (l1 ++ l2) ->
    {'(l1', l2') : _ & prod (Forall2_Type l1' l1) (Forall2_Type l2' l2) & l0 = l1' ++ l2' }.
  Proof.
    induction l1; intros.
    - assert (Forall2_Type nil nil) as HF1 by auto.
      assert (Forall2_Type l0 l2) as HF2 by auto.
      exists (nil,l0); [ split; assumption | reflexivity ].
    - simpl in X; inversion X; subst; clear X.
      apply IHl1 in X1 as [(l1',l2') [HF1 HF2] Heq]; subst.
      assert (Forall2_Type (x :: l1') (a :: l1)) as HF3 by auto.
      exists (x :: l1', l2'); [ split; assumption | reflexivity ].
  Qed.

  Theorem Forall2_Type_app : forall l1 l2 l1' l2',
    Forall2_Type l1 l1' -> Forall2_Type l2 l2' -> Forall2_Type (l1 ++ l2) (l1' ++ l2').
  Proof.
    intros. induction l1 in l1', X, X0 |- *; inversion X; subst; simpl; auto.
  Qed.
End Forall2.

Hint Constructors Forall2 : core.

