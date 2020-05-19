(** Properties of lists with output in [Type] *)

From Coq Require Import PeanoNat Compare_dec List.

Set Implicit Arguments.

Import ListNotations.
Open Scope list_scope.


Section Lists.

  Variable A : Type.

  (** Informative version of [In] (output in [Type]) *)
  Fixpoint In_inf (a:A) (l:list A) : Type :=
    match l with
      | nil => False
      | b :: m => sum (b = a) (In_inf a m)
    end.

End Lists.

Section Facts.

  Variable A : Type.

  Theorem app_eq_unit_inf :
    forall (x y:list A) (a:A),
      x ++ y = [a] -> ((x = []) * (y = [a])) + ((x = [a]) * (y = [])).
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
    injection H as [= H H0].
    assert ([] = l ++ a0 :: l0) by auto.
    apply app_cons_not_nil in H1 as [].
  Qed.

  (** Properties of [In_inf] *)
  Lemma in_inf_in : forall (a : A) l, In_inf a l -> In a l.
  Proof.
  induction l; intros Hin; inversion Hin; try now constructor.
  right; intuition.
  Qed.

  Lemma notF_in_inf_notF_in : forall (F:Prop) (a : A) l,
    (In_inf a l -> F) -> In a l -> F.
  Proof.
  induction l; intros Hnin Hin; inversion Hin; subst.
  - apply Hnin; now constructor.
  - apply IHl; [ | assumption ].
    intros Hin2; apply Hnin.
    now right.
  Qed.

  Lemma notin_inf_notin : forall (a : A) l, (In_inf a l -> False) -> ~ In a l.
  Proof.
  exact (@notF_in_inf_notF_in False).
  Qed.

  (** Facts about [In_inf] *)

  Theorem in_inf_eq : forall (a:A) (l:list A), In_inf a (a :: l).
  Proof.
    simpl; auto.
  Qed.

  Theorem in_inf_cons : forall (a b:A) (l:list A), In_inf b l -> In_inf b (a :: l).
  Proof.
    simpl; auto.
  Qed.

  Theorem not_in_inf_cons (x a : A) (l : list A):
    x<>a -> (In_inf x l -> False) -> In_inf x (a::l) -> False.
  Proof.
    simpl. intuition.
  Qed.

  Theorem not_in_inf_cons_inv (x a : A) (l : list A):
    (In_inf x (a::l) -> False) -> (x<>a) * (In_inf x l -> False).
  Proof.
    simpl. intuition.
  Qed.

  Theorem in_inf_nil : forall a:A, In_inf a [] -> False.
  Proof.
    unfold not; intros a H; inversion_clear H.
  Qed.

  Lemma in_inf_app_or : forall (l m:list A) (a:A),
    In_inf a (l ++ m) -> In_inf a l + In_inf a m.
  Proof.
    intros l m a.
    elim l; simpl; auto.
    intros a0 y H H0.
    now_show ((a0 = a) + In_inf a y + In_inf a m)%type.
    elim H0; auto.
    intro H1.
    now_show ((a0 = a) + In_inf a y + In_inf a m)%type.
    elim (H H1); auto.
  Qed.

  Lemma in_inf_or_app : forall (l m:list A) (a:A),
    (In_inf a l + In_inf a m) -> In_inf a (l ++ m).
  Proof.
    intros l m a.
    elim l; simpl; intro H.
    - now_show (In_inf a m).
      elim H; auto; intro H0.
      now_show (In_inf a m).
      elim H0.
    - intros y H0 H1.
      destruct H1 ; intuition.
  Qed.

  Theorem in_inf_split : forall x (l:list A), In_inf x l ->
    {'(l1,l2) | l = l1 ++ x :: l2 }.
  Proof.
  induction l; simpl; destruct 1.
  - subst a; auto.
    exists (nil, l) ; auto.
  - destruct (IHl i) as ((l1,l2),H0).
    exists (a::l1, l2); simpl. apply f_equal. auto.
  Qed.

  Lemma in_inf_elt : forall (x:A) l1 l2, In_inf x (l1 ++ x :: l2).
  Proof.
  intros.
  apply in_inf_or_app.
  right; left; reflexivity.
  Qed.

  Lemma in_inf_elt_inv : forall (x y : A) l1 l2,
    In_inf x (l1 ++ y :: l2) -> ((x = y) + In_inf x (l1 ++ l2))%type.
  Proof.
  intros x y l1 l2 Hin.
  apply in_inf_app_or in Hin.
  destruct Hin as [Hin|[Hin|Hin]]; [right|left|right];
    try apply in_inf_or_app; intuition.
  Qed.

  Lemma in_inf_inv : forall (a b:A) (l:list A),
    In_inf b (a :: l) -> ((a = b) + In_inf b l)%type.
  Proof. easy. Qed.


  Section FactsEqDec.

    Hypothesis eq_dec : forall x y : A, {x = y}+{x <> y}.

    Theorem in_inf_dec : forall (a:A) (l:list A), In_inf a l + (In_inf a l -> False).
    Proof.
      induction l as [| a0 l IHl].
      right; apply in_inf_nil.
      destruct (eq_dec a0 a); simpl; auto.
      destruct IHl; simpl; auto.
      right; unfold not; intros [Hc1| Hc2]; auto.
    Defined.

    Lemma in_in_inf : forall (a:A) l, In a l -> In_inf a l.
    Proof.
      intros a l Hin.
      destruct (in_inf_dec a l); [ assumption | ].
      exfalso; revert Hin.
      apply notin_inf_notin; assumption.
    Qed.

  End FactsEqDec.

End Facts.

Hint Resolve in_inf_eq in_inf_cons in_inf_inv in_inf_nil
             in_inf_app_or in_inf_or_app: datatypes.



(*******************************************)
(** * Operations on the elements of a list *)
(*******************************************)

Section Elts.

  Variable A : Type.

  (*****************************)
  (** ** Nth element of a list *)
  (*****************************)

  Lemma nth_in_inf_or_default :
    forall (n:nat) (l:list A) (d:A), (In_inf (nth n l d) l + (nth n l d = d))%type.
  Proof.
    intros n l d; revert n; induction l.
    - right; destruct n; trivial.
    - intros [|n]; simpl.
      + left; auto.
      + destruct (IHl n); auto.
  Qed.

  Lemma nth_S_cons_inf :
    forall (n:nat) (l:list A) (d a:A),
      In_inf (nth n l d) l -> In_inf (nth (S n) (a :: l) d) (a :: l).
  Proof.
    simpl; auto.
  Qed.

  (** Results about [nth] *)

  Lemma nth_In_inf :
    forall (n:nat) (l:list A) (d:A), n < length l -> In_inf (nth n l d) l.
  Proof.
    unfold lt; induction n as [| n hn]; simpl.
    - destruct l; simpl; [ inversion 2 | auto ].
    - destruct l; simpl.
      * inversion 2.
      * intros d ie; right; apply hn; auto with arith.
  Qed.

  Lemma In_inf_nth l (x:A) d : In_inf x l ->
    { n | n < length l & nth n l d = x }.
  Proof.
    induction l as [|a l IH].
    - easy.
    - intros [H|H].
      + subst; exists 0; simpl; auto with arith.
      + destruct (IH H) as [n Hn Hn'].
        exists (S n); simpl; auto with arith.
  Qed.

  Lemma nth_split_inf n (l:list A) d : n < length l ->
    {'(l1, l2) | l = l1 ++ nth n l d :: l2 & length l1 = n }.
  Proof.
    revert l.
    induction n as [|n IH]; intros [|a l] H.
    - exists (nil, nil); now simpl.
    - exists (nil, l); now simpl.
    - exfalso; inversion H.
    - destruct (IH l) as [(l1, l2) Hl Hl1].
      + now apply Nat.succ_lt_mono.
      + exists (a::l1, l2); simpl; now f_equal.
  Qed.

  (** Results about [nth_error] *)

  Lemma nth_error_In_inf l n (x:A) : nth_error l n = Some x -> In_inf x l.
  Proof.
    revert n. induction l as [|a l IH]; intros [|n]; simpl; try easy.
    - injection 1; auto.
    - eauto.
  Qed.

 Lemma In_inf_nth_error l (x:A) : In_inf x l -> { n | nth_error l n = Some x }.
  Proof.
    induction l as [|a l IH].
    - easy.
    - intros [H|H].
      * subst; exists 0; simpl; auto with arith.
      * destruct (IH H) as (n,Hn).
        exists (S n); simpl; auto with arith.
  Qed.

  Lemma nth_error_split_inf l n (a:A) : nth_error l n = Some a ->
    {'(l1, l2) | l = l1 ++ a :: l2 & length l1 = n }.
  Proof.
    revert l.
    induction n as [|n IH]; intros [|x l] H; simpl in *; try easy.
    - exists (nil, l); auto. now injection H as [= ->].
    - destruct (IH _ H) as [ (l1, l2) H1 H2 ].
      exists (x::l1, l2); simpl; now f_equal.
  Qed.

End Elts.


Section ListOps.

  Variable A : Type.

  (*************************)
  (** ** Reverse           *)
  (*************************)

  Lemma in_inf_rev : forall l (x:A), In_inf x l -> In_inf x (rev l).
  Proof.
    induction l; simpl; intros; intuition.
    subst.
    apply in_inf_or_app; right; simpl; auto.
  Qed.

(*********************************************)
(** Reverse Induction Principle on Lists  *)
(*********************************************)

  Section Reverse_Induction.

    Lemma rev_list_rect : forall P:list A-> Type,
      P [] ->
      (forall (a:A) (l:list A), P (rev l) -> P (rev (a :: l))) ->
      forall l:list A, P (rev l).
    Proof.
      induction l; auto.
    Qed.

    Theorem rev_rect : forall P:list A -> Type,
      P [] ->
      (forall (x:A) (l:list A), P l -> P (l ++ [x])) -> forall l:list A, P l.
    Proof.
      intros P Hnil Hind l.
      rewrite <- (rev_involutive l).
      apply (rev_list_rect P); simpl; auto.
    Qed.

    Lemma rev_list_rec : forall P:list A-> Set,
      P [] ->
      (forall (a:A) (l:list A), P (rev l) -> P (rev (a :: l))) ->
      forall l:list A, P (rev l).
    Proof.
      intros; now apply rev_list_rect.
    Qed.

    Theorem rev_rec : forall P:list A -> Set,
      P [] ->
      (forall (x:A) (l:list A), P l -> P (l ++ [x])) -> forall l:list A, P l.
    Proof.
      intros; now apply rev_rect.
    Qed.

    Lemma rev_case_inf (l : list A) : (l = nil) + {'(a, tl) | l = tl ++ [a] }.
    Proof.
      induction l using rev_rect; [ left | right ]; auto.
      now exists (x, l).
    Qed.

  End Reverse_Induction.

  (*************************)
  (** ** Concatenation     *)
  (*************************)

  Lemma in_inf_concat : forall l y (x : list A),
    In_inf x l -> In_inf y x -> In_inf y (concat l).
  Proof.
    induction l as [ | a l IHl]; simpl; intros y x Hx Hy.
    - contradiction.
    - apply in_inf_or_app.
      destruct Hx as [Hx | Hx]; subst; auto.
      right; now apply (IHl y x).
  Qed.

  Lemma in_inf_concat_inv : forall l (y : A),
    In_inf y (concat l) -> { x & In_inf x l & In_inf y x }.
  Proof.
    induction l as [ | a l IHl]; simpl; intros y Hy.
    - contradiction.
    - destruct (in_inf_app_or _ _ _ Hy).
      + exists a; auto.
      + destruct (IHl y i) as [x ? ?].
        exists x; auto.
  Qed.

End ListOps.

(************)
(** ** Map  *)
(************)

Section Map.
  Variables (A : Type) (B : Type).
  Variable f : A -> B.

  Lemma in_inf_map :
    forall (l:list A) (x:A), In_inf x l -> In_inf (f x) (map f l).
  Proof.
    induction l; firstorder (subst; auto).
  Qed.

  Lemma in_inf_map_inv : forall l y, In_inf y (map f l) -> { x & f x = y & In_inf x l }.
  Proof.
    induction l; firstorder (subst; auto).
  Qed.

  Lemma map_eq_cons_inf : forall l l' b,
    map f l = b :: l' -> {'(a, tl) | l = a :: tl /\ f a = b /\ map f tl = l' }.
  Proof.
    intros l l' b Heq.
    destruct l; inversion_clear Heq.
    exists (a, l); repeat split.
  Qed.

  Lemma map_eq_app_inf : forall l l1 l2,
    map f l = l1 ++ l2 ->
    {'(l1', l2') | l = l1' ++ l2' /\ map f l1' = l1 /\ map f l2' = l2 }.
  Proof.
    induction l; simpl; intros l1 l2 Heq.
    - symmetry in Heq; apply app_eq_nil in Heq; destruct Heq; subst.
      exists (nil, nil); repeat split.
    - destruct l1; simpl in Heq; inversion Heq as [[Heq2 Htl]].
      + exists (nil, a :: l); repeat split.
      + destruct (IHl _ _ Htl) as [ (l1', l2') (? & ? & ?)]; subst.
        exists (a :: l1', l2'); repeat split.
  Qed.

  (** [flat_map] *)

  Lemma in_inf_flat_map : forall (f:A->list B) l y x,
    In_inf x l -> In_inf y (f x) -> In_inf y (flat_map f l).
  Proof.
    induction l; simpl; intros y x Hin1 Hin2; auto.
    apply in_inf_or_app.
    destruct Hin1 as [ Heq | Hin1 ].
    - subst; auto.
    - right ; apply (IHl y x Hin1 Hin2).
  Qed.

  Lemma in_inf_flat_map_inv : forall (f:A->list B) l y,
    In_inf y (flat_map f l) -> { x & In_inf x l & In_inf y (f x) }.
  Proof.
    induction l; simpl; intros.
    contradiction.
    destruct (in_inf_app_or _ _ _ X).
    - exists a; auto.
    - destruct (IHl y i) as [x H1 H2].
      exists x; auto.
  Qed.

End Map.

Lemma map_ext_in_inf :
  forall (A B : Type)(f g:A->B) l, (forall a, In_inf a l -> f a = g a) -> map f l = map g l.
Proof.
  induction l; simpl; auto.
  intros; rewrite H by intuition; rewrite IHl; auto.
Qed.

Lemma ext_in_inf_map :
  forall (A B : Type)(f g:A->B) l, map f l = map g l -> forall a, In_inf a l -> f a = g a.
Proof.
  intros A B f g l Heq a Hin; apply in_inf_in in Hin.
  now apply ext_in_map with l.
Qed.


  Section Bool.
    Variable A : Type.
    Variable f : A -> bool.

    Lemma existsb_exists_inf :
      forall l, existsb f l = true -> { x & In_inf x l & f x = true }.
    Proof.
      induction l; simpl; intuition.
      - inversion H.
      - case_eq (f a); intros Ha.
        + exists a; intuition.
        + rewrite Ha in H; simpl in H.
          apply IHl in H.
          destruct H as [x Hin Ht].
          exists x; intuition.
    Qed.

    Lemma exists_existsb_inf :
      forall l x, In_inf x l -> f x = true -> existsb f l = true.
    Proof.
      induction l; simpl; intuition; subst.
      - now rewrite H.
      - rewrite (IHl x b H).
        now destruct (f a).
    Qed.

    Lemma forallb_forall_inf :
      forall l, forallb f l = true <-> (forall x, In_inf x l -> f x = true).
    Proof.
      induction l; simpl; split; try now intuition.
      - intros Handb x [Heq|Hin]; destruct (andb_prop _ _ Handb); subst; intuition.
      - intros Hx.
        assert (forallb f l = true) by (apply IHl; intuition).
        rewrite Hx; auto.
    Qed.

    Lemma filter_In_inf : forall x l, In_inf x l -> f x = true -> In_inf x (filter f l).
    Proof.
      induction l; simpl.
      - intuition.
      - case_eq (f a); intros; simpl; intuition congruence.
    Qed.

    Lemma filter_In_inf_inv : forall x l, In_inf x (filter f l) ->
      In_inf x l * (f x = true)%type.
    Proof.
      induction l; simpl.
      - intuition.
      - case_eq (f a); intros; simpl; intuition; inversion_clear X; intuition congruence.
    Qed.

  (** [find] *)

    Lemma find_some_inf l x : find f l = Some x -> In_inf x l * (f x = true)%type.
    Proof.
      induction l as [|a l IH]; simpl; [easy| ].
      case_eq (f a); intros Ha Eq.
      - injection Eq as [= ->]; auto.
      - destruct (IH Eq); auto.
    Qed.

    Lemma find_none_inf l : find f l = None -> forall x, In_inf x l -> f x = false.
    Proof.
      induction l as [|a l IH]; simpl; [easy|].
      case_eq (f a); intros Ha Eq x IN; [easy|].
      destruct IN as [<-|IN]; auto.
    Qed.

  (** [partition] *)

  Theorem elements_in_inf_partition l l1 l2:
    partition f l = (l1, l2) ->
    forall x:A, (In_inf x l -> In_inf x l1 + In_inf x l2)
              * (In_inf x l1 + In_inf x l2 -> In_inf x l).
  Proof.
    revert l1 l2. induction l as [| a l' Hrec]; simpl; intros l1 l2 Eq x.
    - injection Eq as [= <- <-]. tauto.
    - destruct (partition f l') as (left, right).
      specialize (Hrec left right eq_refl x).
      destruct (f a); injection Eq as [= <- <-]; simpl; tauto.
  Qed.

  End Bool.


  (*******************************)
  (** ** Further filtering facts *)
  (*******************************)

  Section Filtering.
    Variables (A : Type).

    Lemma filter_ext_in_inf : forall (f g : A -> bool) (l : list A),
      (forall a, In_inf a l -> f a = g a) -> filter f l = filter g l.
    Proof.
      intros f g l H. rewrite filter_map. apply map_ext_in_inf. auto.
    Qed.

    Lemma ext_in_inf_filter : forall (f g : A -> bool) (l : list A),
      filter f l = filter g l -> (forall a, In_inf a l -> f a = g a).
    Proof.
      intros f g l H. rewrite filter_map in H. apply ext_in_inf_map. assumption.
    Qed.

  End Filtering.


  Section ListPairs.
    Variables (A : Type) (B : Type).

  (** [split] derives two lists from a list of pairs *)

    Lemma in_inf_split_l : forall (l:list (A*B))(p:A*B),
      In_inf p l -> In_inf (fst p) (fst (split l)).
    Proof.
      induction l; simpl; intros; auto.
      destruct p; destruct a; destruct (split l); simpl in *.
      destruct X.
      injection e; auto.
      right; apply (IHl (a0,b) i).
    Qed.

    Lemma in_inf_split_r : forall (l:list (A*B))(p:A*B),
      In_inf p l -> In_inf (snd p) (snd (split l)).
    Proof.
      induction l; simpl; intros; auto.
      destruct p; destruct a; destruct (split l); simpl in *.
      destruct X.
      injection e; auto.
      right; apply (IHl (a0,b) i).
    Qed.

  (** [combine] is the opposite of [split]. *)

    Lemma in_inf_combine_l : forall (l:list A)(l':list B)(x:A)(y:B),
      In_inf (x,y) (combine l l') -> In_inf x l.
    Proof.
      induction l.
      simpl; auto.
      destruct l'; simpl; auto; intros.
      contradiction.
      destruct X.
      injection e; auto.
      right; apply IHl with l' y; auto.
    Qed.

    Lemma in_inf_combine_r : forall (l:list A)(l':list B)(x:A)(y:B),
      In_inf (x,y) (combine l l') -> In_inf y l'.
    Proof.
      induction l.
      simpl; intros; contradiction.
      destruct l'; simpl; auto; intros.
      destruct X.
      injection e; auto.
      right; apply IHl with x; auto.
    Qed.

  (** [list_prod] has the same signature as [combine] *)

    Lemma in_inf_prod_aux :
      forall (x:A) (y:B) (l:list B),
      In_inf y l -> In_inf (x, y) (map (fun y0:B => (x, y0)) l).
    Proof.
      induction l;
      [ simpl; auto
        | simpl; destruct 1 as [H1| ];
          [ left; rewrite H1; trivial | right; auto ] ].
    Qed.

    Lemma in_inf_prod :
      forall (l:list A) (l':list B) (x:A) (y:B),
        In_inf x l -> In_inf y l' -> In_inf (x, y) (list_prod l l').
    Proof.
      induction l;
      [ simpl; tauto
        | simpl; intros; apply in_inf_or_app; destruct X;
          [ left; rewrite e; apply in_inf_prod_aux; assumption | right; auto ] ].
    Qed.

  End ListPairs.


(******************************)
(** ** Set inclusion on list  *)
(******************************)

Section SetIncl.

  Variable A : Type.

  Definition incl_inf (l m:list A) := forall a:A, In_inf a l -> In_inf a m.
  Hint Unfold incl_inf : core.

  Lemma incl_inf_incl (l m:list A) : incl_inf l m -> incl l m.
  Proof.
    intros Hincl x.
    apply notF_in_inf_notF_in; intros Hin.
    now apply in_inf_in, Hincl.
  Qed.

  Lemma incl_inf_nil_l : forall l, incl_inf nil l.
  Proof.
    intros l a Hin; inversion Hin.
  Qed.

  Lemma incl_inf_l_nil : forall l, incl_inf l nil -> l = nil.
  Proof.
    destruct l; intros Hincl.
    - reflexivity.
    - exfalso; apply Hincl with a; simpl; auto.
  Qed.

  Lemma incl_inf_refl : forall l:list A, incl_inf l l.
  Proof.
    auto.
  Qed.
  Hint Resolve incl_inf_refl : core.

  Lemma incl_inf_tl : forall (a:A) (l m:list A), incl_inf l m -> incl_inf l (a :: m).
  Proof.
    auto with datatypes.
  Qed.
  Hint Immediate incl_inf_tl : core.

  Lemma incl_inf_tran : forall l m n:list A, incl_inf l m -> incl_inf m n -> incl_inf l n.
  Proof.
    auto.
  Qed.

  Lemma incl_inf_appl : forall l m n:list A, incl_inf l n -> incl_inf l (n ++ m).
  Proof.
    auto with datatypes.
  Qed.
  Hint Immediate incl_inf_appl : core.

  Lemma incl_inf_appr : forall l m n:list A, incl_inf l n -> incl_inf l (m ++ n).
  Proof.
    auto with datatypes.
  Qed.
  Hint Immediate incl_inf_appr : core.

  Lemma incl_inf_cons :
    forall (a:A) (l m:list A), In_inf a m -> incl_inf l m -> incl_inf (a :: l) m.
  Proof.
    unfold incl; simpl; intros a l m H H0 a0 H1.
    now_show (In_inf a0 m).
    elim H1.
    - now_show (a = a0 -> In_inf a0 m).
      intro; subst; auto.
    - now_show (In_inf a0 l -> In_inf a0 m).
      auto.
  Qed.
  Hint Resolve incl_inf_cons : core.

  Lemma incl_inf_cons_inv : forall (a:A) (l m:list A),
    incl_inf (a :: l) m -> In_inf a m * incl_inf l m.
  Proof.
    intros a l m Hi.
    split; [ | intros ? ? ]; apply Hi; simpl; auto.
  Qed.

  Lemma incl_inf_app : forall l m n:list A,
    incl_inf l n -> incl_inf m n -> incl_inf (l ++ m) n.
  Proof.
    unfold incl; simpl; intros l m n H H0 a H1.
    now_show (In_inf a n).
    elim (in_inf_app_or _ _ _ H1); auto.
  Qed.
  Hint Resolve incl_inf_app : core.

  Lemma incl_inf_app_app : forall l1 l2 m1 m2:list A,
    incl_inf l1 m1 -> incl_inf l2 m2 -> incl_inf (l1 ++ l2) (m1 ++ m2).
  Proof.
    intros.
    apply incl_inf_app; [ apply incl_inf_appl | apply incl_inf_appr]; assumption.
  Qed.

  Lemma incl_inf_app_inv : forall l1 l2 m : list A,
    incl_inf (l1 ++ l2) m -> incl_inf l1 m * incl_inf l2 m.
  Proof.
    induction l1; intros l2 m Hin; split; auto.
    - apply incl_inf_nil_l.
    - intros b Hb; inversion_clear Hb; subst; apply Hin.
      + now constructor.
      + simpl; apply in_inf_cons.
        apply incl_inf_appl with l1; [ apply incl_inf_refl | assumption ].
    - apply IHl1.
      apply incl_inf_cons_inv in Hin.
      now destruct Hin.
  Qed.

  Lemma incl_inf_filter f l : incl_inf (filter f l) l.
  Proof. intros x Hin; apply filter_In_inf_inv in Hin; intuition. Qed.

End SetIncl.

Lemma incl_inf_map A B (f : A -> B) l1 l2 : incl_inf l1 l2 -> incl_inf (map f l1) (map f l2).
Proof.
  intros Hincl x Hinx.
  destruct (in_inf_map_inv _ _ _ Hinx) as [y <- Hiny].
  apply in_inf_map; intuition.
Qed.

Hint Resolve incl_inf_refl incl_inf_tl incl_inf_tran
  incl_inf_appl incl_inf_appr incl_inf_cons incl_inf_app: datatypes.


Section Add.

  Variable A : Type.

  (* [Add_inf a l l'] means that [l'] is exactly [l], with [a] added
     once somewhere *)
  Inductive Add_inf (a:A) : list A -> list A -> Type :=
    | Add_inf_head l : Add_inf a l (a::l)
    | Add_inf_cons x l l' : Add_inf a l l' -> Add_inf a (x::l) (x::l').

  Lemma Add_inf_Add a l1 l2 : Add_inf a l1 l2 -> Add a l1 l2.
  Proof.
    intros HA; induction HA; now constructor.
  Qed.

  Lemma notF_Add_inf_notF_Add (F:Prop) a l1 l2 : (Add_inf a l1 l2 -> F) -> Add a l1 l2 -> F.
  Proof.
    intros HnA HA; induction HA.
    - apply HnA; constructor.
    - apply IHHA; intros HAT; apply HnA; now constructor.
  Qed.

  Lemma notAdd_inf_notAdd a l1 l2 : (Add_inf a l1 l2 -> False) -> ~ Add a l1 l2.
  Proof.
    exact (@notF_Add_inf_notF_Add False a l1 l2).
  Qed.

  Lemma Add_inf_app a l1 l2 : Add_inf a (l1++l2) (l1++a::l2).
  Proof.
    induction l1; simpl; now constructor.
  Qed.

  Lemma Add_inf_split a l l' :
    Add_inf a l l' -> {'(l1, l2) | l = l1++l2 & l' = l1++a::l2 }.
  Proof.
   induction 1.
   - exists (nil, l); split; trivial.
   - destruct IHX as [(l1, l2) Hl Hl'].
     exists (x::l1, l2); simpl; f_equal; trivial.
  Qed.

  Lemma Add_inf_in_inf a l l' : Add_inf a l l' ->
   forall x, In_inf x l' -> In_inf x (a::l).
  Proof.
   induction 1; intros; simpl in *; rewrite ?IHX; firstorder.
  Qed.

  Lemma Add_inf_in_inf_inv a l l' : Add_inf a l l' ->
   forall x, In_inf x (a::l) -> In_inf x l'.
  Proof.
   induction 1; intros; simpl in *; rewrite ?IHX; intuition.
  Qed.

  Lemma Add_inf_length a l l' : Add_inf a l l' -> length l' = S (length l).
  Proof.
   induction 1; simpl; auto with arith.
  Qed.

  Lemma Add_inf_inv a l : In_inf a l -> { l' & Add_inf a l' l }.
  Proof.
   intro Ha. destruct (in_inf_split _ _ Ha) as [(l1,l2) ->].
   exists (l1 ++ l2). apply Add_inf_app.
  Qed.

  Lemma incl_inf_Add_inf_inv a l u v :
    (In_inf a l -> False) -> incl_inf (a::l) v -> Add_inf a u v -> incl_inf l u.
  Proof.
   intros Ha H AD y Hy.
   assert (Hy' : In_inf y (a::u)).
   { apply (Add_inf_in_inf AD). apply H; simpl; auto. }
   destruct Hy'; [ subst; now elim Ha | trivial ].
  Qed.

End Add.


Section ReDun.

  Variable A : Type.

  Inductive NoDup_inf : list A -> Type :=
    | NoDup_inf_nil : NoDup_inf nil
    | NoDup_inf_cons : forall x l, (In_inf x l -> False) -> NoDup_inf l -> NoDup_inf (x::l).

  Lemma NoDup_NoDup_inf : forall l : list A, NoDup l -> NoDup_inf l.
  Proof.
  induction l; intros Hnd; constructor.
  - intros Hnin.
    apply in_inf_in in Hnin.
    inversion Hnd; intuition.
  - apply IHl; now inversion Hnd.
  Qed.

  Lemma NoDup_inf_NoDup : forall l : list A, NoDup_inf l -> NoDup l.
  Proof.
  induction l; intros Hnd; constructor.
  - apply notin_inf_notin; intros Hnin.
    inversion Hnd; intuition.
  - apply IHl; now inversion Hnd.
  Qed.

  Theorem NoDup_inf_cons_imp a l:
    NoDup_inf (a::l) -> (In_inf a l -> False) * NoDup_inf l.
  Proof.
    intros Hd; inversion Hd; subst; split; assumption.
  Qed.

  Lemma NoDup_inf_length_incl_inf l l' :
    NoDup_inf l -> length l' <= length l -> incl_inf l l' -> incl_inf l' l.
  Proof.
   intros N. revert l'. induction N as [|a l Hal N IH].
   - destruct l'; auto.
     simpl; intro Hl; exfalso; inversion Hl.
   - intros l' E H x Hx.
     destruct (Add_inf_inv a l') as (l'', AD). { apply H; simpl; auto. }
     apply (Add_inf_in_inf AD) in Hx. simpl in Hx.
     destruct Hx as [Hx|Hx]; [left; trivial|right].
     revert x Hx. apply (IH l''); trivial.
     * apply le_S_n. now rewrite <- (Add_inf_length AD).
     * now apply incl_inf_Add_inf_inv with a l'.
  Qed.

End ReDun.


Section NatSeq.

  (** [seq] computes the sequence of [len] contiguous integers *)


  Lemma in_inf_seq len start n :
    start <= n < start+len -> In_inf n (seq start len).
  Proof.
   revert start. induction len; simpl; intros start H.
   - inversion_clear H.
     rewrite <- plus_n_O in H1.
     apply (Lt.lt_irrefl _ (Lt.le_lt_trans _ _ _ H0 H1)).
   - destruct H as [H1 H2].
     destruct (le_lt_eq_dec _ _ H1); intuition.
     right; apply IHlen.
     rewrite <- plus_n_Sm in H2.
     intuition auto with arith.
  Qed.

  Lemma in_inf_seq_inv len start n :
    In_inf n (seq start len) -> start <= n < start+len.
  Proof.
   revert start. induction len; simpl; intros.
   - inversion H.
   - rewrite <- plus_n_Sm.
     destruct X; subst.
     + intuition auto with arith.
     + apply IHlen in i.
       intuition auto with arith.
  Qed.

 End NatSeq.

Section Exists_Forall.

  (** * Existential and universal predicates over lists *)

  Variable A:Type.

  Section One_predicate_Type.

    Variable P:A->Type.

    Inductive Exists_inf : list A -> Type :=
      | Exists_inf_cons_hd : forall x l, P x -> Exists_inf (x::l)
      | Exists_inf_cons_tl : forall x l, Exists_inf l -> Exists_inf (x::l).

    Hint Constructors Exists_inf : core.

    Lemma Exists_inf_exists (l:list A) :
      Exists_inf l -> { x  & In_inf x l & P x }.
    Proof.
      induction 1; firstorder.
    Qed.

    Lemma exists_Exists_inf (l:list A) x :
      In_inf x l -> P x -> Exists_inf l.
    Proof.
      induction l; firstorder; subst; auto.
    Qed.

    Lemma Exists_inf_nth l :
      Exists_inf l -> {'(i, d) & i < length l & P (nth i l d) }.
    Proof.
      intros HE; apply Exists_inf_exists in HE.
      destruct HE as [a Hin HP].
      apply In_inf_nth with (d := a) in Hin; destruct Hin as [i Hl Heq].
      rewrite <- Heq in HP.
      now exists (i, a).
    Qed.

    Lemma nth_Exists_inf l i d :
      i < length l -> P (nth i l d) -> Exists_inf l.
    Proof.
      intros Hl HP.
      refine (exists_Exists_inf _ _ HP).
      apply nth_In_inf; assumption.
    Qed.

    Lemma Exists_inf_nil : Exists_inf nil -> False.
    Proof. inversion 1. Qed.

    Lemma Exists_inf_cons x l:
      Exists_inf (x::l) -> P x + Exists_inf l.
    Proof. inversion 1; auto. Qed.

    Lemma Exists_inf_app l1 l2 :
      Exists_inf (l1 ++ l2) -> Exists_inf l1 + Exists_inf l2.
    Proof.
      induction l1; simpl; intros HE; try now intuition.
      inversion_clear HE; intuition.
    Qed.

    Lemma Exists_inf_app_l l1 l2 :
      Exists_inf l1 -> Exists_inf (l1 ++ l2).
    Proof.
      induction l1; simpl; intros HE; try now intuition.
      inversion_clear HE; intuition.
    Qed.

    Lemma Exists_inf_app_r l1 l2 :
      Exists_inf l2 -> Exists_inf (l1 ++ l2).
    Proof.
      induction l1; simpl; intros HE; try now intuition.
    Qed.

    Lemma Exists_inf_rev l : Exists_inf l -> Exists_inf (rev l).
    Proof.
      induction l; intros HE; intuition.
      inversion_clear HE; simpl.
      - apply Exists_inf_app_r; intuition.
      - apply Exists_inf_app_l; intuition.
    Qed.

    Lemma Exists_inf_dec l:
      (forall x:A, P x + (P x -> False)) ->
      Exists_inf l + (Exists_inf l -> False).
    Proof.
      intro Pdec. induction l as [|a l' Hrec].
      - right. now apply Exists_inf_nil.
      - destruct Hrec as [Hl'|Hl'].
        * left. now apply Exists_inf_cons_tl.
        * destruct (Pdec a) as [Ha|Ha].
          + left. now apply Exists_inf_cons_hd.
          + right. now inversion_clear 1.
    Defined.

    Lemma Exists_inf_fold_right l :
      Exists_inf l -> fold_right (fun x => sum (P x)) False l.
    Proof.
      induction l; simpl; intros HE; try now inversion HE; intuition.
    Qed.

    Lemma fold_right_Exists_inf l :
      fold_right (fun x => sum (P x)) False l -> Exists_inf l.
    Proof.
      induction l; simpl; intros HE; try now inversion HE; intuition.
    Qed.

    Lemma incl_inf_Exists_inf l1 l2 : incl_inf l1 l2 -> Exists_inf l1 -> Exists_inf l2.
    Proof.
      intros Hincl HE.
      apply Exists_inf_exists in HE; destruct HE as [a Hin HP].
      apply exists_Exists_inf with a; intuition.
    Qed.

    Inductive Forall_inf : list A -> Type :=
      | Forall_inf_nil : Forall_inf nil
      | Forall_inf_cons : forall x l, P x -> Forall_inf l -> Forall_inf (x::l).

    Hint Constructors Forall_inf : core.

    Lemma Forall_inf_forall (l:list A):
      Forall_inf l -> forall x, In_inf x l -> P x.
    Proof.
      induction 1; firstorder; subst; auto.
    Qed.

    Lemma forall_Forall_inf (l:list A):
      (forall x, In_inf x l -> P x) -> Forall_inf l.
    Proof.
      induction l; intuition.
    Qed.

    Lemma Forall_inf_nth l :
      Forall_inf l -> forall i d, i < length l -> P (nth i l d).
    Proof.
      intros HF i d Hl.
      apply Forall_inf_forall with (x := nth i l d) in HF.
      assumption.
      apply nth_In_inf; assumption.
    Qed.

    Lemma nth_Forall_inf l :
      (forall i d, i < length l -> P (nth i l d)) -> Forall_inf l.
    Proof.
      intros HF.
      apply forall_Forall_inf; intros a Hin.
      apply In_inf_nth with (d := a) in Hin; destruct Hin as [i Hl <-]; intuition.
    Qed.

    Lemma Forall_inf_inv : forall (a:A) l, Forall_inf (a :: l) -> P a.
    Proof.
      intros ? ? H; inversion H; trivial.
    Qed.

    Theorem Forall_inf_inv_tail : forall (a:A) l, Forall_inf (a :: l) -> Forall_inf l.
    Proof.
      intros ? ? H; inversion H; trivial.
    Qed.

    Lemma Forall_inf_app_l l1 l2 :
      Forall_inf (l1 ++ l2) -> Forall_inf l1.
    Proof.
      induction l1; simpl; intros HF; try now intuition.
      inversion_clear HF; intuition.
    Qed.

    Lemma Forall_inf_app_r l1 l2 :
      Forall_inf (l1 ++ l2) -> Forall_inf l2.
    Proof.
      induction l1; simpl; intros HF; try now intuition.
      inversion_clear HF; intuition.
    Qed.

    Lemma Forall_inf_app l1 l2 :
      Forall_inf l1 -> Forall_inf l2 -> Forall_inf (l1 ++ l2).
    Proof.
      induction l1; simpl; intros HF1 HF2; try now intuition.
      inversion_clear HF1; intuition.
    Qed.

    Lemma Forall_inf_elt a l1 l2 : Forall_inf (l1 ++ a :: l2) -> P a.
    Proof.
      intros HF; apply Forall_inf_app_r in HF; now inversion HF.
    Qed.

    Lemma Forall_inf_rev l : Forall_inf l -> Forall_inf (rev l).
    Proof.
      induction l; intros HF; intuition.
      inversion_clear HF; simpl; apply Forall_inf_app; intuition.
    Qed.

    Lemma Forall_inf_rect' : forall (Q : list A -> Type),
      Q [] -> (forall b l, P b -> Q (b :: l)) -> forall l, Forall_inf l -> Q l.
    Proof.
      intros Q H H'; induction l; intro; [|eapply H', Forall_inf_inv]; eassumption.
    Qed.

    Lemma Forall_inf_dec :
      (forall x:A, P x + (P x -> False)) ->
      forall l:list A, Forall_inf l + (Forall_inf l -> False).
    Proof.
      intro Pdec. induction l as [|a l' Hrec].
      - left. apply Forall_inf_nil.
      - destruct Hrec as [Hl'|Hl'].
        + destruct (Pdec a) as [Ha|Ha].
          * left. now apply Forall_inf_cons.
          * right. abstract now inversion 1.
        + right. abstract now inversion 1.
    Defined.

    Lemma Forall_inf_fold_right l :
      Forall_inf l -> fold_right (fun x => prod (P x)) True l.
    Proof.
      induction l; simpl; intros HF; try now inversion HF; intuition.
    Qed.

    Lemma fold_right_Forall_inf l :
      fold_right (fun x => prod (P x)) True l -> Forall_inf l.
    Proof.
      induction l; simpl; intros HF; try now inversion HF; intuition.
    Qed.

    Lemma incl_inf_Forall_inf l1 l2 : incl_inf l2 l1 -> Forall_inf l1 -> Forall_inf l2.
    Proof.
      intros Hincl HF.
      apply forall_Forall_inf; intros a Ha.
      apply Forall_inf_forall with (x:=a) in HF; intuition.
    Qed.

  End One_predicate_Type.

  Lemma Exists_inf_Exists (P:A->Prop) l : Exists_inf P l -> Exists P l.
  Proof. now induction 1; constructor. Qed.

  Lemma Forall_inf_Forall (P:A->Prop) l : Forall_inf P l -> Forall P l.
  Proof. now induction 1; constructor. Qed.

  Theorem Exists_inf_arrow : forall (P Q : A -> Type), (forall a : A, P a -> Q a) ->
    forall l, Exists_inf P l -> Exists_inf Q l.
  Proof.
    intros P Q H l H0.
    induction H0.
    apply (Exists_inf_cons_hd Q x l (H x p)).
    apply (Exists_inf_cons_tl x IHExists_inf).
  Qed.

  Lemma Exists_inf_sum : forall (P Q : A -> Type) l,
    Exists_inf P l + Exists_inf Q l -> Exists_inf (fun x => P x + Q x)%type l.
  Proof.
    induction l; intros [H | H]; inversion H; subst.
    1,3: apply Exists_inf_cons_hd; auto.
    all: apply Exists_inf_cons_tl, IHl; auto.
  Qed.

  Lemma Exists_inf_sum_inv : forall (P Q : A -> Type) l,
    Exists_inf (fun x => P x + Q x)%type l -> Exists_inf P l + Exists_inf Q l.
  Proof.
    induction l; intro Hl; inversion Hl as [ ? ? H | ? ? H ]; subst.
    - inversion H; now repeat constructor.
    - destruct (IHl H); now repeat constructor.
  Qed.

  Lemma Forall_inf_arrow : forall (P Q : A -> Type), (forall a, P a -> Q a) ->
    forall l, Forall_inf P l -> Forall_inf Q l.
  Proof.
    induction l; intros H; inversion H; constructor; auto.
  Qed.

  Lemma Forall_inf_prod : forall (P Q : A -> Type) l,
    Forall_inf P l -> Forall_inf Q l -> Forall_inf (fun x => P x * Q x)%type l.
  Proof.
    induction l; intros HP HQ; constructor; inversion HP; inversion HQ; auto.
  Qed.

  Lemma Forall_inf_prod_inv : forall (P Q : A -> Type) l,
    Forall_inf (fun x => P x * Q x)%type l -> Forall_inf P l * Forall_inf Q l.
  Proof.
    induction l; intro Hl; split; constructor; inversion Hl; firstorder.
  Qed.

  Lemma Forall_inf_Exists_inf_neg (P:A->Type)(l:list A) :
   Forall_inf (fun x => P x -> False) l -> Exists_inf P l -> False.
  Proof.
   induction l; intros HF HE; inversion HE; inversion HF; auto.
  Qed.

  Lemma Exists_inf_neg_Forall_inf (P:A->Type)(l:list A) :
   (Exists_inf P l -> False) -> Forall_inf (fun x => P x -> False) l.
  Proof.
   induction l; intros HE; constructor.
   - intros Ha; apply HE.
     now constructor.
   - apply IHl; intros HF; apply HE.
     now constructor.
  Qed.

  Lemma Exists_inf_Forall_inf_neg (P:A->Type)(l:list A) :
    Exists_inf (fun x => P x -> False) l -> Forall_inf P l -> False.
  Proof.
   induction l; intros HE HF; inversion HE; inversion HF; auto.
  Qed.

  Lemma Forall_inf_neg_Exists_inf (P:A->Type)(l:list A) :
    (forall x, P x + (P x -> False)) ->
    (Forall_inf P l -> False) -> Exists_inf (fun x => P x -> False) l.
  Proof.
   intro Dec.
   induction l; intros HF.
   - contradiction HF. constructor.
   - destruct (Dec a) as [ Ha | Hna ].
     + apply Exists_inf_cons_tl, IHl.
       intros HFl.
       apply HF; now constructor.
     + now apply Exists_inf_cons_hd.
  Qed.

  Lemma Forall_inf_Exists_inf_dec (P:A->Type) :
    (forall x:A, P x + (P x -> False)) ->
    forall l:list A,
    Forall_inf P l + Exists_inf (fun x => P x -> False) l.
  Proof.
    intros Dec l.
    destruct (Forall_inf_dec P Dec l); [left|right]; trivial.
    now apply Forall_inf_neg_Exists_inf.
  Defined.

  Lemma incl_inf_Forall_inf_in_inf l l' :
    incl_inf l l' -> Forall_inf (fun x => In_inf x l') l.
  Proof. now intros; apply forall_Forall_inf. Qed.

  Lemma Forall_inf_in_inf_incl_inf l l' :
    Forall_inf (fun x => In_inf x l') l -> incl_inf l l'.
  Proof. now intros HF x Hin; apply Forall_inf_forall with (x:= x) in HF. Qed.

End Exists_Forall.

Hint Constructors Exists_inf : core.
Hint Constructors Forall_inf : core.

Lemma exists_Forall_inf A B : forall (P : A -> B -> Type) l,
  { k & Forall_inf (P k) l } -> Forall_inf (fun x => { k & P k x }) l.
Proof.
  induction l; intros [k HF]; constructor; inversion_clear HF.
  - now exists k.
  - now apply IHl; exists k.
Qed.

Lemma Forall_inf_image A B : forall (f : A -> B) l,
  Forall_inf (fun y => { x | y = f x }) (map f l).
Proof.
  induction l as [ | a l ]; constructor.
  - now exists a.
  - now apply IHl; exists l.
Qed.

Lemma Forall_inf_image_inv A B : forall (f : A -> B) l,
  Forall_inf (fun y => { x | y = f x }) l -> { l' | l = map f l' }.
Proof.
  induction l as [ | a l ]; intros HF.
  - exists nil; reflexivity.
  - inversion_clear HF as [| ? ? [x ->] HFtl].
    destruct (IHl HFtl) as [l' ->].
    now exists (x :: l').
Qed.

Lemma concat_nil_Forall_inf A : forall (l : list (list A)),
  concat l = nil -> Forall_inf (fun x => x = nil) l.
Proof.
  induction l; simpl; intros Hc; auto.
  apply app_eq_nil in Hc.
  constructor; firstorder.
Qed.

Lemma Forall_inf_concat_nil A : forall (l : list (list A)),
  Forall_inf (fun x => x = nil) l -> concat l = nil.
Proof.
  induction l; simpl; intros Hc; auto.
  inversion Hc; subst; simpl.
  now apply IHl.
Qed.

Lemma in_inf_flat_map_Exists_inf A B : forall (f : A -> list B) x l,
  In_inf x (flat_map f l) -> Exists_inf (fun y => In_inf x (f y)) l.
Proof.
  intros f x l Hin.
  destruct (in_inf_flat_map_inv _ _ _ Hin) as [y Hin1 Hin2].
  now apply exists_Exists_inf with y.
Qed.

Lemma Exists_inf_in_inf_flat_map A B : forall (f : A -> list B) x l,
  Exists_inf (fun y => In_inf x (f y)) l -> In_inf x (flat_map f l).
Proof.
  intros f x l HE.
  destruct (Exists_inf_exists HE) as [y Hin1 Hin2].
  now apply in_inf_flat_map with y.
Qed.

Lemma notin_inf_flat_map_Forall_inf A B : forall (f : A -> list B) x l,
  (In_inf x (flat_map f l) -> False) ->
  Forall_inf (fun y => In_inf x (f y) -> False) l.
Proof.
  intros f x l Hnin.
  apply Exists_inf_neg_Forall_inf.
  now intros HE; apply Exists_inf_in_inf_flat_map in HE.
Qed.

Lemma Forall_inf_notin_inf_flat_map A B : forall (f : A -> list B) x l,
  Forall_inf (fun y => In_inf x (f y) -> False) l ->
  In_inf x (flat_map f l) -> False.
Proof.
  intros f x l HF Hin.
  apply Forall_inf_Exists_inf_neg in HF; [ assumption | ].
  now apply in_inf_flat_map_Exists_inf.
Qed.


Section Forall2_inf.

  (** [Forall2_inf]: stating that elements of two lists are pairwise related. *)

  Variables A B : Type.
  Variable R : A -> B -> Type.

  Inductive Forall2_inf : list A -> list B -> Type :=
    | Forall2_inf_nil : Forall2_inf [] []
    | Forall2_inf_cons : forall x y l l',
      R x y -> Forall2_inf l l' -> Forall2_inf (x::l) (y::l').

  Hint Constructors Forall2_inf : core.

  Theorem Forall2_inf_refl : Forall2_inf [] [].
  Proof. intros; apply Forall2_inf_nil. Qed.

  Theorem Forall2_inf_app_inv_l : forall l1 l2 l,
    Forall2_inf (l1 ++ l2) l ->
    {'(l1', l2') : _ & (Forall2_inf l1 l1' * Forall2_inf l2 l2')%type
                     & l = l1' ++ l2' }.
  Proof.
    induction l1; intros l1' l2' HF.
    - exists (nil, l2'); auto.
    - simpl in HF; inversion_clear HF.
      apply IHl1 in X0 as [(l1'',l2'') [HF1 HF2] ->].
      assert (Forall2_inf (a :: l1) (y :: l1'')) as HF3 by auto.
      exists (y :: l1'', l2''); auto.
  Qed.

  Theorem Forall2_inf_app_inv_r : forall l1 l2 l,
    Forall2_inf l (l1 ++ l2) ->
    {'(l1', l2') : _ & (Forall2_inf l1' l1 * Forall2_inf l2' l2)%type
                     & l = l1' ++ l2' }.
  Proof.
    induction l1; intros l1' l2' HF.
    - exists (nil, l2'); auto.
    - simpl in HF; inversion_clear HF.
      apply IHl1 in X0 as [(l1'',l2'') [HF1 HF2] ->].
      assert (Forall2_inf (x :: l1'') (a :: l1)) as HF3 by auto.
      exists (x :: l1'', l2''); auto.
  Qed.

  Theorem Forall2_inf_app : forall l1 l2 l1' l2',
    Forall2_inf l1 l1' -> Forall2_inf l2 l2' -> Forall2_inf (l1 ++ l2) (l1' ++ l2').
  Proof.
    intros. induction l1 in l1', X, X0 |- *; inversion X; subst; simpl; auto.
  Qed.

  Lemma Forall2_inf_length : forall l1 l2,
    Forall2_inf l1 l2 -> length l1 = length l2.
  Proof.
    intros l1 l2 HF; induction HF; auto.
    now simpl; rewrite IHHF.
  Qed.

End Forall2_inf.

Hint Constructors Forall2_inf : core.

Lemma Forall2_inf_Forall2 {A B} (R : A -> B -> Prop) l1 l2 :
  Forall2_inf R l1 l2 -> Forall2 R l1 l2.
Proof. induction 1 ; auto. Qed.


Section ForallPairs_inf.

  (** [ForallPairs_inf] : specifies that a certain relation should
    always hold when inspecting all possible pairs of elements of a list. *)

  Variable A : Type.
  Variable R : A -> A -> Type.

  Definition ForallPairs_inf l :=
    forall a b, In_inf a l -> In_inf b l -> R a b.

  (** [ForallOrdPairs_inf] : we still check a relation over all pairs
     of elements of a list, but now the order of elements matters. *)

  Inductive ForallOrdPairs_inf : list A -> Type :=
    | FOP_inf_nil : ForallOrdPairs_inf nil
    | FOP_inf_cons : forall a l,
      Forall_inf (R a) l -> ForallOrdPairs_inf l -> ForallOrdPairs_inf (a::l).

  Hint Constructors ForallOrdPairs_inf : core.

  Lemma ForallOrdPairs_inf_In_inf : forall l,
    ForallOrdPairs_inf l ->
    forall x y, In_inf x l -> In_inf y l -> ((x=y) + R x y + R y x)%type.
  Proof.
    induction 1.
    inversion 1.
    simpl; destruct 1; destruct 1; subst; auto.
    - left; right.
      apply Forall_inf_forall with _ _ _ y in f; eauto.
    - right.
      apply Forall_inf_forall with _ _ _ x in f; eauto.
  Qed.

  (** [ForallPairs_inf] implies [ForallOrdPairs_inf].
    The reverse implication is true only when [R] is symmetric and reflexive. *)

  Lemma ForallPairs_inf_ForallOrdPairs_inf l:
    ForallPairs_inf l -> ForallOrdPairs_inf l.
  Proof.
    induction l; auto. intros H.
    constructor.
    apply forall_Forall_inf. intros; apply H; simpl; auto.
    apply IHl. red; intros; apply H; simpl; auto.
  Qed.

  Lemma ForallOrdPairs_inf_ForallPairs_inf :
    (forall x, R x x) ->
    (forall x y, R x y -> R y x) ->
    forall l, ForallOrdPairs_inf l -> ForallPairs_inf l.
  Proof.
    intros Refl Sym l Hl x y Hx Hy.
    destruct (ForallOrdPairs_inf_In_inf Hl _ _ Hx Hy); subst; intuition.
    subst; intuition.
  Qed.

End ForallPairs_inf.

Lemma ForallPairs_inf_ForallPairs {A} (R : A -> A -> Prop) l :
  ForallPairs_inf R l -> ForallPairs R l.
Proof.
intros HFP x y Hinx.
apply notF_in_inf_notF_in; intros Hiny.
revert Hinx; apply notF_in_inf_notF_in; intros Hinx.
now apply HFP.
Qed.

Lemma ForallPairs_ForallPairs_inf {A} (R : A -> A -> Prop) l :
  ForallPairs R l -> ForallPairs_inf R l.
Proof.
intros HFP x y Hinx Hiny.
apply HFP; now apply in_inf_in.
Qed.

Lemma ForallOrdPairs_inf_ForallOrdPairs {A} (R : A -> A -> Prop) l :
  ForallOrdPairs_inf R l -> ForallOrdPairs R l.
Proof.
  induction 1; constructor; intuition.
  now apply Forall_inf_Forall.
Qed.

Section Repeat.

  Variable A : Type.

  Theorem repeat_spec_inf n (x y : A): In_inf y (repeat x n) -> y=x.
  Proof.
    induction n as [|k Hrec]; simpl; destruct 1; auto.
  Qed.

End Repeat.


(** Max of elements of a list of [nat]: [list_max] *)

Lemma list_max_le_inf : forall l n,
  list_max l <= n -> Forall_inf (fun k => k <= n) l.
Proof.
induction l; simpl; intros n; intros H; intuition.
apply Nat.max_lub_iff in H.
now constructor; [ | apply IHl ].
Qed.

Lemma list_max_lt_inf : forall l n, l <> nil ->
  list_max l < n -> Forall_inf (fun k => k < n) l.
Proof.
induction l; simpl; intros n Hnil; intros H; intuition.
destruct l.
- repeat constructor.
  now simpl in H; rewrite Nat.max_0_r in H.
- apply Nat.max_lub_lt_iff in H.
  now constructor; [ | apply IHl ].
Qed.
