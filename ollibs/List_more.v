(* List_more Library *)

(** * Add-ons for List library
Usefull properties apparently missing in the List library. *)

Require Export List.
Require Import Lt Le Plus Max.



(** ** Simplification in lists *)

Ltac list_simpl :=
  repeat (
    repeat simpl ;
    repeat rewrite <- app_assoc ;
    repeat rewrite <- app_comm_cons ;
    repeat rewrite app_nil_r ;
    repeat rewrite <- map_rev ;
    repeat rewrite rev_involutive ;
    repeat rewrite rev_app_distr ;
    repeat rewrite rev_unit ;
    repeat rewrite map_app ).
Ltac list_simpl_hyp H :=
  repeat (
    repeat simpl in H ;
    repeat rewrite <- app_assoc in H ;
    repeat rewrite <- app_comm_cons in H ;
    repeat rewrite app_nil_r in H ;
    repeat rewrite <- map_rev in H ;
    repeat rewrite rev_involutive in H ;
    repeat rewrite rev_app_distr in H ;
    repeat rewrite rev_unit in H ;
    repeat rewrite map_app in H ).
Tactic Notation "list_simpl" "in" hyp(H) := list_simpl_hyp H.
Ltac list_simpl_hyps :=
  match goal with
  | H : _ |- _ => list_simpl in H ; revert H ; list_simpl_hyps ; intro H
  | _ => idtac
  end.
Ltac list_simpl_all := list_simpl_hyps ; list_simpl.


(** ** Removal of [cons] constructions *)

Lemma cons_is_app {A} : forall (x:A) l, x :: l = (x :: nil) ++ l.
Proof.
reflexivity.
Qed.

Ltac cons2app :=
  repeat
  match goal with
  | |- context [ cons ?x ?l ] =>
         lazymatch l with
         | nil => fail
         | _ => rewrite (cons_is_app x l)
           (* one could prefer
                 change (cons x l) with (app (cons x nil) l)
              which leads to simpler generated term
              but does work not with existential variables *)
         end
  end.
Ltac cons2app_hyp H :=
  repeat
  match type of H with
  | context [ cons ?x ?l ]  =>
      lazymatch l with
      | nil => fail
      | _ =>  rewrite (cons_is_app x l) in H
           (* one could prefer
                 change (cons x l) with (app (cons x nil) l) in 
              which leads to simpler generated term
              but does work not with existential variables *)
      end
  end.
Tactic Notation "cons2app" "in" hyp(H) := cons2app_hyp H.
Ltac cons2app_hyps :=
  match goal with
  | H : _ |- _ => cons2app in H ; revert H ; cons2app_hyps ; intro H
  | _ => idtac
  end.
Ltac cons2app_all := cons2app_hyps ; cons2app.


(** ** Inversions of list equalities *)

Ltac unit_vs_elt_inv H := 
  match type of H with
  | ?a :: nil = ?l1 ++ ?x :: ?l2 =>
      let H1 := fresh H in
      let H2 := fresh H in 
        destruct l1 ; inversion H as [[H1 H2]] ;
        [ (try subst x) ; (try subst l2)
        | destruct l1 ; inversion H2 ]
  end.

Lemma dichot_app {A} : forall (l1 : list A) l2 l3 l4,
  l1 ++ l2 = l3 ++ l4 ->
     (exists l2', l1 ++ l2' = l3 /\ l2 = l2' ++ l4)
  \/ (exists l4', l1 = l3 ++ l4' /\ l4' ++ l2 = l4).
Proof with try assumption ; try reflexivity.
induction l1 ; induction l3 ; intros ;
  simpl in H ; inversion H ; subst.
- right.
  exists (@nil A).
  split ; simpl...
- left.
  exists (a::l3).
  split...
- right.
  exists (a::l1).
  split ; simpl...
- inversion H.
  apply IHl1 in H1.
  destruct H1 as [(l2' & H2'1 & H2'2) | (l4' & H4'1 & H4'2)] ;
    [left | right].
  + exists l2'.
    split...
    simpl.
    rewrite H2'1...
  + exists l4'.
    split...
    simpl.
    rewrite H4'1...
Qed.

Ltac dichot_app_exec H :=
  match type of H with
  | _ ++ _ = _ ++ _ => apply dichot_app in H ;
                         let l2 := fresh "l" in
                         let l4 := fresh "l" in
                         let H1 := fresh H in
                         let H2 := fresh H in
                         destruct H as [(l2 & H1 & H2) | (l4 & H1 & H2)]
  end.

Lemma dichot_elt_app {A} : forall l1 (a : A) l2 l3 l4,
  l1 ++ a :: l2 = l3 ++ l4 ->
     (exists l2', l1 ++ a :: l2' = l3 /\ l2 = l2' ++ l4)
  \/ (exists l4', l1 = l3 ++ l4' /\ l4' ++ a :: l2 = l4).
Proof with try reflexivity.
induction l1 ; induction l3 ; intros ;
  simpl in H ; inversion H ; subst.
- right.
  exists (@nil A).
  split ; simpl...
- left.
  exists l3.
  split...
- right.
  exists (a::l1).
  split ; simpl...
- inversion H.
  apply IHl1 in H1.
  destruct H1 as [(l' & H'1 & H'2) | (l' & H'1 & H'2)] ;
    [left | right] ;
    exists l' ;
    (split ; try assumption) ;
    simpl ;
    rewrite H'1...
Qed.

Ltac dichot_elt_app_exec H :=
  match type of H with
  | _ ++ _ :: _ = _ ++ _ => apply dichot_elt_app in H ;
                              let l2 := fresh "l" in
                              let l4 := fresh "l" in
                              let H1 := fresh H in
                              let H2 := fresh H in
                              destruct H as [(l2 & H1 & H2) | (l4 & H1 & H2)]
  | _ ++ _ = _ ++ _ :: _ => simple apply eq_sym in H ;
                            apply dichot_elt_app in H ;
                              let l2 := fresh "l" in
                              let l4 := fresh "l" in
                              let H1 := fresh H in
                              let H2 := fresh H in
                              destruct H as [(l2 & H1 & H2) | (l4 & H1 & H2)]
  end.

Lemma trichot_elt_app {A} : forall l1 (a : A) l2 l3 l4 l5,
  l1 ++ a :: l2 = l3 ++ l4 ++ l5 ->
      (exists l2', l1 ++ a :: l2' = l3 /\ l2 = l2' ++ l4 ++ l5)
   \/ (exists l2' l2'', l1 = l3 ++ l2' /\ l2' ++ a :: l2'' = l4 /\ l2 = l2'' ++ l5)
   \/ (exists l5', l1 = l3 ++ l4 ++ l5' /\ l5' ++ a :: l2 = l5).
Proof with try reflexivity ; try assumption.
induction l1 ; induction l3 ; intros ;
  simpl in H ; inversion H ; subst.
- destruct l4 ; inversion H.
  + right ; right ; exists nil ; split...
  + right ; left ; exists nil ; exists l4 ; split ; [ | split ]...
- left ; exists l3 ; split...
- destruct l4 ; inversion H ; subst.
  + right ; right ; exists (a :: l1) ; split...
  + dichot_elt_app_exec H3 ; subst.
    * right ; left ; exists (a1 :: l1) ; exists l ; split ; [ | split ]...
    * right ; right ; exists l0 ; split...
- apply IHl1 in H2.
  destruct H2 as [(l' & H'1 & H'2) | [ (l2' & l2'' & H'2 & H'3) | (l' & H'1 & H'2) ]] ;
    [ left | right ; left | right ; right ].
  + exists l' ; try rewrite <- H'1 ; split...
  + destruct H'3 ; subst ; exists l2' ; exists l2'' ; split ; [ | split ]...
  + exists l' ; try rewrite H'1 ; split...
Qed.

Ltac trichot_elt_app_exec H :=
  match type of H with
  | _ ++ _ :: _ = _ ++ _ ++ _ => apply trichot_elt_app in H ;
                                   let l2 := fresh "l" in
                                   let l4 := fresh "l" in
                                   let H1 := fresh H in
                                   let H2 := fresh H in
                                   destruct H as [ (l2 & H1 & H2)
                                                 | [ (l2 & l4 & H1 & H2) | (l4 & H1 & H2) ]]
  | _ ++ _ ++ _ = _ ++ _ :: _ => simple apply eq_sym in H ;
                                   apply trichot_elt_app in H ;
                                   let l2 := fresh "l" in
                                   let l4 := fresh "l" in
                                   let H1 := fresh H in
                                   let H2 := fresh H in
                                   destruct H as [ (l2 & H1 & H2)
                                                 | [ (l2 & l4 & H1 & H2) | (l4 & H1 & H2) ]]
  end.

Lemma trichot_elt_elt {A} : forall l1 (a : A) l2 l3 b l4,
  l1 ++ a :: l2 = l3 ++ b :: l4 ->
      (exists l2', l1 ++ a :: l2' = l3 /\ l2 = l2' ++ b :: l4)
   \/ (l1 = l3 /\ a = b /\ l2 = l4)
   \/ (exists l4', l1 = l3 ++ b :: l4' /\ l4' ++ a :: l2 = l4).
Proof with try assumption ; try reflexivity.
intros l1 a l2 l3 b l4 Heq.
change (b :: l4) with ((b :: nil) ++ l4) in Heq.
apply trichot_elt_app in Heq ;
  destruct Heq as [ | [ (l2' & l2'' & H'1 & H'2 & H'3) | ]] ; subst ;
  [ left | right ; left | right ; right ]...
destruct l2' ; inversion H'2 ; subst ; [ | destruct l2' ; inversion H1 ].
split ; [ | split ]...
rewrite app_nil_r...
Qed.

Ltac trichot_elt_elt_exec H :=
  match type of H with
  | ?lh ++ _ :: ?lr = ?l1 ++ ?x :: ?l2 =>
      apply trichot_elt_elt in H ;
        let l' := fresh "l" in
        let H1 := fresh H in
        let H2 := fresh H in
        let H3 := fresh H in
        destruct H as [(l' & H1 & H2) | [(H1 & H2 & H3) | (l' & H1 & H2)]] ;
        [ (try subst l1) ; (try subst lr)
        | (try subst x) ; (try subst l1) ; (try subst l2)
        | (try subst l2) ; (try subst lh) ]
  end.


(** ** [In] *)

Lemma in_elt {A} : forall (a:A) l1 l2, In a (l1 ++ a :: l2).
Proof.
intros.
apply in_or_app.
right. intuition.
Qed.

Lemma in_elt_inv {A} : forall (a b : A) l1 l2,
  In a (l1 ++ b :: l2) -> a = b \/ In a (l1 ++ l2).
Proof.
intros.
apply in_app_or in H.
destruct H ; intuition.
destruct H ; intuition.
Qed.

(** ** [last] *)

Lemma last_last {A} : forall l (a b : A), last (l ++ (a :: nil)) b = a.
Proof with try reflexivity.
induction l ; intros ; simpl...
rewrite IHl.
destruct l ; simpl...
Qed.

Lemma removelast_last {A} : forall l (a : A), removelast (l ++ (a :: nil)) = l.
Proof with try reflexivity.
induction l ; intros ; simpl...
rewrite IHl.
destruct l ; simpl...
Qed.

Lemma map_last : forall A B (f : A -> B) l a,
  map f (l ++ a :: nil) = (map f l) ++ (f a) :: nil.
Proof with try reflexivity.
induction l ; intros ; simpl...
rewrite IHl...
Qed.


(** ** [rev] *)

Lemma app_eq_rev {A} : forall l1 l2 l3 : list A,
  l1 ++ l2 = rev l3 ->
    exists l1' l2', l3 = l2' ++ l1' /\ l1 = rev l1' /\ l2 = rev l2'.
Proof with try assumption ; try reflexivity.
intros l1 l2 ; revert l1.
induction l2 using rev_ind ; intros.
- exists l3 ; exists (@nil A).
  split ; [ | split]...
  rewrite app_nil_r in H...
- destruct l3.
  + destruct l1 ; destruct l2 ; inversion H.
  + simpl in H.
    assert (l1 ++ l2 = rev l3) as Hrev.
    { rewrite app_assoc in H.
      remember (l1 ++ l2) as l4.
      remember (rev l3) as l5.
      clear - H.
      revert l4 H ; induction l5 ; intros l4 H.
      - destruct l4 ; inversion H...
        destruct l4 ; inversion H2.
      - destruct l4 ; inversion H.
        + destruct l5 ; inversion H2.
        + apply IHl5 in H2 ; subst... }
    apply IHl2 in Hrev.
    destruct Hrev as (l1' & l2' & Heq1 & Heq2 & Heq3) ; subst.
    exists l1' ; exists (x :: l2') ; split ; [ | split ]...
    rewrite rev_app_distr in H.
    rewrite <- app_assoc in H.
    apply app_inv_head in H.
    apply app_inv_head in H.
    inversion H ; subst...
Qed.


(** ** Decomposition of [map] *)

Lemma app_eq_map {A B} : forall (f : A -> B) l1 l2 l3,
  l1 ++ l2 = map f l3 ->
    exists l1' l2', l3 = l1' ++ l2' /\ l1 = map f l1' /\ l2 = map f l2'.
Proof with try assumption ; try reflexivity.
intros f.
induction l1 ; intros.
- exists (@nil A) ; exists l3.
  split ; [ | split]...
- destruct l3 ; inversion H.
  apply IHl1 in H2.
  destruct H2 as (? & ? & ? & ? & ?) ; subst.
  exists (a0::x) ; exists x0.
  split ; [ | split]...
Qed.

Lemma cons_eq_map {A B} : forall (f : A -> B) a l2 l3,
  a :: l2 = map f l3 ->
    exists b l2', l3 = b :: l2' /\ a = f b /\ l2 = map f l2'.
Proof.
intros f a l2 l3 H.
destruct l3 ; inversion H ; subst.
eexists ; eexists ; split ; [ | split] ;
  try reflexivity ; try eassumption.
Qed.

Ltac decomp_map_eq H Heq :=
  match type of H with
  | _ ++ _ = map _ _ => apply app_eq_map in H ;
                          let l1 := fresh "l" in
                          let l2 := fresh "l" in
                          let H1 := fresh H in
                          let H2 := fresh H in
                          let Heq1 := fresh Heq in
                          destruct H as (l1 & l2 & Heq1 & H1 & H2) ;
                          rewrite Heq1 in Heq ; clear Heq1 ;
                          decomp_map_eq H1 Heq ; decomp_map_eq H2 Heq
  | _ :: _ = map _ _ => apply cons_eq_map in H ;
                          let x := fresh "x" in
                          let l2 := fresh "l" in
                          let H1 := fresh H in
                          let H2 := fresh H in
                          let Heq1 := fresh Heq in
                          destruct H as (x & l2 & Heq1 & H1 & H2) ;
                          rewrite Heq1 in Heq ; clear Heq1 ;
                          decomp_map_eq H2 Heq
  | _ => idtac
  end.

Ltac decomp_map H :=
  match type of H with
  | _ = map _ ?l => let l' := fresh "l" in
                    let Heq := fresh H in
                    remember l as l' eqn:Heq in H ;
                    decomp_map_eq H Heq ;
                    let H' := fresh H in
                    clear l' ;
                    rename Heq into H'
  end.


(** ** [flat_map] *)

Lemma flat_map_app {A B} : forall (f : A -> list B) l1 l2,
  flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof with try reflexivity.
intros f l1 l2.
induction l1...
simpl.
rewrite IHl1.
rewrite app_assoc...
Qed.

Lemma flat_map_ext : forall (A B : Type) (f g : A -> list B),
  (forall a, f a = g a) -> forall l, flat_map f l = flat_map g l.
Proof with try reflexivity.
intros A B f g Hext.
induction l...
simpl.
rewrite Hext.
rewrite IHl...
Qed.


(** ** Set inclusion on list *)

Lemma incl_nil {A} : forall l : list A, incl nil l.
Proof.
intros l a Hin.
inversion Hin.
Qed.

Lemma incl_app_app {A} : forall l1 l2 m1 m2:list A,
  incl l1 m1 -> incl l2 m2 -> incl (l1 ++ l2) (m1 ++ m2).
Proof.
intros l1 l2 m1 m2 Hi1 Hi2.
apply incl_app.
- apply incl_appl.
  assumption.
- apply incl_appr.
  assumption.
Qed.

Lemma incl_cons_inv {A} : forall (a:A) (l m:list A),
  incl (a :: l) m -> In a m /\ incl l m.
Proof.
intros a l m Hi.
split.
- apply Hi.
  constructor.
  reflexivity.
- intros b Hin.
  apply Hi.
  apply in_cons.
  assumption.
Qed.


(** ** [Forall] and [Exists] *)

Lemma Forall_app_inv {A} : forall P (l1 : list A) l2,
  Forall P (l1 ++ l2) -> Forall P l1 /\ Forall P l2.
Proof with try assumption.
induction l1 ; intros.
- split...
  constructor.
- inversion H ; subst.
  apply IHl1 in H3.
  destruct H3.
  split...
  constructor...
Qed.

Lemma Forall_app {A} : forall P (l1 : list A) l2,
  Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof with try assumption.
induction l1 ; intros...
inversion H ; subst.
apply IHl1 in H0...
constructor...
Qed.

Lemma Forall_In {A} : forall P l (a : A), Forall P l -> In a l -> P a.
Proof.
intros.
eapply (proj1 (Forall_forall _ _)) in H ; eassumption.
Qed.

Lemma Forall_elt {A} : forall P l1 l2 (a : A), Forall P (l1 ++ a :: l2) -> P a.
Proof.
intros P l1 l2 a HF.
eapply Forall_In ; try eassumption.
apply in_elt.
Qed.

Lemma Forall_wedge {A} : forall P Q (l : list A),
  (Forall (fun x => P x /\ Q x) l) -> Forall P l /\ Forall Q l.
Proof with try assumption.
induction l ; intro Hl ; split ; constructor ; inversion Hl ; subst.
- destruct H1...
- apply IHl...
- destruct H1...
- apply IHl...
Qed.

Lemma Forall_nth {A} : forall P l,
  Forall P l -> forall i (a : A), i < length l -> P (nth i l a).
Proof with try assumption.
induction l ; intros.
- inversion H0.
- destruct i ; inversion H...
  simpl in H0.
  apply IHl...
  apply lt_S_n...
Qed.

Lemma exists_Forall {A B} : forall (P : A -> B -> Prop) l,
  (exists k, Forall (P k) l) -> Forall (fun x => exists k, P k x) l .
Proof with try eassumption ; try reflexivity.
induction l ; intros ; constructor ;
  destruct H as [k H] ; inversion H ; subst.
- eexists...
- apply IHl...
  eexists...
Qed.

Lemma Forall_map {A B} : forall (f : A -> B) l,
  Forall (fun x => exists y, x = f y) l <-> exists l0, l = map f l0.
Proof with try reflexivity.
induction l ; split ; intro H.
- exists (@nil A)...
- constructor.
- inversion H ; subst.
  destruct H2 as [y Hy] ; subst.
  apply IHl in H3.
  destruct H3 as [l0 Hl0] ; subst.
  exists (y :: l0)...
- destruct H as [l0 Heq].
  destruct l0 ; inversion Heq ; subst.
  constructor.
  + exists a0...
  + apply IHl.
    exists l0...
Qed.

Lemma map_ext_Forall {A B} : forall (f g : A -> B) l,
  Forall (fun x => f x = g x) l -> map f l = map g l.
Proof.
intros ; apply map_ext_in ; apply Forall_forall ; assumption.
Qed.

Lemma Forall_rev {A} : forall P (l : list A), Forall P l -> Forall P (rev l).
Proof with try assumption.
induction l ; intros HP.
- constructor.
- inversion HP ; subst.
  apply IHl in H2.
  apply Forall_app...
  constructor...
  constructor.
Qed.

Lemma inc_Forall {A} : forall (P : nat -> A -> Prop) l i j,
  (forall i j a, P i a -> i <= j -> P j a) ->
    Forall (P i) l -> i <= j -> Forall (P j) l.
Proof with try eassumption.
intros P l i j Hinc.
induction l ; intros H Hl ; constructor ; inversion H.
- eapply Hinc...
- apply IHl...
Qed.

Lemma Exists_app_inv {A} : forall (P : A -> Prop) l1 l2,
  Exists P (l1 ++ l2) -> Exists P l1 \/ Exists P l2.
Proof with try assumption.
induction l1 ; intros.
- right...
- inversion H ; subst.
  + left.
    apply Exists_cons_hd...
  + apply IHl1 in H1.
    destruct H1.
    * left.
      apply Exists_cons_tl...
    * right...
Qed.

Lemma Exists_app {A} : forall (P : A -> Prop) l1 l2,
  (Exists P l1 \/ Exists P l2) -> Exists P (l1 ++ l2).
Proof with try assumption.
induction l1 ; intros...
- destruct H...
  inversion H.
- destruct H.
  + inversion H ; subst.
    * apply Exists_cons_hd...
    * apply Exists_cons_tl.
      apply IHl1.
      left...
  + apply Exists_cons_tl.
    apply IHl1.
    right...
Qed.

Lemma Exists_rev {A} : forall P (l : list A), Exists P l -> Exists P (rev l).
Proof with try assumption.
induction l ; intros HP ; inversion HP ; subst ;
  apply Exists_app.
- right ; constructor...
- left.
  apply IHl...
Qed.

Lemma Exists_impl {A} : forall (P Q : A -> Prop), (forall a, P a -> Q a) ->
  forall l, Exists P l -> Exists Q l.
Proof.
intros P Q Hi.
induction l ; intros He ; inversion He ; subst.
- apply Hi in H0 ; now constructor.
- apply IHl in H0 ; now constructor.
Qed.


(** ** Map for functions with two arguments : [map2] *)

Fixpoint map2 {A B C} (f : A -> B -> C) l1 l2 :=
  match l1 , l2 with
  | nil , _ => nil
  | _ , nil => nil
  | a1::r1 , a2::r2 => (f a1 a2)::(map2 f r1 r2)
  end.

Lemma map2_length {A B C} : forall (f : A -> B -> C) l1 l2,
  length l1 = length l2 -> length (map2 f l1 l2) = length l2.
Proof with try assumption ; try reflexivity.
induction l1 ; intros...
destruct l2.
+ inversion H.
+ simpl in H.
  injection H ; intro H'.
  apply IHl1 in H'.
  simpl...
  rewrite H'...
Qed.

Lemma length_map2 {A B C} : forall (f : A -> B -> C) l1 l2,
  length (map2 f l1 l2) <= length l1 /\ length (map2 f l1 l2) <= length l2.
Proof.
induction l1 ; intros.
- split ; apply le_0_n.
- destruct l2.
  + split ; apply le_0_n.
  + destruct (IHl1 l2) as [H1 H2].
    split ; simpl ; apply le_n_S ; assumption.
Qed.

Lemma nth_map2 {A B C} : forall (f : A -> B -> C) l1 l2 i a b c,
  i < length (map2 f l1 l2) ->
    nth i (map2 f l1 l2) c = f (nth i l1 a) (nth i l2 b).
Proof with try assumption ; try reflexivity.
induction l1 ; intros.
- inversion H.
- destruct l2.
  + inversion H.
  + destruct i...
    simpl.
    apply IHl1.
    simpl in H.
    apply lt_S_n...
Qed.


(** ** Sum of elements of a list of [nat] : [list_sum] *)

Definition list_sum l := fold_right plus 0 l.

Lemma list_sum_app : forall l1 l2,
   list_sum (l1 ++ l2) = list_sum l1 + list_sum l2.
Proof with try reflexivity.
induction l1 ; intros l2...
simpl ; rewrite IHl1.
rewrite plus_assoc...
Qed.

(** ** Max of elements of a list of [nat] : [list_max] *)

Definition list_max l := fold_right max 0 l.

Lemma list_max_app : forall l1 l2,
   list_max (l1 ++ l2) = max (list_max l1) (list_max l2).
Proof with try reflexivity.
induction l1 ; intros l2...
simpl ; rewrite IHl1.
rewrite max_assoc...
Qed.


