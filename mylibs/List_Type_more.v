(* List_Type_more Library *)

(** * Add-ons for List library
Usefull properties apparently missing in the List library with Type-compatible outputs. *)

Require Export List.
Require Export List_Type.

(** ** Decomposition of [app] *)

Lemma dichot_Type_app {A} : forall (l1 : list A) l2 l3 l4,
  l1 ++ l2 = l3 ++ l4 ->
     { l2' | l1 ++ l2' = l3 /\ l2 = l2' ++ l4 }
   + { l4' | l1 = l3 ++ l4' /\ l4' ++ l2 = l4 }.
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

Ltac dichot_Type_app_exec H :=
  lazymatch type of H with
  | _ ++ _ = _ ++ _ => apply dichot_Type_app in H ;
                         let l2 := fresh "l" in
                         let l4 := fresh "l" in
                         let H1 := fresh H in
                         let H2 := fresh H in
                         destruct H as [(l2 & H1 & H2) | (l4 & H1 & H2)]
  | _ => fail
  end.

Lemma dichot_Type_elt_app {A} : forall l1 (a : A) l2 l3 l4,
  l1 ++ a :: l2 = l3 ++ l4 ->
     { l2' | l1 ++ a :: l2' = l3 /\ l2 = l2' ++ l4 }
   + { l4' | l1 = l3 ++ l4' /\ l4' ++ a :: l2 = l4 }.
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

Ltac dichot_Type_elt_app_exec H :=
  lazymatch type of H with
  | _ ++ _ :: _ = _ ++ _ => apply dichot_Type_elt_app in H ;
                              let l2 := fresh "l" in
                              let l4 := fresh "l" in
                              let H1 := fresh H in
                              let H2 := fresh H in
                              destruct H as [(l2 & H1 & H2) | (l4 & H1 & H2)]
  | _ ++ _ = _ ++ _ :: _ => simple apply eq_sym in H ;
                            apply dichot_Type_elt_app in H ;
                              let l2 := fresh "l" in
                              let l4 := fresh "l" in
                              let H1 := fresh H in
                              let H2 := fresh H in
                              destruct H as [(l2 & H1 & H2) | (l4 & H1 & H2)]
  | _ => fail
  end.


(** ** Decomposition of [map] *)

Lemma app_eq_map_Type {A B} : forall (f : A -> B) l1 l2 l3,
  l1 ++ l2 = map f l3 ->
    { pl | l3 = fst pl ++ snd pl /\ l1 = map f (fst pl) /\ l2 = map f (snd pl) }.
Proof with try assumption ; try reflexivity.
intros f.
induction l1 ; intros.
- exists (@nil A, l3).
  split ; [ | split]...
- destruct l3 ; inversion H.
  apply IHl1 in H2.
  destruct H2 as ((l & l0) & ? & ? & ?) ; subst.
  exists (a0 :: l, l0).
  split ; [ | split]...
Qed.

Lemma cons_eq_map_Type {A B} : forall (f : A -> B) a l2 l3,
  a :: l2 = map f l3 ->
    { pl | l3 = fst pl :: snd pl /\ a = f (fst pl) /\ l2 = map f (snd pl) }.
Proof.
intros f a l2 l3 H.
destruct l3 ; inversion H ; subst.
exists (a0, l3) ; split ; [ | split] ;
  try reflexivity ; try eassumption.
Qed.

Ltac decomp_map_Type_eq H Heq :=
  lazymatch type of H with
  | _ ++ _ = map _ _ => apply app_eq_map_Type in H ;
                          let l1 := fresh "l" in
                          let l2 := fresh "l" in
                          let H1 := fresh H in
                          let H2 := fresh H in
                          let Heq1 := fresh Heq in
                          destruct H as ((l1 & l2) & Heq1 & H1 & H2) ;
                          rewrite Heq1 in Heq ; clear Heq1 ;
                          decomp_map_Type_eq H1 Heq ; decomp_map_Type_eq H2 Heq
  | _ :: _ = map _ _ => apply cons_eq_map_Type in H ;
                          let x := fresh "x" in
                          let l2 := fresh "l" in
                          let H1 := fresh H in
                          let H2 := fresh H in
                          let Heq1 := fresh Heq in
                          destruct H as ((x & l2) & Heq1 & H1 & H2) ;
                          rewrite Heq1 in Heq ; clear Heq1 ;
                          decomp_map_Type_eq H2 Heq
  | _ => idtac
  end.

Ltac decomp_map_Type H :=
  match type of H with
  | _ = map _ ?l => let l' := fresh "l" in
                    let Heq := fresh H in
                    remember l as l' eqn:Heq in H ;
                    decomp_map_Type_eq H Heq ;
                    let H' := fresh H in
                    clear l' ;
                    rename Heq into H'
  end.


(** ** [Forall] and [Exists] *)

Lemma Forall_Type_app_inv {A} : forall P (l1 : list A) l2,
  Forall_Type P (l1 ++ l2) -> Forall_Type P l1 * Forall_Type P l2.
Proof with try assumption.
induction l1 ; intros.
- split...
  constructor.
- inversion X ; subst.
  apply IHl1 in X1.
  destruct X1.
  split...
  constructor...
Qed.

Lemma Forall_Type_app {A} : forall P (l1 : list A) l2,
  Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof with try assumption.
induction l1 ; intros...
inversion H ; subst.
apply IHl1 in H0...
constructor...
Qed.

