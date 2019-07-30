(* flat_map_Type_more Library *)

(** * Add-ons for List library
Properties of flat_map. *)

Require Import Injective.
Require Import List_more.
Require Import List_Type_more.
Require Import Permutation_Type_more.
Require Import CyclicPerm_Type.

Lemma flat_map_elt {A B} {f : A -> list B} : forall a L l1 l2,
     flat_map f L = l1 ++ a :: l2 ->
     {' (L1,L2,L0,l1',l2') | l1 = flat_map f L1 ++ l1' /\ l2 = l2' ++ 
flat_map f L2
                          /\ L = L1 ++ L0 :: L2 /\ f L0 = l1' ++ a :: l2' }.
Proof with try reflexivity.
   intros a L l1 l2 Heq.
   rewrite flat_map_concat_map in Heq.
   apply concat_elt in Heq. destruct Heq as ((((L1 & L2) & l1'') & l2'') & 
eqb & eqt & eq) ; subst.
   symmetry in eq ; decomp_map_Type eq ; subst.
   simpl in eq3 ; symmetry in eq3.
   exists (l0,l2,x,l1'',l2'') ; simpl ; split; [ | split ; [ | split ]] ; try rewrite 
flat_map_concat_map...
   assumption.
Qed.

Lemma app_vs_flat_map {B T} {f : B -> T} : forall L l1 l2,
  l1 ++ l2 = flat_map (fun p => f (fst p) :: (snd p)) L ->
      {' (L1, L2, n, l3, l4) | l4 <> nil
          /\ L = L1 ++ (n , l3 ++ l4) :: L2
          /\ l1 = flat_map (fun p => f (fst p) :: (snd p)) (L1 ++ (n, l3) :: nil)
          /\ l2 = l4 ++ flat_map (fun p => (f (fst p)) :: (snd p)) L2 }
       + {' (L1, L2) | L = L1 ++ L2
          /\ l1 = flat_map (fun p => f (fst p) :: (snd p)) L1
          /\ l2 = flat_map (fun p => f (fst p) :: (snd p)) L2 }.
Proof with try assumption ; try reflexivity.
induction L ; intros l1 l2 Heq.
- right.
  simpl in Heq.
  apply app_eq_nil in Heq ; destruct Heq ; subst.
  exists (nil, nil) ; split ; [ | split ]...
- simpl in Heq.
  rewrite app_comm_cons in Heq.
  dichot_Type_app_exec Heq ; subst.
  + destruct l1.
    * simpl in Heq0 ; subst.
      right.
      exists (nil, a :: L) ; split ; [ | split ]...
    * inversion Heq0 ; subst.
      destruct l.
      -- right.
         destruct a; simpl in H1.
         rewrite app_nil_r in H1.
         exists ((b,l1) :: nil , L) ; split ; [ | split ] ; simpl ; try rewrite app_nil_r...
         rewrite H1...
      -- left.
         destruct a; simpl in H1.
         exists (nil, L, b , l1, t :: l) ; split ; [ | split ; [ | split ]] ;
           simpl ; try rewrite app_nil_r...
         ++ intros Heq ; inversion Heq.
         ++ rewrite H1...
  + apply IHL in Heq1.
    destruct Heq1 as [ (((((L1 & L2) & n) & l1') & l2') & (Hnil & Heq1 & Heq2 & Heq3))
                     | [[L1 L2] (Heq1 & Heq2 & Heq3)]] ; [left | right].
    * exists (a :: L1, L2, n, l1', l2') ; split ; [ | split ; [ | split ]]  ; subst...
    * exists (a :: L1, L2) ; split ; [ | split ]  ; subst...
Qed.

Ltac app_vs_flat_map_inv H :=
  match type of H with
  | ?lh ++ ?lr = flat_map (fun p => ?f (fst p) :: (snd p)) ?L =>
      apply app_vs_flat_map in H ;
        let l1 := fresh "l" in
        let l2 := fresh "l" in
        let n := fresh "n" in
        let L1 := fresh "L" in
        let L2 := fresh "L" in
        let Hnil := fresh "Hnil" in
        let H1 := fresh H in
        let H2 := fresh H in
        let H3 := fresh H in
        destruct H as [ (((((L1 & L2) & n) & l1) & l2) & (Hnil & H1 & H2 & H3))
                     | [[L1 L2] (H1 & H2 & H3)]] ;
        (try simpl in Hnil) ; (try simpl in H1) ; (try simpl in H2) ; (try simpl in H3) ; subst
  end.

Lemma app_vs_app_flat_map {B T} {f : B -> T} : forall l0 L l1 l2,
  l1 ++ l2 = l0 ++ flat_map (fun p => f (fst p) :: (snd p)) L ->
      { l' | l' <> nil
          /\ l0 = l1 ++ l'
          /\ l2 = l' ++ flat_map (fun p => f (fst p) :: (snd p)) L }
      + {' (L1, L2, n, l3, l4) | l4 <> nil
          /\ L = L1 ++ (n , l3 ++ l4) :: L2
          /\ l1 = l0 ++ flat_map (fun p => f (fst p) :: (snd p)) (L1 ++ (n, l3) :: nil)
          /\ l2 = l4 ++ flat_map (fun p => f (fst p) :: (snd p)) L2 }
      + {' (L1, L2) | L = L1 ++ L2
          /\ l1 = l0 ++ flat_map (fun p => f (fst p) :: (snd p)) L1
          /\ l2 = flat_map (fun p => f (fst p) :: (snd p)) L2 }.
Proof with try assumption ; try reflexivity.
intros l0 L l1 l2 Heq.
dichot_Type_app_exec Heq.
- destruct l.
  + right ; subst.
    exists (nil, L) ; simpl ; split ; [ | split ]...
    rewrite 2 app_nil_r...
  + left ; left.
    exists (t :: l) ; subst ; split ; [ | split ]...
    intros Heq ; inversion Heq.
- subst.
  app_vs_flat_map_inv Heq1.
  + left ; right.
    exists (L0, L1, n, l, l1) ; split ; [ | split ; [ | split ]]...
  + right.
    exists (L0, L1) ; split ; [ | split ]...
Qed.

Ltac app_vs_app_flat_map_inv H :=
  match type of H with
  | ?lh ++ ?lr = ?l0 ++ flat_map (fun p => ?f (fst p) :: (snd p)) ?L =>
      apply app_vs_app_flat_map in H ;
        let l1 := fresh "l" in
        let l2 := fresh "l" in
        let n := fresh "n" in
        let L1 := fresh "L" in
        let L2 := fresh "L" in
        let Hnil := fresh "Hnil" in
        let H1 := fresh H in
        let H2 := fresh H in
        let H3 := fresh H in
        destruct H as [ [[l1 (Hnil & H1 & H2)]
                        |(((((L1 & L2) & n) & l1) & l2) & (Hnil & H1 & H2 & H3))]
                      | [[L1 L2] (H1 & H2 & H3)]] ;
        (try simpl in Hnil) ; (try simpl in H1) ; (try simpl in H2) ; (try simpl in H3) ; subst
  end.

Lemma elt_vs_app_flat_map {C T} {f : C -> T} : forall l0 L l1 l2 B,
  l1 ++ B :: l2 = l0 ++ flat_map (fun p => f (fst p) :: snd p) L ->
      { l' | l0 = l1 ++ B :: l'
          /\ l2 = l' ++ flat_map (fun p => f (fst p) :: snd p) L }
    + {' (L1, L2, n, l1',l2') | L = L1 ++ (n , l1' ++ B :: l2') :: L2
          /\ l1 = l0 ++ flat_map (fun p => f (fst p) :: snd p) L1 ++ (f n :: l1')
          /\ l2 = l2' ++ flat_map (fun p => f (fst p) :: snd p) L2 }
    + {' (L1 , L2, n , l) | B = f n
          /\ L = L1 ++ (n , l) :: L2
          /\ l1 = l0 ++ flat_map (fun p => f (fst p) :: snd p) L1
          /\ l2 = l ++ flat_map (fun p => f (fst p) :: snd p) L2 }.
Proof with try assumption ; try reflexivity.
intros l0 L l1 l2 B Heq.
dichot_Type_elt_app_exec Heq.
- left ; left.
  exists l ; subst ; split...
- subst.
  revert l3 l2 Heq1 ; induction L ; intros l3 l2 Heq.
  + exfalso ; destruct l3 ; inversion Heq.
  + simpl in Heq ; rewrite app_comm_cons in Heq.
    dichot_Type_elt_app_exec Heq.
    * destruct l3 ; inversion Heq0 ; subst.
      -- right.
         destruct a as (n , l').
         exists (nil, L, n , l'); split ; [ | split ; [ | split] ]...
      -- left ; right.
         destruct a as (n , l').
         exists (nil, L, n , l3, l) ; split ; [ | split ]...
         rewrite H1...
    * apply IHL in Heq1 ; destruct Heq1 as [[Heqa | Heqb] | [Heq Heqc]].
      -- destruct Heqa as [l [Heqa _]].
         exfalso.
         rewrite <- (app_nil_r l0) in Heqa.
         rewrite <- 2 app_assoc in Heqa.  apply app_inv_head in Heqa.
         simpl in Heqa ; destruct l1 ; inversion Heqa.
      -- left ; right.
         destruct Heqb as (((((L' & L'') & n) & l') & l'') & (Heqb1 & Heqb2 & Heqb3)).
         simpl in Heqb1 ; simpl in Heqb2 ; simpl in Heqb3.
         apply app_inv_head in Heqb2.
         destruct a as (n' & l0').
         exists ((n' , l0') :: L', L'', n, l', l'') ; simpl ; subst ; split ; [ | split ]...
         simpl.
         rewrite ? app_assoc...
      -- right.
         destruct Heq as (((L' & L'') & n) & l').
         destruct Heqc as (Heqc & Heqc1 & Heqc2 & Heqc3).
         simpl in Heqc1 ; simpl in Heqc2 ; simpl in Heqc3.
         apply app_inv_head in Heqc2.
         exists (a :: L', L'', n , l') ; simpl ; subst ; split ; [ | split ; [| split] ]...
Qed.

Ltac elt_vs_app_flat_map_inv H :=
  match type of H with
  | ?lh ++ _ :: ?lr = ?l0 ++ flat_map (fun p => ?f (fst p) ?A :: snd p) ?L =>
      apply elt_vs_app_flat_map in H ;
        let l1 := fresh "l" in
        let l2 := fresh "l" in
        let L1 := fresh "L" in
        let L2 := fresh "L" in
        let n := fresh "n" in
        let H1 := fresh H in
        let H2 := fresh H in
        let H3 := fresh H in
        let Heq := fresh "HeqA" in
        destruct H as [ [[l1 [H1 H2]]
                      | [[((((L1 & L2) & n) & l1) &l2)] (H1 & H2 & H3)]]
                      | [[((L1 & L2) & n & l1)] (Heq & H1 & H2 & H3)]] ;
        [ | | try (inversion HeqA ; fail) ] ;
        (try simpl in H1) ; (try simpl in H2) ; (try simpl in H3) ; subst
  end.

Lemma map_f_flat_map {T T1 T2} {g : T -> T2} : forall (f : T1 -> T2) lw' lw l L,
  map f lw = l ++ flat_map (fun p => g (fst p) :: (snd p)) L ->
  { Lw | l ++ flat_map (fun p => app (map f lw') (snd p)) L = map f Lw }.
Proof.
intros f lw' lw l L ; revert lw l ; induction L ; intros lw l Heq ; simpl in Heq ; simpl.
- subst ; exists lw ; symmetry ; assumption.
- rewrite app_comm_cons in Heq ; rewrite app_assoc in Heq.
  apply IHL in Heq ; destruct Heq as [Lw Heq].
  decomp_map_Type Heq ; simpl in Heq1 ; simpl in Heq2.
  inversion Heq1 ; subst.
  rewrite Heq2 ; simpl.
  exists (l3 ++ lw' ++ l5 ++ l2); simpl in Heq5; rewrite Heq5 ; rewrite <- ? map_app.
  rewrite <- app_assoc ; reflexivity.
Qed.

Lemma perm_Type_app_flat_map {B T} {f : B -> T}: forall lw0 L lw l,
  Permutation_Type lw (l ++ flat_map (fun p => f (fst p) :: snd p) L) ->
{' (L', lw') : _ & prod (L <> nil -> L' <> nil)
      (prod (lw = lw' ++ flat_map (fun p => f (fst p) :: snd p) L')
            (Permutation_Type (lw' ++ flat_map (fun p => app lw0 (snd p)) L')
                              (l ++ flat_map (fun p => app lw0 (snd p)) L))) }.
Proof with try assumption ; try reflexivity.
induction L ; intros lw l HP ; simpl in HP ; simpl.
- exists (nil, lw) ; subst ; simpl ; split ; [ | split ] ; try (rewrite app_nil_r)...
  intros...
- destruct (Permutation_Type_vs_elt_inv _ _ _ _ HP) as ([lw1 lw2] & HP2) ; subst ; simpl in HP.
  apply Permutation_Type_app_inv in HP.
  rewrite app_assoc in HP ; apply IHL in HP.
  destruct HP as [[L' l'] (Hnil' & HeqL' & HP')].
  simpl in Hnil' ; simpl in HeqL' ; simpl in HP' ; simpl.
  simpl in HeqL'; app_vs_app_flat_map_inv HeqL'.
  + destruct a as (n & a).
    exists ((n , l0) :: L', lw1) ; split ; [ | split ] ; simpl...
    * intros _ Heqnil ; inversion Heqnil.
    * rewrite <- ? app_assoc in HP' ; rewrite <- ? app_assoc.
      apply Permutation_Type_app_middle...
  + destruct a as (n' & a).
    exists (L0 ++ (n , l0) :: (n' , l1) :: L1, l') ; split ; [ | split ] ; simpl...
    * intros _ Heqnil ; destruct L0 ; inversion Heqnil.
    * repeat (rewrite ? flat_map_app ; rewrite <- app_assoc) ; simpl ; rewrite app_nil_r...
    * rewrite ? flat_map_app in HP' ; simpl in HP' ; rewrite <- app_assoc in HP'...
      rewrite ? flat_map_app ; simpl...
      rewrite <- ? app_assoc ; rewrite app_assoc ; apply Permutation_Type_app_middle ; simpl.
      etransitivity ; [ | rewrite app_assoc ; apply HP'].
      rewrite app_assoc ; rewrite (app_assoc l') ; apply Permutation_Type_app_middle.
      rewrite <- ? app_assoc...
  + destruct a as (n , a).
    exists (L0 ++ (n , nil) :: L1, l') ; split ; [ | split ] ; simpl...
    * intros _ Heqnil ; destruct L0 ; inversion Heqnil.
    * rewrite ? flat_map_app ; rewrite <- app_assoc...
    * rewrite ? flat_map_app in HP' ; rewrite <- app_assoc in HP'...
      rewrite ? flat_map_app ; rewrite <- app_assoc...
      simpl ; rewrite app_nil_r ; rewrite app_assoc ; apply Permutation_Type_app_middle ;
        rewrite <- app_assoc...
Qed.

Lemma perm_Type_f_app_flat_map {T T1 T2} {g : T -> T2} : forall (f : T1 -> T2) lw0 L lw lw' l,
  Permutation_Type lw lw' -> map f lw' = l ++ flat_map (fun p => g (fst p) :: snd p) L ->
{' (L' , lw') : _ & prod (L <> nil -> L' <> nil)
      (prod (map f lw = lw' ++ flat_map (fun p => g (fst p) :: snd p) L')
            (Permutation_Type (lw' ++ flat_map (fun p => app (map f lw0) (snd p)) L')
                              (l ++ flat_map (fun p => app (map f lw0) (snd p)) L))) }.
Proof.
intros f lw0 L lw lw' l HP Heq.
apply (Permutation_Type_map f) in HP ; rewrite Heq in HP.
apply perm_Type_app_flat_map ; assumption.
Qed.

Lemma perm_flat_map_cons_flat_map_app {T T1 T2} {g : T -> T2} :
forall (f : T1 -> T2), injective f -> forall l0 l1 l2 lp1 lp2 l L,
  Permutation_Type lp1 lp2 ->
  l1 ++ map f lp2 ++ l2 = l ++ flat_map (fun p => g (fst p) :: snd p) L ->
{' (l1',l2',l3',l4',l',L') : _ &  prod (l1 ++ map f lp1 ++ l2 = l' ++ flat_map (fun p => g (fst p) :: snd p) L')
            (prod (Permutation_Type l1' l2')
                  (prod (l3' ++ map f l1' ++ l4'
                             = l' ++ flat_map (fun p => (app (map f l0) (snd p))) L')
                        (l3' ++ map f l2' ++ l4'
                             = l ++ flat_map (fun p => (app (map f l0) (snd p))) L))) }.
Proof with try assumption ; try reflexivity.
intros f Hinj l0 l1 l2 lp1 lp2 l L HP Heq.
app_vs_app_flat_map_inv Heq.
- app_vs_app_flat_map_inv Heq1.
  + exists (lp1,lp2,l1,l ++ flat_map (fun p => (app (map f l0) (snd p))) L,l1 ++ map f lp1 ++ l,L) ;
      list_simpl ; split ; [ | split ; [ | split ]]...
  + destruct (perm_Type_f_app_flat_map f l0 _ _ _ _ HP Heq2) as [[L' l'] (Hnil' & HeqL' & HPL')] ;
      simpl in Hnil' ; simpl in HeqL' ; simpl in HPL'.
    destruct (map_f_flat_map f l0 _ _ _ Heq2) as [Lp HeqLp].
    destruct (map_f_flat_map f l0 _ _ _ HeqL') as [Lp' HeqLp'].
    assert (Permutation_Type Lp' Lp) as HPp
      by (rewrite HeqLp in HPL' ; rewrite HeqLp' in HPL' ; apply (Permutation_Type_map_inv_inj _ Hinj _ _ HPL')).
    induction L' using rev_ind_Type ;
      [ exfalso ; apply Hnil' ; [ intros Heqnil ; destruct L0 ; inversion Heqnil | reflexivity ]
      | clear IHL' ].
    destruct x as (n' , x).
    exists (Lp',Lp,l1,l4 ++ flat_map (fun p => (app (map f l0) (snd p))) L1,l1 ++ l',L' ++ (n' , x ++ l4) :: L1) ;
      list_simpl ; split ; [ | split ; [ | split ]] ;
      try rewrite HeqL'; try rewrite <- HeqLp' ; try rewrite <- HeqLp ; rewrite ? flat_map_app ; list_simpl...
  + destruct (perm_Type_f_app_flat_map f l0 _ _ _ _ HP Heq2) as [[L' l'] (Hnil' & HeqL' & HPL')] ;
      simpl in Hnil' ; simpl in HeqL' ; simpl in HPL'.
    destruct (map_f_flat_map f l0 _ _ _ Heq2) as [Lp HeqLp].
    destruct (map_f_flat_map f l0 _ _ _ HeqL') as [Lp' HeqLp'].
    assert (Permutation_Type Lp' Lp) as HPp
      by (rewrite HeqLp in HPL' ; rewrite HeqLp' in HPL' ; apply (Permutation_Type_map_inv_inj _ Hinj _ _ HPL')).
    exists (Lp',Lp,l1,flat_map (fun p => (app (map f l0) (snd p))) L1,l1 ++ l',L' ++ L1) ;
      list_simpl ; split ; [ | split ; [ | split ]] ;
      try rewrite HeqL'; try rewrite <- HeqLp' ; try rewrite <- HeqLp ; rewrite ? flat_map_app ; list_simpl...
- app_vs_app_flat_map_inv Heq2.
  + exists (lp1,lp2,
            l ++ flat_map (fun p => app (map f l0) (snd p)) (L0 ++ (n , l3) :: nil),l1 ++ flat_map (fun p => app (map f l0) (snd p)) L1,
            l,L0 ++ (n , l3 ++ map f lp1 ++ l1) :: L1) ;
      list_simpl ; split ; [ | split ; [ | split ]] ;
      try rewrite HeqL'; try rewrite <- HeqLp' ; try rewrite <- HeqLp ; rewrite ? flat_map_app ; list_simpl...
  + destruct (perm_Type_f_app_flat_map f l0 _ _ _ _ HP Heq1) as [[L' l''] (Hnil' & HeqL' & HPL')] ;
        simpl in Hnil' ; simpl in HeqL' ; simpl in HPL'.
    destruct (map_f_flat_map f l0 _ _ _ Heq1) as [Lp HeqLp].
    destruct (map_f_flat_map f l0 _ _ _ HeqL') as [Lp' HeqLp'].
    assert (Permutation_Type Lp' Lp) as HPp
      by (rewrite HeqLp in HPL' ; rewrite HeqLp' in HPL' ; apply (Permutation_Type_map_inv_inj _ Hinj _ _ HPL')).
    induction L' using rev_ind_Type ;
      [ exfalso ; apply Hnil' ; [ intros Heqnil ; destruct L ; inversion Heqnil | reflexivity ]
      | clear IHL' ].
    destruct x as (n' , x).
    exists (Lp',Lp,
            l ++ flat_map (fun p => app (map f l0) (snd p)) L0 ++ map f l0 ++ l3,l5 ++ flat_map (fun p => app (map f l0) (snd p)) L2,
            l,L0 ++ (n , l3 ++ l'') :: L' ++ (n', x ++ l5) :: L2) ;
      list_simpl ; split ; [ | split ; [ | split ]] ;
      try rewrite HeqL'; try rewrite <- HeqLp' ; try rewrite <- HeqLp ;
      rewrite ? flat_map_app ; list_simpl ; rewrite ? flat_map_app ; list_simpl...
  + destruct (perm_Type_f_app_flat_map f l0 _ _ _ _ HP Heq1) as [[L' l''] (Hnil' & HeqL' & HPL')] ;
      simpl in Hnil' ; simpl in HeqL' ; simpl in HPL'.
    destruct (map_f_flat_map f l0 _ _ _ Heq1) as [Lp HeqLp].
    destruct (map_f_flat_map f l0 _ _ _ HeqL') as [Lp' HeqLp'].
    assert (Permutation_Type Lp' Lp) as HPp
      by (rewrite HeqLp in HPL' ; rewrite HeqLp' in HPL' ; apply (Permutation_Type_map_inv_inj _ Hinj _ _ HPL')).
    exists (Lp',Lp,
            l ++ flat_map (fun p => app (map f l0) (snd p)) L0 ++ map f l0 ++ l3,flat_map (fun p => app (map f l0) (snd p)) L2,
            l,L0 ++ (n , l3 ++ l'') :: L' ++ L2) ;
      list_simpl ; split ; [ | split ; [ | split ]] ;
      try rewrite HeqL'; try rewrite <- HeqLp' ; try rewrite <- HeqLp ;
      rewrite ? flat_map_app ; list_simpl ; rewrite ? flat_map_app ; list_simpl...
- app_vs_flat_map_inv Heq2.
  + rewrite <- (app_nil_l (flat_map _ _)) in Heq1.
    destruct (perm_Type_f_app_flat_map f l0 _ _ _ _ HP Heq1) as [[L' l''] (Hnil' & HeqL' & HPL')] ;
      simpl in Hnil' ; simpl in HeqL' ; simpl in HPL'.
    destruct (map_f_flat_map f l0 _ _ _ Heq1) as [Lp HeqLp] ; list_simpl in HeqLp.
    destruct (map_f_flat_map f l0 _ _ _ HeqL') as [Lp' HeqLp'].
    assert (Permutation_Type Lp' Lp) as HPp
      by (rewrite HeqLp in HPL' ; rewrite HeqLp' in HPL' ; apply (Permutation_Type_map_inv_inj _ Hinj _ _ HPL')).
    induction L' using rev_ind_Type ;
      [ exfalso ; apply Hnil' ; [ intros Heqnil ; destruct L ; inversion Heqnil | reflexivity ]
      | clear IHL' ].
    induction L0 using rev_ind_Type ; [ | clear IHL0 ].
    * destruct x as (n', x).
      exists (Lp',Lp,l, l3 ++ flat_map (fun p => app (map f l0) (snd p)) L2, l ++ l'',L' ++ (n', x ++ l3) :: L2) ;
        list_simpl ; split ; [ | split ; [ | split ]] ;
        try rewrite HeqL'; try rewrite <- HeqLp' ; try rewrite <- HeqLp ; rewrite ? flat_map_app ; list_simpl...
    * destruct x as (n', x).
      destruct x0 as (n0, x0).
      exists (Lp',Lp,
              l ++ flat_map (fun p => app (map f l0) (snd p)) L0 ++ map f l0 ++ x0,l3 ++ flat_map (fun p => app (map f l0) (snd p)) L2,
              l,L0 ++ (n0 , x0 ++ l'') :: L' ++ (n' , x ++ l3) :: L2) ;
        list_simpl ; split ; [ | split ; [ | split ]] ;
        try rewrite HeqL'; try rewrite <- HeqLp' ; try rewrite <- HeqLp ;
        rewrite ? flat_map_app ; list_simpl ; rewrite ? flat_map_app ; list_simpl...
  + rewrite <- (app_nil_l (flat_map _ _)) in Heq1.
    destruct (perm_Type_f_app_flat_map f l0 _ _ _ _ HP Heq1) as [[L' l''] (Hnil' & HeqL' & HPL')] ;
      simpl in Hnil' ; simpl in HeqL' ; simpl in HPL'.
    destruct (map_f_flat_map f l0 _ _ _ Heq1) as [Lp HeqLp] ; list_simpl in HeqLp.
    destruct (map_f_flat_map f l0 _ _ _ HeqL') as [Lp' HeqLp'].
    assert (Permutation_Type Lp' Lp) as HPp
      by (rewrite HeqLp in HPL' ; rewrite HeqLp' in HPL' ; apply (Permutation_Type_map_inv_inj _ Hinj _ _ HPL')).
    induction L0 using rev_ind_Type ; [ | clear IHL0 ].
    * exists (Lp',Lp,l,flat_map (fun p => app (map f l0) (snd p)) L2,l ++ l'',L' ++ L2) ;
        list_simpl ; split ; [ | split ; [ | split ]] ;
        try rewrite HeqL'; try rewrite <- HeqLp' ; try rewrite <- HeqLp ; rewrite ? flat_map_app ; list_simpl...
    * destruct x as (n' , x).
      exists (Lp',Lp,
              l ++ flat_map (fun p => app (map f l0) (snd p)) L0 ++ map f l0 ++ x,flat_map (fun p => app (map f l0) (snd p)) L2,
              l,L0 ++ (n', x ++ l'') :: L' ++ L2) ;
        list_simpl ; split ; [ | split ; [ | split ]] ;
        try rewrite HeqL'; try rewrite <- HeqLp' ; try rewrite <- HeqLp ;
        rewrite ? flat_map_app ; list_simpl ; rewrite ? flat_map_app ; list_simpl...
Qed.


Lemma cperm_Type_app_flat_map {B T} {f : B -> T}: forall lw0 L lw l,
  CPermutation_Type lw (l ++ flat_map (fun p => f (fst p) :: (snd p)) L) ->
{'(L' , lw') : _ & prod (L <> nil -> L' <> nil)
      (prod (lw = lw' ++ flat_map (fun p => f (fst p) :: (snd p)) L')
            (CPermutation_Type (lw' ++ flat_map (fun p => app lw0 (snd p)) L')
                               (l ++ flat_map (fun p => app lw0 (snd p)) L))) }.
Proof with try assumption ; try reflexivity.
intros lw0 L lw l HC.
inversion HC ; subst.
dichot_Type_app_exec H1; subst.
- induction L using rev_ind_Type ; [ | clear IHL ] ; simpl.
  + exists (nil, l0 ++ l2) ; simpl ; split ; [ | split ] ; rewrite ? app_nil_r...
    * intros ; assumption.
    * constructor.
  + destruct x as (n , x).
    exists (L ++ (n , x ++ l2) :: nil, l0) ; simpl ; split ; [ | split ]...
    * intros _ Heqnil ; destruct L ; inversion Heqnil.
    * rewrite 2 flat_map_app ; simpl ;
        rewrite ? app_nil_r ; rewrite <- ? app_assoc ; rewrite <- app_comm_cons...
    * rewrite 2 flat_map_app ; simpl ; rewrite <- ? app_assoc ; rewrite ? app_nil_r.
      rewrite 3 app_assoc ; rewrite <- (app_assoc l0) ; rewrite <- 2 (app_assoc _ _ x) ; constructor.
- app_vs_flat_map_inv H2.
  + induction L1 using rev_ind_Type ; [ | clear IHL1 ] ; simpl.
    * exists (L0 ++ (n , l0) :: nil, l2 ++ l) ; simpl ; split ; [ | split ] ; rewrite ? app_nil_r...
      -- intros _ Heqnil ; destruct L0 ; inversion Heqnil.
      -- rewrite <- app_assoc...
      -- rewrite 2 flat_map_app ; simpl ; rewrite <- app_assoc ; rewrite ? app_nil_r ; symmetry.
         rewrite 3 app_assoc ; rewrite <- (app_assoc l) ; rewrite <- 2 (app_assoc _ _ l0) ; constructor.
    * destruct x as (n' , x).
      exists (L1 ++ (n' , x ++ l) :: L0 ++ (n , l0) :: nil, l2) ; simpl ; split ; [ | split ]...
      -- intros _ Heqnil ; destruct L1 ; inversion Heqnil.
      -- rewrite ? flat_map_app ; simpl ; rewrite flat_map_app ; simpl ;
           rewrite ? app_nil_r ; rewrite <- ? app_assoc...
      -- rewrite 2 flat_map_app ; simpl ; rewrite 2 flat_map_app ; simpl ;
           rewrite ? app_nil_r ; rewrite <- ? app_assoc.
         rewrite 3 app_assoc ; rewrite <- (app_assoc l2) ; rewrite <- 2 (app_assoc _ _ x).
         etransitivity ; [ apply cperm_Type | ] ; rewrite <- ? app_assoc...
  + induction L1 using rev_ind_Type ; [ | clear IHL1 ] ; simpl.
    * exists (L0, l) ; simpl ; split ; [ | split ] ; rewrite ? app_nil_r...
      intros ; assumption.
    * destruct x as (n , x).
      exists (L1 ++ (n , x ++ l) :: L0, nil) ; simpl ; split ; [ | split ]...
      -- intros _ Heqnil ; destruct L1 ; inversion Heqnil.
      -- rewrite ? flat_map_app ; rewrite <- ? app_assoc ; simpl ; 
           rewrite ? app_nil_r ; rewrite <- ? app_comm_cons ; rewrite <- app_assoc...
      -- rewrite 2 flat_map_app ; simpl ; rewrite flat_map_app ; simpl.
         rewrite (app_assoc l).
         etransitivity ; [ | apply cperm_Type ] ; rewrite <- ? app_assoc...
Qed.

Lemma app_vs_flat_map_cst {T} : forall (A : T) L l1 l2,
  l1 ++ l2 = flat_map (cons A) L ->
      {' (L1, L2, l3, l4) | l4 <> nil
          /\ L = L1 ++ (l3 ++ l4) :: L2
          /\ l1 = flat_map (cons A) (L1 ++ l3 :: nil)
          /\ l2 = l4 ++ flat_map (cons A) L2 }
       + {' (L1, L2) | L = L1 ++ L2
          /\ l1 = flat_map (cons A) L1
          /\ l2 = flat_map (cons A) L2 }.
Proof with try assumption ; try reflexivity.
  intros A L l1 l2 Heq.
  destruct (@app_vs_flat_map _ _ (fun (p : nat) => A) (map (fun x => (1 , x)) L) l1 l2).
  { rewrite Heq.
    clear.
    induction L...
    simpl; rewrite IHL... }
  - destruct s as (((((L1 & L2) & n) & l3) & l4) & H).
    left.
    exists ((map (fun p => snd p) L1) , (map (fun p => snd p) L2), l3 , l4).
    destruct H as (H1 & H2 & H3 & H4).
    split; [ | split ; [ | split]]...
    + clear - H2.
      revert L H2.
      induction L1; intros L H2.
      * simpl.
        destruct L; inversion H2.
        replace (map (fun p : nat * list T => snd p) (map (fun x : list T => (1, x)) L)) with L...
        clear.
        induction L...
        simpl; rewrite <- IHL...
      * destruct L; inversion H2.
        simpl.
        specialize (IHL1 L).
        rewrite IHL1...
    + rewrite H3.
      clear.
      induction L1...
      simpl; rewrite IHL1...
    + replace (flat_map (cons A) (map (fun p => snd p) L2)) with (flat_map (fun p : nat * list T => A :: snd p) L2)...
      clear.
      induction L2...
      simpl; rewrite IHL2...
  - right.
    destruct s as ((L1 & L2) & (H1 & H2 & H3)).
    exists (map (fun p => snd p) L1 , map (fun p => snd p) L2).
    split; [ | split].
    + clear - H1.
      revert L H1.
      induction L1; intros L H1.
      * simpl.
        simpl in H1.
        rewrite<- H1.
        clear.
        induction L...
        simpl; rewrite<- IHL...
      * destruct L; inversion H1.
        simpl.
        specialize (IHL1 L).
        rewrite IHL1...
    + rewrite H2.
      clear.
      induction L1...
      simpl; rewrite IHL1...
    + rewrite H3.
      clear.
      induction L2...
      simpl; rewrite IHL2...  
Qed.

Ltac app_vs_flat_map_cst_inv H :=
  match type of H with
  | ?lh ++ ?lr = flat_map (cons ?A) ?L =>
      apply app_vs_flat_map_cst in H ;
        let l1 := fresh "l" in
        let l2 := fresh "l" in
        let L1 := fresh "L" in
        let L2 := fresh "L" in
        let Hnil := fresh "Hnil" in
        let H1 := fresh H in
        let H2 := fresh H in
        let H3 := fresh H in
        destruct H as [ ((((L1 & L2) & l1) & l2) & (Hnil & H1 & H2 & H3))
                     | [[L1 L2] (H1 & H2 & H3)]] ;
        (try simpl in Hnil) ; (try simpl in H1) ; (try simpl in H2) ; (try simpl in H3) ; subst
  end.


Lemma app_vs_app_flat_map_cst {T} : forall (A : T) l0 L l1 l2,
  l1 ++ l2 = l0 ++ flat_map (cons A) L ->
      { l' | l' <> nil
          /\ l0 = l1 ++ l'
          /\ l2 = l' ++ flat_map (cons A) L }
      + {' (L1, L2, l3, l4) | l4 <> nil
          /\ L = L1 ++ (l3 ++ l4) :: L2
          /\ l1 = l0 ++ flat_map (cons A) (L1 ++ l3 :: nil)
          /\ l2 = l4 ++ flat_map (cons A) L2 }
      + {' (L1, L2) | L = L1 ++ L2
          /\ l1 = l0 ++ flat_map (cons A) L1
          /\ l2 = flat_map (cons A) L2 }.
Proof with try assumption ; try reflexivity.
intros A l0 L l1 l2 Heq.
dichot_Type_app_exec Heq.
- destruct l.
  + right ; subst.
    exists (nil, L) ; simpl ; split ; [ | split ]...
    rewrite 2 app_nil_r...
  + left ; left.
    exists (t :: l) ; subst ; split ; [ | split ]...
    intros Heq ; inversion Heq.
- subst.
  app_vs_flat_map_cst_inv Heq1.
  + left ; right.
    exists (L0, L1, l, l1) ; split ; [ | split ; [ | split ]]...
  + right.
    exists (L0, L1) ; split ; [ | split ]...
Qed.

Ltac app_vs_app_flat_map_cst_inv H :=
  match type of H with
  | ?lh ++ ?lr = ?l0 ++ flat_map (cons ?A) ?L =>
      apply app_vs_app_flat_map_cst in H ;
        let l1 := fresh "l" in
        let l2 := fresh "l" in
        let L1 := fresh "L" in
        let L2 := fresh "L" in
        let Hnil := fresh "Hnil" in
        let H1 := fresh H in
        let H2 := fresh H in
        let H3 := fresh H in
        destruct H as [ [[l1 (Hnil & H1 & H2)]
                        |((((L1 & L2) & l1) & l2) & (Hnil & H1 & H2 & H3))]
                      | [[L1 L2] (H1 & H2 & H3)]] ;
        (try simpl in Hnil) ; (try simpl in H1) ; (try simpl in H2) ; (try simpl in H3) ; subst
  end.

Lemma elt_vs_app_flat_map_cst {T} : forall (A : T) l0 L l1 l2 B,
  l1 ++ B :: l2 = l0 ++ flat_map (cons A) L ->
      { l' | l0 = l1 ++ B :: l'
          /\ l2 = l' ++ flat_map (cons A) L }
    + {' (L1, L2, l1',l2') | L = L1 ++ (l1' ++ B :: l2') :: L2
          /\ l1 = l0 ++ flat_map (cons A) L1 ++ (A :: l1')
          /\ l2 = l2' ++ flat_map (cons A) L2 }
    + {' (L1 , L2 , l) | B = A
          /\ L = L1 ++ l :: L2
          /\ l1 = l0 ++ flat_map (cons A) L1
          /\ l2 = l ++ flat_map (cons A) L2 }.
Proof with try assumption ; try reflexivity.
intros A l0 L l1 l2 B Heq.
dichot_Type_elt_app_exec Heq.
- left ; left.
  exists l ; subst ; split...
- subst.
  revert l3 l2 Heq1 ; induction L ; intros l3 l2 Heq.
  + exfalso ; destruct l3 ; inversion Heq.
  + simpl in Heq ; rewrite app_comm_cons in Heq.
    dichot_Type_elt_app_exec Heq.
    * destruct l3 ; inversion Heq0 ; subst.
      -- right.
         exists (nil, L, a); split ; [ | split ; [ | split] ]...
      -- left ; right.
         exists (nil, L , l3, l) ; split ; [ | split ]...
    * apply IHL in Heq1 ; destruct Heq1 as [[Heqa | Heqb] | [Heq Heqc]].
      -- destruct Heqa as [l [Heqa _]].
         exfalso.
         rewrite <- (app_nil_r l0) in Heqa.
         rewrite <- 2 app_assoc in Heqa.  apply app_inv_head in Heqa.
         simpl in Heqa ; destruct l1 ; inversion Heqa.
      -- left ; right.
         destruct Heqb as ((((L' & L'') & l') & l'') & (Heqb1 & Heqb2 & Heqb3)).
         simpl in Heqb1 ; simpl in Heqb2 ; simpl in Heqb3.
         apply app_inv_head in Heqb2.
         exists (a :: L', L'', l', l'') ; simpl ; subst ; split ; [ | split ]...
         simpl.
         rewrite ? app_assoc...
      -- right.
         destruct Heq as ((L' & L'') & l').
         destruct Heqc as (Heqc & Heqc1 & Heqc2 & Heqc3).
         simpl in Heqc1 ; simpl in Heqc2 ; simpl in Heqc3.
         apply app_inv_head in Heqc2.
         exists (a :: L', L'' , l') ; simpl ; subst ; split ; [ | split ; [| split] ]...
Qed.

Ltac elt_vs_app_flat_map_cst_inv H :=
  match type of H with
  | ?lh ++ _ :: ?lr = ?l0 ++ flat_map (cons ?A) ?L =>
      apply elt_vs_app_flat_map_cst in H ;
        let l1 := fresh "l" in
        let l2 := fresh "l" in
        let L1 := fresh "L" in
        let L2 := fresh "L" in
        let H1 := fresh H in
        let H2 := fresh H in
        let H3 := fresh H in
        let Heq := fresh "HeqA" in
        destruct H as [ [[l1 [H1 H2]]
                      | [(((L1 & L2) & l1) & l2) (H1 & H2 & H3)]]
                      | [((L1 & L2) & l1) (Heq & H1 & H2 & H3)]] ;
        [ | | try (inversion HeqA ; fail) ] ;
        (try simpl in H1) ; (try simpl in H2) ; (try simpl in H3) ; subst
  end.


Lemma map_f_flat_map_cst {T T1} : forall (A : T1) (f : T -> T1) lw' lw l L,
  map f lw = l ++ flat_map (cons A) L ->
  { Lw | l ++ flat_map (app (map f lw')) L = map f Lw }.
Proof.
intros A f lw' lw l L ; revert lw l ; induction L ; intros lw l Heq ; simpl in Heq ; simpl.
- subst ; exists lw ; symmetry ; assumption.
- rewrite app_comm_cons in Heq ; rewrite app_assoc in Heq.
  apply IHL in Heq ; destruct Heq as [Lw Heq].
  decomp_map_Type Heq ; simpl in Heq1 ; simpl in Heq2.
  inversion Heq1 ; subst.
  rewrite Heq2 ; simpl.
  exists (l3 ++ lw' ++ l5 ++ l2); rewrite <- ? map_app.
  rewrite <- app_assoc ; reflexivity.
Qed.


Lemma perm_Type_app_flat_map_cst {T} : forall (A : T) lw0 L lw l,
  Permutation_Type lw (l ++ flat_map (cons A) L) ->
{' (L'  , lw') : _  & prod (L <> nil -> L' <> nil)
      (prod (lw = lw' ++ flat_map (cons A) L')
            (Permutation_Type (lw' ++ flat_map (app lw0) L')
                              (l ++ flat_map (app lw0) L))) }.
Proof with try assumption ; try reflexivity.
  intros A lw0 L lw l HP.
  destruct (@perm_Type_app_flat_map _ _ (fun _ => A) lw0 (map (fun p => (1 , p)) L) lw l).
  { replace (flat_map (fun p : nat * list T => A :: snd p)
                      (map (fun p : list T => (1, p)) L)) with (flat_map (cons A) L)...
    clear; induction L...
    simpl; rewrite IHL... }
  destruct x as (L', lw').
  destruct y as (H1 & H2 & H3).
  split with (map (fun x => snd x) L', lw').
  split; [ | split].
  - intros Hneq Heq.
    apply map_eq_nil in Heq.
    apply H1...
    intros Heq1.
    apply Hneq.
    apply map_eq_nil in Heq1...
  - replace (flat_map (cons A) (map (fun x : nat * list T => snd x) L')) with (flat_map (fun p : nat * list T => A :: snd p) L')...
    clear.
    induction L'...
    simpl; rewrite IHL'...
  - replace (flat_map (app lw0) (map (fun x : nat * list T => snd x) L')) with (flat_map (fun p : nat * list T => lw0 ++ snd p) L') by (clear; induction L'; simpl; try rewrite IHL'; reflexivity).
    replace (flat_map (app lw0) L) with (flat_map (fun p : nat * list T => lw0 ++ snd p)
                                                  (map (fun p : list T => (1, p)) L)) by (clear; induction L; simpl; try rewrite IHL; reflexivity)...
Qed.  

Lemma perm_Type_f_app_flat_map_cst {T T1} : forall (A : T1) (f : T -> T1) lw0 L lw lw' l,
  Permutation_Type lw lw' -> map f lw' = l ++ flat_map (cons A) L ->
{' (L' , lw') : _ & prod (L <> nil -> L' <> nil)
      (prod (map f lw = lw' ++ flat_map (cons A) L')
            (Permutation_Type (lw' ++ flat_map (app (map f lw0)) L')
                              (l ++ flat_map (app (map f lw0)) L))) }.
Proof.
intros A f lw0 L lw lw' l HP Heq.
apply (Permutation_Type_map f) in HP ; rewrite Heq in HP.
apply perm_Type_app_flat_map_cst ; assumption.
Qed.

Lemma perm_flat_map_cons_flat_map_app_cst {T T1} :
forall (A : T1) (f : T -> T1), injective f -> forall l0 l1 l2 lp1 lp2 l L,
  Permutation_Type lp1 lp2 ->
  l1 ++ map f lp2 ++ l2 = l ++ flat_map (cons A) L ->
{' (l1',l2',l3',l4',l',L') : _ &  prod (l1 ++ map f lp1 ++ l2 = l' ++ flat_map (cons A) L')
            (prod (Permutation_Type l1' l2')
                  (prod (l3' ++ map f l1' ++ l4'
                             = l' ++ flat_map (app (map f l0)) L')
                        (l3' ++ map f l2' ++ l4'
                             = l ++ flat_map (app (map f l0)) L))) }.
Proof with try assumption ; try reflexivity.
  intros A f Hinj l0 l1 l2 lp1 lp2 l L HP Heq.
  destruct (@perm_flat_map_cons_flat_map_app _ _ _ (fun _ => A) f Hinj l0 l1 l2 lp1 lp2 l (map (fun p => (1 , p)) L))...
  { rewrite Heq.
    replace (flat_map (fun p : nat * list T1 => A :: snd p)
                      (map (fun p : list T1 => (1, p)) L)) with
        (flat_map (cons A) L) by (clear; induction L; simpl; try rewrite IHL; reflexivity)... }
  destruct x as (((((l1' & l2') & l3') & l4') & l') & L').
  destruct y as (H1 & H2 & H3 & H4).
  split with (l1', l2', l3', l4', l', map (fun p => snd p) L').
  split; [ | split; [ | split]]...
  - rewrite H1.
    replace (flat_map (fun p : nat * list T1 => A :: snd p) L')
      with (flat_map (cons A) (map (fun p : nat * list T1 => snd p) L'))
      by (clear; induction L'; simpl; try rewrite IHL'; reflexivity)...
  - rewrite H3.
    replace (flat_map (fun p : nat * list T1 => map f l0 ++ snd p) L')
      with (flat_map (app (map f l0)) (map (fun p : nat * list T1 => snd p) L'))
      by (clear; induction L'; simpl; try rewrite IHL'; reflexivity)...
  - rewrite H4.
    replace (flat_map (fun p : nat * list T1 => map f l0 ++ snd p)
                      (map (fun p : list T1 => (1, p)) L))
      with (flat_map (app (map f l0)) L)
      by (clear; induction L; simpl; try rewrite IHL; reflexivity)...
Qed.

Lemma cperm_Type_app_flat_map_cst {T} : forall (A : T) lw0 L lw l,
  CPermutation_Type lw (l ++ flat_map (cons A) L) ->
{'(L' , lw') : _ & prod (L <> nil -> L' <> nil)
      (prod (lw = lw' ++ flat_map (cons A) L')
            (CPermutation_Type (lw' ++ flat_map (app lw0) L')
                               (l ++ flat_map (app lw0) L))) }.
Proof with try assumption ; try reflexivity.
  intros A lw0 L lw l HC.
  destruct (@cperm_Type_app_flat_map _ _ (fun p => A) lw0 (map (fun x => (1 , x)) L) lw l) as ((L' & lw') & (H1 & H2 & H3)).
  { replace (flat_map (fun p : nat * list T => A :: snd p)
                      (map (fun x : list T => (1, x)) L))
    with (flat_map (cons A) L)
      by (clear; induction L; simpl; try rewrite IHL; reflexivity)... }
  split with (map (fun x => snd x) L' , lw').
  split; [ | split].
  - intro Hneq.
    intro Heq.
    apply map_eq_nil in Heq.
    apply H1...
    intros Heq1.
    apply map_eq_nil in Heq1.
    apply Hneq...
  - rewrite H2.
    replace (flat_map (fun p : nat * list T => A :: snd p) L')
      with (flat_map (cons A) (map (fun x : nat * list T => snd x) L'))
      by (clear; induction L'; simpl; try rewrite IHL'; reflexivity)...
  - replace (flat_map (app lw0) (map (fun x : nat * list T => snd x) L'))
      with (flat_map (fun p : nat * list T => lw0 ++ snd p) L')
      by (clear; induction L'; simpl; try rewrite IHL'; reflexivity).
    replace (flat_map (app lw0) L)
      with (flat_map (fun p : nat * list T => lw0 ++ snd p)
                     (map (fun x : list T => (1, x)) L))
      by (clear; induction L; simpl; try rewrite IHL; reflexivity)...
Qed.
