(* flat_map_Type_more Library *)

(** * Add-ons for List library
Properties of flat_map. *)

Require Import Injective.
Require Import List_more.
Require Import List_Type_more.
Require Import Permutation_Type_more.
Require Import CyclicPerm_Type.

Lemma app_vs_flat_map {T} : forall (A : T) L l1 l2,
  l1 ++ l2 = flat_map (cons A) L ->
      { ql | snd (snd ql) <> nil
          /\ L = fst (fst ql) ++ (fst (snd ql) ++ snd (snd ql)) :: snd (fst ql)
          /\ l1 = flat_map (cons A) (fst (fst ql) ++ fst (snd ql) :: nil)
          /\ l2 = snd (snd ql) ++ flat_map (cons A) (snd (fst ql)) }
    + { pl | L = fst pl ++ snd pl
          /\ l1 = flat_map (cons A) (fst pl)
          /\ l2 = flat_map (cons A) (snd pl) }.
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
         exists (l1 :: nil , L) ; split ; [ | split ] ; simpl ; try rewrite app_nil_r...
      -- left.
         exists ((nil, L), (l1, t :: l)) ; split ; [ | split ; [ | split ]] ;
           simpl ; try rewrite app_nil_r...
         intros Heq ; inversion Heq.
  + apply IHL in Heq1.
    destruct Heq1 as [[[[L1 L2] [l1' l2']] (Hnil & Heq1 & Heq2 & Heq3)]
                     | [[L1 L2] (Heq1 & Heq2 & Heq3)]] ; [left | right].
    * exists ((a :: L1, L2), (l1', l2')) ; split ; [ | split ; [ | split ]]  ; subst...
    * exists (a :: L1, L2) ; split ; [ | split ]  ; subst...
Qed.

Ltac app_vs_flat_map_inv H :=
  match type of H with
  | ?lh ++ ?lr = flat_map (cons ?A) ?L =>
      apply app_vs_flat_map in H ;
        let l1 := fresh "l" in
        let l2 := fresh "l" in
        let L1 := fresh "L" in
        let L2 := fresh "L" in
        let Hnil := fresh "Hnil" in
        let H1 := fresh H in
        let H2 := fresh H in
        let H3 := fresh H in
        destruct H as [ [[[L1 L2] [l1 l2]] (Hnil & H1 & H2 & H3)]
                      | [[L1 L2] (H1 & H2 & H3)]] ;
        (try simpl in Hnil) ; (try simpl in H1) ; (try simpl in H2) ; (try simpl in H3) ; subst
  end.


Lemma app_vs_app_flat_map {T} : forall (A : T) l0 L l1 l2,
  l1 ++ l2 = l0 ++ flat_map (cons A) L ->
      { l' | l' <> nil
          /\ l0 = l1 ++ l'
          /\ l2 = l' ++ flat_map (cons A) L }
    + { ql | snd (snd ql) <> nil
          /\ L = fst (fst ql) ++ (fst (snd ql) ++ snd (snd ql)) :: snd (fst ql)
          /\ l1 = l0 ++ flat_map (cons A) (fst (fst ql) ++ fst (snd ql) :: nil)
          /\ l2 = snd (snd ql) ++ flat_map (cons A) (snd (fst ql)) }
    + { pl | L = fst pl ++ snd pl
          /\ l1 = l0 ++ flat_map (cons A) (fst pl)
          /\ l2 = flat_map (cons A) (snd pl) }.
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
  app_vs_flat_map_inv Heq1.
  + left ; right.
    exists ((L0, L1), (l, l1)) ; split ; [ | split ; [ | split ]]...
  + right.
    exists (L0, L1) ; split ; [ | split ]...
Qed.

Ltac app_vs_app_flat_map_inv H :=
  match type of H with
  | ?lh ++ ?lr = ?l0 ++ flat_map (cons ?A) ?L =>
      apply app_vs_app_flat_map in H ;
        let l1 := fresh "l" in
        let l2 := fresh "l" in
        let L1 := fresh "L" in
        let L2 := fresh "L" in
        let Hnil := fresh "Hnil" in
        let H1 := fresh H in
        let H2 := fresh H in
        let H3 := fresh H in
        destruct H as [ [[l1 (Hnil & H1 & H2)]
                      | [[[L1 L2] [l1 l2]] (Hnil & H1 & H2 & H3)]]
                      | [[L1 L2] (H1 & H2 & H3)]] ;
        (try simpl in Hnil) ; (try simpl in H1) ; (try simpl in H2) ; (try simpl in H3) ; subst
  end.

Lemma elt_vs_app_flat_map {T} : forall (A : T) l0 L l1 l2 B,
  l1 ++ B :: l2 = l0 ++ flat_map (cons A) L ->
      { l' | l0 = l1 ++ B :: l'
          /\ l2 = l' ++ flat_map (cons A) L }
    + { ql | L = fst (fst ql) ++ (fst (snd ql) ++ B :: snd (snd ql)) :: snd (fst ql)
          /\ l1 = l0 ++ flat_map (cons A) (fst (fst ql)) ++ A :: (fst (snd ql))
          /\ l2 = snd (snd ql) ++ flat_map (cons A) (snd (fst ql)) }
    + (B = A) * 
      { tl | L = fst (fst tl) ++ snd tl :: snd (fst tl)
          /\ l1 = l0 ++ flat_map (cons A) (fst (fst tl))
          /\ l2 = snd tl ++ flat_map (cons A) (snd (fst tl)) }.
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
         split...
         exists (nil, L, a) ; split ; [ | split ]...
      -- left ; right.
         exists ((nil, L), (l3, l)) ; split ; [ | split ]...
    * apply IHL in Heq1 ; destruct Heq1 as [[Heqa | Heqb] | [Heq Heqc]].
      -- destruct Heqa as [l [Heqa _]].
         exfalso.
         rewrite <- (app_nil_r l0) in Heqa.
         rewrite <- 2 app_assoc in Heqa.  apply app_inv_head in Heqa.
         simpl in Heqa ; destruct l1 ; inversion Heqa.
      -- left ; right.
         destruct Heqb as [[[L' L''][l' l'']] (Heqb1 & Heqb2 & Heqb3)].
         simpl in Heqb1 ; simpl in Heqb2 ; simpl in Heqb3.
         apply app_inv_head in Heqb2.
         exists ((a :: L', L''), (l', l'')) ; simpl ; subst ; split ; [ | split ]...
         rewrite <- app_comm_cons ; rewrite <- app_assoc...
      -- right.
         split...
         destruct Heqc as [[[L' L''] l'] (Heqc1 & Heqc2 & Heqc3)].
         simpl in Heqc1 ; simpl in Heqc2 ; simpl in Heqc3.
         apply app_inv_head in Heqc2.
         exists (a :: L', L'', l') ; simpl ; subst ; split ; [ | split ]...
Qed.

Ltac elt_vs_app_flat_map_inv H :=
  match type of H with
  | ?lh ++ _ :: ?lr = ?l0 ++ flat_map (cons ?A) ?L =>
      apply elt_vs_app_flat_map in H ;
        let l1 := fresh "l" in
        let l2 := fresh "l" in
        let L1 := fresh "L" in
        let L2 := fresh "L" in
        let H1 := fresh H in
        let H2 := fresh H in
        let H3 := fresh H in
        let Heq := fresh "HeqA" in
        destruct H as [ [[l1 [H1 H2]]
                      | [[[L1 L2] [l1 l2]] (H1 & H2 & H3)]]
                      | [Heq [[[L1 L2] l1] (H1 & H2 & H3)]]] ;
        [ | | try (inversion HeqA ; fail) ] ;
        (try simpl in H1) ; (try simpl in H2) ; (try simpl in H3) ; subst
  end.


Lemma map_f_flat_map {T1 T2} : forall A (f : T1 -> T2) lw' lw l L ,
  map f lw = l ++ flat_map (cons (f A)) L -> { Lw | l ++ flat_map (app (map f lw')) L = map f Lw }.
Proof.
intros A f lw' lw l L ; revert lw l ; induction L ; intros lw l Heq ; simpl in Heq ; simpl.
- subst ; exists lw ; symmetry ; assumption.
- rewrite app_comm_cons in Heq ; rewrite app_assoc in Heq.
  apply IHL in Heq ; destruct Heq as [Lw Heq].
  decomp_map_Type Heq ; simpl in Heq1 ; simpl in Heq2.
  inversion Heq1 ; subst.
  rewrite Heq2 ; simpl.
  exists (l3 ++ lw' ++ l5 ++ l2) ; rewrite <- ? map_app.
  rewrite <- app_assoc ; reflexivity.
Qed.


Lemma perm_Type_app_flat_map {T} : forall (A : T) lw0 L lw l,
  Permutation_Type lw (l ++ flat_map (cons A) L) ->
{ pl & prod (L <> nil -> fst pl <> nil)
      (prod (lw = snd pl ++ flat_map (cons A) (fst pl))
            (Permutation_Type (snd pl ++ flat_map (app lw0) (fst pl))
                              (l ++ flat_map (app lw0) L))) }.
Proof with try assumption ; try reflexivity.
induction L ; intros lw l HP ; simpl in HP ; simpl.
- exists (nil, lw) ; subst ; simpl ; split ; [ | split ] ; try (rewrite app_nil_r)...
  intros...
- destruct (Permutation_Type_vs_elt_inv _ _ _ _ HP) as ([lw1 lw2] & HP2) ; subst ; simpl in HP.
  apply Permutation_Type_app_inv in HP.
  rewrite app_assoc in HP ; apply IHL in HP.
  destruct HP as [[L' l'] (Hnil' & HeqL' & HP')].
  simpl in Hnil' ; simpl in HeqL' ; simpl in HP' ; simpl.
  simpl in HeqL' ; app_vs_app_flat_map_inv HeqL'.
  + exists (l0 :: L', lw1) ; split ; [ | split ] ; simpl...
    * intros _ Heqnil ; inversion Heqnil.
    * rewrite <- ? app_assoc in HP' ; rewrite <- ? app_assoc.
      apply Permutation_Type_app_middle...
  + exists (L0 ++ l0 :: l1 :: L1, l') ; split ; [ | split ] ; simpl...
    * intros _ Heqnil ; destruct L0 ; inversion Heqnil.
    * repeat (rewrite ? flat_map_app ; rewrite <- app_assoc) ; simpl ; rewrite app_nil_r...
    * rewrite ? flat_map_app in HP' ; simpl in HP' ; rewrite <- app_assoc in HP'...
      rewrite ? flat_map_app ; simpl...
      rewrite <- ? app_assoc ; rewrite app_assoc ; apply Permutation_Type_app_middle ; simpl.
      etransitivity ; [ | rewrite app_assoc ; apply HP'].
      rewrite app_assoc ; rewrite (app_assoc l') ; apply Permutation_Type_app_middle.
      rewrite <- ? app_assoc...
  + exists (L0 ++ nil :: L1, l') ; split ; [ | split ] ; simpl...
    * intros _ Heqnil ; destruct L0 ; inversion Heqnil.
    * rewrite ? flat_map_app ; rewrite <- app_assoc...
    * rewrite ? flat_map_app in HP' ; rewrite <- app_assoc in HP'...
      rewrite ? flat_map_app ; rewrite <- app_assoc...
      simpl ; rewrite app_nil_r ; rewrite app_assoc ; apply Permutation_Type_app_middle ;
        rewrite <- app_assoc...
Qed.

Lemma perm_Type_f_app_flat_map {T1 T2} : forall A (f : T1 -> T2) lw0 L lw lw' l,
  Permutation_Type lw lw' -> map f lw' = l ++ flat_map (cons (f A)) L ->
{ pl & prod (L <> nil -> fst pl <> nil)
      (prod (map f lw = snd pl ++ flat_map (cons (f A)) (fst pl))
            (Permutation_Type (snd pl ++ flat_map (app (map f lw0)) (fst pl))
                              (l ++ flat_map (app (map f lw0)) L))) }.
Proof.
intros A f lw0 L lw lw' l HP Heq.
apply (Permutation_Type_map f) in HP ; rewrite Heq in HP.
apply perm_Type_app_flat_map ; assumption.
Qed.

Lemma perm_flat_map_cons_flat_map_app {T1 T2} :
forall A (f : T1 -> T2), injective f -> forall l0 l1 l2 lp1 lp2 l L,
  Permutation_Type lp1 lp2 ->
  l1 ++ map f lp2 ++ l2 = l ++ flat_map (cons (f A)) L ->
{ sl : _ &  prod (l1 ++ map f lp1 ++ l2 = (fst (snd sl)) ++ flat_map (cons (f A)) (snd (snd sl)))
            (prod (Permutation_Type (fst (fst (fst sl))) (snd (fst (fst sl))))
                  (prod ((fst (snd (fst sl))) ++ map f (fst (fst (fst sl))) ++ (snd (snd (fst sl)))
                             = (fst (snd sl)) ++ flat_map (app (map f l0)) (snd (snd sl)))
                        ((fst (snd (fst sl))) ++ map f (snd (fst (fst sl))) ++ (snd (snd (fst sl)))
                             = l ++ flat_map (app (map f l0)) L))) }.
Proof with try assumption ; try reflexivity.
intros A f Hinj l0 l1 l2 lp1 lp2 l L HP Heq.
app_vs_app_flat_map_inv Heq.
- app_vs_app_flat_map_inv Heq1.
  + exists ((lp1,lp2),(l1,l ++ flat_map (app (map f l0)) L),(l1 ++ map f lp1 ++ l,L)) ;
      list_simpl ; split ; [ | split ; [ | split ]]...
  + destruct (perm_Type_f_app_flat_map _ f l0 _ _ _ _ HP Heq2) as [[L' l'] (Hnil' & HeqL' & HPL')] ;
      simpl in Hnil' ; simpl in HeqL' ; simpl in HPL'.
    destruct (map_f_flat_map _ f l0 _ _ _ Heq2) as [Lp HeqLp].
    destruct (map_f_flat_map _ f l0 _ _ _ HeqL') as [Lp' HeqLp'].
    assert (Permutation_Type Lp' Lp) as HPp
      by (rewrite HeqLp in HPL' ; rewrite HeqLp' in HPL' ; apply (Permutation_Type_map_inv_inj _ Hinj _ _ HPL')).
    induction L' using rev_ind_Type ;
      [ exfalso ; apply Hnil' ; [ intros Heqnil ; destruct L0 ; inversion Heqnil | reflexivity ]
      | clear IHL' ].
    exists ((Lp',Lp),(l1,l4 ++ flat_map (app (map f l0)) L1),(l1 ++ l',L' ++ (x ++ l4) :: L1)) ;
      list_simpl ; split ; [ | split ; [ | split ]] ;
      try rewrite HeqL'; try rewrite <- HeqLp' ; try rewrite <- HeqLp ; rewrite ? flat_map_app ; list_simpl...
  + destruct (perm_Type_f_app_flat_map _ f l0 _ _ _ _ HP Heq2) as [[L' l'] (Hnil' & HeqL' & HPL')] ;
      simpl in Hnil' ; simpl in HeqL' ; simpl in HPL'.
    destruct (map_f_flat_map _ f l0 _ _ _ Heq2) as [Lp HeqLp].
    destruct (map_f_flat_map _ f l0 _ _ _ HeqL') as [Lp' HeqLp'].
    assert (Permutation_Type Lp' Lp) as HPp
      by (rewrite HeqLp in HPL' ; rewrite HeqLp' in HPL' ; apply (Permutation_Type_map_inv_inj _ Hinj _ _ HPL')).
    exists ((Lp',Lp),(l1,flat_map (app (map f l0)) L1),(l1 ++ l',L' ++ L1)) ;
      list_simpl ; split ; [ | split ; [ | split ]] ;
      try rewrite HeqL'; try rewrite <- HeqLp' ; try rewrite <- HeqLp ; rewrite ? flat_map_app ; list_simpl...
- app_vs_app_flat_map_inv Heq2.
  + exists ((lp1,lp2),
            (l ++ flat_map (app (map f l0)) (L0 ++ l3 :: nil),l1 ++ flat_map (app (map f l0)) L1),
            (l,L0 ++ (l3 ++ map f lp1 ++ l1) :: L1)) ;
      list_simpl ; split ; [ | split ; [ | split ]] ;
      try rewrite HeqL'; try rewrite <- HeqLp' ; try rewrite <- HeqLp ; rewrite ? flat_map_app ; list_simpl...
  + destruct (perm_Type_f_app_flat_map _ f l0 _ _ _ _ HP Heq1) as [[L' l''] (Hnil' & HeqL' & HPL')] ;
        simpl in Hnil' ; simpl in HeqL' ; simpl in HPL'.
    destruct (map_f_flat_map _ f l0 _ _ _ Heq1) as [Lp HeqLp].
    destruct (map_f_flat_map _ f l0 _ _ _ HeqL') as [Lp' HeqLp'].
    assert (Permutation_Type Lp' Lp) as HPp
      by (rewrite HeqLp in HPL' ; rewrite HeqLp' in HPL' ; apply (Permutation_Type_map_inv_inj _ Hinj _ _ HPL')).
    induction L' using rev_ind_Type ;
      [ exfalso ; apply Hnil' ; [ intros Heqnil ; destruct L ; inversion Heqnil | reflexivity ]
      | clear IHL' ].
    exists ((Lp',Lp),
            (l ++ flat_map (app (map f l0)) L0 ++ map f l0 ++ l3,l5 ++ flat_map (app (map f l0)) L2),
            (l,L0 ++ (l3 ++ l'') :: L' ++ (x ++ l5) :: L2)) ;
      list_simpl ; split ; [ | split ; [ | split ]] ;
      try rewrite HeqL'; try rewrite <- HeqLp' ; try rewrite <- HeqLp ;
      rewrite ? flat_map_app ; list_simpl ; rewrite ? flat_map_app ; list_simpl...
  + destruct (perm_Type_f_app_flat_map _ f l0 _ _ _ _ HP Heq1) as [[L' l''] (Hnil' & HeqL' & HPL')] ;
      simpl in Hnil' ; simpl in HeqL' ; simpl in HPL'.
    destruct (map_f_flat_map _ f l0 _ _ _ Heq1) as [Lp HeqLp].
    destruct (map_f_flat_map _ f l0 _ _ _ HeqL') as [Lp' HeqLp'].
    assert (Permutation_Type Lp' Lp) as HPp
      by (rewrite HeqLp in HPL' ; rewrite HeqLp' in HPL' ; apply (Permutation_Type_map_inv_inj _ Hinj _ _ HPL')).
    exists ((Lp',Lp),
            (l ++ flat_map (app (map f l0)) L0 ++ map f l0 ++ l3,flat_map (app (map f l0)) L2),
            (l,L0 ++ (l3 ++ l'') :: L' ++ L2)) ;
      list_simpl ; split ; [ | split ; [ | split ]] ;
      try rewrite HeqL'; try rewrite <- HeqLp' ; try rewrite <- HeqLp ;
      rewrite ? flat_map_app ; list_simpl ; rewrite ? flat_map_app ; list_simpl...
- app_vs_flat_map_inv Heq2.
  + rewrite <- (app_nil_l (flat_map _ _)) in Heq1.
    destruct (perm_Type_f_app_flat_map _ f l0 _ _ _ _ HP Heq1) as [[L' l''] (Hnil' & HeqL' & HPL')] ;
      simpl in Hnil' ; simpl in HeqL' ; simpl in HPL'.
    destruct (map_f_flat_map _ f l0 _ _ _ Heq1) as [Lp HeqLp] ; list_simpl in HeqLp.
    destruct (map_f_flat_map _ f l0 _ _ _ HeqL') as [Lp' HeqLp'].
    assert (Permutation_Type Lp' Lp) as HPp
      by (rewrite HeqLp in HPL' ; rewrite HeqLp' in HPL' ; apply (Permutation_Type_map_inv_inj _ Hinj _ _ HPL')).
    induction L' using rev_ind_Type ;
      [ exfalso ; apply Hnil' ; [ intros Heqnil ; destruct L ; inversion Heqnil | reflexivity ]
      | clear IHL' ].
    induction L0 using rev_ind_Type ; [ | clear IHL0 ].
    * exists ((Lp',Lp),(l,l3 ++ flat_map (app (map f l0)) L2),(l ++ l'',L' ++ (x ++ l3) :: L2)) ;
        list_simpl ; split ; [ | split ; [ | split ]] ;
        try rewrite HeqL'; try rewrite <- HeqLp' ; try rewrite <- HeqLp ; rewrite ? flat_map_app ; list_simpl...
    * exists ((Lp',Lp),
              (l ++ flat_map (app (map f l0)) L0 ++ map f l0 ++ x0,l3 ++ flat_map (app (map f l0)) L2),
              (l,L0 ++ (x0 ++ l'') :: L' ++ (x ++ l3) :: L2)) ;
        list_simpl ; split ; [ | split ; [ | split ]] ;
        try rewrite HeqL'; try rewrite <- HeqLp' ; try rewrite <- HeqLp ;
        rewrite ? flat_map_app ; list_simpl ; rewrite ? flat_map_app ; list_simpl...
  + rewrite <- (app_nil_l (flat_map _ _)) in Heq1.
    destruct (perm_Type_f_app_flat_map _ f l0 _ _ _ _ HP Heq1) as [[L' l''] (Hnil' & HeqL' & HPL')] ;
      simpl in Hnil' ; simpl in HeqL' ; simpl in HPL'.
    destruct (map_f_flat_map _ f l0 _ _ _ Heq1) as [Lp HeqLp] ; list_simpl in HeqLp.
    destruct (map_f_flat_map _ f l0 _ _ _ HeqL') as [Lp' HeqLp'].
    assert (Permutation_Type Lp' Lp) as HPp
      by (rewrite HeqLp in HPL' ; rewrite HeqLp' in HPL' ; apply (Permutation_Type_map_inv_inj _ Hinj _ _ HPL')).
    induction L0 using rev_ind_Type ; [ | clear IHL0 ].
    * exists ((Lp',Lp),(l,flat_map (app (map f l0)) L2),(l ++ l'',L' ++ L2)) ;
        list_simpl ; split ; [ | split ; [ | split ]] ;
        try rewrite HeqL'; try rewrite <- HeqLp' ; try rewrite <- HeqLp ; rewrite ? flat_map_app ; list_simpl...
    * exists ((Lp',Lp),
              (l ++ flat_map (app (map f l0)) L0 ++ map f l0 ++ x,flat_map (app (map f l0)) L2),
              (l,L0 ++ (x ++ l'') :: L' ++ L2)) ;
        list_simpl ; split ; [ | split ; [ | split ]] ;
        try rewrite HeqL'; try rewrite <- HeqLp' ; try rewrite <- HeqLp ;
        rewrite ? flat_map_app ; list_simpl ; rewrite ? flat_map_app ; list_simpl...
Qed.


Lemma cperm_Type_app_flat_map {T} : forall (A : T) lw0 L lw l,
  CPermutation_Type lw (l ++ flat_map (cons A) L) ->
{ pl & prod (L <> nil -> fst pl <> nil)
      (prod (lw = snd pl ++ flat_map (cons A) (fst pl))
            (CPermutation_Type (snd pl ++ flat_map (app lw0) (fst pl))
                               (l ++ flat_map (app lw0) L))) }.
Proof with try assumption ; try reflexivity.
intros A lw0 L lw l HC.
inversion HC ; subst.
dichot_Type_app_exec H1; subst.
- induction L using rev_ind_Type ; [ | clear IHL ] ; simpl.
  + exists (nil, l0 ++ l2) ; simpl ; split ; [ | split ] ; rewrite ? app_nil_r...
    * intros ; assumption.
    * constructor.
  + exists (L ++ (x ++ l2) :: nil, l0) ; simpl ; split ; [ | split ]...
    * intros _ Heqnil ; destruct L ; inversion Heqnil.
    * rewrite 2 flat_map_app ; simpl ;
        rewrite ? app_nil_r ; rewrite <- ? app_assoc ; rewrite <- app_comm_cons...
    * rewrite 2 flat_map_app ; simpl ; rewrite <- ? app_assoc ; rewrite ? app_nil_r.
      rewrite 3 app_assoc ; rewrite <- (app_assoc l0) ; rewrite <- 2 (app_assoc _ _ x) ; constructor.
- app_vs_flat_map_inv H2.
  + induction L1 using rev_ind_Type ; [ | clear IHL1 ] ; simpl.
    * exists (L0 ++ l0 :: nil, l2 ++ l) ; simpl ; split ; [ | split ] ; rewrite ? app_nil_r...
      -- intros _ Heqnil ; destruct L0 ; inversion Heqnil.
      -- rewrite <- app_assoc...
      -- rewrite 2 flat_map_app ; simpl ; rewrite <- app_assoc ; rewrite ? app_nil_r ; symmetry.
         rewrite 3 app_assoc ; rewrite <- (app_assoc l) ; rewrite <- 2 (app_assoc _ _ l0) ; constructor.
    * exists (L1 ++ (x ++ l) :: L0 ++ l0 :: nil, l2) ; simpl ; split ; [ | split ]...
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
    * exists (L1 ++ (x ++ l) :: L0, nil) ; simpl ; split ; [ | split ]...
      -- intros _ Heqnil ; destruct L1 ; inversion Heqnil.
      -- rewrite ? flat_map_app ; rewrite <- ? app_assoc ; simpl ; 
           rewrite ? app_nil_r ; rewrite <- ? app_comm_cons ; rewrite <- app_assoc...
      -- rewrite 2 flat_map_app ; simpl ; rewrite flat_map_app ; simpl.
         rewrite (app_assoc l).
         etransitivity ; [ | apply cperm_Type ] ; rewrite <- ? app_assoc...
Qed.


