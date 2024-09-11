(** Add-ons for [List] library:
Properties of [flat_map]. *)

(* TODO add [as p] to tactics cf List_more *)
(* TODO remove some prod in sigT *)

Set Implicit Arguments.

From Yalla.OLlibs Require Import funtheory List_more Permutation_Type_more CPermutation_Type GPermutation_Type.


Lemma flat_map_elt A B (f : A -> list B) a L l1 l2 :
  flat_map f L = l1 ++ a :: l2 ->
  {'(L1, L2, L0, l1', l2') | l1 = flat_map f L1 ++ l1' /\ l2 = l2' ++ flat_map f L2
                           & L = L1 ++ L0 :: L2 /\ f L0 = l1' ++ a :: l2' }.
Proof.
intro Heq. rewrite flat_map_concat_map in Heq.
apply concat_vs_elt in Heq as [(((L1, L2), l1''), l2'') [-> [-> Heq]]].
decomp_map Heq eqn:Hf. subst L.
now exists (L1, L2, x, l1'', l2''); cbn; repeat split; rewrite ? flat_map_concat_map.
Qed.

Lemma app_vs_flat_map B T (f : B -> T) L l1 l2 :
  l1 ++ l2 = flat_map (fun '(p1, p2) => f p1 :: p2) L ->
      {'(L1, L2, n, l3, l4) | l4 <> nil
          /\ L = L1 ++ (n, l3 ++ l4) :: L2
          /\ l1 = flat_map (fun '(p1,p2) => f p1 :: p2) (L1 ++ (n, l3) :: nil)
          /\ l2 = l4 ++ flat_map (fun '(p1,p2) => f p1 :: p2) L2 }
    + {'(L1, L2) | L = L1 ++ L2
          /\ l1 = flat_map (fun '(p1,p2) => f p1 :: p2) L1
          /\ l2 = flat_map (fun '(p1,p2) => f p1 :: p2) L2 }.
Proof.
revert l1 l2; induction L as [|[b l] L IHL]; simpl; intros l1 l2 Heq.
- apply app_eq_nil in Heq; destruct Heq; subst.
  now right; exists (nil, nil).
- rewrite app_comm_cons in Heq.
  dichot_app_inf_exec Heq; subst.
  + destruct l1 as [|t l1].
    * simpl in Heq0; subst.
      now right; exists (nil, (b, l) :: L).
    * inversion Heq0; subst.
      destruct l0 as [|t' l0]; [right|left].
      -- now exists ((b, l1) :: nil , L); simpl; rewrite ? app_nil_r.
      -- now exists (nil, L, b , l1, t' :: l0); simpl; rewrite ? app_nil_r.
  + apply IHL in Heq1.
    destruct Heq1 as [ (((((L1 & L2) & n) & l1') & l2') & (Hnil & -> & -> & ->))
                     | [[L1 L2] [-> [-> ->]]]] ; [left | right].
    * now exists ((b, l) :: L1, L2, n, l1', l2').
    * now exists ((b, l) :: L1, L2).
Qed.

Ltac app_vs_flat_map_inv H :=
  match type of H with
  | ?lh ++ ?lr = flat_map (fun '(p1,p2) => ?f p1 :: p2) ?L =>
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

Lemma app_vs_app_flat_map B T (f : B -> T) l0 L l1 l2 :
  l1 ++ l2 = l0 ++ flat_map (fun '(p1, p2) => f p1 :: p2) L ->
      { l' | l' <> nil
          /\ l0 = l1 ++ l'
          /\ l2 = l' ++ flat_map (fun '(p1,p2) => f p1 :: p2) L }
    + {'(L1, L2, n, l3, l4) | l4 <> nil
          /\ L = L1 ++ (n , l3 ++ l4) :: L2
          /\ l1 = l0 ++ flat_map (fun '(p1,p2) => f p1 :: p2) (L1 ++ (n, l3) :: nil)
          /\ l2 = l4 ++ flat_map (fun '(p1,p2) => f p1 :: p2) L2 }
    + {'(L1, L2) | L = L1 ++ L2
          /\ l1 = l0 ++ flat_map (fun '(p1,p2) => f p1 :: p2) L1
          /\ l2 = flat_map (fun '(p1,p2) => f p1 :: p2) L2 }.
Proof.
intros Heq; dichot_app_inf_exec Heq; subst.
- destruct l as [|t l].
  + now right; exists (nil, L); simpl; rewrite 2 app_nil_r.
  + left; left; exists (t :: l); subst; repeat split.
    intros Heq ; inversion Heq.
- app_vs_flat_map_inv Heq1.
  + now left; right; exists (L0, L1, n, l1, l3).
  + now right; exists (L0, L1).
Qed.

Ltac app_vs_app_flat_map_inv H :=
  match type of H with
  | ?lh ++ ?lr = ?l0 ++ flat_map (fun '(p1,p2) => ?f p1 :: p2) ?L =>
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
        (try simpl in Hnil) ; (try simpl in H1) ; (try simpl in H2) ; (try simpl in H3); subst
  end.

Lemma elt_vs_app_flat_map C T (f : C -> T) l0 L l1 l2 B :
  l1 ++ B :: l2 = l0 ++ flat_map (fun '(p1,p2) => f p1 :: p2) L ->
      { l' | l0 = l1 ++ B :: l'
          /\ l2 = l' ++ flat_map (fun '(p1,p2) => f p1 :: p2) L }
    + {'(L1, L2, n, l1',l2') | L = L1 ++ (n , l1' ++ B :: l2') :: L2
          /\ l1 = l0 ++ flat_map (fun '(p1,p2) => f p1 :: p2) L1 ++ (f n :: l1')
          /\ l2 = l2' ++ flat_map (fun '(p1,p2) => f p1 :: p2) L2 }
    + {'(L1 , L2, n , l) | B = f n
          /\ L = L1 ++ (n , l) :: L2
          /\ l1 = l0 ++ flat_map (fun '(p1,p2) => f p1 :: p2) L1
          /\ l2 = l ++ flat_map (fun '(p1,p2) => f p1 :: p2) L2 }.
Proof.
intro Heq. dichot_elt_app_inf_exec Heq; subst; [ now left; left; exists l | ].
induction L as [|[n l'] L IHL] in l, l2, Heq1 |- *; cbn in Heq1.
- exfalso. nil_vs_elt_inv Heq1.
- rewrite app_comm_cons in Heq1. dichot_elt_app_inf_exec Heq1; subst.
  + destruct l as [|t l]; inversion Heq0; subst.
    * right. exists (nil, L, n, l'). repeat split.
    * left. right. exists (nil, L, n, l, l1). repeat split.
  + apply IHL in Heq2 as [[[l'' [Heqa _]]
                       | [[[[[L' L''] n'] l''] l'''] [-> [->%app_inv_head ->]]]]
                       | [[[[L' L''] n'] l''] [-> [-> [->%app_inv_head ->]]]]].
    * exfalso.
      rewrite <- (app_nil_r l0), <- 2 app_assoc in Heqa. apply app_inv_head in Heqa.
      cbn in Heqa. nil_vs_elt_inv Heqa.
    * left. right. exists ((n, l') :: L', L'', n', l'', l'''). cbn. rewrite ? app_assoc. repeat split.
    * right. exists ((n, l') :: L', L'', n' , l''). repeat split.
Qed.

Ltac elt_vs_app_flat_map_inv H :=
  match type of H with
  | ?lh ++ _ :: ?lr = ?l0 ++ flat_map (fun '(p1,p2) => ?f p1 ?A :: p2) ?L =>
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

Lemma map_f_flat_map T T1 T2 (g : T -> T2) (f : T1 -> T2) lw' lw l L :
  map f lw = l ++ flat_map (fun '(p1, p2) => g p1 :: p2) L ->
  { Lw | l ++ flat_map (fun '(p1, p2) => app (map f lw') p2) L = map f Lw }.
Proof.
induction L as [|[b l0] L IHL] in lw, l |- *; cbn; intro Heq.
- exists lw. symmetry. assumption.
- rewrite app_comm_cons, app_assoc in Heq.
  apply IHL in Heq as [Lw Heq].
  decomp_map Heq eqn:Hf. subst Lw. destruct Hf as [_ <-].
  exists (l ++ (lw' ++ l0) ++ l2). rewrite ! map_app. reflexivity.
Qed.

Lemma Permutation_Type_app_flat_map B T (f : B -> T) lw0 L lw l :
  Permutation_Type lw (l ++ flat_map (fun '(p1, p2) => f p1 :: p2) L) ->
  {'(L', lw') & prod (L <> nil -> L' <> nil)
      (prod (lw = lw' ++ flat_map (fun '(p1,p2) => f p1 :: p2) L')
            (Permutation_Type (lw' ++ flat_map (fun '(p1,p2) => app lw0 p2) L')
                              (l ++ flat_map (fun '(p1,p2) => app lw0 p2) L))) }.
Proof.
revert lw l; induction L as [|[n a] l0 IHL]; simpl; intros lw l HP.
- rewrite app_nil_r in HP.
  now exists (nil, lw); rewrite ? app_nil_r.
- destruct (Permutation_Type_vs_elt_inv _ _ _ HP) as ([lw1 lw2] & HP2); subst; simpl in HP.
  apply Permutation_Type_app_inv in HP.
  rewrite app_assoc in HP; apply IHL in HP.
  destruct HP as [[L' l'] (Hnil' & HeqL' & HP')].
  app_vs_app_flat_map_inv HeqL'.
  + exists ((n, l1) :: L', lw1); simpl; repeat split.
    * intros _ Heqnil; inversion Heqnil.
    * rewrite <- ? app_assoc in HP' ; rewrite <- ? app_assoc.
      now apply Permutation_Type_app_middle.
  + exists (L ++ (n0, l1) :: (n, l2) :: L0, l'); simpl; repeat split.
    * intros _ Heqnil; destruct L; inversion Heqnil.
    * now repeat rewrite ? flat_map_app, <- app_assoc; simpl; rewrite app_nil_r.
    * rewrite ? flat_map_app in HP'; simpl in HP'; rewrite <- app_assoc in HP'; auto.
      rewrite ? flat_map_app; simpl.
      rewrite <- ? app_assoc, app_assoc; apply Permutation_Type_app_middle; simpl.
      etransitivity; [ | rewrite app_assoc; apply HP'].
      rewrite app_assoc, (app_assoc l'); apply Permutation_Type_app_middle.
      now rewrite <- ? app_assoc.
  + exists (L ++ (n , nil) :: L0, l'); simpl; repeat split.
    * intros _ Heqnil; destruct L; inversion Heqnil.
    * now rewrite ? flat_map_app, <- app_assoc.
    * rewrite ? flat_map_app, <- app_assoc in HP'.
      rewrite ? flat_map_app, <- app_assoc; simpl.
      now rewrite app_nil_r, app_assoc; apply Permutation_Type_app_middle; rewrite <- app_assoc.
Qed.

Lemma Permutation_Type_f_app_flat_map T T1 T2 (g : T -> T2) (f : T1 -> T2) lw0 L lw lw' l :
  Permutation_Type lw lw' -> map f lw' = l ++ flat_map (fun '(p1, p2) => g p1 :: p2) L ->
  {'(L', lw') & prod (L <> nil -> L' <> nil)
      (prod (map f lw = lw' ++ flat_map (fun '(p1, p2) => g p1 :: p2) L')
            (Permutation_Type (lw' ++ flat_map (fun '(_, p2) => app (map f lw0) p2) L')
                              (l ++ flat_map (fun '(_, p2) => app (map f lw0) p2) L))) }.
Proof.
intros HP Heq.
apply (Permutation_Type_map f) in HP. rewrite Heq in HP.
apply Permutation_Type_app_flat_map; assumption.
Qed.

Lemma Permutation_Type_flat_map_cons_flat_map_app T T1 T2 (g : T -> T2) (f : T1 -> T2)
  (Hinj : injective f) l0 l1 l2 lp1 lp2 l L :
  Permutation_Type lp1 lp2 ->
  l1 ++ map f lp2 ++ l2 = l ++ flat_map (fun '(p1, p2) => g p1 :: p2) L ->
  {'(l1', l2', l3', l4', l', L') & prod (l1 ++ map f lp1 ++ l2 = l'
                                     ++ flat_map (fun '(p1, p2) => g p1 :: p2) L')
            (prod (Permutation_Type l1' l2')
                  (prod (l3' ++ map f l1' ++ l4'
                             = l' ++ flat_map (fun '(_, p2) => (app (map f l0) p2)) L')
                        (l3' ++ map f l2' ++ l4'
                             = l ++ flat_map (fun '(_, p2) => (app (map f l0) p2)) L))) }.
Proof.
intros HP Heq.
app_vs_app_flat_map_inv Heq.
- app_vs_app_flat_map_inv Heq1.
  + now exists (lp1, lp2, l1,
                l ++ flat_map (fun '(p1,p2) => (app (map f l0) p2)) L,
                l1 ++ map f lp1 ++ l, L); list_simpl; repeat split; try reflexivity.
  + destruct (Permutation_Type_f_app_flat_map _ f l0 _ _ HP Heq2)
      as [[L' l'] (Hnil' & HeqL' & HPL')].
    destruct (map_f_flat_map _ f l0 _ _ _ Heq2) as [Lp HeqLp].
    destruct (map_f_flat_map _ f l0 _ _ _ HeqL') as [Lp' HeqLp'].
    assert (Permutation_Type Lp' Lp) as HPp
      by (rewrite HeqLp, HeqLp' in HPL'; apply (Permutation_Type_map_inv_inj Hinj _ _ HPL')).
    induction L' using rev_rect;
      [ exfalso ; apply Hnil' ; [ intros Heqnil; destruct L0; inversion Heqnil | reflexivity ]
      | clear IHL' ].
    destruct x as (n', x).
    exists (Lp', Lp, l1, l4 ++ flat_map (fun '(p1,p2) => (app (map f l0) p2)) L1,
            l1 ++ l', L' ++ (n' , x ++ l4) :: L1); repeat split.
    * rewrite HeqL'; list_simpl; reflexivity.
    * assumption.
    * rewrite <- HeqLp'; list_simpl; reflexivity.
    * rewrite <- HeqLp; list_simpl; reflexivity.
  + destruct (Permutation_Type_f_app_flat_map _ f l0 _ _ HP Heq2)
      as [[L' l'] (Hnil' & HeqL' & HPL')]; simpl in Hnil', HeqL', HPL'.
    destruct (map_f_flat_map _ f l0 _ _ _ Heq2) as [Lp HeqLp].
    destruct (map_f_flat_map _ f l0 _ _ _ HeqL') as [Lp' HeqLp'].
    assert (Permutation_Type Lp' Lp) as HPp
      by (rewrite HeqLp, HeqLp' in HPL'; apply (Permutation_Type_map_inv_inj Hinj _ _ HPL')).
    exists (Lp', Lp, l1, flat_map (fun '(p1,p2) => (app (map f l0) p2)) L1, l1 ++ l', L' ++ L1);
      repeat split.
    * rewrite HeqL', flat_map_app; list_simpl; reflexivity.
    * assumption.
    * rewrite <- HeqLp', flat_map_app; list_simpl; reflexivity.
    * rewrite <- HeqLp, flat_map_app; list_simpl; reflexivity.
- app_vs_app_flat_map_inv Heq2.
  + now exists (lp1, lp2,
            l ++ flat_map (fun '(p1,p2) => app (map f l0) p2) (L0 ++ (n , l3) :: nil),
            l1 ++ flat_map (fun '(p1,p2) => app (map f l0) p2) L1,
            l, L0 ++ (n , l3 ++ map f lp1 ++ l1) :: L1); repeat split; list_simpl.
  + destruct (Permutation_Type_f_app_flat_map _ f l0 _ _ HP Heq1)
      as [[L' l''] (Hnil' & HeqL' & HPL')].
    destruct (map_f_flat_map _ f l0 _ _ _ Heq1) as [Lp HeqLp].
    destruct (map_f_flat_map _ f l0 _ _ _ HeqL') as [Lp' HeqLp'].
    assert (Permutation_Type Lp' Lp) as HPp
      by (rewrite HeqLp in HPL' ; rewrite HeqLp' in HPL';
          apply (Permutation_Type_map_inv_inj Hinj _ _ HPL')).
    induction L' using rev_rect;
      [ exfalso ; apply Hnil' ; [ intros Heqnil ; destruct L ; inversion Heqnil | reflexivity ]
      | clear IHL' ].
    destruct x as (n' , x).
    exists (Lp', Lp,
            l ++ flat_map (fun '(p1,p2) => app (map f l0) p2) L0 ++ map f l0 ++ l3,
            l5 ++ flat_map (fun '(p1,p2) => app (map f l0) p2) L2,
            l, L0 ++ (n , l3 ++ l'') :: L' ++ (n', x ++ l5) :: L2); repeat split; list_simpl.
    * rewrite HeqL'; list_simpl; reflexivity.
    * assumption.
    * rewrite <- HeqLp'; list_simpl; reflexivity.
    * rewrite <- HeqLp; list_simpl; reflexivity.
  + destruct (Permutation_Type_f_app_flat_map _ f l0 _ _ HP Heq1)
      as [[L' l''] (Hnil' & HeqL' & HPL')].
    destruct (map_f_flat_map _ f l0 _ _ _ Heq1) as [Lp HeqLp].
    destruct (map_f_flat_map _ f l0 _ _ _ HeqL') as [Lp' HeqLp'].
    assert (Permutation_Type Lp' Lp) as HPp
      by (rewrite HeqLp, HeqLp' in HPL' ; apply (Permutation_Type_map_inv_inj Hinj _ _ HPL')).
    exists (Lp', Lp,
            l ++ flat_map (fun '(p1,p2) => app (map f l0) p2) L0 ++ map f l0 ++ l3,
            flat_map (fun '(p1,p2) => app (map f l0) p2) L2,
            l, L0 ++ (n , l3 ++ l'') :: L' ++ L2); repeat split; list_simpl.
    * rewrite HeqL'; list_simpl; reflexivity.
    * assumption.
    * rewrite <- HeqLp'; list_simpl; reflexivity.
    * rewrite <- HeqLp; list_simpl; reflexivity.
- app_vs_flat_map_inv Heq2.
  + rewrite <- (app_nil_l (flat_map _ _)) in Heq1.
    destruct (Permutation_Type_f_app_flat_map _ f l0 _ _ HP Heq1)
      as [[L' l''] (Hnil' & HeqL' & HPL')]; list_simpl in HPL'.
    destruct (map_f_flat_map _ f l0 _ _ _ Heq1) as [Lp HeqLp]; list_simpl in HeqLp.
    destruct (map_f_flat_map _ f l0 _ _ _ HeqL') as [Lp' HeqLp'].
    assert (Permutation_Type Lp' Lp) as HPp
      by (rewrite HeqLp, HeqLp' in HPL' ; apply (Permutation_Type_map_inv_inj Hinj _ _ HPL')).
    induction L' using rev_rect;
      [ exfalso ; apply Hnil' ; [ intros Heqnil ; destruct L ; inversion Heqnil | reflexivity ]
      | clear IHL' ].
    induction L0 using rev_rect; [ | clear IHL0 ].
    * destruct x as (n', x).
      exists (Lp', Lp, l, l3 ++ flat_map (fun '(p1,p2) => app (map f l0) p2) L2,
              l ++ l'', L' ++ (n', x ++ l3) :: L2); repeat split; list_simpl.
      -- rewrite HeqL'; list_simpl; reflexivity.
      -- assumption.
      -- rewrite <- HeqLp'; list_simpl; reflexivity.
      -- rewrite <- HeqLp; list_simpl; reflexivity.
    * destruct x as (n', x), x0 as (n0, x0).
      exists (Lp', Lp,
              l ++ flat_map (fun '(p1,p2) => app (map f l0) p2) L0 ++ map f l0 ++ x0,
              l3 ++ flat_map (fun '(p1,p2) => app (map f l0) p2) L2,
              l, L0 ++ (n0 , x0 ++ l'') :: L' ++ (n' , x ++ l3) :: L2); repeat split; list_simpl.
      -- rewrite HeqL'; list_simpl; reflexivity.
      -- assumption.
      -- rewrite <- HeqLp'; list_simpl; reflexivity.
      -- rewrite <- HeqLp; list_simpl; reflexivity.
  + rewrite <- (app_nil_l (flat_map _ _)) in Heq1.
    destruct (Permutation_Type_f_app_flat_map _ f l0 _ _ HP Heq1)
      as [[L' l''] (Hnil' & HeqL' & HPL')].
    destruct (map_f_flat_map _ f l0 _ _ _ Heq1) as [Lp HeqLp] ; list_simpl in HeqLp.
    destruct (map_f_flat_map _ f l0 _ _ _ HeqL') as [Lp' HeqLp'].
    assert (Permutation_Type Lp' Lp) as HPp
      by (rewrite HeqLp, HeqLp' in HPL' ; apply (Permutation_Type_map_inv_inj Hinj _ _ HPL')).
    induction L0 using rev_rect; [ | clear IHL0 ].
    * exists (Lp', Lp, l, flat_map (fun '(p1,p2) => app (map f l0) p2) L2, l ++ l'', L' ++ L2);
        repeat split; list_simpl.
      -- rewrite HeqL'; list_simpl; reflexivity.
      -- assumption.
      -- rewrite <- HeqLp'; list_simpl; reflexivity.
      -- rewrite <- HeqLp; list_simpl; reflexivity.
    * destruct x as (n' , x).
      exists (Lp', Lp,
              l ++ flat_map (fun '(p1,p2) => app (map f l0) p2) L0 ++ map f l0 ++ x,
              flat_map (fun '(p1,p2) => app (map f l0) p2) L2,
              l, L0 ++ (n', x ++ l'') :: L' ++ L2); repeat split; list_simpl.
      -- rewrite HeqL'; list_simpl; reflexivity.
      -- assumption.
      -- rewrite <- HeqLp'; list_simpl; reflexivity.
      -- rewrite <- HeqLp; list_simpl; reflexivity.
Qed.

Lemma CPermutation_Type_app_flat_map B T (f : B -> T) lw0 L lw l :
  CPermutation_Type lw (l ++ flat_map (fun '(p1,p2) => f p1 :: p2) L) ->
  {'(L', lw') & prod (L <> nil -> L' <> nil)
      (prod (lw = lw' ++ flat_map (fun '(p1,p2) => f p1 :: p2) L')
            (CPermutation_Type (lw' ++ flat_map (fun '(p1,p2) => app lw0 p2) L')
                               (l ++ flat_map (fun '(p1,p2) => app lw0 p2) L))) }.
Proof.
intros HC; inversion HC as [l1 l2 Heq1 Heq2]; subst.
dichot_app_inf_exec Heq2; subst.
- induction L as [|[n l] L IHL] using rev_rect; [ | clear IHL ]; simpl.
  + now exists (nil, l0 ++ l2); rewrite ? app_nil_r.
  + exists (L ++ (n, l ++ l2) :: nil, l0); simpl; repeat split.
    * intros _ Heqnil; destruct L; inversion Heqnil.
    * now rewrite 2 flat_map_app; simpl; rewrite ? app_nil_r, <- ? app_assoc, <- app_comm_cons.
    * rewrite 2 flat_map_app; simpl.
      rewrite <- ? app_assoc, ? app_nil_r, 3 app_assoc, <- (app_assoc l0), <- 2 (app_assoc _ _ l);
      constructor.
- app_vs_flat_map_inv Heq1.
  + induction L1 as [|[n' l'] L1 IHL1] using rev_rect; [ | clear IHL1 ]; simpl.
    * exists (L0 ++ (n , l2) :: nil, l3 ++ l); simpl; rewrite ? app_nil_r; repeat split.
      -- intros _ Heqnil; destruct L0; inversion Heqnil.
      -- now rewrite <- app_assoc.
      -- rewrite 2 flat_map_app; simpl; rewrite <- app_assoc, ? app_nil_r ; symmetry.
         rewrite 3 app_assoc, <- (app_assoc l), <- 2 (app_assoc _ _ l2); constructor.
    * exists (L1 ++ (n' , l' ++ l) :: L0 ++ (n , l2) :: nil, l3); simpl; repeat split.
      -- intros _ Heqnil; destruct L1; inversion Heqnil.
      -- now rewrite ? flat_map_app; simpl; rewrite flat_map_app; simpl;
           rewrite ? app_nil_r, <- ? app_assoc.
      -- rewrite 2 flat_map_app; simpl; rewrite 2 flat_map_app; simpl;
           rewrite ? app_nil_r, <- ? app_assoc, 3 app_assoc,
                   <- (app_assoc l3), <- 2 (app_assoc _ _ l').
         now etransitivity ; [ apply cperm_Type | ]; rewrite <- ? app_assoc.
  + induction L1 as [|[n l'] L1 IHL1] using rev_rect; [ | clear IHL1 ]; simpl.
    * now exists (L0, l); simpl; rewrite ? app_nil_r.
    * exists (L1 ++ (n, l' ++ l) :: L0, nil); simpl; repeat split.
      -- intros _ Heqnil; destruct L1; inversion Heqnil.
      -- now rewrite ? flat_map_app, <- ? app_assoc; simpl; 
           rewrite ? app_nil_r, <- ? app_comm_cons, <- app_assoc.
      -- rewrite 2 flat_map_app; simpl; rewrite flat_map_app; simpl; rewrite (app_assoc l).
         now etransitivity; [ | apply cperm_Type ]; rewrite <- ? app_assoc.
Qed.

Lemma PCPermutation_Type_app_flat_map b B T (f : B -> T) lw0 L lw l :
  PCPermutation_Type b lw (l ++ flat_map (fun '(p1,p2) => f p1 :: p2) L) ->
  {'(L', lw') & prod (L <> nil -> L' <> nil)
      (prod (lw = lw' ++ flat_map (fun '(p1,p2) => f p1 :: p2) L')
            (PCPermutation_Type b (lw' ++ flat_map (fun '(p1,p2) => app lw0 p2) L')
                               (l ++ flat_map (fun '(p1,p2) => app lw0 p2) L))) }.
Proof. destruct b; [ apply Permutation_Type_app_flat_map | apply CPermutation_Type_app_flat_map ]. Qed.


Lemma app_vs_flat_map_cst T (A : T) L l1 l2 :
  l1 ++ l2 = flat_map (cons A) L ->
      {'(L1, L2, l3, l4) | l4 <> nil
          /\ L = L1 ++ (l3 ++ l4) :: L2
          /\ l1 = flat_map (cons A) (L1 ++ l3 :: nil)
          /\ l2 = l4 ++ flat_map (cons A) L2 }
    + {'(L1, L2) | L = L1 ++ L2
          /\ l1 = flat_map (cons A) L1
          /\ l2 = flat_map (cons A) L2 }.
Proof.
intros Heq; destruct (@app_vs_flat_map _ _ (fun (p : nat) => A) (map (fun x => (1 , x)) L) l1 l2).
{ rewrite Heq.
  clear; induction L; auto.
  now simpl; rewrite IHL. }
- destruct s as (((((L1 & L2) & n) & l3) & l4) & H).
  left; exists (map snd L1, map snd L2, l3, l4).
  destruct H as (H1 & H2 & H3 & H4).
  repeat split; auto.
  + clear - H2; revert L H2; induction L1; intros L H2; simpl; destruct L; inversion H2; simpl.
    * replace (map snd (map (fun x => (1, x)) L)) with L; auto.
      clear; induction L; auto.
      now simpl; rewrite <- IHL.
    * specialize (IHL1 L).
      now rewrite IHL1.
  + rewrite H3.
    clear; induction L1; auto.
    now destruct a; simpl; rewrite IHL1.
  + replace (flat_map (cons A) (map snd L2)) with (flat_map (fun '(p1,p2) => A :: p2) L2); auto.
    clear; induction L2; auto.
    now destruct a; simpl; rewrite IHL2.
- right.
  destruct s as ((L1 & L2) & (H1 & H2 & H3)).
  exists (map snd L1, map snd L2); repeat split.
  + clear - H1; revert L H1; induction L1; intros L H1.
    * simpl; simpl in H1; rewrite <- H1.
      clear; induction L; auto.
      now simpl; rewrite<- IHL.
    * destruct L; inversion H1; simpl.
      specialize (IHL1 L).
      now rewrite IHL1.
  + rewrite H2.
    clear; induction L1; auto.
    now destruct a; simpl; rewrite IHL1.
  + rewrite H3.
    clear; induction L2; auto.
    now destruct a; simpl; rewrite IHL2.
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

Lemma app_vs_app_flat_map_cst T (A : T) l0 L l1 l2 :
  l1 ++ l2 = l0 ++ flat_map (cons A) L ->
      { l' | l' <> nil
          /\ l0 = l1 ++ l'
          /\ l2 = l' ++ flat_map (cons A) L }
    + {'(L1, L2, l3, l4) | l4 <> nil
          /\ L = L1 ++ (l3 ++ l4) :: L2
          /\ l1 = l0 ++ flat_map (cons A) (L1 ++ l3 :: nil)
          /\ l2 = l4 ++ flat_map (cons A) L2 }
    + {'(L1, L2) | L = L1 ++ L2
          /\ l1 = l0 ++ flat_map (cons A) L1
          /\ l2 = flat_map (cons A) L2 }.
Proof.
intro Heq. dichot_app_inf_exec Heq.
- destruct l as [|t l]; subst.
  + right; exists (nil, L); simpl; auto.
    now rewrite 2 app_nil_r.
  + left; left; exists (t :: l); auto.
    repeat split.
    intros Heq; inversion Heq.
- app_vs_flat_map_cst_inv Heq1.
  + left; right; exists (L0, L1, l3, l4); auto.
  + right; exists (L0, L1); auto.
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

Lemma elt_vs_app_flat_map_cst T (A : T) l0 L l1 l2 B :
  l1 ++ B :: l2 = l0 ++ flat_map (cons A) L ->
      { l' | l0 = l1 ++ B :: l'
          /\ l2 = l' ++ flat_map (cons A) L }
    + {'(L1, L2, l1', l2') | L = L1 ++ (l1' ++ B :: l2') :: L2
          /\ l1 = l0 ++ flat_map (cons A) L1 ++ (A :: l1')
          /\ l2 = l2' ++ flat_map (cons A) L2 }
    + {'(L1, L2, l) | B = A
          /\ L = L1 ++ l :: L2
          /\ l1 = l0 ++ flat_map (cons A) L1
          /\ l2 = l ++ flat_map (cons A) L2 }.
Proof.
intro Heq. dichot_elt_app_inf_exec Heq; subst; [ left; left; exists l; repeat split | ].
induction L as [|l' L IHL] in l, l2, Heq1 |- *; cbn in Heq1.
- exfalso. nil_vs_elt_inv Heq1.
- rewrite app_comm_cons in Heq1. dichot_elt_app_inf_exec Heq1; subst.
  + destruct l as [|t l]; destr_eq Heq0; subst.
    * right. exists (nil, L, l'). repeat split.
    * left. right. exists (nil, L , l, l1). repeat split.
  + apply IHL in Heq2 as [[[l'' [Heqa _]]
                       | [[[[L' L''] l''] l'''] [-> [->%app_inv_head ->]]]]
                       | [[[L' L''] l''] [-> [-> [->%app_inv_head ->]]]]].
    * exfalso.
      rewrite <- (app_nil_r l0) in Heqa. rewrite <- 2 app_assoc in Heqa. apply app_inv_head in Heqa.
      cbn in Heqa. nil_vs_elt_inv Heqa.
    * left. right. exists (l' :: L', L'', l'', l'''). cbn. rewrite ? app_assoc. repeat split.
    * right. exists (l' :: L', L'', l''). repeat split.
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

Lemma map_f_flat_map_cst T T1 (A : T1) (f : T -> T1) lw' lw l L :
  map f lw = l ++ flat_map (cons A) L ->
  { Lw | l ++ flat_map (app (map f lw')) L = map f Lw }.
Proof.
induction L as [|l0 L IHL] in lw, l |- *; cbn; intro Heq.
- exists lw. symmetry. assumption.
- rewrite app_comm_cons, app_assoc in Heq.
  apply IHL in Heq as [Lw Heq].
  decomp_map Heq eqn:Hf. subst Lw. rewrite <- Hf.
  exists (l ++ (lw' ++ l0) ++ l2). rewrite ! map_app. reflexivity.
Qed.

Lemma Permutation_Type_app_flat_map_cst T (A : T) lw0 L lw l :
  Permutation_Type lw (l ++ flat_map (cons A) L) ->
  {'(L', lw') & prod (L <> nil -> L' <> nil)
      (prod (lw = lw' ++ flat_map (cons A) L')
            (Permutation_Type (lw' ++ flat_map (app lw0) L')
                              (l ++ flat_map (app lw0) L))) }.
Proof.
intro HP.
destruct (@Permutation_Type_app_flat_map _ _ (fun _ => A) lw0 (map (fun p => (1, p)) L) lw l).
{ replace (flat_map (fun '(p1,p2) => A :: p2)
                    (map (fun p => (1,p)) L)) with (flat_map (cons A) L)
    by (clear; induction L as [|? ? IHL]; [ | cbn; rewrite IHL ]; reflexivity).
  assumption. }
destruct x as (L', lw'), y as [H1 [H2 H3]].
split with (map snd L', lw'); repeat split.
- intros Hneq ->%map_eq_nil.
  apply H1; [ | reflexivity ].
  intros ->%map_eq_nil. apply Hneq. reflexivity.
- replace (flat_map (cons A) (map snd L')) with (flat_map (fun '(_, p2) => A :: p2) L')
    by (clear; induction L' as [|[] L' IHL']; [ | cbn; rewrite IHL']; reflexivity).
  assumption.
- replace (flat_map (app lw0) (map snd L')) with (flat_map (fun '(_, p2) => lw0 ++ p2) L')
    by (clear; induction L' as [|[] L' IHL']; [ | cbn; rewrite IHL']; reflexivity).
  replace (flat_map (app lw0) L)
     with (flat_map (fun '(_, p2) => lw0 ++ p2) (map (fun p => (1, p)) L))
       by (clear; induction L as [|? ? IHL]; [ | cbn; rewrite IHL ]; reflexivity).
  assumption.
Qed.

Lemma Permutation_Type_f_app_flat_map_cst T T1 (A : T1) (f : T -> T1) lw0 L lw lw' l :
  Permutation_Type lw lw' -> map f lw' = l ++ flat_map (cons A) L ->
  {'(L' , lw') & prod (L <> nil -> L' <> nil)
      (prod (map f lw = lw' ++ flat_map (cons A) L')
            (Permutation_Type (lw' ++ flat_map (app (map f lw0)) L')
                              (l ++ flat_map (app (map f lw0)) L))) }.
Proof.
intros HP%(Permutation_Type_map f) Heq. rewrite Heq in HP.
apply Permutation_Type_app_flat_map_cst. assumption.
Qed.

Lemma Permutation_Type_flat_map_cons_flat_map_app_cst T T1 (A : T1) (f : T -> T1)
  (Hinj : injective f) l0 l1 l2 lp1 lp2 l L :
  Permutation_Type lp1 lp2 ->
  l1 ++ map f lp2 ++ l2 = l ++ flat_map (cons A) L ->
  {'(l1', l2', l3', l4', l', L')  &  prod (l1 ++ map f lp1 ++ l2 = l' ++ flat_map (cons A) L')
            (prod (Permutation_Type l1' l2')
                  (prod (l3' ++ map f l1' ++ l4'
                             = l' ++ flat_map (app (map f l0)) L')
                        (l3' ++ map f l2' ++ l4'
                             = l ++ flat_map (app (map f l0)) L))) }.
Proof.
intros HP Heq.
destruct (@Permutation_Type_flat_map_cons_flat_map_app _ _ _ (fun _ => A)
            f Hinj l0 l1 l2 lp1 lp2 l (map (fun p => (1 , p)) L)); auto.
{ replace (flat_map (fun '(p1, p2) => A :: p2) (map (fun p => (1, p)) L))
     with (flat_map (cons A) L) by (clear; induction L as [|? ? IHL]; [ | cbn; rewrite IHL]; reflexivity).
  assumption. }
destruct x as [[[[[l1' l2'] l3'] l4'] l'] L'], y as [H1 [H2 [H3 H4]]].
split with (l1', l2', l3', l4', l', map snd L'); repeat split; auto.
- replace (flat_map (cons A) (map snd L'))
     with (flat_map (fun '(_, p2) => A :: p2) L')
    by (clear; induction L' as [|[] L' IHL']; [ | cbn; rewrite IHL']; reflexivity).
  assumption.
- replace (flat_map (app (map f l0)) (map snd L'))
     with (flat_map (fun '(_, p2) => map f l0 ++ p2) L')
    by (clear; induction L' as [|[] L' IHL']; [ | cbn; rewrite IHL']; reflexivity).
  assumption.
- replace (flat_map (app (map f l0)) L)
     with (flat_map (fun '(_, p2) => map f l0 ++ p2) (map (fun p  => (1, p)) L))
    by (clear; induction L as [|? ? IHL]; [ | cbn; rewrite IHL]; reflexivity).
  assumption.
Qed.

Lemma CPermutation_Type_app_flat_map_cst T (A : T) lw0 L lw l :
  CPermutation_Type lw (l ++ flat_map (cons A) L) ->
  {'(L', lw') & prod (L <> nil -> L' <> nil)
      (prod (lw = lw' ++ flat_map (cons A) L')
            (CPermutation_Type (lw' ++ flat_map (app lw0) L')
                               (l ++ flat_map (app lw0) L))) }.
Proof.
intro HC.
destruct (@CPermutation_Type_app_flat_map _ _ (fun p => A) lw0 (map (fun x => (1 , x)) L) lw l)
  as [[L' lw'] [H1 [H2 H3]]].
{ replace (flat_map (fun '(_, p2) => A :: p2) (map (fun x => (1, x)) L))
     with (flat_map (cons A) L)
    by (clear; induction L as [|[] L IHL]; [ | cbn; rewrite IHL .. ]; reflexivity).
  assumption. }
split with (map snd L' , lw'); repeat split.
- intros Hneq ->%map_eq_nil.
  apply H1; [ | reflexivity ].
  intros ->%map_eq_nil.
  apply Hneq. reflexivity.
- replace (flat_map (cons A) (map snd L'))
     with (flat_map (fun '(_, p2) => A :: p2) L')
    by (clear; induction L' as [|[] L' IHL']; [ | cbn; rewrite IHL']; reflexivity).
  assumption.
- replace (flat_map (app lw0) (map snd L'))
     with (flat_map (fun '(_, p2) => lw0 ++ p2) L')
    by (clear; induction L' as [|[] L' IHL']; [ | cbn; rewrite IHL']; reflexivity).
  replace (flat_map (app lw0) L)
    with (flat_map (fun '(_, p2) => lw0 ++ p2) (map (fun x => (1, x)) L))
    by (clear; induction L; [ | cbn; rewrite IHL ]; reflexivity).
  assumption.
Qed.
