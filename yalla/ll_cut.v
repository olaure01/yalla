(* ll_cut library for yalla *)

(** * Cut elimination for [ll] from cut elimination for [ill] *)


Require Import Arith.

Require Import List_more.
Require Import Permutation_Type_more.
Require Import Permutation_Type_solve.
Require Import genperm_Type.

Require Export ll_def.
Require Import ll_mix.
Require Import subs.
Require Import ill_cut.
Require Import nn_def.



(** Ingredients for generating fresh variables *)
Definition a2n := yalla_ax.a2n.
Definition n2a := yalla_ax.n2a.
Definition n2n_a := yalla_ax.n2n_a.


Section CutElimTransfer.

Variable P : pfrag.
Hypothesis Hgax_at : forall a, Forall atomic (projT2 (pgax P) a).
Hypothesis Hgax_ex : forall a l, PCperm_Type (pperm P) (projT2 (pgax P) a) l ->
                     exists b, l = projT2 (pgax P) b.
Hypothesis Hgax_cut : forall a b x l1 l2 l3,
  projT2 (pgax P) a = (dual x :: l1) -> projT2 (pgax P) b = (l2 ++ x :: l3) ->
  exists c, projT2 (pgax P) c = l2 ++ l1 ++ l3.


Hypothesis Hperm : pperm P = true.  (* TODO generalize to the cyclic case *)

Theorem cut_elim_no_mix : pmix0 P = false -> pmix2 P = false -> forall A l1 l2,
ll P (dual A :: l1) -> ll P (A :: l2) -> ll P (l2 ++ l1).
Proof with myeasy.
intros Hmix0 Hmix2.
intros A l1 l2 pi1 pi2.
specialize (ax_loc _ _ pi1) as pi1'.
specialize (ax_loc _ _ pi2) as pi2'.
remember (gax_elts pi1) as lax1 ; clear Heqlax1.
remember (gax_elts pi2) as lax2 ; clear Heqlax2.
pose (axupd_pfrag P
        (existT (fun x => x -> list formula) (Fin.t (length (lax1 ++ lax2)))
                (fun n => projT2 (pgax P) (Vector.nth (Vector.of_list (lax1 ++ lax2)) n))))
  as PP.
assert (ll PP (dual A :: l1)) as pi1''...
{ eapply stronger_pfrag ; [ | apply pi1' ].
  nsplit 5...
  unfold PP ; simpl.
  intros a ; clear.
  enough ({ b | Vector.nth (Vector.of_list lax1) a
              = Vector.nth (Vector.of_list (lax1 ++ lax2)) b }) as [b Hb]
    by (exists b ; rewrite Hb ; reflexivity).
  induction lax1...
  - inversion a.
  - simpl in a.
    eapply (Fin.caseS' a).
    + exists Fin.F1...
    + intros a'.
      destruct (IHlax1 a') as [b Hb].
      exists (Fin.FS b)... }
assert (ll PP (A :: l2)) as pi2''...
{ eapply stronger_pfrag ; [ | apply pi2' ].
  nsplit 5...
  unfold PP ; simpl.
  intros a ; clear.
  enough ({ b | Vector.nth (Vector.of_list lax2) a
              = Vector.nth (Vector.of_list (lax1 ++ lax2)) b }) as [b Hb]
    by (exists b ; rewrite Hb ; reflexivity).
  induction lax1...
  - exists a...
  - destruct IHlax1 as [b Hb].
    exists (Fin.FS b)... }
clear pi1 pi2 pi1' pi2'.
apply (stronger_pfrag _ _ (cutupd_pfrag_true _)) in pi1''.
apply (stronger_pfrag _ _ (cutupd_pfrag_true _)) in pi2''.
pose (nat_fresh_of_list a2n ((rev l1 ++ rev l2) ++ flat_map (projT2 (pgax P)) (lax1 ++ lax2)))
  as z.
apply (ll_to_ill_trans (ivar (a2i (n2a z)))) in pi1'' ;
  [ | assumption | simpl ; intros f ; rewrite f in Hmix0 ; inversion Hmix0
                 | simpl ; intros f ; rewrite f in Hmix2 ; inversion Hmix2 ].
apply (ll_to_ill_trans (ivar (a2i (n2a z)))) in pi2'' ;
  [ | assumption | simpl ; intros f ; rewrite f in Hmix0 ; inversion Hmix0
                 | simpl ; intros f ; rewrite f in Hmix2 ; inversion Hmix2 ].
simpl in pi1'' ; simpl in pi2''.
apply negR_irr in pi1''.
apply negR_irr in pi2''.
assert (ipperm (cutupd_ipfrag (p2ipfrag (ivar (a2i (n2a z))) PP) true) = true) as Hperm'
  by (simpl ; rewrite Hperm ; reflexivity).
assert (pi0 := trans_dual (ivar (a2i (n2a z))) Hperm' eq_refl A).
rewrite <- (app_nil_l _) in pi0.
eapply (cut_ir _ _ _ _ _ _ pi2'') in pi0.
list_simpl in pi0.
eapply (cut_ir _ _ _ _ _ _ pi1'') in pi0.
pose (existT (fun x => x -> list iformula * iformula)
             (Fin.t (length (lax1 ++ lax2)))
             (fun n => (map (trans (ivar (a2i (n2a z))))
                 (projT2 (pgax P) (Vector.nth (Vector.of_list (lax1 ++ lax2)) n)), ivar (a2i (n2a z)))))
  as Ax.
eapply (stronger_ipfrag _ (axupd_ipfrag (p2ipfrag (ivar (a2i (n2a z))) (cutupd_pfrag P true)) Ax))
  in pi0.
- pose ((fun x => Vector.nth (Vector.of_list (lax1 ++ lax2)) x)
       : projT1 Ax -> projT1 (ipgax (p2ipfrag (ivar (a2i (n2a z))) (cutupd_pfrag P true)))) as f.
  eapply (cut_admissible_ipgax_sat _ _ _ _ _ f) in pi0...
  apply (ill_to_ll i2a) in pi0.
  list_simpl in pi0.
  apply (subs_ll bot (n2a z)) in pi0.
  list_simpl in pi0.
  rewrite repl_at_eq in pi0 ; [ | rewrite a2a_i ; reflexivity ].
  apply (ax_gen _ P) in pi0...
  + rewrite <- app_nil_l in pi0.
    eapply bot_rev_axat in pi0 ; [ | | reflexivity ]...
    list_simpl in pi0.
    apply (ex_r _ (rev l1 ++ rev l2)) ;
      [ | rewrite Hperm ; 
          rewrite <- rev_app_distr ;
          symmetry ; apply Permutation_Type_rev ].
    eapply munit_elim ; [ | exact pi0 | ]...
    rewrite <- ? map_app.
    remember (rev l1 ++ rev l2) as l ; clear.
    remember (lax1 ++ lax2) as lax ; clear.
    assert (HF : Forall (fun x : formula => nat_fresh_of a2n x <= z) l).
    { assert (Hle : nat_fresh_of_list a2n l <= z)
        by (unfold z ; unfold nat_fresh_of_list ; list_simpl ; rewrite list_max_app ; myeasy).
      clearbody z ; revert Hle ; clear.
      unfold nat_fresh_of_list.
      revert z ; induction l ; intros z Hle ; constructor.
      - simpl in Hle...
      - apply IHl ; simpl in Hle... }
    clearbody z ; revert HF ; induction l ; intros HF ; constructor.
    * rewrite <- (yalla_ax.a2a_n z).
      apply munit_trans.
      rewrite yalla_ax.a2a_n.
       inversion HF ; simpl...
    * apply IHl.
     inversion HF ; subst ; assumption.
  + intros a ; simpl in a.
    destruct a as [x Hsat].
    apply bot_r.
    rewrite map_rev.
    eapply ex_r ; [ | rewrite Hperm ; apply Permutation_Type_rev ].
    assert (pi := gax_r _ x).
    specialize (Hgax_at x).
    simpl ; remember (projT2 (pgax P) x) as l.
    rewrite <- app_nil_l.
    rewrite <- app_nil_l in Hgax_at.
    rewrite <- app_nil_l in pi.
    revert Hgax_at pi.
    assert (nat_fresh_of_list a2n l <= z) as Hz.
    { subst ; unfold z ; remember (lax1 ++ lax2) as lax ; clear - Hperm Hsat.
      unfold nat_fresh_of_list.
      list_simpl ; rewrite list_max_app.
      etransitivity ; [ | apply Nat.le_max_r ].
      list_simpl ; rewrite list_max_app.
      etransitivity ; [ | apply Nat.le_max_r ].
      unfold Ax in Hsat ; unfold f in Hsat ; unfold z in Hsat ; simpl in Hsat ;
        clear - Hperm Hsat.
      induction Hsat.
      - revert x ; induction lax ; intros x...
        + inversion x.
        + simpl in x ; apply (Fin.caseS' x) ; simpl.
          * list_simpl.
            rewrite list_max_app.
            apply Nat.le_max_l.
          * intros y.
            etransitivity ; [ apply (IHlax y) | ].
            list_simpl.
            rewrite list_max_app.
            apply Nat.le_max_r.
      - simpl in X ; simpl in a ; simpl in b.
        etransitivity ; [ | apply IHHsat ].
        apply PEperm_Type_map_inv_inj in X ; [ | apply trans_inj ].
        remember (projT2 (pgax P) a) as la.
        remember (projT2 (pgax P) b) as lb.
        rewrite Hperm in X ; simpl in X ; clear - X.
        induction X ; simpl...
      - simpl in a ; simpl in b ; simpl in c ;
          simpl in H ; simpl in H0 ; simpl in H1 ; simpl in H2 ; simpl in H3.
        etransitivity ; [ | apply (proj2 (Nat.max_lub_iff _ _ _) (conj IHHsat1 IHHsat2)) ].
        rewrite_all H0.
        remember (projT2 (pgax P) a) as la.
        remember (projT2 (pgax P) b) as lb.
        remember (projT2 (pgax P) c) as lc.
        clear - H H1 H2.
        symmetry in H ; decomp_map H ; subst ; clear H3.
        symmetry in H1 ; decomp_map H1 ; subst ; clear H1.
        rewrite <- ? map_app in H2.
        apply Injective.map_inj in H2 ; [ | apply trans_inj ] ; subst.
        list_simpl.
        rewrite ? list_max_app.
        simpl... }
    remember nil as l' ; clear - Hperm Hz ; revert l'.
    induction l ; intros l' Hat pi...
    unfold nat_fresh_of_list in Hz.
    apply Nat.max_lub_iff in Hz.
    destruct Hz as [Hz1 Hz2].
    assert (Ha_at := Forall_elt _ _ _ _ Hat).
    destruct a ; (try now (exfalso ; inversion Hat)) ; list_simpl.
    * rewrite repl_at_eq ; simpl...
      eapply ex_r ; [ | rewrite Hperm ; apply Permutation_Type_app_comm ].
      list_simpl.
      rewrite <- (app_nil_r l').
      rewrite app_assoc.
      apply tens_r ; [ apply one_r | ].
      assert (i2a (a2i a) <> n2a z) as Haz.
      { rewrite a2a_i.
        intros Heq ; subst.
        simpl in Hz1.
        rewrite n2n_a in Hz1... }
      rewrite repl_at_neq...
      cons2app in pi.
      rewrite app_assoc in pi.
      apply IHl in pi ; list_simpl...
      eapply ex_r ; [ apply pi | ]...
      rewrite Hperm ; list_simpl ; perm_Type_solve.
    * assert (i2a (a2i a) <> n2a z) as Haz.
      { rewrite a2a_i.
        intros Heq ; subst.
        simpl in Hz1.
        rewrite n2n_a in Hz1... }
      rewrite repl_at_neq...
      cons2app in pi.
      rewrite app_assoc in pi.
      apply IHl in pi ; list_simpl...
      eapply ex_r ; [ apply pi | ]...
      rewrite Hperm ; list_simpl ; perm_Type_solve.
- nsplit 3 ; simpl...
  intros a ; exists a...
Unshelve. all : try intuition.
+ simpl.
  specialize (Hgax_at a).
  remember (projT2 (pgax P) a) as l.
  revert Hgax_at ; clear ; induction l ; intros Hgax_at ; constructor ;
    inversion Hgax_at ; subst.
  * inversion H1 ; subst ; simpl ; constructor.
  * apply IHl...
+ simpl ; constructor.
+ rewrite Hperm in Hgax_ex ; simpl in Hgax_ex.
  simpl in X ; rewrite Hperm in X ; simpl in X.
  symmetry in X.
  destruct (Permutation_Type_map_inv _ _ _ X) as [l' Heq HP] ; subst.
  destruct (Hgax_ex _ _ HP) as [b Hgax] ; subst.
  exists b...
+ simpl.
  simpl in H ; symmetry in H ; decomp_map H ; subst ; symmetry in H.
  destruct x0 ; inversion H3.
  change (covar a0) with (dual (var a0)) in H.
  simpl in H1 ; symmetry in H1 ; decomp_map H1 ; subst ; symmetry in H6.
  destruct x0 ; inversion H1.
  assert (a0 = a1) by (destruct a0 ; destruct a1 ; intuition) ; subst.
  destruct (Hgax_cut _ _ _ _ _ _ H H6) as [c Heq] ; subst.
  exists c ; split...
  rewrite Heq ; list_simpl...
Qed.

Lemma cut_elim_with_wn : pmix0 P = false -> pmix2 P = false -> forall A l1 l2 l0,
  ll P (dual A :: l1 ++ map wn l0) -> ll P (A :: l2 ++ map wn l0) ->
  ll P (l2 ++ l1 ++ map wn l0).
Proof with myeeasy.
intros Hmix0 Hmix2.
intros A l1 l2 l0 pi1 pi2.
eapply ex_r ; [ | rewrite Hperm ; rewrite app_assoc ; apply Permutation_Type_app_swap ].
apply co_std_list_r.
eapply ex_r ; [ | rewrite Hperm ; apply Permutation_Type_app_swap ].
list_simpl ; rewrite app_assoc.
eapply cut_elim_no_mix...
eapply ex_r...
rewrite Hperm ; simpl ; perm_Type_solve.
Qed.

End CutElimTransfer.


Section CutElimTransfer2.

Variable P : pfrag.
Hypothesis Hgax_at : forall a, Forall atomic (projT2 (pgax P) a).
Hypothesis Hgax_ex : forall a l, PCperm_Type (pperm P) (projT2 (pgax P) a) l ->
                     exists b, l = projT2 (pgax P) b.
Hypothesis Hgax_cut : forall a b x l1 l2 l3,
  projT2 (pgax P) a = (dual x :: l1) -> projT2 (pgax P) b = (l2 ++ x :: l3) ->
  exists c, projT2 (pgax P) c = l2 ++ l1 ++ l3.


Hypothesis Hperm : pperm P = true.  (* TODO generalize to the cyclic case *)

Theorem cut_elim_mix0 : pmix0 P = true -> pmix2 P = false -> forall A l1 l2,
  ll P (dual A :: l1) -> ll P (A :: l2) -> ll P (l2 ++ l1).
Proof with myeeasy.
intros Hmix0 Hmix2.
intros A l1 l2 pi1 pi2.
pose (Q := mk_pfrag P.(pcut) P.(pgax) false P.(pmix2) true).
assert (P = mix0add_pfrag Q) as HP.
{ destruct P ; unfold mix0add_pfrag ; simpl.
  simpl in Hmix0 ; rewrite Hmix0.
  simpl in Hperm ; rewrite Hperm... }
rewrite HP in pi1.
apply mix0_to_ll in pi1...
rewrite HP in pi2.
apply mix0_to_ll in pi2...
eapply ex_r in pi1 ; [ | apply Permutation_Type_cons_append ].
rewrite <- app_comm_cons in pi1.
eapply ex_r in pi2 ; [ | apply Permutation_Type_cons_append ].
rewrite <- app_comm_cons in pi2.
rewrite HP.
apply ll_to_mix0...
apply (ex_r _ (l2 ++ l1 ++ map wn (one :: nil))) ; [ | simpl ; perm_Type_solve ].
eapply cut_elim_with_wn...
unfold Q ; simpl.
intros a l HP'.
apply (Hgax_ex a).
rewrite Hperm...
Qed.

Theorem cut_elim_mix2 : pmix0 P = false -> pmix2 P = true -> forall A l1 l2,
  ll P (dual A :: l1) -> ll P (A :: l2) -> ll P (l2 ++ l1).
Proof with myeeasy.
intros Hmix0 Hmix2.
intros A l1 l2 pi1 pi2.
pose (Q := mk_pfrag P.(pcut) P.(pgax) P.(pmix0) false true).
assert (P = mix2add_pfrag Q) as HP.
{ destruct P ; unfold mix2add_pfrag ; simpl.
  simpl in Hmix2 ; rewrite Hmix2.
  simpl in Hperm ; rewrite Hperm... }
rewrite HP in pi1.
apply mix2_to_ll in pi1...
rewrite HP in pi2.
apply mix2_to_ll in pi2...
eapply ex_r in pi1 ; [ | apply Permutation_Type_cons_append ].
rewrite <- app_comm_cons in pi1.
eapply ex_r in pi2 ; [ | apply Permutation_Type_cons_append ].
rewrite <- app_comm_cons in pi2.
rewrite HP.
apply ll_to_mix2...
apply (ex_r _ (l2 ++ l1 ++ map wn (tens bot bot :: nil))) ; [ | simpl ; perm_Type_solve ].
eapply cut_elim_with_wn...
unfold Q ; simpl.
intros a l HP'.
apply (Hgax_ex a).
rewrite Hperm...
Qed.

Theorem cut_elim_mix02 : pmix0 P = true -> pmix2 P = true -> forall A l1 l2,
  ll P (dual A :: l1) -> ll P (A :: l2) -> ll P (l2 ++ l1).
Proof with myeeasy.
intros Hmix0 Hmix2.
intros A l1 l2 pi1 pi2.
pose (Q := mk_pfrag P.(pcut) P.(pgax) false false true).
assert (P = mix2add_pfrag (mix0add_pfrag Q)) as HP.
{ destruct P ; unfold mix2add_pfrag ; simpl.
  simpl in Hmix0 ; rewrite Hmix0.
  simpl in Hmix2 ; rewrite Hmix2.
  simpl in Hperm ; rewrite Hperm... }
rewrite HP in pi1.
apply (@mix02_to_ll' Q) in pi1...
rewrite HP in pi2.
apply (@mix02_to_ll' Q) in pi2...
eapply ex_r in pi1 ; [ | apply Permutation_Type_cons_append ].
rewrite <- app_comm_cons in pi1.
eapply ex_r in pi1 ; [ | apply Permutation_Type_cons_append ].
list_simpl in pi1.
eapply ex_r in pi2 ; [ | apply Permutation_Type_cons_append ].
rewrite <- app_comm_cons in pi2.
eapply ex_r in pi2 ; [ | apply Permutation_Type_cons_append ].
list_simpl in pi2.
rewrite HP.
apply ll_to_mix02...
apply (ex_r _ (l2 ++ l1 ++ map wn (one :: tens bot bot :: nil))) ; [ | simpl ; perm_Type_solve ].
eapply cut_elim_with_wn...
unfold Q ; simpl.
intros a l HP'.
apply (Hgax_ex a).
rewrite Hperm...
Qed.


Theorem cut_elim_perm : forall A l1 l2,
  ll P (dual A :: l1) -> ll P (A :: l2) -> ll P (l2 ++ l1).
Proof with myeasy.
case_eq (pcut P) ; intros Hcut.
- apply cut_r...
- case_eq (pmix0 P) ; case_eq (pmix2 P) ; intros Hmix2 Hmix0.
  + apply cut_elim_mix02...
  + apply cut_elim_mix0...
  + apply cut_elim_mix2...
  + apply cut_elim_no_mix...
Qed.

End CutElimTransfer2.


Axiom cut_elim_cyclic :
  forall P, pperm P = false ->
  forall P_gax_atomic : forall a, Forall atomic (projT2 (pgax P) a),
  (forall a l, PCperm_Type (pperm P) (projT2 (pgax P) a) l -> exists b, l = projT2 (pgax P) b) ->
  (forall a b x l1 l2 l3, projT2 (pgax P) a = (dual x :: l1) -> projT2 (pgax P) b = (l2 ++ x :: l3) ->
     exists c, projT2 (pgax P) c = l2 ++ l1 ++ l3) ->
  forall A l1 l2 l3,
  ll P (dual A :: l1) -> ll P (l2 ++ A :: l3) -> ll P (l2 ++ l1 ++ l3).

Theorem cut_elim :
  forall P,
  forall P_gax_atomic : forall a, Forall atomic (projT2 (pgax P) a),
  (forall a l, PCperm_Type (pperm P) (projT2 (pgax P) a) l -> exists b, l = projT2 (pgax P) b) ->
  (forall a b x l1 l2 l3, projT2 (pgax P) a = (dual x :: l1) -> projT2 (pgax P) b = (l2 ++ x :: l3) ->
     exists c, projT2 (pgax P) c = l2 ++ l1 ++ l3) ->
  forall A l1 l2 l3,
  ll P (dual A :: l1) -> ll P (l2 ++ A :: l3) -> ll P (l2 ++ l1 ++ l3).
Proof.
intros P.
case_eq (pperm P).
- intros Hperm Hgax_at Hgax_ex Hgax_cut A l1 l2 l3 pi1 pi2.
  eapply ex_r in pi2 ; [ | rewrite Hperm ; apply Permutation_Type_app_swap ].
  rewrite <- app_comm_cons in pi2.
  eapply ex_r ; [ | rewrite Hperm ; apply Permutation_Type_app_rot ].
  rewrite app_assoc.
  refine (cut_elim_perm _ _ _ _ _ A _ _ _ _) ; try assumption.
  rewrite Hperm ; assumption.
- intros Hperm Hgax_at Hgax_ex Hgax_cut A l1 l2 l3 pi1 pi2.
  refine (cut_elim_cyclic _ _ _ _ _ A _ _ _ _ _) ; try assumption.
  rewrite Hperm ; assumption.
Qed.


