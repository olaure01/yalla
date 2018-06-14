(* bbb library for yalla *)

(* output in Type *)


(** * Study of Linear Logic enriched with [bot = oc bot] *)

Require Import Arith.
Require Import Psatz.

Require Import List_more.
Require Import Permutation_Type_more.
Require Import Permutation_Type_solve.
Require Import genperm_Type.

Require Import ll_fragments.

(** ** The system [ll_bbb] *)
(** It contains [ll_mix2] but allows [mix0] as well above one side of each [mix2] rule. *)

Inductive ll_bbb : list formula -> Type :=
| ax_bbb_r : forall X, ll_bbb (covar X :: var X :: nil)
| ex_bbb_r : forall l1 l2, ll_bbb l1 -> Permutation_Type l1 l2 -> ll_bbb l2
| mix2_bbb_r : forall l1 l2, ll_bbb l1 -> ll_mix02 l2 -> ll_bbb (l2 ++ l1)
| one_bbb_r : ll_bbb (one :: nil)
| bot_bbb_r : forall l, ll_bbb l -> ll_bbb (bot :: l)
| tens_bbb_r : forall A B l1 l2,
                ll_bbb (A :: l1) -> ll_bbb (B :: l2) -> ll_bbb (tens A B :: l2 ++ l1)
| parr_bbb_r : forall A B l, ll_bbb (A :: B :: l) -> ll_bbb (parr A B :: l)
| top_bbb_r : forall l, ll_bbb (top :: l)
| plus_bbb_r1 : forall A B l, ll_bbb (A :: l) -> ll_bbb (aplus A B :: l)
| plus_bbb_r2 : forall A B l, ll_bbb (A :: l) -> ll_bbb (aplus B A :: l)
| with_bbb_r : forall A B l, ll_bbb (A :: l) -> ll_bbb (B :: l) ->
                                   ll_bbb (awith A B :: l)
| oc_bbb_r : forall A l, ll_bbb (A :: map wn l) -> ll_bbb (oc A :: map wn l)
| de_bbb_r : forall A l, ll_bbb (A :: l) -> ll_bbb (wn A :: l)
| wk_bbb_r : forall A l, ll_bbb l -> ll_bbb (wn A :: l)
| co_bbb_r : forall A l, ll_bbb (wn A :: wn A :: l) -> ll_bbb (wn A :: l).

(*
Ltac inversion_ll_bbb H X l Hl Hr HP :=
  match type of H with 
  | ll_bbb _ _ => inversion H as [ X
                             | l ? ? Hl HP
                             | ? ? ? ? Hl Hr
                             | 
                             | ? ? Hl
                             | ? ? ? ? ? ? Hl Hr
                             | ? ? ? ? Hl
                             | l
                             | ? ? ? ? Hl
                             | ? ? ? ? Hl
                             | ? ? ? ? ? Hl Hr
                             | ? ? ? Hl
                             | ? ? ? Hl
                             | ? ? ? Hl
                             | ? ? ? Hl] ;
               subst
  end.
*)

(** Generalized weakening for lists *)
Lemma wk_list_bbb_r : forall l l', ll_bbb l' ->
  ll_bbb (map wn l ++ l').
Proof with myeeasy ; try perm_Type_solve.
induction l ; intros...
apply wk_bbb_r.
apply IHl...
Qed.

(** Generalized contraction for lists *)
Lemma co_list_bbb_r : forall l l',
ll_bbb (map wn l ++ map wn l ++ l') -> ll_bbb (map wn l ++ l').
Proof with myeeasy ; try perm_Type_solve.
induction l ; intros...
apply (ex_bbb_r (map wn l ++ wn a :: l'))...
apply IHl.
apply (ex_bbb_r (wn a :: map wn l ++ map wn l ++ l'))...
apply co_bbb_r.
eapply ex_bbb_r...
Qed.

(** [ll_mix2] is contained in [ll_bbb] *)
Lemma mix2_to_bbb : forall l, ll_mix2 l -> ll_bbb l.
Proof with myeeasy.
intros l H.
induction H ; try now constructor.
- apply (ex_bbb_r l1)...
- inversion f.
- apply mix2_bbb_r...
  eapply stronger_pfrag...
  nsplit 5...
  intros a ; exists a...
- apply co_bbb_r.
  eapply ex_bbb_r ; [ apply IHll | ].
  perm_Type_solve.
- inversion a.
Qed.

(** [ll_bbb] is contained in [ll_mix02] *)
Lemma bbb_to_mix02 : forall l, ll_bbb l -> ll_mix02 l.
Proof with myeasy.
intros l H.
induction H ; try now constructor.
- apply (ex_r _ l1)...
- change l with (map wn nil ++ l).
  apply co_r...
Qed.




(** ** Cut elimination for [ll_bbb] *)

(* TODO *)
Axiom cut_bbb_r : forall A l1 l2,
  ll_bbb (dual A :: l1)-> ll_bbb (A :: l2) -> ll_bbb (l2 ++ l1).
(* TODO
Lemma key_case_oc_subst_bbb : forall A l lwn l1 l1' s s1,
  (forall l2 l3 s2, ll_bbb (l2 ++ (dual A) :: l3) s2 ->
     exists s' : nat, ll_bbb (l2 ++ (map wn l) ++ l3) s') ->
  ll_bbb (A :: map wn l) s -> ll_bbb l1' s1 ->
    Forall (fun x => x = wn (dual A)) lwn -> Permutation l1' (lwn ++ l1) -> 
      exists s', ll_bbb (map wn l ++ l1) s'.
Proof with myeeasy ; try perm_solve.
intros A l lwn l1 l1' s s1 IHA Hbox H.
revert l1 lwn.
induction H ; intros l' lwn Hlwn HP.
- (* ax *)
  apply Permutation_length_2_inv in HP.
  destruct HP as [HP | HP] ; destruct lwn ; inversion HP ; subst.
  + simpl in HP ; subst.
    clear.
    induction l.
    * eexists.
      apply ax_bbb_r.
    * destruct IHl as [s' IHl].
      eexists.
      eapply wk_bbb_r...
  + apply Forall_inv in Hlwn.
    inversion Hlwn.
  + simpl in HP ; subst.
    clear.
    induction l.
    * simpl.
      eexists.
      eapply ex_bbb_r ; [ apply ax_bbb_r | ]...
    * destruct IHl as [s' IHl].
      eexists.
      eapply wk_bbb_r...
  + apply Forall_inv in Hlwn.
    inversion Hlwn.
- (* ex *)
  eapply IHll_bbb in Hlwn...
- (* mix2 *)
  apply Permutation_app_app_inv in HP.
  destruct HP as (lwn' & lwn'' & l'' & l''' & H2 & H1 & Hwn & H').
  assert (Forall (fun x : formula => x = wn (dual A)) (lwn' ++ lwn''))
    as HP3 by (apply (Permutation_Forall _ lwn) ; myeasy).
  apply Forall_app_inv in HP3.
  destruct HP3 as [HP3 HP4].
  apply IHll_bbb in H1...
  destruct H1 as [s'1 H1].
  apply bbb_to_mix02 in Hbox.
  destruct lwn'.
  + eexists.
    eapply ex_r in H0 ; [ | apply H2 ].
    apply (ex_bbb_r (l'' ++ (map wn l ++ l''')))...
    apply mix2_bbb_r...
  + revert s2 l2 H0 H2 HP3 ; clear - Hbox H1 H' ; induction lwn' ;
      intros s2 l2 H0 H2 HP3.
    * inversion HP3 ; subst.
      apply (ex_r _ _ _ _ H0) in H2.
      change (wn (dual A)) with (dual (oc A)) in H2.
      eapply oc_r in Hbox.
      eapply (cut_mix02_r _ _ _ _ _ H2) in Hbox.
      destruct Hbox as [s0 Hbox].
      eapply co_list_bbb_r.
      eapply (ex_bbb_r ((map wn l ++ l'') ++ map wn l ++ l'''))...
      apply mix2_bbb_r...
    * inversion HP3.
      inversion H5 ; subst.
      apply (ex_r _ _ _ _ H0) in H2.
      rewrite <- (app_nil_l (_ :: lwn')) in H2.
      change nil with (map wn nil) in H2.
      rewrite <- ? app_comm_cons in H2.
      rewrite <- ? app_assoc in H2.
      rewrite <- app_comm_cons in H2.
      apply co_r in H2.
      eapply IHlwn' ; [ apply H2 | | ]...
- (* one *)
  apply Permutation_length_1_inv in HP.
  destruct lwn ; inversion HP ; subst.
  + simpl in HP ; subst.
    eapply wk_list_bbb_r.
    eapply one_bbb_r.
  + apply Forall_inv in Hlwn.
    inversion Hlwn.
- (* bot *)
  assert (Heq := HP).
  symmetry in Heq.
  apply Permutation_vs_cons_inv in Heq.
  destruct Heq as (l2 & l3 & Heq).
  symmetry in Heq.
  dichot_elt_app_exec Heq ; subst.
  + apply Forall_app_inv in Hlwn.
    destruct Hlwn as [_ Hlwn].
    apply Forall_inv in Hlwn.
    inversion Hlwn.
  + rewrite app_assoc in HP.
    apply Permutation_cons_app_inv in HP.
    rewrite <- app_assoc in HP.
    apply IHll_bbb in HP...
    destruct HP as [s' HP].
    eexists.
    eapply ex_bbb_r ; [ apply bot_bbb_r | ]...
- (* tens *)
  assert (Heq := HP).
  symmetry in Heq.
  apply Permutation_vs_cons_inv in Heq.
  destruct Heq as (l1' & l1'' & Heq).
  symmetry in Heq.
  dichot_elt_app_exec Heq ; subst.
  + apply Forall_app_inv in Hlwn.
    destruct Hlwn as [_ Hlwn].
    apply Forall_inv in Hlwn.
    inversion Hlwn.
  + rewrite app_assoc in HP.
    apply Permutation_cons_app_inv in HP.
    rewrite <- app_assoc in HP.
    apply Permutation_app_app_inv in HP.
    destruct HP as (lwn' & lwn'' & l'' & l''' & H2 & H1 & Hwn & H').
    assert (Forall (fun x : formula => x = wn (dual A)) (lwn' ++ lwn''))
      as HP3 by (apply (Permutation_Forall _ lwn) ; myeasy).
    apply Forall_app_inv in HP3.
    destruct HP3 as [HP3 HP4].
    apply (Permutation_cons_app _ _ A0) in H1.
    apply IHll_bbb1 in H1...
    destruct H1 as [s'1 H1].
    apply (Permutation_cons_app _ _ B) in H2.
    apply IHll_bbb2 in H2...
    destruct H2 as [s'2 H2].
    eapply co_list_bbb_r.
    apply (ex_bbb_r (tens A0 B :: (map wn l ++ l'') ++ map wn l ++ l'''))...
    * eapply tens_bbb_r...
      -- apply (ex_bbb_r (map wn l ++ A0 :: l'''))...
      -- apply (ex_bbb_r (map wn l ++ B :: l''))...
    * (* Permutation: difficult case but should be automatically solvable *)
      cons2app ; perm_rot...
- (* parr *)
  assert (Heq := HP).
  symmetry in Heq.
  apply Permutation_vs_cons_inv in Heq.
  destruct Heq as (l2 & l3 & Heq).
  symmetry in Heq.
  dichot_elt_app_exec Heq ; subst.
  + apply Forall_app_inv in Hlwn.
    destruct Hlwn as [_ Hlwn].
    apply Forall_inv in Hlwn.
    inversion Hlwn.
  + rewrite app_assoc in HP.
    apply Permutation_cons_app_inv in HP.
    rewrite <- app_assoc in HP.
    assert (HP2 := HP).
    apply (Permutation_cons_app _ _ B) in HP.
    apply (Permutation_cons_app _ _ A0) in HP.
    apply IHll_bbb in HP...
    destruct HP as [s' HP].
    eexists.
    eapply (ex_bbb_r (parr A0 B :: map wn l ++ l4 ++ l3))...
    eapply parr_bbb_r.
    eapply (ex_bbb_r (map wn l ++ A0 :: B :: l4 ++ l3))...
- (* top *)
  assert (Heq := HP).
  symmetry in Heq.
  apply Permutation_vs_cons_inv in Heq.
  destruct Heq as (l2 & l3 & Heq).
  symmetry in Heq.
  dichot_elt_app_exec Heq ; subst.
  + apply Forall_app_inv in Hlwn.
    destruct Hlwn as [_ Hlwn].
    apply Forall_inv in Hlwn.
    inversion Hlwn.
  + eexists.
    eapply (ex_bbb_r (top :: map wn l ++ l4 ++ l3))...
    eapply top_bbb_r.
- (* plus_1 *)
  assert (Heq := HP).
  symmetry in Heq.
  apply Permutation_vs_cons_inv in Heq.
  destruct Heq as (l2 & l3 & Heq).
  symmetry in Heq.
  dichot_elt_app_exec Heq ; subst.
  + apply Forall_app_inv in Hlwn.
    destruct Hlwn as [_ Hlwn].
    apply Forall_inv in Hlwn.
    inversion Hlwn.
  + rewrite app_assoc in HP.
    apply Permutation_cons_app_inv in HP.
    rewrite <- app_assoc in HP.
    assert (HP2 := HP).
    apply (Permutation_cons_app _ _ A0) in HP.
    apply IHll_bbb in HP...
    destruct HP as [s' HP].
    eexists.
    eapply (ex_bbb_r (aplus A0 B :: map wn l ++ l4 ++ l3))...
    eapply plus_bbb_r1.
    eapply (ex_bbb_r (map wn l ++ A0 :: l4 ++ l3))...
- (* plus_2 *)
  assert (Heq := HP).
  symmetry in Heq.
  apply Permutation_vs_cons_inv in Heq.
  destruct Heq as (l2 & l3 & Heq).
  symmetry in Heq.
  dichot_elt_app_exec Heq ; subst.
  + apply Forall_app_inv in Hlwn.
    destruct Hlwn as [_ Hlwn].
    apply Forall_inv in Hlwn.
    inversion Hlwn.
  + rewrite app_assoc in HP.
    apply Permutation_cons_app_inv in HP.
    rewrite <- app_assoc in HP.
    assert (HP2 := HP).
    apply (Permutation_cons_app _ _ A0) in HP.
    apply IHll_bbb in HP...
    destruct HP as [s' HP].
    eexists.
    eapply (ex_bbb_r (aplus B A0 :: map wn l ++ l4 ++ l3))...
    eapply plus_bbb_r2.
    eapply (ex_bbb_r (map wn l ++ A0 :: l4 ++ l3))...
- (* with *)
  assert (Heq := HP).
  symmetry in Heq.
  apply Permutation_vs_cons_inv in Heq.
  destruct Heq as (l2 & l3 & Heq).
  symmetry in Heq.
  dichot_elt_app_exec Heq ; subst.
  + apply Forall_app_inv in Hlwn.
    destruct Hlwn as [_ Hlwn].
    apply Forall_inv in Hlwn.
    inversion Hlwn.
  + rewrite app_assoc in HP.
    apply Permutation_cons_app_inv in HP.
    rewrite <- app_assoc in HP.
    assert (HP1 := HP).
    assert (HP2 := HP).
    apply (Permutation_cons_app _ _ A0) in HP.
    apply IHll_bbb1 in HP...
    destruct HP as [s1' HP].
    apply (Permutation_cons_app _ _ B) in HP1.
    apply IHll_bbb2 in HP1...
    destruct HP1 as [s2' HP1].
    eexists.
    eapply (ex_bbb_r (awith A0 B :: map wn l ++ l4 ++ l3))...
    eapply with_bbb_r.
    * eapply (ex_bbb_r (map wn l ++ A0 :: l4 ++ l3))...
    * eapply (ex_bbb_r (map wn l ++ B :: l4 ++ l3))...
- (* oc *)
  assert (Heq := HP).
  symmetry in Heq.
  apply Permutation_vs_cons_inv in Heq.
  destruct Heq as (l2 & l3 & Heq).
  symmetry in Heq.
  dichot_elt_app_exec Heq ; subst.
  + apply Forall_app_inv in Hlwn.
    destruct Hlwn as [_ Hlwn].
    apply Forall_inv in Hlwn.
    inversion Hlwn.
  + rewrite app_assoc in HP.
    apply Permutation_cons_app_inv in HP.
    rewrite <- app_assoc in HP.
    assert (HP2 := HP).
    apply (Permutation_cons_app _ _ A0) in HP.
    apply IHll_bbb in HP...
    destruct HP as [s' HP].
    apply (Permutation_Forall (fun x => exists y, x = wn y)) in HP2.
    apply Forall_app_inv in HP2.
    * destruct HP2 as [_ HP2].
      assert (exists l', l4 ++ l3 = map wn l').
      { revert HP2.
        clear.
        revert l3.
        induction l4 ; intros.
        - revert HP2.
          simpl.
          induction l3 ; intros.
          + exists (@nil formula)...
          + inversion HP2 ; subst.
            apply IHl3 in H2.
            destruct H1 as [b H1] ; subst.
            destruct H2 as [l' H2] ; subst.
            exists (b::l')...
        - inversion HP2 ; subst.
          apply IHl4 in H2.
          destruct H1 as [b H1] ; subst.
          destruct H2 as [l' H2] ; subst.
          rewrite <- app_comm_cons.
          rewrite H2.
          exists (b::l')... }
      destruct H0 as [l' H0].
      eexists.
      eapply (ex_bbb_r (oc A0 :: map wn l ++ l4 ++ l3))...
      rewrite_all H0.
      rewrite <- map_app.
      eapply oc_bbb_r...
      rewrite map_app.
      eapply (ex_bbb_r (map wn l ++ A0 :: map wn l'))...
    * clear.
      induction l0 ; constructor...
      exists a...
- (* de *)
  assert (Heq := HP).
  symmetry in Heq.
  apply Permutation_vs_cons_inv in Heq.
  destruct Heq as (l2 & l3 & Heq).
  symmetry in Heq.
  dichot_elt_app_exec Heq ; subst.
  + apply Forall_app_inv in Hlwn.
    destruct Hlwn as [Hlwn1 Hlwn2].
    inversion Hlwn2 ; subst.
    inversion H2 ; subst.
    rewrite <- app_assoc in HP.
    rewrite <- app_comm_cons in HP.
    apply Permutation_cons_app_inv in HP.
    rewrite app_assoc in HP.
    apply (Permutation_cons_app _ _ (dual A)) in HP.
    apply IHll_bbb in HP.
    * destruct HP as [s' HP].
      apply IHA in HP...
      destruct HP as [s'' HP].
      eapply co_list_bbb_r...
    * apply Forall_app...
  + rewrite app_assoc in HP.
    apply Permutation_cons_app_inv in HP.
    rewrite <- app_assoc in HP.
    assert (HP2 := HP).
    apply (Permutation_cons_app _ _ A0) in HP.
    apply IHll_bbb in HP...
    destruct HP as [s' HP].
    eexists.
    eapply (ex_bbb_r (wn A0 :: map wn l ++ l4 ++ l3))...
    eapply de_bbb_r.
    eapply (ex_bbb_r (map wn l ++ A0 :: l4 ++ l3))...
- (* wk *)
  assert (Heq := HP).
  symmetry in Heq.
  apply Permutation_vs_cons_inv in Heq.
  destruct Heq as (l2 & l3 & Heq).
  symmetry in Heq.
  dichot_elt_app_exec Heq ; subst.
  + apply Forall_app_inv in Hlwn.
    destruct Hlwn as [Hlwn1 Hlwn2].
    inversion Hlwn2 ; subst.
    inversion H2 ; subst.
    rewrite <- app_assoc in HP.
    rewrite <- app_comm_cons in HP.
    apply Permutation_cons_app_inv in HP.
    rewrite app_assoc in HP.
    apply IHll_bbb in HP...
    apply Forall_app...
  + rewrite app_assoc in HP.
    apply Permutation_cons_app_inv in HP.
    rewrite <- app_assoc in HP.
    assert (HP2 := HP).
    apply IHll_bbb in HP...
    destruct HP as [s' HP].
    eexists.
    eapply (ex_bbb_r (wn A0 :: map wn l ++ l4 ++ l3))...
    eapply wk_bbb_r...
- (* co *)
  assert (Heq := HP).
  symmetry in Heq.
  apply Permutation_vs_cons_inv in Heq.
  destruct Heq as (l2 & l3 & Heq).
  symmetry in Heq.
  dichot_elt_app_exec Heq ; subst.
  + apply Forall_app_inv in Hlwn.
    destruct Hlwn as [Hlwn1 Hlwn2].
    inversion Hlwn2 ; subst.
    inversion H2 ; subst.
    rewrite <- app_assoc in HP.
    rewrite <- app_comm_cons in HP.
    apply Permutation_cons_app_inv in HP.
    rewrite app_assoc in HP.
    eapply (@Permutation_cons _ _ (wn (dual A)) eq_refl) in HP.
    eapply (@Permutation_cons _ _ (wn (dual A)) eq_refl) in HP.
    rewrite ?app_comm_cons in HP.
    apply IHll_bbb in HP...
    constructor...
    constructor...
    apply (Forall_app _ _ _ Hlwn1 H3).
  + eapply (Permutation_cons_app _ _ (wn A0)) in HP.
    apply IHll_bbb in HP...
    destruct HP as [s' HP].
    eexists.
    eapply (ex_bbb_r (wn A0 :: map wn l ++ l4 ++ l3))...
    eapply co_bbb_r...
    eapply ex_bbb_r...
Qed.

Lemma key_case_oc_co_bbb : forall A l l1 s s1,
  (forall l2 l3 s2, ll_bbb (l2 ++ (dual A) :: l3) s2 ->
     exists s' : nat, ll_bbb (l2 ++ (map wn l) ++ l3) s') ->
  ll_bbb (A :: map wn l) s -> ll_bbb (wn (dual A) :: wn (dual A) :: l1) s1 ->
     exists s', ll_bbb (map wn l ++ l1) s'.
Proof with myeeasy.
intros.
change (wn (dual A) :: wn (dual A) :: l1)
  with ((wn (dual A) :: wn (dual A) :: nil) ++ l1) in H1.
eapply key_case_oc_subst_bbb...
constructor...
constructor...
constructor...
Qed.

Theorem cut_elim_bbb : forall c s A l1 l2 l3 s1 s2, 
  ll_bbb (dual A :: l1) s1 -> ll_bbb (l2 ++ A :: l3) s2 ->
    s = s1 + s2 -> fsize A <= c -> exists s',
    ll_bbb (l2 ++ l1 ++ l3) s'.
Proof with myeeasy ; try fsize_auto ; try perm_solve ; try PCperm_solve.
induction c using (well_founded_induction lt_wf).
assert (
  forall A l1 l2 l3 s1 s2,
    ll_bbb (dual A :: l1) s1 ->
    ll_bbb (l2 ++ A :: l3) s2 ->
    fsize A < c -> exists s' : nat, ll_bbb (l2 ++ l1 ++ l3) s'
  ) as IHcut by (intros ; eapply H ; myeeasy).
clear H.
induction s using (well_founded_induction lt_wf).
assert (
  forall A l1 l2 l3 s1 s2,
    ll_bbb (dual A :: l1) s1 ->
    ll_bbb (l2 ++ A :: l3) s2 ->
    s1 + s2 < s -> fsize A <= c -> exists s' : nat, ll_bbb (l2 ++ l1 ++ l3) s'
  ) as IHsize by (intros ; eapply H ; myeeasy).
clear H.
intros A l1 l2 l3 s1 s2 Hl Hr Heqs Hc.
rewrite_all Heqs ; clear s Heqs.
inversion_ll_bbb Hr X l' Hl2 Hr2 HP2.
- (* ax *)
  destruct l2 ; inversion H.
  + destruct l3 ; inversion H2 ; subst.
    eexists.
    eapply ex_bbb_r in Hl...
  + destruct l2 ; inversion H2 ; subst.
    * eexists.
      eapply ex_bbb_r in Hl...
    * destruct l2 ; inversion H4.
- (* ex *)
  assert (Heq := HP2).
  apply Permutation_vs_elt_inv in Heq.
  destruct Heq as (l2' & l3' & Heq).
  subst.
  eapply IHsize in Hl2...
  destruct Hl2 as [s' Hl2].
  eexists.
  eapply ex_bbb_r in Hl2...
- (* mix2 *)
  dichot_elt_app_exec H ; subst.
  + apply bbb_to_mix02 in Hl.
    eapply ex_r in Hr2 ;
      [ | unfold PCperm ; simpl ; symmetry ;
          apply Permutation_cons_app ; reflexivity ].
    eapply cut_mix02_r in Hr2...
    destruct Hr2 as [s' Hr2].
    eexists.
    rewrite ? app_assoc.
    apply mix2_bbb_r...
    eapply ex_r...
  + eapply IHsize in Hl2...
    destruct Hl2 as [s' Hl2].
    eexists.
    rewrite <- app_assoc.
    apply mix2_bbb_r...
- (* one *)
  destruct l2 ; inversion H ; subst.
  + rewrite app_nil_r.
    inversion_ll_bbb Hl X l' Hl1 Hr1 HP1.
    * assert (Heq := HP1).
      apply Permutation_vs_cons_inv in Heq.
        destruct Heq as (l2' & l3' & Heq).
        subst.
      eapply IHsize in Hl1...
      destruct Hl1 as [s' Hl1].
      eexists.
      apply (ex_bbb_r (l2' ++ l3'))...
    * rewrite <- (app_nil_l (_ :: l1)) in H0.
      dichot_elt_app_exec H0 ; subst.
      -- apply bbb_to_mix02 in Hr.
         eapply cut_mix02_r in Hr...
         destruct Hr as [s' Hr].
         eexists.
         simpl.
         apply mix2_bbb_r...
      -- eapply IHsize in Hl1...
         destruct Hl1 as [s' Hl1].
         apply eq_sym in H1.
         apply app_eq_nil in H1.
         destruct H1 ; subst.
         eexists...
    * eexists...
  + destruct l2 ; inversion H2.
- (* bot *)
  destruct l2 ; inversion H ; subst.
  + inversion_ll_bbb Hl X l' Hl1 Hr1 HP1.
    * assert (Heq := HP1).
      apply Permutation_vs_cons_inv in Heq.
        destruct Heq as (l2' & l3' & Heq).
        subst.
      eapply IHsize in Hl1...
      destruct Hl1 as [s' Hl1].
      eexists.
      apply (ex_bbb_r (l2' ++ l3 ++ l3'))...
    * rewrite <- (app_nil_l (_ :: l1)) in H0.
      dichot_elt_app_exec H0 ; subst.
      -- apply bbb_to_mix02 in Hr.
         eapply cut_mix02_r in Hr...
         destruct Hr as [s' Hr].
         eexists.
         simpl.
         apply (ex_bbb_r ((l ++ l3) ++ l0))...
         apply mix2_bbb_r...
         eapply ex_r...
      -- eapply IHsize in Hl1...
         destruct Hl1 as [s' Hl1].
         apply eq_sym in H1.
         apply app_eq_nil in H1.
         destruct H1 ; subst.
         eexists...
         apply (ex_bbb_r (l3 ++ l1))...
    * eexists...
  + eapply IHsize in Hl2...
    destruct Hl2 as [s' Hl2].
    eexists.
    eapply bot_bbb_r...
- (* tens *)
  destruct l2 ; inversion H ; subst.
  + inversion_ll_bbb Hl X l' Hl1 Hr1 HP1.
    * assert (Heq := HP1).
      apply Permutation_vs_cons_inv in Heq.
        destruct Heq as (l2' & l3' & Heq).
        subst.
      rewrite <- (bidual (tens A0 B)) in Hr.
      eapply IHsize in Hl1...
      destruct Hl1 as [s' Hl1].
      eexists.
      apply (ex_bbb_r (l2' ++ (l4 ++ l0) ++ l3'))...
    * simpl in Hr.
      rewrite <- (bidual (tens A0 B)) in Hr.
      rewrite <- (app_nil_l (_ :: l1)) in H0.
      dichot_elt_app_exec H0 ; subst.
      -- change (parr (dual B) (dual A0)) with (dual (tens A0 B)) in Hr1.
         apply bbb_to_mix02 in Hr.
         eapply cut_mix02_r in Hr ; rewrite ? bidual...
         destruct Hr as [s' Hr].
         eexists.
         simpl.
         apply (ex_bbb_r (((l4 ++ l0) ++ l)++l2))...
         apply mix2_bbb_r...
      -- change (parr (dual B) (dual A0)) with (dual (tens A0 B)) in Hl1.
         eapply IHsize in Hl1...
         destruct Hl1 as [s' Hl1].
         apply eq_sym in H1.
         apply app_eq_nil in H1.
         destruct H1 ; subst.
         eexists...
         apply (ex_bbb_r ((l4 ++ l0) ++ l1))...
    * rewrite <- (bidual B) in Hr2.
      rewrite <- (app_nil_l (_ :: _ :: l1)) in Hl1.
      eapply (IHcut _ _ nil (dual A0 :: l1)) in Hr2...
      destruct Hr2 as [s' Hr2].
      rewrite <- (bidual A0) in Hl2.
      eapply IHcut in Hl2...
      destruct Hl2 as [s'' Hl2].
      eexists.
      eapply (ex_bbb_r _ _ _ Hl2)...
  + dichot_elt_app_exec H2 ; subst.
    * rewrite app_comm_cons in Hr2.
      eapply IHsize in Hr2...
      destruct Hr2 as [s' Hr2].
      eexists.
      rewrite <- app_comm_cons.
      rewrite ? app_assoc.
      eapply tens_bbb_r...
      rewrite <- app_assoc...
    * rewrite app_comm_cons in Hl2.
      eapply IHsize in Hl2...
      destruct Hl2 as [s' Hl2].
      eexists.
      rewrite app_comm_cons.
      rewrite <- app_assoc.
      apply tens_bbb_r...
- (* parr *)
  destruct l2 ; inversion H ; subst.
  + inversion_ll_bbb Hl X l' Hl1 Hr1 HP1.
    * assert (Heq := HP1).
      apply Permutation_vs_cons_inv in Heq.
        destruct Heq as (l2' & l3' & Heq).
        subst.
      rewrite <- (bidual (parr A0 B)) in Hr.
      eapply IHsize in Hl1...
      destruct Hl1 as [s' Hl1].
      eexists.
      apply (ex_bbb_r (l2' ++ l3 ++ l3'))...
    * simpl in Hr.
      rewrite <- (bidual (parr A0 B)) in Hr.
      rewrite <- (app_nil_l (_ :: l1)) in H0.
      dichot_elt_app_exec H0 ; subst.
      -- change (tens (dual B) (dual A0)) with (dual (parr A0 B)) in Hr1.
         apply bbb_to_mix02 in Hr.
         eapply cut_mix02_r in Hr ; rewrite ? bidual...
         destruct Hr as [s' Hr].
         eexists.
         simpl.
         apply (ex_bbb_r ((l3 ++ l) ++ l0))...
         apply mix2_bbb_r...
      -- change (tens (dual B) (dual A0)) with (dual (parr A0 B)) in Hl1.
         eapply IHsize in Hl1...
         destruct Hl1 as [s' Hl1].
         apply eq_sym in H1.
         apply app_eq_nil in H1.
         destruct H1 ; subst.
         eexists...
         apply (ex_bbb_r (l3 ++ l1))...
    * (* key case parr/tens bis *)
      change (A0 :: B :: l3) with ((A0 :: nil) ++ B :: l3) in Hl2.
      eapply IHcut in Hl2...
      destruct Hl2 as [s' Hl2].
      simpl in Hl2.
      rewrite <- (app_nil_l (_ :: l0 ++ l3)) in Hl2.
      eapply IHcut in Hl2...
      destruct Hl2 as [s'' Hl2].
      rewrite <- app_assoc.
      eexists...
  + rewrite ? app_comm_cons in Hl2.
    eapply IHsize in Hl2...
    destruct Hl2 as [s' Hl2].
    eexists.
    rewrite <- app_comm_cons.
    eapply parr_bbb_r...
- (* top *)
  destruct l2 ; inversion H ; subst.
  + inversion_ll_bbb Hl X l' Hl1 Hr1 HP1.
    * assert (Heq := HP1).
      apply Permutation_vs_cons_inv in Heq.
        destruct Heq as (l2' & l3' & Heq).
        subst.
      eapply IHsize in Hl1...
      destruct Hl1 as [s' Hl1].
      eexists.
      apply (ex_bbb_r (l2' ++ l3 ++ l3'))...
    * rewrite <- (app_nil_l (_ :: l1)) in H0.
      dichot_elt_app_exec H0 ; subst.
      -- apply bbb_to_mix02 in Hr.
         eapply cut_mix02_r in Hr...
         destruct Hr as [s' Hr].
         eexists.
         simpl.
         apply (ex_bbb_r ((l ++ l3) ++ l0))...
         apply mix2_bbb_r...
         eapply ex_r...
      -- eapply IHsize in Hl1...
         destruct Hl1 as [s' Hl1].
         apply eq_sym in H1.
         apply app_eq_nil in H1.
         destruct H1 ; subst.
         eexists...
         apply (ex_bbb_r (l3 ++ l1))...
  + eexists.
    rewrite <- app_comm_cons.
    eapply top_bbb_r.
- (* plus_1 *)
  destruct l2 ; inversion H ; subst.
  + inversion_ll_bbb Hl X l' Hl1 Hr1 HP1.
    * assert (Heq := HP1).
      apply Permutation_vs_cons_inv in Heq.
        destruct Heq as (l2' & l3' & Heq).
        subst.
      rewrite <- (bidual (aplus A0 B)) in Hr.
      eapply IHsize in Hl1...
      destruct Hl1 as [s' Hl1].
      eexists.
      apply (ex_bbb_r (l2' ++ l3 ++ l3'))...
    * rewrite <- (app_nil_l (_ :: l1)) in H0.
      dichot_elt_app_exec H0 ; subst.
      -- simpl in Hr.
         rewrite <- (bidual (aplus A0 B)) in Hr.
         change (awith (dual A0) (dual B)) with (dual (aplus A0 B)) in Hr1.
         apply bbb_to_mix02 in Hr.
         eapply cut_mix02_r in Hr ; rewrite ? bidual...
         destruct Hr as [s' Hr].
         eexists.
         simpl.
         apply (ex_bbb_r ((l3 ++ l) ++ l0))...
         apply mix2_bbb_r...
      -- simpl in Hr.
         rewrite <- (bidual (aplus A0 B)) in Hr.
         change (awith (dual A0) (dual B)) with (dual (aplus A0 B)) in Hl1.
         eapply IHsize in Hl1...
         destruct Hl1 as [s' Hl1].
         apply eq_sym in H1.
         apply app_eq_nil in H1.
         destruct H1 ; subst.
         eexists...
         apply (ex_bbb_r (l3 ++ l1))...
    * eapply IHcut in Hl1...
  + rewrite app_comm_cons in Hl2.
    eapply IHsize in Hl2...
    destruct Hl2 as [s' Hl2].
    eexists.
    rewrite <- app_comm_cons.
    eapply plus_bbb_r1...
- (* plus_2 *)
  destruct l2 ; inversion H ; subst.
  + inversion_ll_bbb Hl X l' Hl1 Hr1 HP1.
    * assert (Heq := HP1).
      apply Permutation_vs_cons_inv in Heq.
        destruct Heq as (l2' & l3' & Heq).
        subst.
      rewrite <- (bidual (aplus B A0)) in Hr.
      eapply IHsize in Hl1...
      destruct Hl1 as [s' Hl1].
      eexists.
      apply (ex_bbb_r (l2' ++ l3 ++ l3'))...
    * rewrite <- (app_nil_l (_ :: l1)) in H0.
      dichot_elt_app_exec H0 ; subst.
      -- simpl in Hr.
         rewrite <- (bidual (aplus B A0)) in Hr.
         change (awith (dual B) (dual A0)) with (dual (aplus B A0)) in Hr1.
         apply bbb_to_mix02 in Hr.
         eapply cut_mix02_r in Hr ; rewrite ? bidual...
         destruct Hr as [s' Hr].
         eexists.
         simpl.
         apply (ex_bbb_r ((l3 ++ l) ++ l0))...
         apply mix2_bbb_r...
      -- simpl in Hr.
         rewrite <- (bidual (aplus B A0)) in Hr.
         change (awith (dual B) (dual A0)) with (dual (aplus B A0)) in Hl1.
         eapply IHsize in Hl1...
         destruct Hl1 as [s' Hl1].
         apply eq_sym in H1.
         apply app_eq_nil in H1.
         destruct H1 ; subst.
         eexists...
         apply (ex_bbb_r (l3 ++ l1))...
    * eapply IHcut in Hr1...
  + rewrite app_comm_cons in Hl2.
    eapply IHsize in Hl2...
    destruct Hl2 as [s' Hl2].
    eexists.
    rewrite <- app_comm_cons.
    eapply plus_bbb_r2...
- (* with *)
  destruct l2 ; inversion H ; subst.
  + inversion_ll_bbb Hl X l' Hl1 Hr1 HP1.
    * assert (Heq := HP1).
      apply Permutation_vs_cons_inv in Heq.
        destruct Heq as (l2' & l3' & Heq).
        subst.
      rewrite <- (bidual (awith A0 B)) in Hr.
      eapply IHsize in Hl1...
      destruct Hl1 as [s' Hl1].
      eexists.
      apply (ex_bbb_r (l2' ++ l3 ++ l3'))...
    * rewrite <- (app_nil_l (_ :: l1)) in H0.
      dichot_elt_app_exec H0 ; subst.
      -- simpl in Hr.
         rewrite <- (bidual (awith A0 B)) in Hr.
         change (aplus (dual A0) (dual B)) with (dual (awith A0 B)) in Hr1.
         apply bbb_to_mix02 in Hr.
         eapply cut_mix02_r in Hr ; rewrite ? bidual...
         destruct Hr as [s' Hr].
         eexists.
         simpl.
         apply (ex_bbb_r ((l3 ++ l) ++ l0))...
         apply mix2_bbb_r...
      -- simpl in Hr.
         rewrite <- (bidual (awith A0 B)) in Hr.
         change (aplus (dual A0) (dual B)) with (dual (awith A0 B)) in Hl1.
         eapply IHsize in Hl1...
         destruct Hl1 as [s' Hl1].
         apply eq_sym in H1.
         apply app_eq_nil in H1.
         destruct H1 ; subst.
         eexists...
         apply (ex_bbb_r (l3 ++ l1))...
    * eapply IHcut in Hl1...
    * eapply IHcut in Hl1...
  + rewrite app_comm_cons in Hl2.
    eapply IHsize in Hl2...
    destruct Hl2 as [s1' Hl2].
    rewrite app_comm_cons in Hr2.
    eapply IHsize in Hr2...
    destruct Hr2 as [s2' Hr2].
    eexists.
    rewrite <- app_comm_cons.
    eapply with_bbb_r...
- (* oc *)
  destruct l2 ; inversion H ; subst.
  + inversion_ll_bbb Hl X l' Hl1 Hr1 HP1.
    * assert (Heq := HP1).
      apply Permutation_vs_cons_inv in Heq.
        destruct Heq as (l2' & l3' & Heq).
        subst.
      rewrite <- (bidual (oc A0)) in Hr.
      eapply IHsize in Hl1...
      destruct Hl1 as [s' Hl1].
      eexists.
      eapply (ex_bbb_r (l2' ++ (map wn l) ++ l3'))...
    * rewrite <- (app_nil_l (_ :: l1)) in H0.
      dichot_elt_app_exec H0 ; subst.
      -- simpl in Hr.
         rewrite <- (bidual (oc A0)) in Hr.
         change (wn (dual A0)) with (dual (oc A0)) in Hr1.
         apply bbb_to_mix02 in Hr.
         eapply cut_mix02_r in Hr ; rewrite ? bidual...
         destruct Hr as [s' Hr].
         eexists.
         simpl.
         apply (ex_bbb_r ((map wn l ++ l3) ++ l0))...
         apply mix2_bbb_r...
      -- simpl in Hr.
         rewrite <- (bidual (oc A0)) in Hr.
         change (wn (dual A0)) with (dual (oc A0)) in Hl1.
         eapply IHsize in Hl1...
         destruct Hl1 as [s' Hl1].
         apply eq_sym in H1.
         apply app_eq_nil in H1.
         destruct H1 ; subst.
         eexists...
         eapply (ex_bbb_r ((map wn l) ++ l1))...
    * (* key case de *)
      eapply IHcut in Hl1...
    * (* key case wk *)
      clear - Hl1.
      eapply (wk_list_bbb_r l) in Hl1.
      destruct Hl1 as [s' Hl1].
      eexists.
      apply (ex_bbb_r (map wn l ++ l1))...
    * eapply key_case_oc_co_bbb in Hl1...
      destruct Hl1 as [s' Hl1].
      eexists.
      eapply ex_bbb_r...
      intros.
      rewrite <- (bidual A0) in Hl2.
      eapply IHcut...
  + assert (Heq := H2).
    apply eq_sym in Heq.
    decomp_map Heq ; subst.
    inversion_ll_bbb Hl X l' Hl1 Hr1 HP1.
    * inversion_ll_bbb Hl1 X l'' Hl1' Hr1' HP1'.
      -- (* ax *)
         apply Permutation_length_2_inv in HP1.
         destruct HP1 ; inversion H0.
      -- (* ex *)
         eapply (ex_bbb_r _ (dual (wn x) :: l1)) in Hl1'...
         eapply IHsize in Hl1'...
      -- (* mix2 *)
         assert (Heq := HP1).
         apply Permutation_vs_cons_inv in Heq.
         destruct Heq as (l' & l'' & Heq).
         apply eq_sym in Heq.
         dichot_elt_app_exec Heq ; subst.
         ++ eapply (ex_r _ _ (dual (wn x) :: l' ++ l)) in Hr1'...
            apply bbb_to_mix02 in Hr.
            eapply ex_r in Hr ; [ | 
              symmetry ; apply Permutation_cons_app ; reflexivity].
            eapply cut_mix02_r in Hr1' ; try rewrite bidual...
           destruct Hr1' as [s' Hr1'].
           eexists.
           simpl.
           eapply (ex_bbb_r
              (((l' ++ l) ++ (oc A0 :: map wn l4) ++ map wn l6) ++ l0))...
           eapply mix2_bbb_r...
         ++ eapply (ex_bbb_r _ (dual (wn x) :: l'' ++ l3)) in Hl1'...
           eapply IHsize in Hl1'...
           destruct Hl1' as [s' Hl1'].
           eexists.
           eapply (ex_bbb_r
              (l2 ++ ((oc A0 :: map wn l4) ++ (l'' ++ l3) ++ map wn l6)))...
           eapply mix2_bbb_r...
      -- (* one *)
         apply Permutation_length_1_inv in HP1.
         inversion HP1.
      -- (* bot *)
         assert (Heq := HP1).
         apply Permutation_vs_cons_inv in Heq.
         destruct Heq as (l' & l'' & Heq).
         apply eq_sym in Heq.
         destruct l' ; inversion Heq ; subst.
         eapply (ex_bbb_r _ (dual (wn x) :: l'' ++ l')) in Hl1'...
         eapply IHsize in Hl1'...
         destruct Hl1' as [s' Hl1'].
         eexists.
         eapply (ex_bbb_r
           (bot :: (oc A0 :: map wn l4) ++ (l'' ++ l') ++ map wn l6))...
         eapply bot_bbb_r...
      -- (* tens *)
         assert (Heq := HP1).
         apply Permutation_vs_cons_inv in Heq.
         destruct Heq as (l' & l'' & Heq).
         apply eq_sym in Heq.
         rewrite app_comm_cons in Heq.
         dichot_elt_app_exec Heq ; subst.
         ++ destruct l' ; inversion Heq0 ; subst.
            eapply (ex_bbb_r _ (dual (wn x) :: B :: l' ++ l)) in Hr1'...
            eapply IHsize in Hr1'...
            destruct Hr1' as [s' Hr1'].
            eexists.
            eapply (ex_bbb_r
              (tens A B :: ((oc A0 :: map wn l4)
                ++ (l' ++ l) ++ map wn l6) ++ l0))...
            eapply tens_bbb_r...
            eapply (ex_bbb_r
              ((oc A0 :: map wn l4) ++ (B :: l' ++ l) ++ map wn l6))...
         ++ eapply (ex_bbb_r _ (dual (wn x) :: A :: l'' ++ l3)) in Hl1'...
            eapply IHsize in Hl1'...
            destruct Hl1' as [s' Hl1'].
            eexists.
            eapply (ex_bbb_r
              (tens A B :: l2 ++ (oc A0 :: map wn l4)
                ++ (l'' ++ l3) ++ map wn l6))...
            eapply tens_bbb_r...
            eapply (ex_bbb_r
             ((oc A0 :: map wn l4) ++ (A :: l'' ++ l3) ++ map wn l6))...
      -- (* parr *)
         assert (Heq := HP1).
         apply Permutation_vs_cons_inv in Heq.
         destruct Heq as (l' & l'' & Heq).
         apply eq_sym in Heq.
         destruct l' ; inversion Heq ; subst.
         eapply (ex_bbb_r _ (dual (wn x) :: l'' ++ A :: B :: l')) in Hl1'...
         eapply IHsize in Hl1'...
         destruct Hl1' as [s' Hl1'].
         eexists.
         eapply (ex_bbb_r
           (parr A B :: (oc A0 :: map wn l4)
             ++ (l'' ++ l') ++ map wn l6))...
         eapply parr_bbb_r...
         eapply (ex_bbb_r
           ((oc A0 :: map wn l4) ++ (l'' ++ A :: B :: l') ++ map wn l6))...
      -- (* top *)
         assert (Heq := HP1).
         apply Permutation_vs_cons_inv in Heq.
         destruct Heq as (l1'' & l2'' & Heq).
         destruct l1'' ; inversion Heq ; subst.
         eexists.
         eapply (ex_bbb_r (top :: l1'' ++ l2'' ++
                            (oc A0 :: map wn l4) ++ map wn l6))...
         eapply top_bbb_r.
      -- (* plus_1 *)
         assert (Heq := HP1).
         apply Permutation_vs_cons_inv in Heq.
         destruct Heq as (l' & l'' & Heq).
         symmetry in Heq.
         destruct l' ; inversion Heq ; subst.
         eapply (ex_bbb_r _ (dual (wn x) :: l'' ++ A :: l')) in Hl1'...
         eapply IHsize in Hl1'...
         destruct Hl1' as [s' Hl1'].
         eexists.
         eapply (ex_bbb_r
           (aplus A B :: (oc A0 :: map wn l4)
           ++ (l'' ++ l') ++ map wn l6))...
         eapply plus_bbb_r1...
         eapply (ex_bbb_r
           ((oc A0 :: map wn l4) ++ (l'' ++ A :: l') ++ map wn l6))...
      -- (* plus_2 *)
         assert (Heq := HP1).
         apply Permutation_vs_cons_inv in Heq.
         destruct Heq as (l' & l'' & Heq).
         symmetry in Heq.
         destruct l' ; inversion Heq ; subst.
         eapply (ex_bbb_r _ (dual (wn x) :: l'' ++ A :: l')) in Hl1'...
         eapply IHsize in Hl1'...
         destruct Hl1' as [s' Hl1'].
         eexists.
         eapply (ex_bbb_r
           (aplus B A :: (oc A0 :: map wn l4)
           ++ (l'' ++ l') ++ map wn l6))...
         eapply plus_bbb_r2...
         eapply (ex_bbb_r
               ((oc A0 :: map wn l4) ++ (l'' ++ A :: l') ++ map wn l6))...
      -- (* with *)
         assert (Heq := HP1).
         apply Permutation_vs_cons_inv in Heq.
         destruct Heq as (l' & l'' & Heq).
         apply eq_sym in Heq.
         destruct l' ; inversion Heq ; subst.
         eapply (ex_bbb_r _ (dual (wn x) :: l'' ++ A :: l')) in Hl1'...
         eapply (ex_bbb_r _ (dual (wn x) :: l'' ++ B :: l')) in Hr1'...
         eapply IHsize in Hl1'...
         destruct Hl1' as [s' Hl1'].
         eapply IHsize in Hr1'...
         destruct Hr1' as [s'' Hr1'].
         eexists.
         eapply (ex_bbb_r
           (awith A B :: (oc A0 :: map wn l4)
           ++ (l'' ++ l') ++ map wn l6))...
         eapply with_bbb_r...
         ++ eapply (ex_bbb_r
             ((oc A0 :: map wn l4) ++ (l'' ++ A :: l') ++ map wn l6))...
         ++ eapply (ex_bbb_r
             ((oc A0 :: map wn l4) ++ (l'' ++ B :: l') ++ map wn l6))...
      -- (* oc *)
         assert (A = dual x).
         {
           symmetry in HP1.
           apply (Permutation_in (dual (wn x))) in HP1.
           - inversion HP1.
             + inversion H0...
             + exfalso.
               simpl in H0.
               revert H0 ; clear ; induction l ; intros.
               * simpl in H0...
               * inversion H0.
                 inversion H.
                 apply IHl...
           - constructor...
         }
         subst.
         change (oc (dual x)) with (dual (wn x)) in Hl1.
         eapply IHsize in Hl1...
         destruct Hl1 as [s' Hl1].
         eexists.
         eapply (ex_bbb_r ((oc A0 :: map wn l4) ++ map wn l ++ map wn l6))...
      -- (* de *) 
         assert (Heq := HP1).
         apply Permutation_vs_cons_inv in Heq.
         destruct Heq as (l' & l'' & Heq).
         symmetry in Heq.
         destruct l' ; inversion Heq ; subst.
         eapply (ex_bbb_r _ (dual (wn x) :: l'' ++ A :: l')) in Hl1'...
         eapply IHsize in Hl1'...
         destruct Hl1' as [s' Hl1'].
         eexists.
         eapply (ex_bbb_r
           (wn A :: (oc A0 :: map wn l4)
           ++ (l'' ++ l') ++ map wn l6))...
         eapply de_bbb_r...
         eapply (ex_bbb_r
           ((oc A0 :: map wn l4) ++ (l'' ++ A :: l') ++ map wn l6))...
      -- (* wk *)
         assert (Heq := HP1).
         apply Permutation_vs_cons_inv in Heq.
         destruct Heq as (l' & l'' & Heq).
         symmetry in Heq.
         destruct l' ; inversion Heq ; subst.
         eapply (ex_bbb_r _ (dual (wn x) :: l'' ++ l')) in Hl1'...
         eapply IHsize in Hl1'...
         destruct Hl1' as [s' Hl1'].
         eexists.
         eapply (ex_bbb_r
           (wn A :: (oc A0 :: map wn l4)
           ++ (l'' ++ l') ++ map wn l6))...
         eapply wk_bbb_r...
      -- (* co *)
         assert (Heq := HP1).
         apply Permutation_vs_cons_inv in Heq.
         destruct Heq as (l' & l'' & Heq).
         symmetry in Heq.
         destruct l' ; inversion Heq ; subst.
         eapply (ex_bbb_r _
           (dual (wn x) :: l'' ++ wn A :: wn A :: l')) in Hl1'...
         eapply IHsize in Hl1'...
         destruct Hl1' as [s' Hl1'].
         eexists.
         eapply (ex_bbb_r
           (wn A :: (oc A0 :: map wn l4)
           ++ (l'' ++ l') ++ map wn l6))...
         eapply co_bbb_r...
         eapply (ex_bbb_r
           ((oc A0 :: map wn l4)
           ++ (l'' ++ wn A :: wn A :: l') ++ map wn l6))...
    * rewrite <- (app_nil_l (_ :: l1)) in H0.
      dichot_elt_app_exec H0 ; subst.
      -- simpl in Hr.
         rewrite <- (bidual (oc _)) in Hr1.
         change (dual (oc (dual x))) with (dual (dual (wn x))) in Hr1.
         rewrite bidual in Hr1.
         rewrite app_comm_cons in Hr.
         apply bbb_to_mix02 in Hr.
         eapply ex_r in Hr ;
           [ | symmetry ; apply Permutation_cons_app ; reflexivity ].
         eapply cut_mix02_r in Hr...
         destruct Hr as [s' Hr].
         eexists.
         simpl.
         eapply (ex_bbb_r
           ((((oc A0 :: map wn l4) ++ map wn l6) ++ l) ++ l0))...
         eapply mix2_bbb_r...
      -- symmetry in H1.
         apply app_eq_nil in H1.
         destruct H1 ; subst.
         simpl in Hl1.
         eapply IHsize in Hr...
    * rewrite H2 in Hl2.
      rewrite app_comm_cons in Hl2.
      eapply IHsize in Hl2...
      destruct Hl2 as [s' Hl2].
      eexists.
      rewrite <- app_comm_cons in Hl2.
      rewrite <- ?map_app in Hl2.
      rewrite <- app_comm_cons.
      rewrite <- ?map_app.
      eapply oc_bbb_r...
- (* de *)
  destruct l2 ; inversion H ; subst.
  + inversion_ll_bbb Hl X l' Hl1 Hr1 HP1.
    * assert (Heq := HP1).
      apply Permutation_vs_cons_inv in Heq.
      destruct Heq as (l2' & l3' & Heq).
      subst.
      rewrite <- (bidual (wn A0)) in Hr.
      eapply IHsize in Hl1...
      destruct Hl1 as [s' Hl1].
      eexists.
      apply (ex_bbb_r (l2' ++ l3 ++ l3'))...
    * rewrite <- (app_nil_l (_ :: l1)) in H0.
      dichot_elt_app_exec H0 ; subst.
      -- apply bbb_to_mix02 in Hr.
         eapply cut_mix02_r in Hr...
         destruct Hr as [s' Hr].
         eexists.
         simpl.
         apply (ex_bbb_r ((l3 ++ l) ++ l0))...
         apply mix2_bbb_r...
      -- eapply IHsize in Hl1 ; simpl ; try rewrite bidual...
         destruct Hl1 as [s' Hl1].
         symmetry in H1.
         apply app_eq_nil in H1.
         destruct H1 ; subst.
         eexists...
         apply (ex_bbb_r (l3 ++ l1))...
    * eapply IHcut in Hl1...
  + rewrite app_comm_cons in Hl2.
    eapply IHsize in Hl2...
    destruct Hl2 as [s' Hl2].
    eexists.
    rewrite <- app_comm_cons.
    eapply de_bbb_r...
- (* wk *)
  destruct l2 ; inversion H ; subst.
  + inversion_ll_bbb Hl X l' Hl1 Hr1 HP1.
    * assert (Heq := HP1).
      apply Permutation_vs_cons_inv in Heq.
      destruct Heq as (l2' & l3' & Heq).
      subst.
      simpl in Hr.
      rewrite <- (bidual (wn _)) in Hr.
      eapply IHsize in Hl1...
      destruct Hl1 as [s' Hl1].
      eexists.
      apply (ex_bbb_r (l2' ++ l3 ++ l3'))...
    * rewrite <- (app_nil_l (_ :: l1)) in H0.
      dichot_elt_app_exec H0 ; subst.
      -- simpl in Hr1.
         apply bbb_to_mix02 in Hr.
         eapply cut_mix02_r in Hr...
         destruct Hr as [s' Hr].
         eexists.
         apply (ex_bbb_r ((l3 ++ l) ++ l0))...
         apply mix2_bbb_r...
      -- simpl in Hr.
         replace (wn A0) with (dual (oc (dual A0))) in Hr.
         ++ eapply IHsize in Hl1...
            destruct Hl1 as [s' Hl1].
            symmetry in H1.
            apply app_eq_nil in H1.
            destruct H1 ; subst.
            eexists...
            apply (ex_bbb_r (l3 ++ l1))...
         ++ simpl.
            rewrite bidual...
    * clear - Hl2.
      eapply (wk_list_bbb_r l) in Hl2.
      destruct Hl2 as [s' Hl2].
      eexists.
      eapply ex_bbb_r...
  + eapply IHsize in Hl2...
    destruct Hl2 as [s' Hl2].
    eexists.
    eapply wk_bbb_r...
- (* co *)
  destruct l2 ; inversion H ; subst.
  + inversion_ll_bbb Hl X l' Hl1 Hr1 HP1.
    * assert (Heq := HP1).
      apply Permutation_vs_cons_inv in Heq.
      destruct Heq as (l2' & l3' & Heq).
      subst.
      rewrite <- (bidual (wn A0)) in Hr.
      eapply IHsize in Hl1...
      destruct Hl1 as [s' Hl1].
      eexists.
      apply (ex_bbb_r (l2' ++ l3 ++ l3'))...
    * simpl in Hr.
      rewrite <- (bidual (wn A0)) in Hr.
      rewrite <- (app_nil_l (_ :: l1)) in H0.
      dichot_elt_app_exec H0 ; subst.
      -- change (oc (dual A0)) with (dual (wn A0)) in Hr1.
         apply bbb_to_mix02 in Hr.
         eapply cut_mix02_r in Hr ; try (rewrite bidual)...
         destruct Hr as [s' Hr].
         eexists.
         apply (ex_bbb_r ((l3 ++ l) ++ l0))...
         apply mix2_bbb_r...
      -- change (oc (dual A0)) with (dual (wn A0)) in Hl1.
         eapply IHsize in Hl1...
         destruct Hl1 as [s' Hl1].
         symmetry in H1.
         apply app_eq_nil in H1.
         destruct H1 ; subst.
         eexists...
         apply (ex_bbb_r (l3 ++ l1))...
    * (* key case oc/co bis *)
      eapply (key_case_oc_co_bbb (dual A0))...
      intros.
      rewrite bidual in H0.
      eapply (IHcut A0)...
      rewrite ? bidual...
  + rewrite ? app_comm_cons in Hl2.
    eapply IHsize in Hl2...
    destruct Hl2 as [s' Hl2].
    eexists.
    rewrite <- app_comm_cons.
    eapply co_bbb_r...
Qed.

Lemma cut_bbb_r : forall A l1 l2 s1 s2, 
  ll_bbb (dual A :: l1) s1 -> ll_bbb (A :: l2) s2 -> exists s',
    ll_bbb (l2 ++ l1) s'.
Proof with myeeasy.
intros.
rewrite <- (app_nil_l (l2 ++ l1))...
eapply cut_elim_bbb...
rewrite bidual...
Qed.
*)


(** ** Comparison with LL + [bot = oc bot] *)

Lemma mix2_bb_r : forall l1 l2, llR (oc bot) l1 -> llR (oc bot) l2 ->
  llR (oc bot) (l2 ++ l1).
Proof with myeeasy.
intros.
assert (pgax (pfrag_llR (oc bot)) (oc bot :: one :: nil))
  as Hax by (right ; reflexivity).
apply gax_r in Hax.
eapply (wk_r _ one) in H0.
eapply (@cut_r (pfrag_llR _) eq_refl) in H0...
eapply bot_r in H.
eapply ex_r in H0 ; [ | apply Permutation_app_comm ].
eapply (@cut_r (pfrag_llR _) eq_refl) in H0 ; simpl...
eexists...
Qed.

Lemma mix2_to_bb : forall l s, ll_mix2 l s -> exists s', llR (oc bot) l s'.
Proof with myeeasy.
intros l s pi.
induction pi ;
  try destruct IHpi as [s' IHpi] ;
  try destruct IHpi1 as [s1' IHpi1] ;
  try destruct IHpi2 as [s2' IHpi2] ;
  try (inversion f ; fail) ;
  try (inversion H ; fail) ;
  try (eapply mix2_bb_r ; myeeasy ; fail) ;
  eexists ;
  try (constructor ; myeeasy ; fail).
eapply ex_r...
Qed.

Theorem bb_to_bbb : forall l s, llR (oc bot) l s -> exists s', ll_bbb l s'.
Proof with myeeasy ; try PCperm_solve.
intros l s pi.
induction pi ;
  try (inversion f ; fail) ;
  try destruct IHpi as [s' IHpi] ;
  try destruct IHpi1 as [s1' IHpi1] ;
  try destruct IHpi2 as [s2' IHpi2] ;
  try (eexists ; constructor ; myeeasy ; fail).
- eexists ; eapply ex_bbb_r...
- eexists ; apply co_bbb_r.
  eapply ex_bbb_r...
- eapply cut_bbb_r...
- destruct H ; subst ; eexists.
  + apply de_bbb_r.
    apply one_bbb_r.
  + rewrite <- (app_nil_l (one :: _)).
    rewrite app_comm_cons.
    apply mix2_bbb_r.
    * apply one_bbb_r.
    * change nil with (map wn nil).
      apply oc_r.
      eapply bot_r.
      eapply (@mix0_r pfrag_mix02 eq_refl).
Qed.

(** The converse of [bb_to_bbb] is proved in the [nn] library. *)

(** *** Examples *)
(*
Goal exists s, ll_bbb (one :: oc (parr one one) :: nil) s.
Proof with myeeasy.
eexists.
change (one :: oc (parr one one) :: nil)
  with ((one :: nil) ++ oc (parr one one) :: nil).
eapply mix2_bbb_r.
- change nil with (map wn nil).
  apply oc_bbb_r.
  apply parr_bbb_r.
  simpl.
  change (one :: one :: nil) with ((one :: nil) ++ one :: nil).
  apply mix2_bbb_r.
  + apply one_bbb_r.
  + eapply one_r.
- eapply one_r.
Qed.

Goal exists s, llR (oc bot) (one :: oc (parr one one) :: nil) s.
Proof with myeeasy.
assert (exists s, llR (oc bot) ((one :: nil) ++ one :: nil) s)
  as [s Hr] by (eapply mix2_bb_r ; apply one_r).
change (one :: oc (parr one one) :: nil)
  with ((one :: nil) ++ oc (parr one one) :: nil).
eapply mix2_bb_r.
- change nil with (map wn nil).
  apply oc_r.
  apply parr_r...
- apply one_r.
Qed.
*)

Example bbb_ex : exists s,
  ll_bbb (one :: oc (tens (parr one one) bot) :: nil) s.
Proof with myeeasy ; try perm_solve.
eexists.
change (one :: oc (tens (parr one one) bot) :: nil)
  with ((one :: nil) ++ (oc (tens (parr one one) bot) :: nil)).
apply (ex_bbb_r ((oc (tens (parr one one) bot) :: nil) ++ one :: nil))...
eapply mix2_bbb_r.
- apply one_bbb_r.
- change (oc (tens (parr one one) bot) :: nil)
    with (oc (tens (parr one one) bot) :: map wn (nil ++ nil)).
  eapply oc_r.
  rewrite map_app.
  eapply tens_r.
  + eapply parr_r.
    simpl.
    change (one :: one :: nil) with ((one :: nil) ++ one :: nil).
    eapply (@mix2_r pfrag_mix02 eq_refl).
    * eapply one_r.
    * eapply one_r.
  + eapply bot_r.
    eapply (@mix0_r pfrag_mix02 eq_refl).
Qed.

Example bb_ex : exists s,
  llR (oc bot) (one :: oc (tens (parr one one) bot) :: nil) s.
Proof with myeeasy ; try perm_solve.
assert (pgax (pfrag_llR (oc bot)) (oc bot :: one :: nil))
  as Hax by (right ; reflexivity).
apply gax_r in Hax.
assert (exists s, llR (oc bot) ((one :: nil) ++ one :: nil) s)
  as [s Hr] by (eapply mix2_bb_r ; apply one_r).
eexists.
eapply (@cut_r (pfrag_llR _) eq_refl) in Hax...
- apply Hax.
- eapply ex_r ; [ | apply PCperm_swap ].
  simpl.
  change (wn one :: nil) with (map wn (one :: nil)).
  apply oc_r.
  simpl.
  rewrite <- (app_nil_l nil).
  rewrite app_comm_cons.
  apply tens_r.
  + apply parr_r...
  + apply bot_r.
    change wn with wn.
    apply de_r.
    apply one_r.
Qed.


(** ** Additional results on a weakened version of [ll_bbb]
 without [mix2] above [mix2] on the [mix0] side *)
Inductive ll_bbb0 : list formula -> nat -> Prop :=
| ax_bbb0_r : forall X, ll_bbb0 (covar X :: var X :: nil) 1
| ex_bbb0_r : forall l1 l2 s, ll_bbb0 l1 s -> Permutation l1 l2 -> ll_bbb0 l2 (S s)
| mix2_bbb0_r : forall l1 l2 s1 s2, ll_bbb0 l1 s1 -> ll_mix0 l2 s2 ->
                                    ll_bbb0 (l2 ++ l1) (S (s1 + s2))
| one_bbb0_r : ll_bbb0 (one :: nil) 1
| bot_bbb0_r : forall l s, ll_bbb0 l s -> ll_bbb0 (bot :: l) (S s)
| tens_bbb0_r : forall A B l1 l2 s1 s2, ll_bbb0 (A :: l1) s1 -> ll_bbb0 (B :: l2) s2 ->
                                        ll_bbb0 (tens A B :: l2 ++ l1) (S (s1 + s2))
| parr_bbb0_r : forall A B l s, ll_bbb0 (A :: B :: l) s -> ll_bbb0 (parr A B :: l) (S s)
| top_bbb0_r : forall l, ll_bbb0 (top :: l) 1
| plus_bbb0_r1 : forall A B l s, ll_bbb0 (A :: l) s -> ll_bbb0 (aplus A B :: l) (S s)
| plus_bbb0_r2 : forall A B l s, ll_bbb0 (A :: l) s -> ll_bbb0 (aplus B A :: l) (S s)
| with_bbb0_r : forall A B l s1 s2, ll_bbb0 (A :: l) s1 -> ll_bbb0 (B :: l) s2 ->
                                    ll_bbb0 (awith A B :: l) (S (max s1 s2))
| oc_bbb0_r : forall A l s, ll_bbb0 (A :: map wn l) s -> ll_bbb0 (oc A :: map wn l) (S s)
| de_bbb0_r : forall A l s, ll_bbb0 (A :: l) s -> ll_bbb0 (wn A :: l) (S s)
| wk_bbb0_r : forall A l s, ll_bbb0 l s -> ll_bbb0 (wn A :: l) (S s)
| co_bbb0_r : forall A l s, ll_bbb0 (wn A :: wn A :: l) s -> ll_bbb0 (wn A :: l) (S s).

(** The example given above in [ll_bbb] and [llR (oc bot)] is not cut-free provable
    in [ll_bbb0]. *)
Lemma mix0_bbb0_false : forall s, ll_bbb0 nil s -> False.
Proof with myeasy.
intros s H.
remember nil as l.
revert Heql ; induction H ; intros Heql ; inversion Heql ; subst.
- symmetry in H0.
  apply Permutation_nil in H0 ; subst.
  apply IHll_bbb0...
- apply app_eq_nil in Heql.
  destruct Heql ; subst.
  apply IHll_bbb0...
Qed.

Lemma ex_implies_mix2_mix02 : forall l s,
  ll_bbb0 l s -> Permutation l (one :: oc (tens (parr one one) bot) :: nil) ->
    exists s', ll_mix0 (one :: one :: nil) s'.
Proof with myeeasy ; try perm_solve.
intros l s H.
induction H ; intro HP ;
  try (apply Permutation_sym in HP ;
       apply Permutation_length_2_inv in HP ;
       destruct HP as [HP | HP] ;
       inversion HP ;
       fail).
- apply IHll_bbb0...
- apply Permutation_sym in HP.
  apply Permutation_length_2_inv in HP.
  destruct HP as [HP | HP].
  + apply eq_sym in HP.
    rewrite <- (app_nil_l (one :: _)) in HP.
    dichot_elt_app_exec HP ; subst.
    * apply eq_sym in HP1.
      apply app_eq_unit in HP1.
      destruct HP1 ; destruct H1 ; subst.
      -- clear - H.
         exfalso.
         remember (oc (tens (parr one one) bot) :: nil) as l.
         revert Heql ; induction H ; intro Heql ; inversion Heql ; subst.
         ++ symmetry in H0.
            apply Permutation_length_1_inv in H0.
            apply IHll_bbb0...
         ++ apply app_eq_unit in Heql.
            destruct Heql ; destruct H1 ; subst.
            ** apply IHll_bbb0...
            ** eapply mix0_bbb0_false...
         ++ rewrite_all H2.
            clear - H.
            remember (tens (parr one one) bot :: nil) as l.
            revert Heql ; induction H ; intro Heql ; inversion Heql ; subst.
            ** symmetry in H0.
               apply Permutation_length_1_inv in H0.
               apply IHll_bbb0...
            ** apply app_eq_unit in Heql.
               destruct Heql ; destruct H1 ; subst.
               --- apply IHll_bbb0...
               --- eapply mix0_bbb0_false...
            ** apply app_eq_nil in H4.
               destruct H4 ; subst.
               clear - H0.
               remember (bot :: nil) as l.
               revert Heql ; induction H0 ; intro Heql ; inversion Heql ; subst.
               --- symmetry in H.
                   apply Permutation_length_1_inv in H.
                   apply IHll_bbb0...
               --- apply app_eq_unit in Heql.
                   destruct Heql ; destruct H1 ; subst.
                   +++ apply IHll_bbb0...
                   +++ eapply mix0_bbb0_false...
               --- eapply mix0_bbb0_false...
      -- exfalso.
         eapply mix0_bbb0_false...
    * symmetry in HP0.
      apply app_eq_nil in HP0.
      destruct HP0 ; subst.
      apply IHll_bbb0...
  + symmetry in HP.
    rewrite <- (app_nil_l (oc _::_)) in HP.
    dichot_elt_app_exec HP ; subst.
    * symmetry in HP1.
      apply app_eq_unit in HP1.
      destruct HP1 ; destruct H1 ; subst.
      -- clear - H0.
         simpl in H0.
         remember (oc (tens (parr one one) bot) :: nil) as l.
         revert Heql ; induction H0 ; intro Heql ; inversion Heql ; subst.
         ++ symmetry in H.
           simpl in H.
           apply Permutation_length_1_inv in H.
           apply IHll...
         ++ inversion f.
         ++ rewrite_all H2.
            clear - H0.
            remember (tens (parr one one) bot :: nil) as l.
            revert Heql ; induction H0 ; intro Heql ; inversion Heql ; subst.
            ** symmetry in H.
               simpl in H.
               apply Permutation_length_1_inv in H.
               apply IHll...
            ** inversion f.
            ** apply app_eq_nil in H2.
               destruct H2 ; subst.
               clear - H0_.
               remember (parr one one :: nil) as l.
               revert Heql ; induction H0_ ; intro Heql ; inversion Heql ; subst.
               --- symmetry in H.
                   simpl in H.
                   apply Permutation_length_1_inv in H.
                   apply IHH0_...
               --- inversion f.
               --- eexists...
               --- inversion f.
               --- inversion H.
            ** inversion f.
            ** inversion H.
         ++ inversion f.
         ++ inversion H.
      -- exfalso.
         eapply mix0_bbb0_false...
    * symmetry in HP0.
      apply app_eq_nil in HP0.
      destruct HP0 ; subst.
      apply IHll_bbb0...
- symmetry in HP.
  apply Permutation_length_2_inv in HP.
  destruct HP as [HP | HP] ; inversion HP.
  destruct l ; inversion H2.
Defined.

Lemma ex_not_bbb0 : forall s, ~ ll_bbb0 (one :: oc (tens (parr one one) bot) :: nil) s.
Proof.
intros s H.
apply ex_implies_mix2_mix02 in H ; [ | reflexivity ].
clear s ; destruct H as [s pi].
apply mix0_not_mix2 in pi.
assumption.
Qed.

Lemma bbb_neq_bbb0 : exists l, (exists s, ll_bbb l s) /\ (forall s, ~ ll_bbb0 l s).
Proof.
eexists ; split ; [ apply bbb_ex | apply ex_not_bbb0 ].
Qed.

(** The same example is provable in [ll_bbb0] with cut,
    thus cut-elimination does not hold for [ll_bbb0]. *)

Section bbb0_with_cut.

Hypothesis cut_bbb0_r : forall A l1 l2 s1 s2,
  ll_bbb0 (dual A :: l1) s1 -> ll_bbb0 (A :: l2) s2 -> exists s,
    ll_bbb0 (l2 ++ l1) s.

Theorem llR_oc_bot_to_bbb0_cut : forall l s, llR (oc bot) l s ->
  exists s', ll_bbb0 l s'.
Proof with myeeasy ; try PCperm_solve.
intros l s pi.
induction pi ;
  try (inversion f ; fail) ;
  try destruct IHpi as [s' IHpi] ;
  try destruct IHpi1 as [s1' IHpi1] ;
  try destruct IHpi2 as [s2' IHpi2] ;
  try (eexists ; constructor ; myeeasy ; fail).
- eexists ; eapply ex_bbb0_r...
- eexists ; apply co_bbb0_r.
  eapply ex_bbb0_r...
- eapply cut_bbb0_r...
- destruct H ; subst ; eexists.
  + apply de_bbb0_r.
    apply one_bbb0_r.
  + rewrite <- (app_nil_l (one :: _)).
    rewrite app_comm_cons.
    apply mix2_bbb0_r.
    * apply one_bbb0_r.
    * change nil with (map wn nil).
      apply oc_r.
      eapply bot_r.
      eapply (@mix0_r pfrag_mix0 eq_refl).
Qed.

Example bbb0_cut_ex : exists s,
  ll_bbb0 (one :: oc (tens (parr one one) bot) :: nil) s.
Proof.
destruct bb_ex as [s Hex].
apply llR_oc_bot_to_bbb0_cut in Hex.
assumption.
Qed.

End bbb0_with_cut.

Lemma cut_not_elim_bbb0 :
~ forall A l1 l2 s1 s2, ll_bbb0 (dual A :: l1) s1 -> ll_bbb0 (A :: l2) s2 ->
    exists s, ll_bbb0 (l2 ++ l1) s.
Proof.
intros Hcut.
apply bbb0_cut_ex in Hcut.
destruct Hcut as [s Hex].
apply ex_not_bbb0 in Hex.
assumption.
Qed.


