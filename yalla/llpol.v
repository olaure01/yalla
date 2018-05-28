(* llpol example file for yalla library *)
(* Coq 8.6 *)
(* v 1.0   Olivier Laurent *)


(** * Example of a concrete use of the yalla library: polarized linear logic LLpol *)

Require Import Injective.
Require Import List_more.
Require Import Permutation_more.
Require Import Permutation_solve.


(** ** 0. load the [ll] library *)

Require ll.


(** ** 1. define formulas *)

(** Positive and negative formulas *)
Inductive pformula : Set :=
| var : formulas.Atom -> pformula
| one : pformula
| tens : pformula -> pformula -> pformula
| zero : pformula
| aplus : pformula -> pformula -> pformula
| oc : nformula -> pformula
with nformula : Set :=
| covar : formulas.Atom -> nformula
| bot : nformula
| parr : nformula -> nformula -> nformula
| top : nformula
| awith : nformula -> nformula -> nformula
| wn : pformula -> nformula.

Scheme pform_ind := Induction for pformula Sort Prop
  with nform_ind := Induction for nformula Sort Prop.
Combined Scheme polform_ind from pform_ind, nform_ind.

Inductive formula : Set :=
| pos : pformula -> formula
| neg : nformula -> formula.

Fixpoint pdual P :=
match P with
| var x     => covar x
| one       => bot
| tens P Q  => parr (pdual Q) (pdual P)
| zero      => top
| aplus P Q => awith (pdual P) (pdual Q)
| oc N      => wn (ndual N)
end
with ndual N :=
match N with
| covar x   => var x
| bot       => one
| parr N M  => tens (ndual M) (ndual N)
| top       => zero
| awith N M => aplus (ndual N) (ndual M)
| wn P      => oc (pdual P)
end.

Lemma bipndual :
     (forall P, ndual (pdual P) = P)
  /\ (forall N, pdual (ndual N) = N).
Proof.
apply polform_ind ; intros ; simpl ;
  try rewrite H ; try rewrite H0 ; try reflexivity.
Qed.

Function dual A :=
match A with
| pos P => neg (pdual P)
| neg N => pos (ndual N)
end.


(** ** 2. define embedding into [formulas.formula] *)

Fixpoint pllpol2ll P :=
match P with
| var x => formulas.var x
| one => formulas.one
| tens P Q => formulas.tens (pllpol2ll P) (pllpol2ll Q)
| zero => formulas.zero
| aplus P Q => formulas.aplus (pllpol2ll P) (pllpol2ll Q)
| oc N => formulas.oc (nllpol2ll N)
end
with nllpol2ll N :=
match N with
| covar x => formulas.covar x
| bot => formulas.bot
| parr N M => formulas.parr (nllpol2ll N) (nllpol2ll M)
| top => formulas.top
| awith N M => formulas.awith (nllpol2ll N) (nllpol2ll M)
| wn P => formulas.wn (pllpol2ll P)
end.

Function llpol2ll A :=
match A with
| pos P => pllpol2ll P
| neg N => nllpol2ll N
end.

Lemma billpol2ll_inj : injective pllpol2ll /\ injective nllpol2ll.
Proof with try reflexivity.
apply polform_ind ;
  try (intros P Heq ; destruct P ; inversion Heq ; reflexivity) ;
  try (intros A IH1 B IH2 C Heq ; destruct C ; inversion Heq ;
       apply IH1 in H0 ; apply IH2 in H1 ; subst ; reflexivity).
- intros x P Heq ; destruct P ; inversion Heq...
- intros N IH M Heq ; destruct M ; inversion Heq.
  apply IH in H0 ; subst...
- intros x N Heq ; destruct N ; inversion Heq...
- intros P IH Q Heq ; destruct Q ; inversion Heq.
  apply IH in H0 ; subst...
Qed.

Lemma llpol2ll_inj : injective llpol2ll.
Proof with try assumption.
intros A B Heq.
destruct A ; destruct B.
- simpl in Heq.
  f_equal.
  apply billpol2ll_inj...
- destruct p ; destruct n ; inversion Heq.
- destruct p ; destruct n ; inversion Heq.
- simpl in Heq.
  f_equal.
  apply billpol2ll_inj...
Qed.

Lemma billpol2ll_dual :
     (forall P, formulas.dual (pllpol2ll P) = nllpol2ll (pdual P))
  /\ (forall N, formulas.dual (nllpol2ll N) = pllpol2ll (ndual N)).
Proof.
apply polform_ind ; intros ; simpl ;
  try rewrite H ; try rewrite H0 ; reflexivity.
Qed.

Lemma llpol2ll_dual : forall A, formulas.dual (llpol2ll A) = llpol2ll (dual A).
Proof.
destruct A ; apply billpol2ll_dual.
Qed.

Lemma bidual : forall A, dual (dual A) = A.
Proof.
intros A.
apply llpol2ll_inj.
rewrite <- 2 llpol2ll_dual.
rewrite formulas.bidual.
reflexivity.
Qed.

Lemma llpol2ll_map_wn : forall l,
    map llpol2ll (map neg (map wn l))
  = map formulas.wn (map pllpol2ll l).
Proof with try reflexivity.
induction l...
simpl ; rewrite IHl...
Qed.

Lemma llpol2ll_map_wn_inv : forall l1 l2,
  map formulas.wn l1 = map llpol2ll l2 ->
    exists l2', l2 = map neg (map wn l2') /\ l1 = map pllpol2ll l2'.
Proof with try assumption ; try reflexivity.
induction l1 ; intros l2 Heq ;
  destruct l2 ; inversion Heq...
- exists nil ; split...
- apply IHl1 in H1.
  destruct f ; inversion H0 ;
    [ destruct p | destruct n ] ; inversion H0 ; subst.
  destruct H1 as (l2' & Heq1 & H1) ; subst.
  exists (p :: l2') ; split...
Qed.


(** ** 3. define proofs *)

(** [ll] restricted to polarized formulas *)
Inductive llpol : list formula -> Prop :=
| ax_r : forall X, llpol (neg (covar X) :: pos (var X) :: nil)
| ex_r : forall l1 l2, llpol l1 ->
              Permutation l1 l2 -> llpol l2
| one_r : llpol (pos one :: nil)
| bot_r : forall l, llpol l -> llpol (neg bot :: l)
| tens_r : forall P Q l1 l2,
              llpol (pos P :: l1) -> llpol (pos Q :: l2) ->
              llpol (pos (tens P Q) :: l1 ++ l2)
| parr_r : forall N M l,
              llpol (neg N :: neg M :: l) ->
              llpol (neg (parr N M) :: l)
| top_r : forall l, llpol (neg top :: l)
| plus_r1 : forall P Q l,
              llpol (pos P :: l) -> llpol (pos (aplus P Q) :: l)
| plus_r2 : forall P Q l,
              llpol (pos P :: l) -> llpol (pos (aplus Q P) :: l)
| with_r : forall N M l,
              llpol (neg N :: l) -> llpol (neg M :: l) ->
              llpol (neg (awith N M) :: l)
| oc_r : forall N l,
              llpol (neg N :: map neg (map wn l)) ->
              llpol (pos (oc N) :: map neg (map wn l))
| de_r : forall P l,
              llpol (pos P :: l) -> llpol (neg (wn P) :: l)
| wk_r : forall P l,
              llpol l -> llpol (neg (wn P) :: l)
| co_r : forall P l,
              llpol (neg (wn P) :: neg (wn P) :: l) ->
              llpol (neg (wn P) :: l).


(** ** 4. characterize corresponding [ll] fragment *)

(*
Definition llpol_fragment A := exists B, A = llpol2ll B.

Lemma llpol_is_fragment : ll.fragment llpol_fragment.
Proof.
intros A HfA B Hsf.
induction Hsf ;
  try (apply IHHsf ;
       destruct HfA ;
       destruct x ; inversion H ;
       [ destruct p ; inversion H
       | destruct n ; inversion H ] ;
       try (eexists (pos _) ; reflexivity) ;
       try (eexists (neg _) ; reflexivity)).
assumption.
Qed.
*)

(** cut / axioms / mix0 / mix2 / permutation *)
Definition pfrag_mell := ll.mk_pfrag false (fun _ => False) false false true.
(*                                   cut   axioms           mix0  mix2  perm  *)


(** ** 5. prove equivalence of proof predicates *)

Lemma llpol2llpolfrag : forall l, llpol l ->
  exists s, ll.ll pfrag_mell (map llpol2ll l) s.
Proof with try reflexivity ; try eassumption.
intros l pi.
induction pi ;
  try destruct IHpi as [s' pi'] ;
  try destruct IHpi1 as [s1' pi1'] ;
  try destruct IHpi2 as [s2' pi2'] ;
  eexists ; simpl ; rewrite ? map_app.
- apply ll.ax_r.
- eapply ll.ex_r...
  apply Permutation_map...
- eapply ll.one_r.
- eapply ll.bot_r...
- eapply ll.ex_r.
  + apply (ll.tens_r _ _ _ _ _ _ _ pi1' pi2').
  + simpl ; perm_solve.
- apply ll.parr_r...
- apply ll.top_r.
- apply ll.plus_r1...
- apply ll.plus_r2...
- apply ll.with_r...
- rewrite llpol2ll_map_wn.
  apply ll.oc_r.
  rewrite <- llpol2ll_map_wn...
- apply ll.de_r...
- apply ll.wk_r...
- rewrite <- (app_nil_l (map _ _)).
  change nil with (map formulas.wn nil).
  apply ll.co_r...
Qed.

Lemma llpolfrag2llpol : forall l s,
  ll.ll pfrag_mell (map llpol2ll l) s -> llpol l.
Proof with try reflexivity.
intros l s pi.
remember (map llpol2ll l) as l0.
revert l Heql0 ; induction pi ; intros l' Heql0 ; subst ;
  try (now (destruct l' ; inversion Heql0 ;
            destruct f ; inversion H0 ;
              [ destruct p | destruct n ] ; inversion H0 ; subst ;
            constructor ;
            apply IHpi ; reflexivity)) ;
  try (now inversion f).
- decomp_map Heql0 ; subst.
  destruct l1 ; inversion Heql4.
  destruct x ; inversion Heql2 ;
    [ destruct p | destruct n ] ; inversion Heql2.
  destruct x0 ; inversion Heql0 ;
    [destruct p | destruct n ] ; inversion Heql0.
  subst ; subst.
  apply ax_r.
- simpl in H.
  apply Permutation_map_inv in H.
  destruct H as (l'' & Heq & HP) ; subst.
  symmetry in HP.
  eapply ex_r ; [ | eassumption ].
  apply IHpi...
- destruct l' ; inversion Heql0.
  destruct f ; inversion H0 ;
    [ destruct p | destruct n ] ; inversion H0.
  destruct l' ; inversion H1.
  apply one_r.
- decomp_map Heql0 ; subst.
  destruct x ; inversion Heql2 ;
    [ destruct p | destruct n ] ; inversion Heql2 ; subst.
  eapply ex_r.
  apply tens_r.
  + apply IHpi1...
  + apply IHpi2...
  + perm_solve.
- destruct l' ; inversion Heql0.
  destruct f ; inversion H0 ;
    [ destruct p | destruct n ] ; inversion H0 ; subst.
  apply with_r.
  + apply IHpi1...
  + apply IHpi2...
- destruct l' ; inversion Heql0.
  destruct f ; inversion H0 ; 
    [destruct p | destruct n ] ; inversion H0 ; subst.
  apply llpol2ll_map_wn_inv in H1.
  destruct H1 as (l'' & Heq1 & Heq2) ; subst.
  apply oc_r.
  apply IHpi.
  simpl ; rewrite llpol2ll_map_wn...
- destruct l' ; inversion Heql0.
  destruct f ; inversion H0 ;
    [ destruct p | destruct n ] ; inversion H0 ; subst.
  decomp_map H1 ; subst.
  apply co_r.
  apply llpol2ll_map_wn_inv in H4.
  destruct H4 as (l'' & Heq1 & Heq2) ; subst.
  eapply ex_r.
  + apply IHpi...
    rewrite <- llpol2ll_map_wn.
    replace (formulas.wn (pllpol2ll p)
                            :: map llpol2ll (map neg (map wn l''))
          ++ formulas.wn (pllpol2ll p) :: map llpol2ll l2)
      with (map llpol2ll (neg (wn p) :: map neg (map wn l'')
                        ++ neg (wn p) :: l2))...
    list_simpl...
  + perm_solve.
- inversion H.
Qed.


(** ** 6. import properties *)

(** *** axiom expansion *)

Lemma ax_gen_r : forall A, llpol (dual A :: A :: nil).
Proof.
intro A.
destruct (@ll.ax_exp pfrag_mell (formulas.dual (llpol2ll A)))
  as [s Hax].
rewrite formulas.bidual in Hax.
rewrite llpol2ll_dual in Hax.
eapply llpolfrag2llpol.
eassumption.
Qed.

(** *** cut elimination *)

Lemma cut_r : forall A l1 l2, 
  llpol (A :: l1) -> llpol (dual A :: l2) -> llpol (l1 ++ l2).
Proof with try eassumption.
intros A l1 l2 pi1 pi2.
destruct (llpol2llpolfrag _ pi1) as [s1 pi1'] ; simpl in pi1'.
destruct (llpol2llpolfrag _ pi2) as [s2 pi2'] ; simpl in pi2'.
eapply ll.cut_r_axfree in pi1' ;
  [ | | rewrite llpol2ll_dual ]...
- destruct pi1' as [s pi].
  rewrite <- map_app in pi.
  eapply llpolfrag2llpol...
- intros l Hax ; inversion Hax.
Qed.


(** ** 7. specific developments *)

Lemma par_inv : forall N M l,
  llpol (neg (parr N M) :: l) -> llpol (neg N :: neg M :: l).
Proof with try assumption.
intros N M l pi.
rewrite <- (app_nil_l l).
eapply ex_r ; [ | apply perm_swap ].
rewrite 2 app_comm_cons.
eapply cut_r.
- rewrite <- (app_nil_l (neg N :: nil)).
  rewrite 2 app_comm_cons.
  rewrite <- app_comm_cons.
  apply (tens_r (ndual M) (ndual N)).
  + change (pos (ndual M)) with (dual (neg M)).
    apply ax_gen_r.
  + change (pos (ndual N)) with (dual (neg N)).
    apply ax_gen_r.
- simpl ; rewrite 2 (proj2 bipndual)...
Qed.

Lemma with_inv_1 : forall N M l,
  llpol (neg (awith N M) :: l) ->  llpol (neg N :: l).
Proof with try assumption.
intros N M l pi.
rewrite <- (app_nil_l l).
rewrite app_comm_cons.
eapply cut_r.
- apply (plus_r1 (ndual N) (ndual M)).
  change (pos (ndual N)) with (dual (neg N)).
  apply ax_gen_r.
- simpl ; rewrite 2 (proj2 bipndual)...
Qed.

Lemma with_inv_2 : forall N M l,
  llpol (neg (awith M N) :: l) ->  llpol (neg N :: l).
Proof with try assumption.
intros N M l pi.
rewrite <- (app_nil_l l).
rewrite app_comm_cons.
eapply cut_r.
- apply (plus_r2 (ndual N) (ndual M)).
  change (pos (ndual N)) with (dual (neg N)).
  apply ax_gen_r.
- simpl ; rewrite 2 (proj2 bipndual)...
Qed.

(** Polarized sequents are those with at most one positive formula. *)
Definition polsequent l :=
     (exists l0, l = map neg l0)
  \/ (exists l0 P, Permutation l (pos P :: (map neg l0))).

(*
Lemma uniq_polsequent : forall l1 l2 P1 P2,
  Permutation (pos P1 :: map neg l1) (pos P2 :: map neg l2) ->
    P1 = P2 /\ Permutation l1 l2.
Proof with try eassumption ; try reflexivity.
intros l1 l2 P1 P2 HP.
assert (HP' := HP).
apply Permutation_vs_cons_inv in HP'.
destruct HP' as (l' & l'' & Heq).
destruct l' ; inversion Heq.
- split...
  rewrite H0 in HP.
  apply Permutation_cons_inv in HP.
  apply Permutation_map_inv_inj in HP...
  intros N M Hneg.
  inversion Hneg...
- symmetry in H1.
  exfalso.
  decomp_map H1.
  inversion H1.
Qed.

Lemma polsequent_app : forall l1 l2,
  polsequent (l1 ++ l2) ->
    exists l, (l2 = map neg l /\ polsequent l1)
           \/ (l1 = map neg l /\ polsequent l2).
Proof with try eassumption ; try reflexivity.
intros l1 l2 Hi.
assert (Hi' := Hi).
destruct Hi' as [ (l0 & Hi') | (l0 & P & Hi') ].
- decomp_map Hi' ; subst.
  exists l4 ; left ; split...
  left ; eexists...
- assert (Hi'' := Hi').
  apply Permutation_vs_cons_inv in Hi'.
  destruct Hi' as (l3 & l4 & Heq).
  dichot_elt_app_exec Heq ; subst.
  + list_simpl in Hi''.
    symmetry in Hi''.
    apply Permutation_cons_app_inv in Hi''.
    symmetry in Hi''.
    apply Permutation_map_inv in Hi''.
    destruct Hi'' as (l' & Heq & HP).
    decomp_map Heq ; subst.
    eexists ; left ; split...
    right ; exists (l4 ++ l6) ; exists P ; perm_solve.
  + symmetry in Hi''.
    rewrite app_assoc in Hi''.
    apply Permutation_cons_app_inv in Hi''.
    list_simpl in Hi''.
    symmetry in Hi''.
    apply Permutation_map_inv in Hi''.
    destruct Hi'' as (l' & Heq & HP).
    decomp_map Heq ; subst.
    eexists ; right ; split...
    right ; exists (l6 ++ l7) ; exists P ; perm_solve.
Qed.
*)

Lemma polsequent_neg_add : forall N l,
  polsequent l -> polsequent (neg N :: l).
Proof.
intros N l Hpol.
destruct Hpol as [ (l0 & Heq) | (l0 & P & HP) ] ; subst.
- left ; exists (N :: l0) ; reflexivity.
- assert (HP' := HP).
  apply Permutation_vs_cons_inv in HP'.
  destruct HP' as (l2 & l3 & Heq) ; subst.
  symmetry in HP.
  apply Permutation_cons_app_inv in HP.
  symmetry in HP.
  apply Permutation_map_inv in HP.
  destruct HP as (l1 & Heq' & _).
  list_simpl in Heq' ; decomp_map Heq' ; subst.
  right ; exists (N :: l4 ++ l5) ; exists P ; perm_solve.
Qed.

Lemma polsequent_neg_rem : forall N l,
  polsequent (neg N :: l) -> polsequent l.
Proof.
intros N l Hpol.
destruct Hpol as [ (l0 & Heq) | (l0 & P & HP) ] ; subst.
- destruct l0 ; inversion Heq.
  left ; exists l0 ; reflexivity.
- assert (HP' := HP).
  apply Permutation_vs_cons_inv in HP'.
  destruct HP' as (l2 & l3 & Heq).
  destruct l2 ; inversion Heq ; subst.
  symmetry in HP.
  rewrite app_comm_cons in HP.
  apply Permutation_cons_app_inv in HP.
  symmetry in HP.
  apply Permutation_map_inv in HP.
  destruct HP as (l1 & Heq' & _).
  list_simpl in Heq' ; decomp_map Heq' ; subst.
  right ; exists (l5 ++ l6) ; exists P ; perm_solve.
Qed.

Lemma polsequent_pos_rem : forall P l,
  polsequent (pos P :: l) -> exists l', l = map neg l'.
Proof with try reflexivity.
intros P l Hs.
destruct Hs as [ (l0 & Heq) | (l0 & Q & HP) ].
- decomp_map Heq ; inversion Heq1.
- assert (HP' := HP).
  apply Permutation_vs_cons_inv in HP'.
  destruct HP' as (l' & l'' & Heq).
  destruct l' ; inversion Heq ; subst.
  + apply Permutation_cons_inv in HP.
    apply Permutation_map_inv in HP...
    destruct HP as (l' & Heq' & HP') ; subst.
    eexists...
  + exfalso.
    symmetry in HP.
    rewrite app_comm_cons in HP.
    apply Permutation_cons_app_inv in HP.
    symmetry in HP.
    apply Permutation_map_inv in HP.
    destruct HP as (l2 & Heq' & HP').
    destruct l2 ; inversion Heq'.
Qed.

(** Version of [llpol] with a predicate parameter for constraining sequents inside proofs. *)
Inductive llpol_ps (PS : list formula -> Prop) : list formula -> Prop :=
| ax_ps_r : forall X, PS (neg (covar X) :: pos (var X) :: nil) ->
                llpol_ps PS (neg (covar X) :: pos (var X) :: nil)
| ex_ps_r : forall l1 l2, PS l2 ->
                llpol_ps PS l1 -> Permutation l1 l2 -> llpol_ps PS l2
| one_ps_r : PS (pos one :: nil) -> llpol_ps PS (pos one :: nil)
| bot_ps_r : forall l, PS (neg bot :: l) ->
                llpol_ps PS l -> llpol_ps PS (neg bot :: l)
| tens_ps_r : forall P Q l1 l2, PS (pos (tens P Q) :: l1 ++ l2) ->
                llpol_ps PS (pos P :: l1) -> llpol_ps PS (pos Q :: l2) ->
                llpol_ps PS (pos (tens P Q) :: l1 ++ l2)
| parr_ps_r : forall N M l, PS (neg (parr N M) :: l) -> 
                llpol_ps PS (neg N :: neg M :: l) ->
                llpol_ps PS (neg (parr N M) :: l)
| top_ps_r : forall l, PS (neg top :: l) -> llpol_ps PS (neg top :: l)
| plus_ps_r1 : forall P Q l, PS (pos (aplus P Q) :: l) ->
                llpol_ps PS (pos P :: l)-> llpol_ps PS (pos (aplus P Q) :: l)
| plus_ps_r2 : forall P Q l, PS (pos (aplus Q P) :: l) ->
                llpol_ps PS (pos P :: l)-> llpol_ps PS (pos (aplus Q P) :: l)
| with_ps_r : forall N M l, PS (neg (awith N M) :: l) ->
                llpol_ps PS (neg N :: l) -> llpol_ps PS (neg M :: l) ->
                llpol_ps PS (neg (awith N M) :: l)
| oc_ps_r : forall N l, PS (pos (oc N) :: map neg (map wn l)) ->
                llpol_ps PS (neg N :: map neg (map wn l)) ->
                llpol_ps PS (pos (oc N) :: map neg (map wn l))
| de_ps_r : forall P l, PS (neg (wn P) :: l) ->
                llpol_ps PS (pos P :: l) -> llpol_ps PS (neg (wn P) :: l)
| wk_ps_r : forall P l, PS (neg (wn P) :: l) ->
                llpol_ps PS l -> llpol_ps PS (neg (wn P) :: l)
| co_ps_r : forall P l, PS (neg (wn P) :: l) ->
                llpol_ps PS (neg (wn P) :: neg (wn P) :: l) ->
                llpol_ps PS (neg (wn P) :: l).

Lemma llpol_ps_is_ps : forall l PS, llpol_ps PS l -> PS l.
Proof.
intros l PS Hll.
inversion Hll ; assumption.
Qed.

Lemma llpol_ps_is_llpol : forall l PS, llpol_ps PS l -> llpol l.
Proof with try eassumption.
intros l PS pi.
induction pi ;
  try (destruct IHpi as [s IHpi]) ;
  try (destruct IHpi1 as [s1 IHpi1]) ;
  try (destruct IHpi2 as [s2 IHpi2]) ;
  try (constructor ; eassumption ; fail).
eapply ex_r...
Qed.

Lemma llpol_is_llpol_ps : forall l, llpol l -> llpol_ps (fun _ => True) l.
Proof with try eassumption ; try reflexivity.
intros l pi.
induction pi ;
  try (constructor ; try assumption ; try reflexivity ; fail).
eapply ex_ps_r...
Qed.

(** Formulas with [top] below negative connectives only. Such formulas are equivalent to [top]. *)
Inductive top_surf : nformula -> Prop :=
| top_s : top_surf top
| par_ls : forall N M, top_surf N -> top_surf (parr N M)
| par_rs : forall N M, top_surf N -> top_surf (parr M N)
| with_s : forall N M, top_surf N -> top_surf M -> top_surf (awith N M).

Lemma top_imp_top_surf_ps : forall N l,
  top_surf N -> polsequent l -> llpol_ps polsequent (neg N :: l).
Proof with try eassumption.
induction N ; intros l Ht Hp ; inversion Ht ; subst.
- eapply IHN1 in H0.
  + apply parr_ps_r...
    apply llpol_ps_is_ps in H0.
    apply polsequent_neg_add.
    eapply polsequent_neg_rem.
    eapply polsequent_neg_rem...
  + apply polsequent_neg_add...
- eapply IHN2 in H0.
  apply parr_ps_r ; [ | eapply ex_ps_r ; [ | | now apply perm_swap ]]...
  + apply llpol_ps_is_ps in H0.
    apply polsequent_neg_add.
    eapply polsequent_neg_rem.
    eapply polsequent_neg_rem...
  + apply llpol_ps_is_ps in H0.
    apply polsequent_neg_add.
    apply polsequent_neg_add.
    eapply polsequent_neg_rem.
    eapply polsequent_neg_rem...
  + apply polsequent_neg_add...
- apply top_ps_r.
  apply polsequent_neg_add...
- apply with_ps_r.
  + apply polsequent_neg_add...
  + eapply IHN1 in H1...
  + eapply IHN2 in H2...
Qed.

Lemma bipos_top_surf : forall l,
  llpol l -> forall P Q l', Permutation l (pos P :: pos Q :: l') ->
    exists N l1 l2, l' = l1 ++ neg N :: l2 /\ top_surf N.
Proof with try assumption ; try reflexivity.
intros l pi ; induction pi ; intros P' Q' l' HP.
- apply Permutation_length_2_inv in HP.
  destruct HP as [ HP | HP ] ; inversion HP.
- eapply IHpi.
  etransitivity ; [ apply H | apply HP ].
- apply Permutation_length_1_inv in HP.
  inversion HP.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_vs_cons_inv in HP'.
  destruct HP' as (l2 & l3 & Heq).
  destruct l2 ; inversion Heq.
  destruct l2 ; inversion H1 ; subst.
  rewrite 2 app_comm_cons in HP.
  apply Permutation_cons_app_inv in HP.
  list_simpl in HP.
  apply IHpi in HP.
  destruct HP as (N & l0 & l1 & Heq' & Htop).
  exists N.
  dichot_elt_app_exec Heq' ; subst.
  + exists l0 ; exists (l4 ++ neg bot :: l3) ; list_simpl ; split...
  + exists (l2 ++ neg bot :: l5) ; exists l1 ; list_simpl ; split...
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_vs_cons_inv in HP'.
  destruct HP' as (l2' & l3' & Heq).
  destruct l2' ; inversion Heq ; subst.
  + apply Permutation_cons_inv in HP.
    assert (HP' := HP).
    apply Permutation_vs_cons_inv in HP'.
    destruct HP' as (l3 & l4 & Heq').
    rewrite Heq' in HP.
    symmetry in HP.
    apply Permutation_cons_app_inv in HP.
    dichot_app_exec Heq' ;
      [ | destruct l0 ; inversion Heq'1 ; list_simpl in Heq'1 ] ; subst.
    * list_simpl in HP.
      assert (Permutation (pos Q :: l ++ pos Q' :: l4)
                          (pos Q :: pos Q' :: l ++ l4))
        as HP' by perm_solve.
      apply IHpi2 in HP'.
      destruct HP' as (N & l5 & l6 & Heq' & Htop).
      exists N.
      rewrite Heq' in HP.
      rewrite app_assoc in HP.
      apply Permutation_vs_elt_inv in HP.
      destruct HP as (l7 & l8 & Heq'').
      exists l7 ; exists l8 ; split...
    * destruct (IHpi2 Q Q' l4 (Permutation_refl _))
        as (N & l5 & l6 & Heq' & Htop) ; subst.
      exists N.
      rewrite app_assoc in HP.
      apply Permutation_vs_elt_inv in HP.
      destruct HP as (l7 & l8 & Heq'').
      exists l7 ; exists l8 ; split...
    * assert (Permutation (pos P :: l3 ++ pos Q' :: l0)
                          (pos P :: pos Q' :: l3 ++ l0))
        as HP' by perm_solve.
      apply IHpi1 in HP'.
      destruct HP' as (N & l5 & l6 & Heq' & Htop).
      exists N.
      rewrite app_assoc in HP.
      rewrite Heq' in HP.
      list_simpl in HP.
      apply Permutation_vs_elt_inv in HP.
      destruct HP as (l7 & l8 & Heq'').
      exists l7 ; exists l8 ; split...
  + destruct l2' ; inversion H1 ; subst.
    * rewrite <- (app_nil_l (pos (tens _ _) :: l3')) in HP.
      rewrite (app_comm_cons _ _ (pos P')) in HP.
      apply Permutation_cons_app_inv in HP.
      list_simpl in HP.
      assert (HP' := HP).
      apply Permutation_vs_cons_inv in HP'.
      destruct HP' as (l4 & l5 & Heq').
      dichot_app_exec Heq' ;
        [ | destruct l0 ; inversion Heq'1 ; list_simpl in Heq'1 ] ; subst.
      -- symmetry in HP.
         rewrite app_assoc in HP.
         apply Permutation_cons_app_inv in HP.
         list_simpl in HP.
         assert (Permutation (pos Q :: l ++ pos P' :: l5)
                             (pos Q :: pos P' :: l ++ l5))
           as HP' by perm_solve.
         apply IHpi2 in HP'.
         destruct HP' as (N & l6 & l7 & Heq' & Htop).
         exists N.
         rewrite Heq' in HP.
         rewrite app_assoc in HP.
         apply Permutation_vs_elt_inv in HP.
         destruct HP as (l8 & l9 & Heq'').
         exists l8 ; exists l9 ; split...
      -- destruct (IHpi2 Q P' l5 (Permutation_refl _))
           as (N & l6 & l7 & Heq' & Htop) ; subst.
         exists N.
         list_simpl in HP.
         symmetry in HP.
         apply Permutation_cons_app_inv in HP.
         rewrite app_assoc in HP.
         apply Permutation_vs_elt_inv in HP.
         destruct HP as (l8 & l9 & Heq'').
         exists l8 ; exists l9 ; split...
      -- assert (Permutation (pos P :: l4 ++ pos P' :: l0)
                             (pos P :: pos P' :: l4 ++ l0))
           as HP' by perm_solve.
         apply IHpi1 in HP'.
         destruct HP' as (N & l6 & l7 & Heq' & Htop).
         exists N.
         list_simpl in HP.
         symmetry in HP.
         apply Permutation_cons_app_inv in HP.
         rewrite app_assoc in HP.
         rewrite Heq' in HP.
         list_simpl in HP.
         apply Permutation_vs_elt_inv in HP.
         destruct HP as (l8 & l9 & Heq'').
         exists l8 ; exists l9 ; split...
    * rewrite 2 (app_comm_cons _ (pos (tens _ _) :: l3')) in HP.
      apply Permutation_cons_app_inv in HP.
      list_simpl in HP.
      assert (HP' := HP).
      apply Permutation_vs_cons_inv in HP'.
      destruct HP' as (l4 & l5 & Heq').
      dichot_app_exec Heq' ; subst.
      -- assert (Permutation (pos Q :: l ++ pos P' :: l5)
                             (pos Q :: pos P' :: l ++ l5))
           as HP' by perm_solve.
         apply IHpi2 in HP'.
         destruct HP' as (N & l6 & l7 & Heq' & Htop).
         exists N.
         symmetry in HP.
         rewrite app_assoc in HP.
         apply Permutation_cons_app_inv in HP.
         list_simpl in HP.
         rewrite Heq' in HP.
         rewrite app_assoc in HP.
         apply Permutation_vs_elt_inv in HP.
         destruct HP as (l8 & l9 & Heq'').
         destruct l8 ; inversion Heq''.
         dichot_app_exec H2 ;
           [ | destruct l2 ; inversion Heq'' ; list_simpl in H4 ] ; subst.
         ++ exists (l2' ++ pos (tens P Q) :: l0) ; exists l9 ;
              list_simpl ; split...
         ++ exists (l8 ++ pos (tens P Q) :: nil) ; exists l9 ;
              list_simpl ; split...
         ++ inversion H4 ; subst.
            exists l8 ; exists (l2 ++ pos (tens P Q) :: l3') ;
              list_simpl ; split...
      -- destruct l0 ; inversion Heq'1 ; list_simpl in Heq'1 ; subst.
         ++ destruct (IHpi2 Q P' l5 (Permutation_refl _))
              as (N & l6 & l7 & Heq' & Htop) ; subst.
            exists N.
            list_simpl in HP.
            symmetry in HP.
            apply Permutation_cons_app_inv in HP.
            rewrite app_assoc in HP.
            apply Permutation_vs_elt_inv in HP.
            destruct HP as (l8 & l9 & Heq'').
            destruct l8 ; inversion Heq'' ; subst.
            dichot_app_exec H3 ;
              [ | destruct l0 ; inversion H2 ; list_simpl in H2 ] ; subst.
            ** exists (l2' ++ pos (tens P Q) :: l) ; exists l9 ;
                 list_simpl ; split...
            ** exists (l8 ++ pos (tens P Q) :: nil) ; exists l9 ;
                 list_simpl ; split...
            ** exists l8 ; exists (l0 ++ pos (tens P Q) :: l3') ;
                 list_simpl ; split...
         ++ assert (Permutation (pos P :: l4 ++ pos P' :: l0)
                                (pos P :: pos P' :: l4 ++ l0))
              as HP' by perm_solve.
            apply IHpi1 in HP'.
            destruct HP' as (N & l6 & l7 & Heq' & Htop).
            exists N.
            symmetry in HP.
            list_simpl in HP.
            apply Permutation_cons_app_inv in HP.
            rewrite app_assoc in HP.
            rewrite Heq' in HP.
            list_simpl in HP.
            apply Permutation_vs_elt_inv in HP.
            destruct HP as (l8 & l9 & Heq'').
            destruct l8 ; inversion Heq''.
            dichot_app_exec H2 ; 
              [ | destruct l1 ; inversion H4 ; list_simpl in H4 ] ; subst.
            ** exists (l2' ++ pos (tens P Q) :: l) ; exists l9 ;
                 list_simpl ; split...
            ** exists (l8 ++ pos (tens P Q) :: nil) ; exists l9 ;
                 list_simpl ; split...
            ** exists l8 ; exists (l1 ++ pos (tens P Q) :: l3') ;
                 list_simpl ; split...
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_vs_cons_inv in HP'.
  destruct HP' as (l2 & l3 & Heq).
  destruct l2 ; inversion Heq.
  destruct l2 ; inversion H1 ; subst.
  rewrite 2 app_comm_cons in HP.
  apply Permutation_cons_app_inv in HP.
  apply (Permutation_cons_app _ _ (neg M)) in HP.
  apply (Permutation_cons_app _ _ (neg N)) in HP.
  list_simpl in HP.
  apply IHpi in HP.
  destruct HP as (N' & l0 & l1 & Heq' & Htop).
  dichot_elt_app_exec Heq' ; subst.
  + destruct l4 ; inversion Heq'1 ; subst.
    * exists (parr N N') ; exists l2 ; exists l1 ; list_simpl ; split...
      apply par_rs...
    * exists N' ; exists (l2 ++ neg (parr N M) :: l4) ; exists l1 ;
        list_simpl ; split...
  + destruct l5 ; inversion Heq'1 ; subst.
    * exists (parr N' M) ; exists l0 ; exists l3 ; list_simpl ; split...
      apply par_ls...
    * exists N' ; exists l0 ; exists (l5 ++ neg (parr N M) :: l3) ;
        list_simpl ; split...
- symmetry in HP.
  apply Permutation_vs_cons_inv in HP.
  destruct HP as (l2 & l3 & Heq).
  destruct l2 ; inversion Heq.
  destruct l2 ; inversion H1 ; subst.
  exists top ; exists l2 ; exists l3 ; split...
  apply top_s.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_vs_cons_inv in HP'.
  destruct HP' as (l2 & l3 & Heq).
  destruct l2 ; inversion Heq ; subst.
  + apply Permutation_cons_inv in HP.
    apply (@Permutation_cons _ _ (pos P) eq_refl) in HP.
    apply IHpi in HP.
    destruct HP as (N & l0 & l1 & Heq' & Htop) ; subst.
    exists N ; exists l0 ; exists l1 ; split...
  + destruct l2 ; inversion H1 ; subst.
    * rewrite <- (app_nil_l (pos (aplus _ _) :: l3)) in HP.
      rewrite app_comm_cons in HP.
      apply Permutation_cons_app_inv in HP.
      apply (@Permutation_cons _ _ (pos P) eq_refl) in HP.
      list_simpl in HP.
      apply IHpi in HP.
      destruct HP as (N & l0 & l1 & Heq' & Htop) ; subst.
      exists N ; exists l0 ; exists l1 ; split...
    * rewrite 2 app_comm_cons in HP.
      apply Permutation_cons_app_inv in HP.
      apply (Permutation_cons_app _ _ (pos P)) in HP.
      list_simpl in HP.
      apply IHpi in HP.
      destruct HP as (N' & l0 & l1 & Heq' & Htop).
      dichot_elt_app_exec Heq' ; subst.
      -- exists N' ; exists (l2 ++ pos (aplus P Q) :: l4) ; exists l1 ;
           list_simpl ; split...
      -- destruct l5 ; inversion Heq'1 ; subst.
         exists N' ; exists l0 ; exists (l5 ++ pos (aplus P Q) :: l3) ;
           list_simpl ; split...
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_vs_cons_inv in HP'.
  destruct HP' as (l2 & l3 & Heq).
  destruct l2 ; inversion Heq ; subst.
  + apply Permutation_cons_inv in HP.
    apply (@Permutation_cons _ _ (pos P) eq_refl) in HP.
    apply IHpi in HP.
    destruct HP as (N & l0 & l1 & Heq' & Htop) ; subst.
    exists N ; exists l0 ; exists l1 ; split...
  + destruct l2 ; inversion H1 ; subst.
    * rewrite <- (app_nil_l (pos (aplus _ _) :: l3)) in HP.
      rewrite app_comm_cons in HP.
      apply Permutation_cons_app_inv in HP.
      apply (@Permutation_cons _ _ (pos P) eq_refl) in HP.
      list_simpl in HP.
      apply IHpi in HP.
      destruct HP as (N & l0 & l1 & Heq' & Htop) ; subst.
      exists N ; exists l0 ; exists l1 ; split...
    * rewrite 2 app_comm_cons in HP.
      apply Permutation_cons_app_inv in HP.
      apply (Permutation_cons_app _ _ (pos P)) in HP.
      list_simpl in HP.
      apply IHpi in HP.
      destruct HP as (N' & l0 & l1 & Heq' & Htop).
      dichot_elt_app_exec Heq' ; subst.
      -- exists N' ; exists (l2 ++ pos (aplus Q P) :: l4) ; exists l1 ;
           list_simpl ; split...
      -- destruct l5 ; inversion Heq'1 ; subst.
         exists N' ; exists l0 ; exists (l5 ++ pos (aplus Q P) :: l3) ;
           list_simpl ; split...
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_vs_cons_inv in HP'.
  destruct HP' as (l2 & l3 & Heq).
  destruct l2 ; inversion Heq.
  destruct l2 ; inversion H1 ; subst.
  rewrite 2 app_comm_cons in HP.
  apply Permutation_cons_app_inv in HP.
  assert (HP1 := (Permutation_cons_app _ _ (neg N) HP)).
  assert (HP2 := (Permutation_cons_app _ _ (neg M) HP)).
  list_simpl in HP1 ; apply IHpi1 in HP1.
  list_simpl in HP2 ; apply IHpi2 in HP2.
  destruct HP1 as (N' & l0 & l1 & Heq' & Htop).
  destruct HP2 as (M' & l0' & l1' & Heq'' & Htop').
  dichot_elt_app_exec Heq' ; subst.
  + exists N' ; exists (l2 ++ neg (awith N M) :: l4) ; exists l1 ;
      list_simpl ; split...
  + destruct l5 ; inversion Heq'1 ; subst.
    * list_simpl in Heq''.
      dichot_elt_app_exec Heq'' ; subst.
      -- exists M' ; exists (l0 ++ neg (awith N' M) :: l2) ; exists l1' ;
           list_simpl ; split...
      -- destruct l3 ; inversion Heq''1 ; subst.
         ++ exists (awith N' M') ; exists l0' ; exists l1' ;
              list_simpl ; split...
            apply with_s...
         ++ exists M' ; exists l0' ; exists (l3 ++ neg (awith N' M) :: l1) ;
              list_simpl ; split...
    * exists N' ; exists l0 ; exists (l5 ++ neg (awith N M) :: l3) ;
        list_simpl ; split...
- exfalso.
  assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_vs_cons_inv in HP'.
  destruct HP' as (l2 & l3 & Heq).
  destruct l2 ; inversion Heq ; subst.
  + apply Permutation_cons_inv in HP.
    apply Permutation_vs_cons_inv in HP.
    destruct HP as (l2 & l3 & Heq').
    symmetry in Heq'.
    decomp_map Heq'.
    discriminate Heq'3.
  + destruct l2 ; inversion H1 ; subst.
    * rewrite <- (app_nil_l (pos (oc _) :: l3)) in HP.
      rewrite app_comm_cons in HP.
      apply Permutation_cons_app_inv in HP.
      apply Permutation_vs_cons_inv in HP.
      destruct HP as (l2' & l3' & Heq').
      symmetry in Heq'.
      decomp_map Heq'.
      discriminate Heq'3.
    * rewrite 2 app_comm_cons in HP.
      apply Permutation_cons_app_inv in HP.
      apply Permutation_vs_cons_inv in HP.
      destruct HP as (l2' & l3' & Heq').
      symmetry in Heq'.
      decomp_map Heq'.
      discriminate Heq'3.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_vs_cons_inv in HP'.
  destruct HP' as (l2 & l3 & Heq).
  destruct l2 ; inversion Heq.
  destruct l2 ; inversion H1 ; subst.
  rewrite 2 app_comm_cons in HP.
  apply Permutation_cons_app_inv in HP.
  apply (Permutation_cons_app _ _ (pos P)) in HP.
  list_simpl in HP.
  apply IHpi in HP.
  destruct HP as (N' & l0 & l1 & Heq' & Htop).
  dichot_elt_app_exec Heq' ; subst.
  + exists N' ; exists (l2 ++ neg (wn P) :: l4) ; exists l1 ;
      list_simpl ; split...
  + destruct l5 ; inversion Heq'1 ; subst.
    exists N' ; exists l0 ; exists (l5 ++ neg (wn P) :: l3) ;
      list_simpl ; split...
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_vs_cons_inv in HP'.
  destruct HP' as (l2 & l3 & Heq).
  destruct l2 ; inversion Heq.
  destruct l2 ; inversion H1 ; subst.
  rewrite 2 app_comm_cons in HP.
  apply Permutation_cons_app_inv in HP.
  list_simpl in HP.
  apply IHpi in HP.
  destruct HP as (N & l0 & l1 & Heq' & Htop).
  exists N.
  dichot_elt_app_exec Heq' ; subst.
  + exists l0 ; exists (l4 ++ neg (wn P) :: l3) ; list_simpl ; split...
  + exists (l2 ++ neg (wn P) :: l5) ; exists l1 ; list_simpl ; split...
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_vs_cons_inv in HP'.
  destruct HP' as (l2 & l3 & Heq).
  destruct l2 ; inversion Heq.
  destruct l2 ; inversion H1 ; subst.
  rewrite 2 app_comm_cons in HP.
  apply Permutation_cons_app_inv in HP.
  apply (Permutation_cons_app _ _ (neg (wn P))) in HP.
  apply (Permutation_cons_app _ _ (neg (wn P))) in HP.
  list_simpl in HP.
  apply IHpi in HP.
  destruct HP as (N' & l0 & l1 & Heq' & Htop).
  dichot_elt_app_exec Heq' ; subst.
  + destruct l4 ; inversion Heq'1 ; subst.
    * inversion Htop.
    * exists N' ; exists (l2 ++ neg (wn P) :: l4) ; exists l1 ;
        list_simpl ; split...
  + destruct l5 ; inversion Heq'1 ; subst.
    * inversion Htop.
    * exists N' ; exists l0 ; exists (l5 ++ neg (wn P) :: l3) ;
        list_simpl ; split...
Qed.

Theorem llpol_is_ll_polsequent : forall l,
  llpol l -> polsequent l -> llpol_ps polsequent l.
Proof with try eassumption ; try reflexivity.
intros l pi.
induction pi ; intros Hpol.
- constructor.
  right.
  exists (covar X :: nil) ; exists (var X).
  apply perm_swap.
- eapply ex_ps_r...
  apply IHpi.
  destruct Hpol as [ (l0 & Heq) | (l0 & P & HP) ] ; subst.
  + apply Permutation_map_inv in H.
    destruct H as (l & Heq & _) ; subst.
    left ; eexists...
  + assert (HP' := HP).
    apply Permutation_vs_cons_inv in HP'.
    destruct HP' as (l3 & l4 & Heq) ; subst.
    symmetry in HP.
    apply Permutation_cons_app_inv in HP.
    symmetry in HP.
    apply Permutation_map_inv in HP.
    destruct HP as (l & Heq & HP).
    decomp_map Heq ; subst.
    right ; exists (l5 ++ l6) ; exists P ; perm_solve.
- constructor.
  right ; exists nil ; exists one...
- constructor...
  apply IHpi.
  eapply polsequent_neg_rem...
- apply polsequent_pos_rem in Hpol.
  destruct Hpol as [ l' Heq ].
  decomp_map Heq ; subst.
  constructor...
  + right ; exists (l0 ++ l3) ; exists (tens P Q) ; perm_solve.
  + apply IHpi1.
    right ; exists l0 ; exists P ; perm_solve.
  + apply IHpi2.
    right ; exists l3 ; exists Q ; perm_solve.
- constructor...
  apply IHpi.
  apply polsequent_neg_add.
  apply polsequent_neg_add.
  eapply polsequent_neg_rem...
- constructor...
- assert (Hpol' := Hpol).
  apply polsequent_pos_rem in Hpol'.
  destruct Hpol' as [ l' Heq ] ; subst.
  constructor...
  apply IHpi.
  right ; exists l' ; exists P ; perm_solve.
- assert (Hpol' := Hpol).
  apply polsequent_pos_rem in Hpol'.
  destruct Hpol' as [ l' Heq ] ; subst.
  apply plus_ps_r2...
  apply IHpi.
  right ; exists l' ; exists P ; perm_solve.
- constructor...
  + apply IHpi1.
    apply polsequent_neg_add.
    eapply polsequent_neg_rem...
  + apply IHpi2.
    apply polsequent_neg_add.
    eapply polsequent_neg_rem...
- constructor...
  apply IHpi.
  left ; exists (N :: map wn l)...
- destruct Hpol as [ (l0 & Heq) | (l0 & Q & HP) ] ; subst.
  + apply de_ps_r.
    * left ; rewrite Heq ; eexists...
    * apply IHpi...
      destruct l0 ; inversion Heq ; subst.
      right ; exists l0 ; exists P...
  + assert (HP' := HP).
    apply Permutation_vs_cons_inv in HP'.
    destruct HP' as (l2 & l3 & Heq).
    destruct l2 ; inversion Heq ; subst.
    assert (pi' := pi).
    apply bipos_top_surf with _ P Q (l2 ++ l3) in pi' ; [ | perm_solve ].
    destruct pi' as (N & l & l' & Heq' & Htop).
    apply (ex_r _ (pos P :: pos Q :: l2 ++ l3)) in pi ; [ | perm_solve ].
    rewrite Heq' in pi.
    apply (ex_r _ (neg N :: pos P :: pos Q :: l ++ l')) in pi ; [ | perm_solve ].
    eapply top_imp_top_surf_ps in Htop.
    * apply (ex_ps_r _ (neg N :: neg (wn P) :: pos Q :: l ++ l'))...
      -- right ; eexists ; eexists...
      -- transitivity (neg (wn P) :: pos Q :: l2 ++ l3) ;
           [ rewrite Heq' | ] ; perm_solve.
    * apply (polsequent_neg_rem N).
      right ; exists l0 ; exists Q.
      etransitivity ; [ | apply HP ].
      transitivity (neg (wn P) :: pos Q :: l2 ++ l3) ;
        [ rewrite Heq' | ] ; perm_solve.
- apply wk_ps_r...
  apply IHpi.
  eapply polsequent_neg_rem...
- apply co_ps_r...
  apply IHpi.
  apply polsequent_neg_add...
Qed.

(** [llpol] with [top] rule constrained to at most one positive formula. *)
Inductive llpolt : list formula -> Prop :=
| ax_rt : forall X, llpolt (neg (covar X) :: pos (var X) :: nil)
| ex_rt : forall l1 l2, llpolt l1 ->
               Permutation l1 l2 -> llpolt l2
| one_rt : llpolt (pos one :: nil)
| bot_rt : forall l, llpolt l -> llpolt (neg bot :: l)
| tens_rt : forall P Q l1 l2,
               llpolt (pos P :: l1) -> llpolt (pos Q :: l2) ->
               llpolt (pos (tens P Q) :: l1 ++ l2)
| parr_rt : forall N M l,
               llpolt (neg N :: neg M :: l) ->
               llpolt (neg (parr N M) :: l)
| top_rt : forall l, polsequent l -> llpolt (neg top :: l)
| plus_rt1 : forall P Q l, llpolt (pos P :: l) ->
               llpolt (pos (aplus P Q) :: l)
| plus_rt2 : forall P Q l, llpolt (pos P :: l) ->
               llpolt (pos (aplus Q P) :: l)
| with_rt : forall N M l,
               llpolt (neg N :: l) -> llpolt (neg M :: l) ->
               llpolt (neg (awith N M) :: l)
| oc_rt : forall N l,
               llpolt (neg N :: map neg (map wn l)) ->
               llpolt (pos (oc N) :: map neg (map wn l))
| de_rt : forall P l,
               llpolt (pos P :: l) -> llpolt (neg (wn P) :: l)
| wk_rt : forall P l,
               llpolt l -> llpolt (neg (wn P) :: l)
| co_rt : forall P l,
               llpolt (neg (wn P) :: neg (wn P) :: l) ->
               llpolt (neg (wn P) :: l).

(** For polarized sequents [llpol] corresponds to [top] rule with at most one positive formula. *)
Theorem llpol_llpolt : forall l, (polsequent l /\ llpol l) <-> llpolt l.
Proof with try eassumption ; try reflexivity.
intros l ; split.
- intros [ Hpol pi ].
  apply llpol_is_ll_polsequent in pi...
  clear Hpol ; induction pi ; try (now constructor).
  + eapply ex_rt...
  + apply top_rt.
    eapply polsequent_neg_rem...
- intros pi.
  induction pi ; (split ; [ | try (now constructor) ]) ;
    try (destruct IHpi as [Hpol pi']) ;
    try (destruct IHpi1 as [Hpol1 pi1']) ;
    try (destruct IHpi2 as [Hpol2 pi2'])...
  + right ; exists (covar X :: nil) ; exists (var X) ; perm_solve.
  + destruct Hpol.
    * destruct H0 as [l0 H0] ; subst.
      symmetry in H.
      apply Permutation_map_inv in H.
      destruct H as (l3 & Heq & HP) ; subst.
      left ; exists l3...
    * destruct H0 as (l0 & P & H0) ; subst.
      assert (HP := H0).
      apply Permutation_vs_cons_inv in H0.
      destruct H0 as (l3 & l4 & Heq) ; subst.
      symmetry in HP.
      apply Permutation_cons_app_inv in HP.
      right ; exists l0 ; exists P ; perm_solve.
  + eapply ex_r...
  + right ; exists nil ; exists one ; perm_solve.
  + apply polsequent_neg_add...
  + apply polsequent_pos_rem in Hpol1.
    destruct Hpol1 as [l1' Heq] ; subst.
    apply polsequent_pos_rem in Hpol2.
    destruct Hpol2 as [l2' Heq] ; subst.
    right ; exists (l1' ++ l2') ; exists (tens P Q) ; perm_solve.
  + apply polsequent_neg_rem in Hpol.
    apply polsequent_neg_rem in Hpol.
    eapply polsequent_neg_add...
  + eapply polsequent_neg_add...
  + apply polsequent_pos_rem in Hpol.
    destruct Hpol as [l' Heq] ; subst.
    right ; exists l' ; exists (aplus P Q) ; perm_solve.
  + apply polsequent_pos_rem in Hpol.
    destruct Hpol as [l' Heq] ; subst.
    right ; exists l' ; exists (aplus Q P) ; perm_solve.
  + apply polsequent_neg_rem in Hpol1.
    eapply polsequent_neg_add...
  + right ; exists (map wn l) ; exists (oc N) ; perm_solve.
  + apply polsequent_pos_rem in Hpol.
    destruct Hpol as [l' Heq] ; subst.
    left ; exists (wn P :: l')...
  + eapply polsequent_neg_add...
  + eapply polsequent_neg_rem...
Qed.



