(* llpol example file for yalla library *)

(** * Example of a concrete use of the yalla library: polarized linear logic LLpol *)

From Coq Require Import CMorphisms.
From OLlibs Require Import funtheory dectype List_more
                           Permutation_Type Permutation_Type_more Permutation_Type_solve.


(** ** 0. load the [ll] library *)

From Yalla Require ll_cut.


Section Atoms.

Context {atom : DecType}.

(** ** 1. define formulas *)

(** Positive and negative formulas *)
Inductive pformula :=
| var : atom -> pformula
| one : pformula
| tens : pformula -> pformula -> pformula
| zero : pformula
| aplus : pformula -> pformula -> pformula
| oc : nformula -> pformula
with nformula :=
| covar : atom -> nformula
| bot : nformula
| parr : nformula -> nformula -> nformula
| top : nformula
| awith : nformula -> nformula -> nformula
| wn : pformula -> nformula.

Scheme pform_ind := Induction for pformula Sort Prop
  with nform_ind := Induction for nformula Sort Prop.
Combined Scheme polform_ind from pform_ind, nform_ind.

Inductive formula :=
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
apply polform_ind ; intros ; cbn ;
  try rewrite H ; try rewrite H0 ; try reflexivity.
Qed.

Definition dual A :=
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

Definition llpol2ll A :=
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
- cbn in Heq.
  f_equal.
  apply billpol2ll_inj...
- destruct p ; destruct n ; inversion Heq.
- destruct p ; destruct n ; inversion Heq.
- cbn in Heq.
  f_equal.
  apply billpol2ll_inj...
Qed.

Lemma billpol2ll_dual :
     (forall P, formulas.dual (pllpol2ll P) = nllpol2ll (pdual P))
  /\ (forall N, formulas.dual (nllpol2ll N) = pllpol2ll (ndual N)).
Proof.
apply polform_ind ; intros ; cbn ;
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
cbn ; rewrite IHl...
Qed.

Lemma llpol2ll_map_wn_inv : forall l1 l2,
  map formulas.wn l1 = map llpol2ll l2 ->
    { l2' : _ & l2 = map neg (map wn l2') & l1 = map pllpol2ll l2' }.
Proof with try assumption ; try reflexivity.
induction l1 ; intros l2 Heq ;
  destruct l2 ; inversion Heq...
- exists nil ; split...
- apply IHl1 in H1.
  destruct f ; inversion H0 ;
    [ destruct p | destruct n ] ; inversion H0 ; subst.
  destruct H1 as [l2' Heq1 H1] ; subst.
  exists (p :: l2') ; split...
Qed.


(** ** 3. define proofs *)

(** [ll] restricted to polarized formulas *)
Inductive llpol : list formula -> Type :=
| ax_r : forall X, llpol (neg (covar X) :: pos (var X) :: nil)
| ex_r : forall l1 l2, llpol l1 ->
              Permutation_Type l1 l2 -> llpol l2
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

Instance llpol_perm : Proper ((@Permutation_Type _) ==> Basics.arrow) llpol.
Proof.
intros l1 l2 HP pi.
eapply ex_r ; eassumption.
Qed.


(** ** 4. characterize corresponding [ll] fragment *)

(*
Lemma llpol2ll_dec : forall A,
  {B | A = llpol2ll B} + (forall B, A = llpol2ll B -> False).
Proof with try reflexivity.
induction A.
- left ; exists (pos (var a))...
- left ; exists (neg (covar a))...
- left ; exists (pos one)...
- left ; exists (neg bot)...
- destruct IHA1 as [[[p1 | n1] Heq1] | pi1] ;
  destruct IHA2 as [[[p2 | n2] Heq2] | pi2] ; subst ;
    try now
      (right ; intros B Heq ; 
       destruct B ; try destruct p ; try destruct n ; inversion Heq ;
       (try now (destruct n1 ; destruct p1 ; inversion H0)) ;
       (try now (destruct n2 ; destruct p2 ; inversion H1)) ;
       (try now (destruct n2 ; destruct p3 ; inversion H1))).
  + left ; exists (pos (tens p1 p2))...
  + right ; intros B Heq.
    destruct B ; try destruct n ; try destruct p ; inversion Heq ; subst.
    apply (pi2 (pos p3))...
  + right ; intros B Heq.
    destruct B ; try destruct n ; try destruct p ; inversion Heq ; subst.
    apply (pi1 (pos p1))...
  + right ; intros B Heq.
    destruct B ; try destruct n ; try destruct p ; inversion Heq ; subst.
    apply (pi2 (pos p2))...
- destruct IHA1 as [[[p1 | n1] Heq1] | pi1] ;
  destruct IHA2 as [[[p2 | n2] Heq2] | pi2] ; subst ;
    try now
      (right ; intros B Heq ; 
       destruct B ; try destruct p ; try destruct n ; inversion Heq ;
       (try now (destruct n1 ; destruct p1 ; inversion H0)) ;
       (try now (destruct n2 ; destruct p2 ; inversion H1)) ;
       (try now (destruct p2 ; destruct n3 ; inversion H1))).
  + left ; exists (neg (parr n1 n2))...
  + right ; intros B Heq.
    destruct B ; try destruct n ; try destruct p ; inversion Heq ; subst.
    apply (pi2 (neg n3))...
  + right ; intros B Heq.
    destruct B ; try destruct n ; try destruct p ; inversion Heq ; subst.
    apply (pi1 (neg n1))...
  + right ; intros B Heq.
    destruct B ; try destruct n ; try destruct p ; inversion Heq ; subst.
    apply (pi2 (neg n2))...
- left ; exists (pos zero)...
- left ; exists (neg top)...
- destruct IHA1 as [[[p1 | n1] Heq1] | pi1] ;
  destruct IHA2 as [[[p2 | n2] Heq2] | pi2] ; subst ;
    try now
      (right ; intros B Heq ; 
       destruct B ; try destruct p ; try destruct n ; inversion Heq ;
       (try now (destruct n1 ; destruct p1 ; inversion H0)) ;
       (try now (destruct n2 ; destruct p2 ; inversion H1)) ;
       (try now (destruct n2 ; destruct p3 ; inversion H1))).
  + left ; exists (pos (aplus p1 p2))...
  + right ; intros B Heq.
    destruct B ; try destruct n ; try destruct p ; inversion Heq ; subst.
    apply (pi2 (pos p3))...
  + right ; intros B Heq.
    destruct B ; try destruct n ; try destruct p ; inversion Heq ; subst.
    apply (pi1 (pos p1))...
  + right ; intros B Heq.
    destruct B ; try destruct n ; try destruct p ; inversion Heq ; subst.
    apply (pi2 (pos p2))...
- destruct IHA1 as [[[p1 | n1] Heq1] | pi1] ;
  destruct IHA2 as [[[p2 | n2] Heq2] | pi2] ; subst ;
    try now
      (right ; intros B Heq ; 
       destruct B ; try destruct p ; try destruct n ; inversion Heq ;
       (try now (destruct n1 ; destruct p1 ; inversion H0)) ;
       (try now (destruct n2 ; destruct p2 ; inversion H1)) ;
       (try now (destruct p2 ; destruct n3 ; inversion H1))).
  + left ; exists (neg (awith n1 n2))...
  + right ; intros B Heq.
    destruct B ; try destruct n ; try destruct p ; inversion Heq ; subst.
    apply (pi2 (neg n3))...
  + right ; intros B Heq.
    destruct B ; try destruct n ; try destruct p ; inversion Heq ; subst.
    apply (pi1 (neg n1))...
  + right ; intros B Heq.
    destruct B ; try destruct n ; try destruct p ; inversion Heq ; subst.
    apply (pi2 (neg n2))...
- destruct IHA as [[[p | n] Heq] | pi] ; subst.
  + right ; intros B Heq.
    destruct B ; try destruct p0 ; try destruct n ;
      destruct p ; inversion Heq.
  + left ; exists (pos (oc n))...
  + right ; intros B Heq.
    destruct B ; try destruct p ; inversion Heq ; subst...
    * apply (pi (neg n))...
    * destruct n ; inversion H0.
- destruct IHA as [[[p | n] Heq] | pi] ; subst.
  + left ; exists (neg (wn p))...
  + right ; intros B Heq.
    destruct B ; try destruct n0 ; try destruct p ;
      destruct n ; inversion Heq.
  + right ; intros B Heq.
    destruct B ; try destruct n ; inversion Heq ; subst...
    * destruct p ; inversion H0.
    * apply (pi (pos p))...
Qed.

Definition llpol_fragment A :=
match (llpol2ll_dec A) with
| inl _ => true
| inr _ => false
end.

Lemma llpol_is_fragment : ll_prop.fragment llpol_fragment.
Proof with try reflexivity.
intros A HfA B Hsf.
induction Hsf ;
unfold llpol_fragment in HfA ;
(destruct (llpol2ll_dec A) ;
  [ destruct s as [A' Heq] ; subst ;
    unfold llpol_fragment ;
    destruct (llpol2ll_dec (llpol2ll A')) ;
    [ | exfalso ; eapply f ]
  | ])...
- inversion HfA.
- destruct (llpol2ll_dec (formulas.tens B C)) ; try now inversion HfA.
  destruct s as [B' Heq].
  destruct B' ; [ destruct p | destruct n ] ; inversion Heq ; subst.
  apply IHHsf.
  unfold llpol_fragment ; destruct (llpol2ll_dec (pllpol2ll p1)) ;
    [ | exfalso ; apply (f0 (pos p1)) ]...
- destruct (llpol2ll_dec (formulas.tens C B)) ; try now inversion HfA.
  destruct s as [B' Heq].
  destruct B' ; [ destruct p | destruct n ] ; inversion Heq ; subst.
  apply IHHsf.
  unfold llpol_fragment ; destruct (llpol2ll_dec (pllpol2ll p2)) ;
    [ | exfalso ; apply (f0 (pos p2)) ]...
- destruct (llpol2ll_dec (formulas.parr B C)) ; try now inversion HfA.
  destruct s as [B' Heq].
  destruct B' ; [ destruct p | destruct n ] ; inversion Heq ; subst.
  apply IHHsf.
  unfold llpol_fragment ; destruct (llpol2ll_dec (nllpol2ll n1)) ;
    [ | exfalso ; apply (f0 (neg n1)) ]...
- destruct (llpol2ll_dec (formulas.parr C B)) ; try now inversion HfA.
  destruct s as [B' Heq].
  destruct B' ; [ destruct p | destruct n ] ; inversion Heq ; subst.
  apply IHHsf.
  unfold llpol_fragment ; destruct (llpol2ll_dec (nllpol2ll n2)) ;
    [ | exfalso ; apply (f0 (neg n2)) ]...
- destruct (llpol2ll_dec (formulas.aplus B C)) ; try now inversion HfA.
  destruct s as [B' Heq].
  destruct B' ; [ destruct p | destruct n ] ; inversion Heq ; subst.
  apply IHHsf.
  unfold llpol_fragment ; destruct (llpol2ll_dec (pllpol2ll p1)) ;
    [ | exfalso ; apply (f0 (pos p1)) ]...
- destruct (llpol2ll_dec (formulas.aplus C B)) ; try now inversion HfA.
  destruct s as [B' Heq].
  destruct B' ; [ destruct p | destruct n ] ; inversion Heq ; subst.
  apply IHHsf.
  unfold llpol_fragment ; destruct (llpol2ll_dec (pllpol2ll p2)) ;
    [ | exfalso ; apply (f0 (pos p2)) ]...
- destruct (llpol2ll_dec (formulas.awith B C)) ; try now inversion HfA.
  destruct s as [B' Heq].
  destruct B' ; [ destruct p | destruct n ] ; inversion Heq ; subst.
  apply IHHsf.
  unfold llpol_fragment ; destruct (llpol2ll_dec (nllpol2ll n1)) ;
    [ | exfalso ; apply (f0 (neg n1)) ]...
- destruct (llpol2ll_dec (formulas.awith C B)) ; try now inversion HfA.
  destruct s as [B' Heq].
  destruct B' ; [ destruct p | destruct n ] ; inversion Heq ; subst.
  apply IHHsf.
  unfold llpol_fragment ; destruct (llpol2ll_dec (nllpol2ll n2)) ;
    [ | exfalso ; apply (f0 (neg n2)) ]...
- destruct (llpol2ll_dec (formulas.oc B)) ; try now inversion HfA.
  destruct s as [B' Heq].
  destruct B' ; [ destruct p | destruct n ] ; inversion Heq ; subst.
  apply IHHsf.
  unfold llpol_fragment ; destruct (llpol2ll_dec (nllpol2ll n)) ;
    [ | exfalso ; apply (f0 (neg n)) ]...
- destruct (llpol2ll_dec (formulas.wn B)) ; try now inversion HfA.
  destruct s as [B' Heq].
  destruct B' ; [ destruct p | destruct n ] ; inversion Heq ; subst.
  apply IHHsf.
  unfold llpol_fragment ; destruct (llpol2ll_dec (pllpol2ll p)) ;
    [ | exfalso ; apply (f0 (pos p)) ]...
Qed.
*)

(** cut / axioms / pmix / permutation *)
Definition pfrag_mell := @ll_def.mk_pfrag atom  false ll_def.NoAxioms (fun x => false) true.
(*                                        atoms cut   axioms               pmix        perm  *)


(** ** 5. prove equivalence of proof predicates *)

Lemma llpol2llpolfrag : forall l, llpol l ->
  ll_def.ll pfrag_mell (map llpol2ll l).
Proof with try eassumption ; try reflexivity.
intros l pi ; induction pi ; try now (constructor ; intuition).
- eapply ll_def.ex_r...
  apply Permutation_Type_map...
- eapply ll_def.ex_r.
  + apply (ll_def.tens_r IHpi1 IHpi2).
  + cbn ; Permutation_Type_solve.
- cbn ; rewrite ? map_app.
  rewrite llpol2ll_map_wn.
  apply ll_def.oc_r.
  rewrite <- llpol2ll_map_wn...
Qed.

Lemma llpolfrag2llpol : forall l,
  ll_def.ll pfrag_mell (map llpol2ll l) -> llpol l.
Proof with try reflexivity.
intros l pi.
remember (map llpol2ll l) as l0.
revert l Heql0 ; induction pi ; intros l' Heql0 ; subst ;
  try (now (destruct l' ; inversion Heql0 ;
            destruct f ; inversion H0 ;
              [ destruct p | destruct n ] ; inversion H0 ; subst ;
            constructor ;
            apply IHpi ; reflexivity)) ;
  try (now inversion f).
- symmetry in Heql0; decomp_map_inf Heql0 ; subst.
  destruct l1 ; inversion Heql4.
  destruct x ; inversion Heql2 ;
    [ destruct p | destruct n ] ; inversion Heql2.
  destruct x0 ; inversion Heql0 ;
    [destruct p | destruct n ] ; inversion Heql0.
  subst ; subst.
  apply ax_r.
- cbn in p.
  apply Permutation_Type_map_inv in p.
  destruct p as [l'' Heq HP] ; subst.
  symmetry in HP.
  eapply ex_r ; [ | eassumption ].
  apply IHpi...
- symmetry in Heql0; decomp_map_inf Heql0 ; subst; symmetry in Heql0.
  cbn in Heql0 ; apply llpol2ll_map_wn_inv in Heql0 ;
    destruct Heql0 as [l Heq1 Heq2] ; subst.
  apply Permutation_Type_map_inv in p ; destruct p as [l' Heq HP] ; subst.
  apply (Permutation_Type_map wn) in HP.
  apply (Permutation_Type_map neg) in HP.
  eapply ex_r.
  + rewrite <- llpol2ll_map_wn in IHpi.
    apply IHpi ; rewrite <- ? map_app...
  + Permutation_Type_solve.
- destruct l' ; inversion Heql0.
  destruct f ; inversion H0 ;
    [ destruct p | destruct n ] ; inversion H0.
  destruct l' ; inversion H1.
  apply one_r.
- symmetry in Heql0; decomp_map_inf Heql0 ; subst.
  destruct x ; inversion Heql2 ;
    [ destruct p | destruct n ] ; inversion Heql2 ; subst.
  eapply ex_r.
  apply tens_r.
  + apply IHpi1...
  + apply IHpi2...
  + Permutation_Type_solve.
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
  destruct H1 as [l'' Heq1 Heq2] ; subst.
  apply oc_r.
  apply IHpi.
  cbn ; rewrite llpol2ll_map_wn...
- inversion a.
Qed.


(** ** 6. import properties *)

(** *** axiom expansion *)

Lemma ax_gen_r : forall A, llpol (dual A :: A :: nil).
Proof.
intro A.
eapply ex_r ; [ | apply Permutation_Type_swap ].
apply llpolfrag2llpol.
cbn ; rewrite <- llpol2ll_dual.
apply ll_def.ax_exp.
Qed.

(** *** cut admissibility *)

Lemma cut_r : forall A l1 l2, 
  llpol (A :: l1) -> llpol (dual A :: l2) -> llpol (l1 ++ l2).
Proof with try eassumption.
intros A l1 l2 pi1 pi2.
apply llpol2llpolfrag in pi1 ; cbn in pi1.
apply llpol2llpolfrag in pi2 ; cbn in pi2.
eapply ll_cut.cut_r_axfree in pi1 ;
  [ | | rewrite llpol2ll_dual ]...
- rewrite <- map_app in pi1.
  eapply llpolfrag2llpol...
- intros Hax ; inversion Hax.
Qed.


(** ** 7. specific developments *)

Lemma par_inv : forall N M l,
  llpol (neg (parr N M) :: l) -> llpol (neg N :: neg M :: l).
Proof with try assumption.
intros N M l pi.
rewrite <- (app_nil_l l).
eapply ex_r ; [ | apply Permutation_Type_swap ].
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
- cbn ; rewrite 2 (proj2 bipndual)...
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
- cbn ; rewrite 2 (proj2 bipndual)...
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
- cbn ; rewrite 2 (proj2 bipndual)...
Qed.

(** Polarized sequents are those with at most one positive formula. *)
Definition polsequent l :=
 sum { l0 | l = map neg l0 }
     { lP & Permutation_Type l (pos (snd lP) :: (map neg (fst lP))) }.

Lemma uniq_polsequent : forall l1 l2 P1 P2,
  Permutation_Type (pos P1 :: l1) (pos P2 :: map neg l2) ->
    { l1' : _ & l1 = map neg l1' & prod (P1 = P2) (Permutation_Type l1' l2) }.
Proof with try eassumption ; try reflexivity.
intros l1 l2 P1 P2 HP.
assert (HP' := HP).
symmetry in HP'.
apply Permutation_Type_vs_cons_inv in HP'.
destruct HP' as ((l' & l'') & Heq) ; cbn in Heq.
destruct l' ; inversion Heq ; subst.
- apply Permutation_Type_cons_inv in HP.
  apply Permutation_Type_map_inv in HP.
  destruct HP as [l Heq' HP'] ; subst.
  exists l ; [ | split ]...
  symmetry...
- exfalso; decomp_map H1; inversion H1.
Qed.

(*
Lemma polsequent_app : forall l1 l2,
  polsequent (l1 ++ l2) ->
    { l & sum (prod (l2 = map neg l) (polsequent l1))
              (prod (l1 = map neg l) (polsequent l2)) }.
Proof with try eassumption ; try reflexivity.
intros l1 l2 Hi.
assert (Hi' := Hi).
destruct Hi' as [ (l0 & Hi') | ((l0 & P) & Hi') ].
- decomp_map_inf Hi' ; subst.
  exists l4 ; left ; split...
  left ; eexists...
- assert (Hi'' := Hi').
  apply Permutation_Type_vs_cons_inv in Hi'.
  destruct Hi' as ((l3 & l4) & Heq).
  dichot_elt_app_inf_exec Heq ; subst.
  + list_simpl in Hi''.
    symmetry in Hi''.
    apply Permutation_Type_cons_app_inv in Hi''.
    symmetry in Hi''.
    apply Permutation_Type_map_inv in Hi''.
    destruct Hi'' as [l' Heq HP].
    decomp_map_inf Heq ; subst.
    eexists ; left ; split...
    right ; exists (l5 ++ l7, P) ; Permutation_Type_solve.
  + symmetry in Hi''.
    rewrite app_assoc in Hi''.
    apply Permutation_Type_cons_app_inv in Hi''.
    list_simpl in Hi''.
    symmetry in Hi''.
    apply Permutation_Type_map_inv in Hi''.
    destruct Hi'' as [l' Heq HP].
    decomp_map_inf Heq ; subst.
    eexists ; right ; split...
    right ; exists (l7 ++ l8, P) ; Permutation_Type_solve.
Qed.
*)

Lemma polsequent_neg_add : forall N l,
  polsequent l -> polsequent (neg N :: l).
Proof.
intros N l [ (l0 & Heq) | ((l0 & P) & HP) ] ; subst.
- left ; exists (N :: l0) ; reflexivity.
- assert (HP' := HP).
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as ((l2 & l3) & Heq) ; subst.
  symmetry in HP.
  apply Permutation_Type_cons_app_inv in HP.
  symmetry in HP.
  apply Permutation_Type_map_inv in HP.
  destruct HP as [l1 Heq' _].
  list_simpl in Heq' ; symmetry in Heq'; decomp_map_inf Heq' ; subst.
  right ; exists (N :: l4 ++ l5, P) ; Permutation_Type_solve.
Qed.

Lemma polsequent_neg_rem : forall N l,
  polsequent (neg N :: l) -> polsequent l.
Proof.
intros N l Hpol.
destruct Hpol as [ (l0 & Heq) | ((l0 & P) & HP) ] ; subst.
- destruct l0 ; inversion Heq.
  left ; exists l0 ; reflexivity.
- assert (HP' := HP).
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as ((l2 & l3) & Heq).
  destruct l2 ; inversion Heq ; subst.
  symmetry in HP.
  rewrite app_comm_cons in HP.
  apply Permutation_Type_cons_app_inv in HP.
  symmetry in HP.
  apply Permutation_Type_map_inv in HP.
  destruct HP as [l1 Heq' _].
  list_simpl in Heq' ; symmetry in Heq'; decomp_map_inf Heq' ; subst.
  right ; exists (l5 ++ l6, P) ; Permutation_Type_solve.
Qed.

Lemma polsequent_pos_rem : forall P l,
  polsequent (pos P :: l) -> { l' | l = map neg l' }.
Proof with try reflexivity.
intros P l Hs.
destruct Hs as [ (l0 & Heq) | ((l0 & Q) & HP) ].
- symmetry in Heq; decomp_map_inf Heq ; inversion Heq1.
- assert (HP' := HP).
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as ((l' & l'') & Heq).
  destruct l' ; inversion Heq ; subst.
  + apply Permutation_Type_cons_inv in HP.
    apply Permutation_Type_map_inv in HP...
    destruct HP as [l' Heq' HP'] ; subst.
    eexists...
  + exfalso.
    symmetry in HP.
    rewrite app_comm_cons in HP.
    apply Permutation_Type_cons_app_inv in HP.
    symmetry in HP.
    apply Permutation_Type_map_inv in HP.
    destruct HP as [l2 Heq' HP'].
    destruct l2 ; inversion Heq'.
Qed.

Lemma polsequent_dec : forall l, polsequent l + (polsequent l -> False).
Proof.
induction l.
- left ; left ; exists nil ; reflexivity.
- destruct a.
  + destruct IHl.
    * destruct p0.
      -- destruct s as [l0 Heq] ; subst.
         left ; right ; exists (l0,p) ; reflexivity.
      -- destruct s as [[l0 P] HP].
         right ; intros Hps ; destruct Hps.
         ++ destruct s as [l1 Heq] ; subst.
            destruct l1 ; inversion Heq.
         ++ destruct s as [[l1 Q] HP'].
            apply uniq_polsequent in HP'.
            destruct HP' as [l' Heq [Heq' HP']] ; subst.
            cbn in HP ; symmetry in HP.
            apply Permutation_Type_map_inv in HP.
            destruct HP as [l Heq _].
            destruct l ; inversion Heq.
    * right ; intros Hps.
      apply f.
      left ; eapply polsequent_pos_rem ; eassumption.
  + destruct IHl.
    * left.
      apply polsequent_neg_add ; assumption.
    * right ; intros Hps.
      apply f ; clear f.
      eapply polsequent_neg_rem ; eassumption.
Qed.

Definition polsequent_bool l :=
match polsequent_dec l with
| inl _ => true
| inr _ => false
end.

Lemma true_polsequent : forall l,
  polsequent_bool l = true -> polsequent l.
Proof.
intros l Hb ; unfold polsequent_bool in Hb ; destruct (polsequent_dec l).
- assumption.
- inversion Hb.
Qed.

Lemma polsequent_true : forall l,
  polsequent l -> polsequent_bool l = true.
Proof.
intros l Hp.
unfold polsequent_bool ; destruct (polsequent_dec l) ; intuition.
Qed.

(** Version of [llpol] with a predicate parameter for constraining sequents inside proofs. *)
Inductive llpol_ps PS : list formula -> Type :=
| ax_ps_r : forall X, is_true (PS (neg (covar X) :: pos (var X) :: nil)) ->
                llpol_ps PS (neg (covar X) :: pos (var X) :: nil)
| ex_ps_r : forall l1 l2, is_true (PS l2) ->
                llpol_ps PS l1 -> Permutation_Type l1 l2 -> llpol_ps PS l2
| one_ps_r : is_true (PS (pos one :: nil)) -> llpol_ps PS (pos one :: nil)
| bot_ps_r : forall l, is_true (PS (neg bot :: l)) ->
                llpol_ps PS l -> llpol_ps PS (neg bot :: l)
| tens_ps_r : forall P Q l1 l2, is_true (PS (pos (tens P Q) :: l1 ++ l2)) ->
                llpol_ps PS (pos P :: l1) -> llpol_ps PS (pos Q :: l2) ->
                llpol_ps PS (pos (tens P Q) :: l1 ++ l2)
| parr_ps_r : forall N M l, is_true (PS (neg (parr N M) :: l)) ->
                llpol_ps PS (neg N :: neg M :: l) ->
                llpol_ps PS (neg (parr N M) :: l)
| top_ps_r : forall l, is_true (PS (neg top :: l)) -> llpol_ps PS (neg top :: l)
| plus_ps_r1 : forall P Q l, is_true (PS (pos (aplus P Q) :: l)) ->
                llpol_ps PS (pos P :: l)-> llpol_ps PS (pos (aplus P Q) :: l)
| plus_ps_r2 : forall P Q l, is_true (PS (pos (aplus Q P) :: l)) ->
                llpol_ps PS (pos P :: l)-> llpol_ps PS (pos (aplus Q P) :: l)
| with_ps_r : forall N M l, is_true (PS (neg (awith N M) :: l)) ->
                llpol_ps PS (neg N :: l) -> llpol_ps PS (neg M :: l) ->
                llpol_ps PS (neg (awith N M) :: l)
| oc_ps_r : forall N l, is_true (PS (pos (oc N) :: map neg (map wn l))) ->
                llpol_ps PS (neg N :: map neg (map wn l)) ->
                llpol_ps PS (pos (oc N) :: map neg (map wn l))
| de_ps_r : forall P l, is_true (PS (neg (wn P) :: l)) ->
                llpol_ps PS (pos P :: l) -> llpol_ps PS (neg (wn P) :: l)
| wk_ps_r : forall P l, is_true (PS (neg (wn P) :: l)) ->
                llpol_ps PS l -> llpol_ps PS (neg (wn P) :: l)
| co_ps_r : forall P l, is_true (PS (neg (wn P) :: l)) ->
                llpol_ps PS (neg (wn P) :: neg (wn P) :: l) ->
                llpol_ps PS (neg (wn P) :: l).

Lemma llpol_ps_is_ps : forall l PS, llpol_ps PS l -> is_true (PS l).
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

Lemma llpol_is_llpol_ps : forall l, llpol l -> llpol_ps (fun _ => true) l.
Proof with try eassumption ; try reflexivity.
intros l pi.
induction pi ;
  try (constructor ; try assumption ; try reflexivity ; fail).
eapply ex_ps_r...
Qed.

(** Formulas with [top] below negative connectives only. Such formulas are equivalent to [top]. *)
Inductive top_surf : nformula -> Type :=
| top_s : top_surf top
| par_ls : forall N M, top_surf N -> top_surf (parr N M)
| par_rs : forall N M, top_surf N -> top_surf (parr M N)
| with_s : forall N M, top_surf N -> top_surf M -> top_surf (awith N M).

Lemma top_imp_top_surf_ps : forall N l,
  top_surf N -> polsequent l -> llpol_ps polsequent_bool (neg N :: l).
Proof with try eassumption.
induction N; intros l Ht Hp; inversion_clear Ht as [ | ? ? Ht' | ? ? Ht' | ? ? Ht' Ht'' ].
- eapply IHN1 in Ht'.
  + apply parr_ps_r...
    apply llpol_ps_is_ps in Ht'.
    apply true_polsequent in Ht'.
    apply polsequent_true.
    apply polsequent_neg_add.
    eapply polsequent_neg_rem.
    eapply polsequent_neg_rem...
  + apply polsequent_neg_add...
- eapply IHN2 in Ht'.
  apply parr_ps_r ; [ | eapply ex_ps_r ; [ | | now apply Permutation_Type_swap ]]...
  + apply llpol_ps_is_ps in Ht'.
    apply true_polsequent in Ht'.
    apply polsequent_true.
    apply polsequent_neg_add.
    eapply polsequent_neg_rem.
    eapply polsequent_neg_rem...
  + apply llpol_ps_is_ps in Ht'.
    apply true_polsequent in Ht'.
    apply polsequent_true.
    apply polsequent_neg_add.
    apply polsequent_neg_add.
    eapply polsequent_neg_rem.
    eapply polsequent_neg_rem...
  + apply polsequent_neg_add...
- apply top_ps_r.
    apply polsequent_true.
  apply polsequent_neg_add...
- apply with_ps_r.
  + apply polsequent_true.
    apply polsequent_neg_add...
  + eapply IHN1 in Ht'...
  + eapply IHN2 in Ht''...
Qed.

Lemma bipos_top_surf : forall l,
  llpol l -> forall P Q l', Permutation_Type l (pos P :: pos Q :: l') ->
    { Nll : _ & l' = fst (snd Nll) ++ neg (fst Nll) :: snd (snd Nll)
              & top_surf (fst Nll) }.
Proof with try assumption ; try reflexivity.
intros l pi ; induction pi ; intros P' Q' l' HP.
- apply Permutation_Type_length_2_inv in HP.
  destruct HP as [ HP | HP ] ; inversion HP.
- eapply IHpi.
  etransitivity ; [ apply p | apply HP ].
- apply Permutation_Type_length_1_inv in HP.
  inversion HP.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as ((l2 & l3) & Heq).
  destruct l2 ; inversion Heq.
  destruct l2 ; inversion H1 ; subst.
  rewrite 2 app_comm_cons in HP.
  apply Permutation_Type_cons_app_inv in HP.
  list_simpl in HP.
  apply IHpi in HP.
  destruct HP as [(N & l0 & l1) Heq' Htop].
  dichot_elt_app_inf_exec Heq' ; subst.
  + exists (N,(l0,l4 ++ neg bot :: l3)) ; list_simpl...
  + exists (N,(l2 ++ neg bot :: l5,l1)) ; list_simpl...
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as ((l2' & l3') & Heq).
  destruct l2' ; inversion Heq ; subst.
  + apply Permutation_Type_cons_inv in HP.
    assert (HP' := HP).
    apply Permutation_Type_vs_cons_inv in HP'.
    destruct HP' as ((l3 & l4) & Heq').
    rewrite Heq' in HP.
    symmetry in HP.
    apply Permutation_Type_cons_app_inv in HP.
    dichot_app_inf_exec Heq' ;
      [ | destruct l0 ; inversion Heq'1 ; list_simpl in Heq'1 ] ;
        cbn in Heq'0 ; subst.
    * list_simpl in HP.
      assert (Permutation_Type (pos Q :: l ++ pos Q' :: l4)
                               (pos Q :: pos Q' :: l ++ l4))
        as HP' by Permutation_Type_solve.
      apply IHpi2 in HP'.
      destruct HP' as [(N & l5 & l6) Heq' Htop] ; cbn in Heq'.
      rewrite Heq' in HP.
      rewrite app_assoc in HP.
      apply Permutation_Type_vs_elt_inv in HP.
      destruct HP as ((l7 & l8) & Heq'').
      exists (N,(l7,l8))...
    * destruct (IHpi2 Q Q' l4 (Permutation_Type_refl _))
        as [(N & l5 & l6) Heq' Htop] ; subst ; cbn in HP.
      rewrite app_assoc in HP.
      apply Permutation_Type_vs_elt_inv in HP.
      destruct HP as ((l7 & l8) & Heq'').
      exists (N,(l7,l8))...
    * assert (Permutation_Type (pos P :: l3 ++ pos Q' :: l0)
                               (pos P :: pos Q' :: l3 ++ l0))
        as HP' by Permutation_Type_solve.
      apply IHpi1 in HP'.
      destruct HP' as [(N & l5 & l6) Heq' Htop] ;
        cbn in Heq' ; cbn in HP.
      rewrite app_assoc in HP.
      rewrite Heq' in HP.
      list_simpl in HP.
      apply Permutation_Type_vs_elt_inv in HP.
      destruct HP as ((l7 & l8) & Heq'').
      exists (N,(l7,l8))...
  + destruct l2' ; inversion H1 ; subst.
    * rewrite <- (app_nil_l (pos (tens _ _) :: l3')) in HP.
      rewrite (app_comm_cons _ _ (pos P')) in HP.
      apply Permutation_Type_cons_app_inv in HP.
      list_simpl in HP.
      destruct (Permutation_Type_vs_cons_inv HP) as [(l4, l5) Heq'].
      dichot_app_inf_exec Heq' ;
        [ | destruct l0 ; inversion Heq'1 ; list_simpl in Heq'1 ] ;
          cbn in Heq'1 ; cbn in HP ; subst.
      -- symmetry in HP.
         rewrite app_assoc in HP.
         apply Permutation_Type_cons_app_inv in HP.
         list_simpl in HP.
         assert (Permutation_Type (pos Q :: l ++ pos P' :: l5)
                                  (pos Q :: pos P' :: l ++ l5))
           as HP' by Permutation_Type_solve.
         apply IHpi2 in HP'.
         destruct HP' as [(N & l6 & l7) Heq' Htop].
         rewrite Heq' in HP.
         rewrite app_assoc in HP.
         apply Permutation_Type_vs_elt_inv in HP.
         destruct HP as ((l8 & l9) & Heq'').
         exists (N,(l8,l9))...
      -- destruct (IHpi2 Q P' l5 (Permutation_Type_refl _))
           as [(N & l6 & l7) Heq' Htop] ; subst.
         list_simpl in HP.
         symmetry in HP.
         apply Permutation_Type_cons_app_inv in HP.
         rewrite app_assoc in HP.
         apply Permutation_Type_vs_elt_inv in HP.
         destruct HP as ((l8 & l9) & Heq'').
         exists (N,(l8,l9))...
      -- assert (Permutation_Type (pos P :: l4 ++ pos P' :: l0)
                                  (pos P :: pos P' :: l4 ++ l0))
           as HP' by Permutation_Type_solve.
         apply IHpi1 in HP'.
         destruct HP' as [(N & l6 & l7) Heq' Htop].
         list_simpl in HP.
         symmetry in HP.
         apply Permutation_Type_cons_app_inv in HP.
         rewrite app_assoc in HP.
         rewrite Heq' in HP.
         list_simpl in HP.
         apply Permutation_Type_vs_elt_inv in HP.
         destruct HP as ((l8 & l9) & Heq'').
         exists (N,(l8,l9))...
    * rewrite 2 (app_comm_cons _ (pos (tens _ _) :: l3')) in HP.
      apply Permutation_Type_cons_app_inv in HP.
      list_simpl in HP.
      destruct (Permutation_Type_vs_cons_inv HP) as [(l4, l5) Heq'].
      dichot_app_inf_exec Heq' ; subst.
      -- assert (Permutation_Type (pos Q :: l ++ pos P' :: l5)
                                  (pos Q :: pos P' :: l ++ l5))
           as HP' by Permutation_Type_solve.
         apply IHpi2 in HP'.
         destruct HP' as [(N & l6 & l7) Heq' Htop].
         symmetry in HP.
         rewrite app_assoc in HP.
         apply Permutation_Type_cons_app_inv in HP.
         list_simpl in HP.
         rewrite Heq' in HP.
         rewrite app_assoc in HP.
         apply Permutation_Type_vs_elt_inv in HP.
         destruct HP as ((l8 & l9) & Heq'').
         destruct l8 ; inversion Heq''.
         dichot_app_inf_exec H2 ;
           [ | destruct l2 ; inversion Heq'' ; list_simpl in H4 ] ; subst.
         ++ exists (N,(l2' ++ pos (tens P Q) :: l0,l9)) ; list_simpl...
         ++ exists (N,(l8 ++ pos (tens P Q) :: nil,l9)) ; list_simpl...
         ++ inversion H4 ; subst.
            exists (N,(l8,l2 ++ pos (tens P Q) :: l3')) ; list_simpl...
      -- destruct l0 ; inversion Heq'1 ; list_simpl in Heq'1 ; subst.
         ++ destruct (IHpi2 Q P' l5 (Permutation_Type_refl _))
              as [(N & l6 & l7) Heq' Htop] ; subst.
            list_simpl in HP.
            symmetry in HP.
            apply Permutation_Type_cons_app_inv in HP.
            rewrite app_assoc in HP.
            apply Permutation_Type_vs_elt_inv in HP.
            destruct HP as ((l8 & l9) & Heq'').
            destruct l8 ; inversion Heq'' ; subst.
            dichot_app_inf_exec H3 ;
              [ | destruct l0 ; inversion H2 ; list_simpl in H2 ] ; subst.
            ** exists (N,(l2' ++ pos (tens P Q) :: l,l9)) ; list_simpl...
            ** exists (N,(l8 ++ pos (tens P Q) :: nil,l9)) ; list_simpl...
            ** exists (N,(l8,l0 ++ pos (tens P Q) :: l3')) ; list_simpl...
         ++ assert (Permutation_Type (pos P :: l4 ++ pos P' :: l0)
                                     (pos P :: pos P' :: l4 ++ l0))
              as HP' by Permutation_Type_solve.
            apply IHpi1 in HP'.
            destruct HP' as [(N & l6 & l7) Heq' Htop].
            symmetry in HP.
            list_simpl in HP.
            apply Permutation_Type_cons_app_inv in HP.
            rewrite app_assoc in HP.
            rewrite Heq' in HP.
            list_simpl in HP.
            apply Permutation_Type_vs_elt_inv in HP.
            destruct HP as ((l8 & l9) & Heq'').
            destruct l8 ; inversion Heq''.
            dichot_app_inf_exec H2 ; 
              [ | destruct l1 ; inversion H4 ; list_simpl in H4 ] ; subst.
            ** exists (N,(l2' ++ pos (tens P Q) :: l,l9)) ; list_simpl...
            ** exists (N,(l8 ++ pos (tens P Q) :: nil,l9)) ; list_simpl...
            ** exists (N,(l8,l1 ++ pos (tens P Q) :: l3')) ; list_simpl...
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as ((l2 & l3) & Heq).
  destruct l2 ; inversion Heq.
  destruct l2 ; inversion H1 ; subst.
  rewrite 2 app_comm_cons in HP.
  apply Permutation_Type_cons_app_inv in HP.
  apply (Permutation_Type_cons_app _ _ (neg M)) in HP.
  apply (Permutation_Type_cons_app _ _ (neg N)) in HP.
  list_simpl in HP.
  apply IHpi in HP.
  destruct HP as [(N' & l0 & l1) Heq' Htop].
  dichot_elt_app_inf_exec Heq' ; subst.
  + destruct l4 ; inversion Heq'1 ; subst.
    * exists (parr N N',(l2,l1)) ; list_simpl...
      apply par_rs...
    * exists (N',(l2 ++ neg (parr N M) :: l4,l1)) ; list_simpl...
  + destruct l5 ; inversion Heq'1 ; subst.
    * exists (parr N' M,(l0,l3)) ; list_simpl...
      apply par_ls...
    * exists (N',(l0,l5 ++ neg (parr N M) :: l3)) ; list_simpl...
- symmetry in HP.
  apply Permutation_Type_vs_cons_inv in HP.
  destruct HP as ((l2 & l3) & Heq).
  destruct l2 ; inversion Heq.
  destruct l2 ; inversion H1 ; subst.
  exists (top,(l2,l3))...
  apply top_s.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as ((l2 & l3) & Heq).
  destruct l2 ; inversion Heq ; subst.
  + apply Permutation_Type_cons_inv in HP.
    apply (@Permutation_Type_cons _ _ (pos P) eq_refl) in HP.
    apply IHpi in HP.
    destruct HP as [(N & l0 & l1) Heq' Htop] ; subst.
    exists (N,(l0,l1))...
  + destruct l2 ; inversion H1 ; subst.
    * rewrite <- (app_nil_l (pos (aplus _ _) :: l3)) in HP.
      rewrite app_comm_cons in HP.
      apply Permutation_Type_cons_app_inv in HP.
      apply (@Permutation_Type_cons _ _ (pos P) eq_refl) in HP.
      list_simpl in HP.
      apply IHpi in HP.
      destruct HP as [(N & l0 & l1) Heq' Htop] ; subst.
      exists (N,(l0,l1))...
    * rewrite 2 app_comm_cons in HP.
      apply Permutation_Type_cons_app_inv in HP.
      apply (Permutation_Type_cons_app _ _ (pos P)) in HP.
      list_simpl in HP.
      apply IHpi in HP.
      destruct HP as [(N' & l0 & l1) Heq' Htop].
      dichot_elt_app_inf_exec Heq' ; subst.
      -- exists (N',(l2 ++ pos (aplus P Q) :: l4,l1)) ; list_simpl...
      -- destruct l5 ; inversion Heq'1 ; subst.
         exists (N',(l0,l5 ++ pos (aplus P Q) :: l3)) ; list_simpl...
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as ((l2 & l3) & Heq).
  destruct l2 ; inversion Heq ; subst.
  + apply Permutation_Type_cons_inv in HP.
    apply (@Permutation_Type_cons _ _ (pos P) eq_refl) in HP.
    apply IHpi in HP.
    destruct HP as [(N & l0 & l1) Heq' Htop] ; subst.
    exists (N,(l0,l1))...
  + destruct l2 ; inversion H1 ; subst.
    * rewrite <- (app_nil_l (pos (aplus _ _) :: l3)) in HP.
      rewrite app_comm_cons in HP.
      apply Permutation_Type_cons_app_inv in HP.
      apply (@Permutation_Type_cons _ _ (pos P) eq_refl) in HP.
      list_simpl in HP.
      apply IHpi in HP.
      destruct HP as [(N & l0 & l1) Heq' Htop] ; subst.
      exists (N,(l0,l1))...
    * rewrite 2 app_comm_cons in HP.
      apply Permutation_Type_cons_app_inv in HP.
      apply (Permutation_Type_cons_app _ _ (pos P)) in HP.
      list_simpl in HP.
      apply IHpi in HP.
      destruct HP as [(N' & l0 & l1) Heq' Htop].
      dichot_elt_app_inf_exec Heq' ; subst.
      -- exists (N',(l2 ++ pos (aplus Q P) :: l4,l1)) ; list_simpl...
      -- destruct l5 ; inversion Heq'1 ; subst.
         exists (N',(l0,l5 ++ pos (aplus Q P) :: l3)) ; list_simpl...
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as ((l2 & l3) & Heq).
  destruct l2 ; inversion Heq.
  destruct l2 ; inversion H1 ; subst.
  rewrite 2 app_comm_cons in HP.
  apply Permutation_Type_cons_app_inv in HP.
  assert (HP1 := (Permutation_Type_cons_app _ _ (neg N) HP)).
  assert (HP2 := (Permutation_Type_cons_app _ _ (neg M) HP)).
  list_simpl in HP1 ; apply IHpi1 in HP1.
  list_simpl in HP2 ; apply IHpi2 in HP2.
  destruct HP1 as [(N' & l0 & l1) Heq' Htop].
  destruct HP2 as [(M' & l0' & l1') Heq'' Htop'].
  dichot_elt_app_inf_exec Heq' ; subst.
  + exists (N',(l2 ++ neg (awith N M) :: l4,l1)) ; list_simpl...
  + destruct l5 ; inversion Heq'1 ; subst.
    * list_simpl in Heq''.
      dichot_elt_app_inf_exec Heq'' ; subst.
      -- exists (M',(l0 ++ neg (awith N' M) :: l2,l1')) ; list_simpl...
      -- destruct l3 ; inversion Heq''1 ; subst.
         ++ exists (awith N' M',(l0',l1')) ;list_simpl...
            apply with_s...
         ++ exists (M',(l0',l3 ++ neg (awith N' M) :: l1)) ; list_simpl...
    * exists (N',(l0,l5 ++ neg (awith N M) :: l3)) ; list_simpl...
- exfalso.
  assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as ((l2 & l3) & Heq).
  destruct l2 ; inversion Heq ; subst.
  + apply Permutation_Type_cons_inv in HP.
    apply Permutation_Type_vs_cons_inv in HP.
    destruct HP as ((l2 & l3) & Heq').
    decomp_map Heq'; discriminate Heq'3.
  + destruct l2 ; inversion H1 ; subst.
    * rewrite <- (app_nil_l (pos (oc _) :: l3)) in HP.
      rewrite app_comm_cons in HP.
      apply Permutation_Type_cons_app_inv in HP.
      apply Permutation_Type_vs_cons_inv in HP.
      destruct HP as ((l2' & l3') & Heq').
      decomp_map Heq'; discriminate Heq'3.
    * rewrite 2 app_comm_cons in HP.
      apply Permutation_Type_cons_app_inv in HP.
      apply Permutation_Type_vs_cons_inv in HP.
      destruct HP as ((l2' & l3') & Heq').
      decomp_map Heq'; discriminate Heq'3.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as ((l2 & l3) & Heq).
  destruct l2 ; inversion Heq.
  destruct l2 ; inversion H1 ; subst.
  rewrite 2 app_comm_cons in HP.
  apply Permutation_Type_cons_app_inv in HP.
  apply (Permutation_Type_cons_app _ _ (pos P)) in HP.
  list_simpl in HP.
  apply IHpi in HP.
  destruct HP as [(N' & l0 & l1) Heq' Htop].
  dichot_elt_app_inf_exec Heq' ; subst.
  + exists (N',(l2 ++ neg (wn P) :: l4,l1)) ; list_simpl...
  + destruct l5 ; inversion Heq'1 ; subst.
    exists (N',(l0,l5 ++ neg (wn P) :: l3)) ; list_simpl...
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as ((l2 & l3) & Heq).
  destruct l2 ; inversion Heq.
  destruct l2 ; inversion H1 ; subst.
  rewrite 2 app_comm_cons in HP.
  apply Permutation_Type_cons_app_inv in HP.
  list_simpl in HP.
  apply IHpi in HP.
  destruct HP as [(N & l0 & l1) Heq' Htop].
  dichot_elt_app_inf_exec Heq' ; subst.
  + exists (N,(l0,l4 ++ neg (wn P) :: l3)) ; list_simpl...
  + exists (N,(l2 ++ neg (wn P) :: l5,l1)) ; list_simpl...
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as ((l2 & l3) & Heq).
  destruct l2 ; inversion Heq.
  destruct l2 ; inversion H1 ; subst.
  rewrite 2 app_comm_cons in HP.
  apply Permutation_Type_cons_app_inv in HP.
  apply (Permutation_Type_cons_app _ _ (neg (wn P))) in HP.
  apply (Permutation_Type_cons_app _ _ (neg (wn P))) in HP.
  list_simpl in HP.
  apply IHpi in HP.
  destruct HP as [(N' & l0 & l1) Heq' Htop].
  dichot_elt_app_inf_exec Heq' ; subst.
  + destruct l4 ; inversion Heq'1 ; subst.
    * inversion Htop.
    * exists (N',(l2 ++ neg (wn P) :: l4,l1)) ; list_simpl...
  + destruct l5 ; inversion Heq'1 ; subst.
    * inversion Htop.
    * exists (N',(l0,l5 ++ neg (wn P) :: l3)) ; list_simpl...
Qed.

Theorem llpol_is_ll_polsequent : forall l,
  llpol l -> polsequent l -> llpol_ps polsequent_bool l.
Proof with try eassumption ; try reflexivity.
intros l pi.
induction pi ; intros Hpol.
- constructor.
  apply polsequent_true.
  right.
  exists (covar X :: nil,var X).
  apply Permutation_Type_swap.
- eapply ex_ps_r ; [ apply polsequent_true | | ]...
  apply IHpi.
  destruct Hpol as [ (l0 & Heq) | ((l0 & P) & HP) ] ; subst.
  + apply Permutation_Type_map_inv in p.
    destruct p as [l Heq _] ; subst.
    left ; eexists...
  + assert (HP' := HP).
    apply Permutation_Type_vs_cons_inv in HP'.
    destruct HP' as ((l3 & l4) & Heq) ; subst.
    symmetry in HP.
    apply Permutation_Type_cons_app_inv in HP.
    symmetry in HP.
    apply Permutation_Type_map_inv in HP.
    destruct HP as [l Heq HP].
    symmetry in Heq; decomp_map_inf Heq ; cbn in Heq1 ; cbn in Heq2 ;
      subst ; cbn in p.
    right ; exists (l5 ++ l6,P) ; cbn ; Permutation_Type_solve.
- constructor.
  apply polsequent_true.
  right ; exists (nil,one)...
- constructor ; [ apply polsequent_true | ]...
  apply IHpi.
  eapply polsequent_neg_rem...
- apply polsequent_pos_rem in Hpol.
  destruct Hpol as [ l' Heq ].
  symmetry in Heq; decomp_map_inf Heq ; subst.
  constructor...
  + apply polsequent_true.
    right ; exists (l0 ++ l3,tens P Q) ; Permutation_Type_solve.
  + apply IHpi1.
    right ; exists (l0,P) ; Permutation_Type_solve.
  + apply IHpi2.
    right ; exists (l3,Q) ; Permutation_Type_solve.
- constructor ; [ apply polsequent_true | ]...
  apply IHpi.
  apply polsequent_neg_add.
  apply polsequent_neg_add.
  eapply polsequent_neg_rem...
- constructor ; apply polsequent_true...
- assert (Hpol' := Hpol).
  apply polsequent_pos_rem in Hpol'.
  destruct Hpol' as [ l' Heq ] ; subst.
  constructor ; [ apply polsequent_true | ]...
  apply IHpi.
  right ; exists (l',P) ; Permutation_Type_solve.
- assert (Hpol' := Hpol).
  apply polsequent_pos_rem in Hpol'.
  destruct Hpol' as [ l' Heq ] ; subst.
  apply plus_ps_r2 ; [ apply polsequent_true | ]...
  apply IHpi.
  right ; exists (l',P) ; Permutation_Type_solve.
- constructor ; [ apply polsequent_true | | ]...
  + apply IHpi1.
    apply polsequent_neg_add.
    eapply polsequent_neg_rem...
  + apply IHpi2.
    apply polsequent_neg_add.
    eapply polsequent_neg_rem...
- constructor ; [ apply polsequent_true | ]...
  apply IHpi.
  left ; exists (N :: map wn l)...
- destruct Hpol as [ (l0 & Heq) | ((l0 & Q) & HP) ] ; subst.
  + apply de_ps_r.
    * apply polsequent_true.
      left ; rewrite Heq ; eexists...
    * apply IHpi...
      destruct l0 ; inversion Heq ; subst.
      right ; exists (l0,P)...
  + destruct (Permutation_Type_vs_cons_inv HP) as [(l2, l3) Heq].
    destruct l2 ; inversion Heq ; subst.
    assert (pi' := pi).
    apply bipos_top_surf with _ P Q (l2 ++ l3) in pi' ; [ | Permutation_Type_solve ].
    destruct pi' as [(N & l & l') Heq' Htop].
    apply (ex_r _ (pos P :: pos Q :: l2 ++ l3)) in pi ; [ | Permutation_Type_solve ].
    rewrite Heq' in pi.
    apply (ex_r _ (neg N :: pos P :: pos Q :: l ++ l')) in pi ; [ | Permutation_Type_solve ].
    eapply top_imp_top_surf_ps in Htop.
    * apply (ex_ps_r _ (neg N :: neg (wn P) :: pos Q :: l ++ l'))...
      -- apply polsequent_true.
         right ; eexists...
      -- transitivity (neg (wn P) :: pos Q :: l2 ++ l3) ;
           [ rewrite Heq' | ] ; Permutation_Type_solve.
    * apply (polsequent_neg_rem N).
      right ; exists (l0,Q).
      etransitivity ; [ | apply HP ].
      transitivity (neg (wn P) :: pos Q :: l2 ++ l3) ;
        [ rewrite Heq' | ] ; Permutation_Type_solve.
- apply wk_ps_r ; [ apply polsequent_true | ]...
  apply IHpi.
  eapply polsequent_neg_rem...
- apply co_ps_r ; [ apply polsequent_true | ]...
  apply IHpi.
  apply polsequent_neg_add...
Qed.

(** [llpol] with [top] rule constrained to at most one positive formula. *)
Inductive llpolt : list formula -> Type :=
| ax_rt : forall X, llpolt (neg (covar X) :: pos (var X) :: nil)
| ex_rt : forall l1 l2, llpolt l1 ->
               Permutation_Type l1 l2 -> llpolt l2
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

Instance llpolt_perm : Proper ((@Permutation_Type _) ==> Basics.arrow) llpolt.
Proof.
intros l1 l2 HP pi.
eapply ex_rt ; eassumption.
Qed.

(** For polarized sequents [llpol] corresponds to [top] rule with at most one positive formula. *)
Theorem llpol_llpolt : forall l, polsequent l -> llpol l -> llpolt l.
Proof with try eassumption ; try reflexivity.
intros l Hpol pi.
apply llpol_is_ll_polsequent in pi...
clear Hpol ; induction pi ; try (now constructor).
- eapply ex_rt...
- apply true_polsequent in i.
  apply top_rt.
  eapply polsequent_neg_rem...
Qed.

Theorem llpolt_llpol : forall l, llpolt l -> (polsequent l * llpol l).
Proof with try eassumption ; try reflexivity.
intros l pi.
induction pi ; split ;
  try (destruct IHpi as [Hpol pi']) ;
  try (destruct IHpi1 as [Hpol1 pi1']) ;
  try (destruct IHpi2 as [Hpol2 pi2']) ;
  try now constructor...
- right ; exists (covar X :: nil,var X) ; Permutation_Type_solve.
- destruct Hpol.
  + destruct s as [l0 H0] ; subst.
    symmetry in p.
    apply Permutation_Type_map_inv in p.
    destruct p as [l3 Heq HP] ; subst.
    left ; exists l3...
  + destruct s as ((l0 & P) & H0) ; subst.
    assert (HP := H0).
    apply Permutation_Type_vs_cons_inv in H0.
    destruct H0 as ((l3 & l4) & Heq) ; subst.
    symmetry in HP.
    apply Permutation_Type_cons_app_inv in HP.
    right ; exists (l0,P) ; Permutation_Type_solve.
- eapply ex_r...
- right ; exists (nil,one) ; Permutation_Type_solve.
- apply polsequent_neg_add...
- apply polsequent_pos_rem in Hpol1.
  destruct Hpol1 as [l1' Heq] ; subst.
  apply polsequent_pos_rem in Hpol2.
  destruct Hpol2 as [l2' Heq] ; subst.
  right ; exists (l1' ++ l2',tens P Q) ; Permutation_Type_solve.
- apply polsequent_neg_rem in Hpol.
  apply polsequent_neg_rem in Hpol.
  eapply polsequent_neg_add...
- eapply polsequent_neg_add...
- apply polsequent_pos_rem in Hpol.
  destruct Hpol as [l' Heq] ; subst.
  right ; exists (l',aplus P Q) ; Permutation_Type_solve.
- apply polsequent_pos_rem in Hpol.
  destruct Hpol as [l' Heq] ; subst.
  right ; exists (l',aplus Q P) ; Permutation_Type_solve.
- apply polsequent_neg_rem in Hpol1.
  eapply polsequent_neg_add...
- right ; exists (map wn l,oc N) ; Permutation_Type_solve.
- apply polsequent_pos_rem in Hpol.
  destruct Hpol as [l' Heq] ; subst.
  left ; exists (wn P :: l')...
- eapply polsequent_neg_add...
- eapply polsequent_neg_rem...
Qed.

End Atoms.
