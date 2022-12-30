(* llpol example file for yalla library *)

(** * Example of a concrete use of the yalla library: polarized linear logic LLpol *)

From Coq Require Import CMorphisms.
From OLlibs Require Import funtheory dectype List_more Permutation_Type Permutation_Type_more.


(** ** 0. load the [ll] library *)

From Yalla Require ll_cut.

Set Implicit Arguments.


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
Proof. apply polform_ind; intros; cbn; try rewrite H; try rewrite H0; reflexivity. Qed.

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
Proof.
apply polform_ind;
  try (intros P Heq; destruct P; inversion Heq; reflexivity);
  try (intros A IH1 B IH2 C Heq; destruct C; inversion Heq;
       apply IH1 in H0; apply IH2 in H1; subst; reflexivity).
- intros x P Heq; destruct P; inversion Heq; reflexivity.
- intros N IH M Heq; destruct M; inversion Heq.
  apply IH in H0; subst; reflexivity.
- intros x N Heq; destruct N; inversion Heq; reflexivity.
- intros P IH Q Heq; destruct Q; inversion Heq.
  apply IH in H0; subst; reflexivity.
Qed.

Lemma llpol2ll_inj : injective llpol2ll.
Proof.
intros A B Heq; destruct A, B.
- cbn in Heq; f_equal.
  apply billpol2ll_inj; assumption.
- destruct p, n; inversion Heq.
- destruct p, n; inversion Heq.
- cbn in Heq; f_equal.
  apply billpol2ll_inj; assumption.
Qed.

Lemma billpol2ll_dual :
     (forall P, formulas.dual (pllpol2ll P) = nllpol2ll (pdual P))
  /\ (forall N, formulas.dual (nllpol2ll N) = pllpol2ll (ndual N)).
Proof. apply polform_ind; intros; cbn; rewrite ? H, ? H0; reflexivity. Qed.

Lemma llpol2ll_dual A : formulas.dual (llpol2ll A) = llpol2ll (dual A).
Proof. destruct A; apply billpol2ll_dual. Qed.

Lemma bidual A : dual (dual A) = A.
Proof. apply llpol2ll_inj; rewrite <- 2 llpol2ll_dual, formulas.bidual; reflexivity. Qed.

Lemma llpol2ll_map_wn l: map llpol2ll (map neg (map wn l)) = map formulas.wn (map pllpol2ll l).
Proof. induction l as [ | a l IHl ]; [ | cbn; rewrite IHl ]; reflexivity. Qed.

Lemma llpol2ll_map_wn_inv l1 l2 : map formulas.wn l1 = map llpol2ll l2 ->
  { l2' & l2 = map neg (map wn l2') & l1 = map pllpol2ll l2' }.
Proof.
induction l1 in l2 |- *; intros Heq; destruct l2; inversion Heq.
- exists nil; reflexivity.
- apply IHl1 in H1.
  destruct f; inversion H0; [ destruct p | destruct n ]; inversion H0; subst.
  destruct H1 as [l2' -> ->].
  exists (p :: l2'); reflexivity.
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

Instance llpol_perm : Proper ((@Permutation_Type _) ==> arrow) llpol.
Proof. intros l1 l2 HP pi; eapply ex_r; eassumption. Qed.


(** ** 4. characterize corresponding [ll] fragment *)

(*
From Yalla Require ll_prop.

Lemma llpol2ll_dec A : {B | A = llpol2ll B} + (forall B, A = llpol2ll B -> False).
Proof.
induction A.
- left; eexists (pos (var _)); reflexivity.
- left; eexists (neg (covar _)); reflexivity.
- left; exists (pos one); reflexivity.
- left; exists (neg bot); reflexivity.
- destruct IHA1 as [[[p1 | n1] Heq1] | pi1];
  destruct IHA2 as [[[p2 | n2] Heq2] | pi2]; subst;
    try now
      (right; intros B Heq; destruct B;
       try destruct p; try destruct n; inversion Heq;
       (try now (destruct n1; destruct p1; inversion H0));
       (try now (destruct n2; destruct p2; inversion H1));
       (try now (destruct n2; destruct p3; inversion H1))).
  + left; exists (pos (tens p1 p2)); reflexivity.
  + right; intros B Heq.
    destruct B; try destruct n; try destruct p; inversion Heq; subst.
    apply (pi2 (pos p3)); reflexivity.
  + right; intros B Heq.
    destruct B; try destruct n; try destruct p; inversion Heq; subst.
    apply (pi1 (pos p1)); reflexivity.
  + right; intros B Heq.
    destruct B; try destruct n; try destruct p; inversion Heq; subst.
    apply (pi2 (pos p2)); reflexivity.
- destruct IHA1 as [[[p1 | n1] Heq1] | pi1];
  destruct IHA2 as [[[p2 | n2] Heq2] | pi2]; subst;
    try now
      (right; intros B Heq; destruct B;
       try destruct p; try destruct n; inversion Heq;
       (try now (destruct n1; destruct p1; inversion H0));
       (try now (destruct n2; destruct p2; inversion H1));
       (try now (destruct p2; destruct n3; inversion H1))).
  + left; exists (neg (parr n1 n2)); reflexivity.
  + right; intros B Heq.
    destruct B; try destruct n; try destruct p; inversion Heq; subst.
    apply (pi2 (neg n3)); reflexivity.
  + right; intros B Heq.
    destruct B; try destruct n; try destruct p; inversion Heq; subst.
    apply (pi1 (neg n1)); reflexivity.
  + right; intros B Heq.
    destruct B; try destruct n; try destruct p; inversion Heq; subst.
    apply (pi2 (neg n2)); reflexivity.
- left; exists (pos zero); reflexivity.
- left; exists (neg top); reflexivity.
- destruct IHA1 as [[[p1 | n1] Heq1] | pi1];
  destruct IHA2 as [[[p2 | n2] Heq2] | pi2]; subst;
    try now
      (right; intros B Heq; destruct B;
       try destruct p; try destruct n; inversion Heq;
       (try now (destruct n1; destruct p1; inversion H0));
       (try now (destruct n2; destruct p2; inversion H1));
       (try now (destruct n2; destruct p3; inversion H1))).
  + left; exists (pos (aplus p1 p2)); reflexivity.
  + right; intros B Heq.
    destruct B; try destruct n; try destruct p; inversion Heq; subst.
    apply (pi2 (pos p3)); reflexivity.
  + right; intros B Heq.
    destruct B; try destruct n; try destruct p; inversion Heq; subst.
    apply (pi1 (pos p1)); reflexivity.
  + right; intros B Heq.
    destruct B; try destruct n; try destruct p; inversion Heq; subst.
    apply (pi2 (pos p2)); reflexivity.
- destruct IHA1 as [[[p1 | n1] Heq1] | pi1];
  destruct IHA2 as [[[p2 | n2] Heq2] | pi2]; subst;
    try now
      (right; intros B Heq; destruct B;
       try destruct p; try destruct n; inversion Heq;
       (try now (destruct n1; destruct p1; inversion H0));
       (try now (destruct n2; destruct p2; inversion H1));
       (try now (destruct p2; destruct n3; inversion H1))).
  + left; exists (neg (awith n1 n2)); reflexivity.
  + right; intros B Heq.
    destruct B; try destruct n; try destruct p; inversion Heq; subst.
    apply (pi2 (neg n3)); reflexivity.
  + right; intros B Heq.
    destruct B; try destruct n; try destruct p; inversion Heq; subst.
    apply (pi1 (neg n1)); reflexivity.
  + right; intros B Heq.
    destruct B; try destruct n; try destruct p; inversion Heq; subst.
    apply (pi2 (neg n2)); reflexivity.
- destruct IHA as [[[p | n] Heq] | pi]; subst.
  + right; intros B Heq.
    destruct B; try destruct p0; try destruct n; destruct p; inversion Heq.
  + left; exists (pos (oc n)); reflexivity.
  + right; intros B Heq.
    destruct B; try destruct p; inversion Heq; subst.
    * apply (pi (neg n)); reflexivity.
    * destruct n; inversion H0.
- destruct IHA as [[[p | n] Heq] | pi]; subst.
  + left; exists (neg (wn p)); reflexivity.
  + right; intros B Heq.
    destruct B; try destruct n0; try destruct p; destruct n; inversion Heq.
  + right; intros B Heq.
    destruct B; try destruct n; inversion Heq; subst.
    * destruct p; inversion H0.
    * apply (pi (pos p)); reflexivity.
Qed.

Definition llpol_fragment A :=
match (llpol2ll_dec A) with
| inl _ => true
| inr _ => false
end.

Lemma llpol_is_fragment : ll_prop.fragmentb llpol_fragment.
Proof.
intros A HfA B Hsf.
induction Hsf;
unfold llpol_fragment in HfA;
(destruct (llpol2ll_dec A);
  [ destruct s as [A' Heq]; subst;
    unfold llpol_fragment; destruct (llpol2ll_dec (llpol2ll A'));
    [ | exfalso; eapply f ]
  | ]); try reflexivity.
- inversion HfA.
- destruct (llpol2ll_dec (formulas.tens B C)); try now inversion HfA.
  destruct s as [B' Heq].
  destruct B'; [ destruct p | destruct n ]; inversion Heq; subst.
  apply IHHsf.
  unfold llpol_fragment; destruct (llpol2ll_dec (pllpol2ll p1));
    [ | exfalso; apply (f0 (pos p1)) ]; reflexivity.
- destruct (llpol2ll_dec (formulas.tens C B)); try now inversion HfA.
  destruct s as [B' Heq].
  destruct B'; [ destruct p | destruct n ]; inversion Heq; subst.
  apply IHHsf.
  unfold llpol_fragment; destruct (llpol2ll_dec (pllpol2ll p2));
    [ | exfalso ; apply (f0 (pos p2)) ]; reflexivity.
- destruct (llpol2ll_dec (formulas.parr B C)); try now inversion HfA.
  destruct s as [B' Heq].
  destruct B'; [ destruct p | destruct n ]; inversion Heq; subst.
  apply IHHsf.
  unfold llpol_fragment; destruct (llpol2ll_dec (nllpol2ll n1));
    [ | exfalso; apply (f0 (neg n1)) ]; reflexivity.
- destruct (llpol2ll_dec (formulas.parr C B)); try now inversion HfA.
  destruct s as [B' Heq].
  destruct B'; [ destruct p | destruct n ]; inversion Heq; subst.
  apply IHHsf.
  unfold llpol_fragment ; destruct (llpol2ll_dec (nllpol2ll n2));
    [ | exfalso ; apply (f0 (neg n2)) ]; reflexivity.
- destruct (llpol2ll_dec (formulas.aplus B C)); try now inversion HfA.
  destruct s as [B' Heq].
  destruct B'; [ destruct p | destruct n ]; inversion Heq; subst.
  apply IHHsf.
  unfold llpol_fragment; destruct (llpol2ll_dec (pllpol2ll p1));
    [ | exfalso ; apply (f0 (pos p1)) ]; reflexivity.
- destruct (llpol2ll_dec (formulas.aplus C B)); try now inversion HfA.
  destruct s as [B' Heq].
  destruct B'; [ destruct p | destruct n ]; inversion Heq; subst.
  apply IHHsf.
  unfold llpol_fragment; destruct (llpol2ll_dec (pllpol2ll p2));
    [ | exfalso; apply (f0 (pos p2)) ]; reflexivity.
- destruct (llpol2ll_dec (formulas.awith B C)); try now inversion HfA.
  destruct s as [B' Heq].
  destruct B'; [ destruct p | destruct n ]; inversion Heq; subst.
  apply IHHsf.
  unfold llpol_fragment; destruct (llpol2ll_dec (nllpol2ll n1));
    [ | exfalso; apply (f0 (neg n1)) ]; reflexivity.
- destruct (llpol2ll_dec (formulas.awith C B)); try now inversion HfA.
  destruct s as [B' Heq].
  destruct B'; [ destruct p | destruct n ]; inversion Heq; subst.
  apply IHHsf.
  unfold llpol_fragment; destruct (llpol2ll_dec (nllpol2ll n2));
    [ | exfalso; apply (f0 (neg n2)) ]; reflexivity.
- destruct (llpol2ll_dec (formulas.oc B)); try now inversion HfA.
  destruct s as [B' Heq].
  destruct B'; [ destruct p | destruct n ]; inversion Heq; subst.
  apply IHHsf.
  unfold llpol_fragment; destruct (llpol2ll_dec (nllpol2ll n));
    [ | exfalso; apply (f0 (neg n)) ]; reflexivity.
- destruct (llpol2ll_dec (formulas.wn B)); try now inversion HfA.
  destruct s as [B' Heq].
  destruct B'; [ destruct p | destruct n ]; inversion Heq; subst.
  apply IHHsf.
  unfold llpol_fragment; destruct (llpol2ll_dec (pllpol2ll p));
    [ | exfalso; apply (f0 (pos p)) ]; reflexivity.
Qed.
*)

(** cut / axioms / pmix / permutation *)
Definition pfrag_mell := @ll_def.mk_pfrag atom  false ll_def.NoAxioms (fun x => false) true.
(*                                        atoms cut   axioms               pmix        perm  *)


(** ** 5. prove equivalence of proof predicates *)

Lemma llpol2llpolfrag l : llpol l -> ll_def.ll pfrag_mell (map llpol2ll l).
Proof.
intros pi; induction pi; try now (constructor; auto).
- eapply ll_def.ex_r; [ eassumption | ].
  apply Permutation_Type_map; assumption.
- eapply ll_def.ex_r.
  + cbn in IHpi1, IHpi2; apply (ll_def.tens_r IHpi1 IHpi2).
  + apply Permutation_Type_cons; [ reflexivity | ].
    fold (map llpol2ll); rewrite map_app.
    apply Permutation_Type_app_comm.
- cbn; rewrite ? map_app, llpol2ll_map_wn.
  apply ll_def.oc_r.
  rewrite <- llpol2ll_map_wn; assumption.
Qed.

Lemma llpolfrag2llpol l : ll_def.ll pfrag_mell (map llpol2ll l) -> llpol l.
Proof.
intros pi.
remember (map llpol2ll l) as l0.
revert l Heql0; induction pi; intros l' Heql0; subst;
  try (now (destruct l'; inversion Heql0;
            destruct f; inversion H0;
              [ destruct p | destruct n ]; inversion H0; subst;
            constructor;
            apply IHpi; reflexivity));
  try (now inversion f).
- symmetry in Heql0; decomp_map_inf Heql0; subst.
  destruct l1; inversion Heql4.
  destruct x; inversion Heql2; [ destruct p | destruct n ]; inversion Heql2.
  destruct x0; inversion Heql0; [destruct p | destruct n ]; inversion Heql0; subst.
  apply ax_r.
- cbn in p.
  apply Permutation_Type_map_inv in p as [l'' Heq HP]; subst.
  symmetry in HP.
  eapply ex_r; [ | eassumption ].
  apply IHpi; reflexivity.
- symmetry in Heql0; decomp_map_inf Heql0; subst; symmetry in Heql0.
  cbn in Heql0; apply llpol2ll_map_wn_inv in Heql0 as [l -> ->].
  apply Permutation_Type_map_inv in p as [l' -> HP].
  apply (Permutation_Type_map wn), (Permutation_Type_map neg) in HP.
  eapply ex_r.
  + rewrite <- llpol2ll_map_wn in IHpi.
    apply IHpi; rewrite <- ? map_app; reflexivity.
  + symmetry; apply Permutation_Type_app_head, Permutation_Type_app_tail; assumption.
- destruct l'; inversion Heql0.
  destruct f; inversion H0; [ destruct p | destruct n ]; inversion H0.
  destruct l'; inversion H1.
  apply one_r.
- symmetry in Heql0; decomp_map_inf Heql0; subst.
  destruct x; inversion Heql2; [ destruct p | destruct n ]; inversion Heql2; subst.
  eapply ex_r; [ apply tens_r | ].
  + apply IHpi1; reflexivity.
  + apply IHpi2; reflexivity.
  + apply Permutation_Type_cons, Permutation_Type_app_comm; reflexivity.
- destruct l'; inversion Heql0.
  destruct f; inversion H0 ; [ destruct p | destruct n ]; inversion H0; subst.
  apply with_r; [ apply IHpi1 | apply IHpi2 ]; reflexivity.
- destruct l'; inversion Heql0.
  destruct f; inversion H0; [destruct p | destruct n ]; inversion H0; subst.
  apply llpol2ll_map_wn_inv in H1 as [l'' -> ->].
  apply oc_r, IHpi.
  cbn; rewrite llpol2ll_map_wn; reflexivity.
- inversion a.
Qed.


(** ** 6. import properties *)

(** *** axiom expansion *)

Lemma ax_gen_r A : llpol (dual A :: A :: nil).
Proof.
eapply ex_r; [ | apply Permutation_Type_swap ].
apply llpolfrag2llpol.
cbn; rewrite <- llpol2ll_dual.
apply ll_def.ax_exp.
Qed.

(** *** cut admissibility *)

Lemma cut_r A l1 l2 : llpol (A :: l1) -> llpol (dual A :: l2) -> llpol (l1 ++ l2).
Proof.
intros pi1%llpol2llpolfrag pi2%llpol2llpolfrag.
cbn in pi1, pi2.
eapply ll_cut.cut_r_axfree in pi1; [ | | rewrite llpol2ll_dual; eassumption ].
- rewrite <- map_app in pi1.
  apply llpolfrag2llpol; assumption.
- intros Hax ; inversion Hax.
Qed.


(** ** 7. specific developments *)

Lemma par_inv N M l : llpol (neg (parr N M) :: l) -> llpol (neg N :: neg M :: l).
Proof.
intros pi.
rewrite <- (app_nil_l l).
eapply ex_r; [ | apply Permutation_Type_swap ].
rewrite 2 app_comm_cons.
eapply cut_r.
- rewrite <- (app_nil_l (neg N :: nil)), 2 app_comm_cons, <- app_comm_cons.
  apply (@tens_r (ndual M) (ndual N)).
  + change (pos (ndual M)) with (dual (neg M)).
    apply ax_gen_r.
  + change (pos (ndual N)) with (dual (neg N)).
    apply ax_gen_r.
- cbn; rewrite 2 (proj2 bipndual); assumption.
Qed.

Lemma with_inv_1 N M l : llpol (neg (awith N M) :: l) ->  llpol (neg N :: l).
Proof.
intros pi.
rewrite <- (app_nil_l l), app_comm_cons.
eapply cut_r.
- apply (@plus_r1 (ndual N) (ndual M)).
  change (pos (ndual N)) with (dual (neg N)).
  apply ax_gen_r.
- cbn; rewrite 2 (proj2 bipndual); assumption.
Qed.

Lemma with_inv_2 N M l : llpol (neg (awith M N) :: l) ->  llpol (neg N :: l).
Proof.
intros pi.
rewrite <- (app_nil_l l), app_comm_cons.
eapply cut_r.
- apply (@plus_r2 (ndual N) (ndual M)).
  change (pos (ndual N)) with (dual (neg N)).
  apply ax_gen_r.
- cbn; rewrite 2 (proj2 bipndual); assumption.
Qed.

(** Polarized sequents are those with at most one positive formula. *)
Definition polsequent l :=
  ({ l0 | l = map neg l0 } +
   { lP & Permutation_Type l (pos (snd lP) :: (map neg (fst lP))) })%type.

Lemma uniq_polsequent l1 l2 P1 P2 : Permutation_Type (pos P1 :: l1) (pos P2 :: map neg l2) ->
  { l1' & l1 = map neg l1' & ((P1 = P2) * Permutation_Type l1' l2)%type }.
Proof.
intros HP.
assert (HP' := HP).
symmetry in HP'.
apply Permutation_Type_vs_cons_inv in HP' as ((l' & l'') & Heq); cbn in Heq.
destruct l'; inversion Heq; subst.
- apply Permutation_Type_cons_inv, Permutation_Type_map_inv in HP.
  destruct HP as [l -> HP'].
  exists l; repeat split.
  symmetry; assumption.
- exfalso; decomp_map H1; inversion H1.
Qed.

(*
Lemma polsequent_app l1 l2 : polsequent (l1 ++ l2) ->
  { l & (((l2 = map neg l) * (polsequent l1)) +
         ((l1 = map neg l) * (polsequent l2)))%type }.
Proof.
intros Hi.
assert (Hi' := Hi).
destruct Hi' as [ (l0 & Hi') | ((l0 & P) & Hi') ].
- symmetry in Hi'; decomp_map_inf Hi'; subst.
  exists l4; left; repeat split.
  left; eexists; reflexivity.
- assert (Hi'' := Hi').
  apply Permutation_Type_vs_cons_inv in Hi' as ((l3 & l4) & Heq).
  dichot_elt_app_inf_exec Heq; subst.
  + list_simpl in Hi''.
    symmetry in Hi''.
    apply Permutation_Type_cons_app_inv in Hi''.
    symmetry in Hi''.
    apply Permutation_Type_map_inv in Hi'' as [l' Heq HP].
    symmetry in Heq; decomp_map_inf Heq; subst.
    eexists; left; repeat split.
    right; exists (l4 ++ l6, P); cbn; rewrite map_app.
    symmetry; apply Permutation_Type_middle.
  + symmetry in Hi''.
    rewrite app_assoc in Hi''.
    apply Permutation_Type_cons_app_inv in Hi''.
    list_simpl in Hi''.
    symmetry in Hi''.
    apply Permutation_Type_map_inv in Hi''.
    destruct Hi'' as [l' Heq HP].
    symmetry in Heq; decomp_map_inf Heq; subst.
    eexists; right; repeat split.
    right; exists (l6 ++ l7, P); cbn; rewrite map_app.
    symmetry; apply Permutation_Type_middle.
Qed.
*)

Lemma polsequent_neg_add N l : polsequent l -> polsequent (neg N :: l).
Proof.
intros [ (l0 & ->) | ((l0 & P) & HP) ].
- left; exists (N :: l0); reflexivity.
- assert (HP' := HP).
  apply Permutation_Type_vs_cons_inv in HP'.
  destruct HP' as ((l2 & l3) & ->).
  symmetry in HP.
  apply Permutation_Type_cons_app_inv in HP.
  symmetry in HP.
  apply Permutation_Type_map_inv in HP as [l1 Heq' _].
  list_simpl in Heq'; symmetry in Heq'; decomp_map_inf Heq'; subst.
  right; exists (N :: l4 ++ l5, P); cbn; rewrite map_app, app_comm_cons.
  symmetry; apply Permutation_Type_cons_app; reflexivity.
Qed.

Lemma polsequent_neg_rem N l : polsequent (neg N :: l) -> polsequent l.
Proof.
intros [ (l0 & Heq) | ((l0 & P) & HP) ].
- destruct l0; inversion Heq.
  left; exists l0; reflexivity.
- assert (HP' := HP).
  apply Permutation_Type_vs_cons_inv in HP' as ((l2 & l3) & Heq).
  destruct l2; inversion Heq; subst.
  symmetry in HP.
  rewrite app_comm_cons in HP.
  apply Permutation_Type_cons_app_inv in HP.
  symmetry in HP.
  apply Permutation_Type_map_inv in HP as [l1 Heq' _].
  list_simpl in Heq'; symmetry in Heq'; decomp_map_inf Heq'; subst.
  right; exists (l5 ++ l6, P); cbn; rewrite map_app.
  symmetry; apply Permutation_Type_middle.
Qed.

Lemma polsequent_pos_rem P l : polsequent (pos P :: l) -> { l' | l = map neg l' }.
Proof.
intros [ (l0 & Heq) | ((l0 & Q) & HP) ].
- symmetry in Heq; decomp_map_inf Heq; inversion Heq1.
- assert (HP' := HP).
  apply Permutation_Type_vs_cons_inv in HP' as ((l' & l'') & Heq).
  destruct l'; inversion Heq; subst.
  + apply Permutation_Type_cons_inv in HP.
    apply Permutation_Type_map_inv in HP as [l' -> HP'].
    eexists; reflexivity.
  + exfalso.
    symmetry in HP.
    rewrite app_comm_cons in HP.
    apply Permutation_Type_cons_app_inv in HP.
    symmetry in HP.
    apply Permutation_Type_map_inv in HP as [l2 Heq' HP'].
    destruct l2; inversion Heq'.
Qed.

Lemma polsequent_dec l : polsequent l + (polsequent l -> False).
Proof.
induction l.
- left; left; exists nil; reflexivity.
- destruct a, IHl.
  + destruct p0.
    * destruct s as [l0 ->].
      left; right; exists (l0,p); reflexivity.
    * destruct s as [[l0 P] HP].
      right; intros Hps; destruct Hps.
      -- destruct s as [[|a l1] Heq]; inversion Heq.
      -- destruct s as [[l1 Q] HP'%uniq_polsequent].
         destruct HP' as [l' -> [-> HP']].
         cbn in HP; symmetry in HP.
         apply Permutation_Type_map_inv in HP as [[|a l] Heq _]; inversion Heq.
  + right; intros Hps.
    apply f.
    left; eapply polsequent_pos_rem; eassumption.
  + left; apply polsequent_neg_add; assumption.
  + right; intros Hps.
    apply f.
    eapply polsequent_neg_rem; eassumption.
Qed.

Definition polsequent_bool l :=
match polsequent_dec l with
| inl _ => true
| inr _ => false
end.

(* TODO move to ollibs (factorize with llfoc_triadic.v) *)
Inductive reflectT (P : Type) : bool -> Type :=
  | ReflectTT : P -> reflectT P true
  | ReflectTF : notT P -> reflectT P false.
Hint Constructors reflectT : bool.

Lemma reflectT_iffT : forall P b, reflectT P b -> (CRelationClasses.iffT P (b = true)).
Proof. now destruct 1; split; [ | | | discriminate ]. Qed.
(* END TODO *)

Lemma polsequent_spec l : reflectT (polsequent l) (polsequent_bool l).
Proof. unfold polsequent_bool; case_eq (polsequent_dec l); intros; constructor; assumption. Qed.

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

Lemma llpol_ps_is_ps l PS : llpol_ps PS l -> is_true (PS l).
Proof. intros Hll; inversion Hll; assumption. Qed.

Lemma llpol_ps_is_llpol l PS : llpol_ps PS l -> llpol l.
Proof.
intros pi; induction pi;
  try (destruct IHpi as [s IHpi]);
  try (destruct IHpi1 as [s1 IHpi1]); try (destruct IHpi2 as [s2 IHpi2]) ;
  try now (econstructor; eassumption).
(* TODO last [try] is useless but much quicker: bug? *)
Qed.

Lemma llpol_is_llpol_ps l : llpol l -> llpol_ps (fun _ => true) l.
Proof.
intros pi; induction pi; try now constructor.
now eapply ex_ps_r; try eassumption.
Qed.

(** Formulas with [top] below negative connectives only. Such formulas are equivalent to [top]. *)
Inductive top_surf : nformula -> Type :=
| top_s : top_surf top
| par_ls : forall N M, top_surf N -> top_surf (parr N M)
| par_rs : forall N M, top_surf N -> top_surf (parr M N)
| with_s : forall N M, top_surf N -> top_surf M -> top_surf (awith N M).

Lemma top_imp_top_surf_ps N l : top_surf N -> polsequent l ->
  llpol_ps polsequent_bool (neg N :: l).
Proof.
induction N in l |- *; intros Ht Hp; inversion_clear Ht as [ | ? ? Ht' | ? ? Ht' | ? ? Ht' Ht'' ].
- eapply IHN1 in Ht'.
  + apply parr_ps_r; [ | eassumption ].
    apply llpol_ps_is_ps in Ht'.
    apply (reflectT_iffT (polsequent_spec _)) in Ht'.
    apply (reflectT_iffT (polsequent_spec _)).
    apply polsequent_neg_add.
    eapply polsequent_neg_rem, polsequent_neg_rem; eassumption.
  + apply polsequent_neg_add; assumption.
- eapply IHN2 in Ht'; [ | apply polsequent_neg_add; eassumption ].
  apply parr_ps_r; [ | eapply ex_ps_r; [ | | now apply Permutation_Type_swap ]].
  + apply llpol_ps_is_ps in Ht'.
    apply (reflectT_iffT (polsequent_spec _)) in Ht'.
    apply (reflectT_iffT (polsequent_spec _)).
    apply polsequent_neg_add.
    eapply polsequent_neg_rem, polsequent_neg_rem; eassumption.
  + apply llpol_ps_is_ps in Ht'.
    apply (reflectT_iffT (polsequent_spec _)) in Ht'.
    apply (reflectT_iffT (polsequent_spec _)).
    apply polsequent_neg_add, polsequent_neg_add.
    eapply polsequent_neg_rem, polsequent_neg_rem; eassumption.
  + eassumption.
- apply top_ps_r.
  apply (reflectT_iffT (polsequent_spec _)).
  apply polsequent_neg_add; assumption.
- apply with_ps_r.
  + apply (reflectT_iffT (polsequent_spec _)).
    apply polsequent_neg_add; assumption.
  + eapply IHN1 in Ht'; eassumption.
  + eapply IHN2 in Ht''; eassumption.
Qed.

Lemma bipos_top_surf l : llpol l -> forall P Q l', Permutation_Type l (pos P :: pos Q :: l') ->
  { '(N, l1, l2) & l' = l1 ++ neg N :: l2 & top_surf N }.
Proof.
intros pi; induction pi; intros P' Q' l' HP.
- apply Permutation_Type_length_2_inv in HP as [ HP | HP ]; inversion HP.
- eapply IHpi.
  etransitivity; [ apply p | apply HP ].
- apply Permutation_Type_length_1_inv in HP; inversion HP.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP' as ((l2 & l3) & Heq).
  destruct l2; inversion Heq.
  destruct l2; inversion H1; subst.
  rewrite 2 app_comm_cons in HP.
  apply Permutation_Type_cons_app_inv in HP.
  list_simpl in HP.
  apply IHpi in HP as [[[N l0] l1] Heq' Htop].
  dichot_elt_app_inf_exec Heq'; subst.
  + now exists (N, l0, l4 ++ neg bot :: l3); list_simpl.
  + now exists (N, l2 ++ neg bot :: l5, l1); list_simpl.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP' as ((l2' & l3') & Heq).
  destruct l2'; inversion Heq; subst.
  + apply Permutation_Type_cons_inv in HP.
    assert (HP' := HP).
    apply Permutation_Type_vs_cons_inv in HP' as ((l3 & l4) & Heq').
    rewrite Heq' in HP.
    symmetry in HP.
    apply Permutation_Type_cons_app_inv in HP.
    dichot_app_inf_exec Heq';
      [ | destruct l0; inversion Heq'1; list_simpl in Heq'1 ]; subst.
    * list_simpl in HP.
      assert (Permutation_Type (pos Q :: l ++ pos Q' :: l4)
                               (pos Q :: pos Q' :: l ++ l4)) as HP'
        by (symmetry; apply Permutation_Type_cons, Permutation_Type_cons_app; reflexivity).
      apply IHpi2 in HP' as [[[N l5] l6] Heq' Htop]; cbn in Heq'.
      rewrite Heq', app_assoc in HP.
      apply Permutation_Type_vs_elt_inv in HP as ((l7 & l8) & ->).
      now exists (N, l7, l8).
    * destruct (IHpi2 Q Q' l4 (Permutation_Type_refl _)) as [[[N l5] l6] -> Htop].
      rewrite app_assoc in HP.
      apply Permutation_Type_vs_elt_inv in HP.
      destruct HP as ((l7 & l8) & ->).
      now exists (N, l7, l8).
    * assert (Permutation_Type (pos P :: l3 ++ pos Q' :: l0)
                               (pos P :: pos Q' :: l3 ++ l0)) as HP'
        by (symmetry; apply Permutation_Type_cons, Permutation_Type_cons_app; reflexivity).
      apply IHpi1 in HP' as [[[N l5] l6] Heq' Htop].
      rewrite app_assoc, Heq' in HP.
      list_simpl in HP.
      apply Permutation_Type_vs_elt_inv in HP as ((l7 & l8) & ->).
      now exists (N, l7, l8).
  + destruct l2'; inversion H1; subst.
    * rewrite <- (app_nil_l (pos (tens _ _) :: l3')),(app_comm_cons _ _ (pos P')) in HP.
      apply Permutation_Type_cons_app_inv in HP.
      list_simpl in HP.
      destruct (Permutation_Type_vs_cons_inv HP) as [(l4, l5) Heq'].
      dichot_app_inf_exec Heq';
        [ | destruct l0 ; inversion Heq'1 ; list_simpl in Heq'1 ]; subst.
      -- symmetry in HP.
         rewrite app_assoc in HP.
         apply Permutation_Type_cons_app_inv in HP.
         list_simpl in HP.
         assert (Permutation_Type (pos Q :: l ++ pos P' :: l5)
                                  (pos Q :: pos P' :: l ++ l5)) as HP'
           by (symmetry; apply Permutation_Type_cons, Permutation_Type_cons_app; reflexivity).
         apply IHpi2 in HP' as [[[N l6] l7] Heq' Htop].
         rewrite Heq', app_assoc in HP.
         apply Permutation_Type_vs_elt_inv in HP as ((l8 & l9) & ->).
         now exists (N, l8, l9).
      -- destruct (IHpi2 Q P' l5 (Permutation_Type_refl _)) as [[[N l6] l7] -> Htop].
         list_simpl in HP.
         symmetry in HP.
         apply Permutation_Type_cons_app_inv in HP.
         rewrite app_assoc in HP.
         apply Permutation_Type_vs_elt_inv in HP as ((l8 & l9) & ->).
         now exists (N, l8, l9).
      -- assert (Permutation_Type (pos P :: l4 ++ pos P' :: l0)
                                  (pos P :: pos P' :: l4 ++ l0)) as HP' 
           by (symmetry; apply Permutation_Type_cons, Permutation_Type_cons_app; reflexivity).
         apply IHpi1 in HP' as [[[N l6] l7] Heq' Htop].
         list_simpl in HP.
         symmetry in HP.
         apply Permutation_Type_cons_app_inv in HP.
         rewrite app_assoc, Heq' in HP.
         list_simpl in HP.
         apply Permutation_Type_vs_elt_inv in HP as ((l8 & l9) & ->).
         now exists (N, l8, l9).
    * rewrite 2 (app_comm_cons _ (pos (tens _ _) :: l3')) in HP.
      apply Permutation_Type_cons_app_inv in HP.
      list_simpl in HP.
      destruct (Permutation_Type_vs_cons_inv HP) as [(l4, l5) Heq'].
      dichot_app_inf_exec Heq'; subst.
      -- assert (Permutation_Type (pos Q :: l ++ pos P' :: l5)
                                  (pos Q :: pos P' :: l ++ l5)) as HP'
           by (symmetry; apply Permutation_Type_cons, Permutation_Type_cons_app; reflexivity).
         apply IHpi2 in HP' as [[[N l6] l7] Heq' Htop].
         symmetry in HP.
         rewrite app_assoc in HP.
         apply Permutation_Type_cons_app_inv in HP.
         list_simpl in HP.
         rewrite Heq', app_assoc in HP.
         apply Permutation_Type_vs_elt_inv in HP as ((l8 & l9) & Heq'').
         destruct l8; inversion Heq''.
         dichot_app_inf_exec H2;
           [ | destruct l2; inversion Heq''; list_simpl in H4 ]; subst.
         ++ now exists (N, l2' ++ pos (tens P Q) :: l0, l9); list_simpl.
         ++ now exists (N, l8 ++ pos (tens P Q) :: nil, l9); list_simpl.
         ++ inversion H4; subst.
            now exists (N, l8, l2 ++ pos (tens P Q) :: l3'); list_simpl.
      -- destruct l0; inversion Heq'1; list_simpl in Heq'1; subst.
         ++ destruct (IHpi2 Q P' l5 (Permutation_Type_refl _)) as [[[N l6] l7] -> Htop].
            list_simpl in HP.
            symmetry in HP.
            apply Permutation_Type_cons_app_inv in HP.
            rewrite app_assoc in HP.
            apply Permutation_Type_vs_elt_inv in HP as ((l8 & l9) & Heq'').
            destruct l8; inversion Heq''; subst.
            dichot_app_inf_exec H3;
              [ | destruct l0; inversion H2; list_simpl in H2 ]; subst.
            ** now exists (N, l2' ++ pos (tens P Q) :: l, l9); list_simpl.
            ** now exists (N, l8 ++ pos (tens P Q) :: nil, l9); list_simpl.
            ** now exists (N, l8, l0 ++ pos (tens P Q) :: l3'); list_simpl.
         ++ assert (Permutation_Type (pos P :: l4 ++ pos P' :: l0)
                                     (pos P :: pos P' :: l4 ++ l0)) as HP'
              by (symmetry; apply Permutation_Type_cons, Permutation_Type_cons_app; reflexivity).
            apply IHpi1 in HP' as [[[N l6] l7] Heq' Htop].
            symmetry in HP.
            list_simpl in HP.
            apply Permutation_Type_cons_app_inv in HP.
            rewrite app_assoc, Heq' in HP.
            list_simpl in HP.
            apply Permutation_Type_vs_elt_inv in HP as ((l8 & l9) & Heq'').
            destruct l8; inversion Heq''.
            dichot_app_inf_exec H2;
              [ | destruct l1; inversion H4; list_simpl in H4 ]; subst.
            ** now exists (N, l2' ++ pos (tens P Q) :: l, l9); list_simpl.
            ** now exists (N, l8 ++ pos (tens P Q) :: nil, l9); list_simpl.
            ** now exists (N, l8, l1 ++ pos (tens P Q) :: l3'); list_simpl.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP' as ((l2 & l3) & Heq).
  destruct l2; inversion Heq.
  destruct l2; inversion H1; subst.
  rewrite 2 app_comm_cons in HP.
  apply Permutation_Type_cons_app_inv in HP.
  apply (Permutation_Type_cons_app _ _ (neg M)) in HP.
  apply (Permutation_Type_cons_app _ _ (neg N)) in HP.
  list_simpl in HP.
  apply IHpi in HP as [[[N' l0] l1] Heq' Htop].
  dichot_elt_app_inf_exec Heq'; subst.
  + destruct l4; inversion Heq'1; subst.
    * exists (parr N N', l2, l1); list_simpl; [ reflexivity | ].
      apply par_rs; assumption.
    * now exists (N', l2 ++ neg (parr N M) :: l4, l1); list_simpl.
  + destruct l5; inversion Heq'1; subst.
    * exists (parr N' M, l0, l3); list_simpl; [ reflexivity | ].
      apply par_ls; assumption.
    * now exists (N', l0, l5 ++ neg (parr N M) :: l3); list_simpl.
- symmetry in HP.
  apply Permutation_Type_vs_cons_inv in HP as ((l2 & l3) & Heq).
  destruct l2; inversion Heq.
  destruct l2; inversion H1; subst.
  exists (top, l2, l3); [ reflexivity | ].
  apply top_s.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP' as ((l2 & l3) & Heq).
  destruct l2; inversion Heq; subst.
  + apply Permutation_Type_cons_inv in HP.
    apply (@Permutation_Type_cons _ _ (pos P) eq_refl) in HP.
    apply IHpi in HP as [[[N l0] l1] -> Htop].
    now exists (N, l0, l1).
  + destruct l2; inversion H1; subst.
    * rewrite <- (app_nil_l (pos (aplus _ _) :: l3)), app_comm_cons in HP.
      apply Permutation_Type_cons_app_inv in HP.
      apply (@Permutation_Type_cons _ _ (pos P) eq_refl) in HP.
      list_simpl in HP.
      apply IHpi in HP as [[[N l0] l1] -> Htop].
      now exists (N, l0, l1).
    * rewrite 2 app_comm_cons in HP.
      apply Permutation_Type_cons_app_inv in HP.
      apply (Permutation_Type_cons_app _ _ (pos P)) in HP.
      list_simpl in HP.
      apply IHpi in HP as [[[N' l0] l1] Heq' Htop].
      dichot_elt_app_inf_exec Heq'; subst.
      -- now exists (N', l2 ++ pos (aplus P Q) :: l4, l1); list_simpl.
      -- destruct l5; inversion Heq'1; subst.
         now exists (N', l0, l5 ++ pos (aplus P Q) :: l3); list_simpl.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP' as ((l2 & l3) & Heq).
  destruct l2; inversion Heq; subst.
  + apply Permutation_Type_cons_inv in HP.
    apply (@Permutation_Type_cons _ _ (pos P) eq_refl) in HP.
    apply IHpi in HP as [[[N l0] l1] -> Htop].
    now exists (N, l0, l1).
  + destruct l2; inversion H1; subst.
    * rewrite <- (app_nil_l (pos (aplus _ _) :: l3)), app_comm_cons in HP.
      apply Permutation_Type_cons_app_inv in HP.
      apply (@Permutation_Type_cons _ _ (pos P) eq_refl) in HP.
      list_simpl in HP.
      apply IHpi in HP as [[[N l0] l1] -> Htop].
      now exists (N, l0, l1).
    * rewrite 2 app_comm_cons in HP.
      apply Permutation_Type_cons_app_inv in HP.
      apply (Permutation_Type_cons_app _ _ (pos P)) in HP.
      list_simpl in HP.
      apply IHpi in HP as [[[N' l0] l1] Heq' Htop].
      dichot_elt_app_inf_exec Heq'; subst.
      -- now exists (N', l2 ++ pos (aplus Q P) :: l4, l1); list_simpl.
      -- destruct l5; inversion Heq'1; subst.
         now exists (N', l0, l5 ++ pos (aplus Q P) :: l3); list_simpl.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP' as ((l2 & l3) & Heq).
  destruct l2; inversion Heq.
  destruct l2; inversion H1; subst.
  rewrite 2 app_comm_cons in HP.
  apply Permutation_Type_cons_app_inv in HP.
  assert (HP1 := (Permutation_Type_cons_app _ _ (neg N) HP)).
  assert (HP2 := (Permutation_Type_cons_app _ _ (neg M) HP)).
  list_simpl in HP1; apply IHpi1 in HP1 as [[[N' l0] l1] Heq' Htop].
  list_simpl in HP2; apply IHpi2 in HP2 as [[[M' l0'] l1'] Heq'' Htop'].
  dichot_elt_app_inf_exec Heq'; subst.
  + now exists (N', l2 ++ neg (awith N M) :: l4, l1); list_simpl.
  + destruct l5; inversion Heq'1; subst.
    * list_simpl in Heq''.
      dichot_elt_app_inf_exec Heq''; subst.
      -- now exists (M', l0 ++ neg (awith N' M) :: l2, l1'); list_simpl.
      -- destruct l3; inversion Heq''1; subst.
         ++ exists (awith N' M', l0', l1');list_simpl; [ reflexivity | ].
            apply with_s; assumption.
         ++ now exists (M', l0', l3 ++ neg (awith N' M) :: l1); list_simpl.
    * now exists (N', l0, l5 ++ neg (awith N M) :: l3); list_simpl.
- exfalso.
  assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP' as ((l2 & l3) & Heq).
  destruct l2; inversion Heq; subst.
  + apply Permutation_Type_cons_inv in HP.
    apply Permutation_Type_vs_cons_inv in HP as ((l2 & l3) & Heq').
    decomp_map Heq'; discriminate Heq'3.
  + destruct l2; inversion H1; subst.
    * rewrite <- (app_nil_l (pos (oc _) :: l3)), app_comm_cons in HP.
      apply Permutation_Type_cons_app_inv in HP.
      apply Permutation_Type_vs_cons_inv in HP as ((l2' & l3') & Heq').
      decomp_map Heq'; discriminate Heq'3.
    * rewrite 2 app_comm_cons in HP.
      apply Permutation_Type_cons_app_inv in HP.
      apply Permutation_Type_vs_cons_inv in HP as ((l2' & l3') & Heq').
      decomp_map Heq'; discriminate Heq'3.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP' as ((l2 & l3) & Heq).
  destruct l2; inversion Heq.
  destruct l2; inversion H1; subst.
  rewrite 2 app_comm_cons in HP.
  apply Permutation_Type_cons_app_inv in HP.
  apply (Permutation_Type_cons_app _ _ (pos P)) in HP.
  list_simpl in HP.
  apply IHpi in HP as [[[N' l0] l1] Heq' Htop].
  dichot_elt_app_inf_exec Heq'; subst.
  + now exists (N', l2 ++ neg (wn P) :: l4, l1); list_simpl.
  + destruct l5; inversion Heq'1; subst.
    now exists (N', l0, l5 ++ neg (wn P) :: l3); list_simpl.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP' as ((l2 & l3) & Heq).
  destruct l2; inversion Heq.
  destruct l2; inversion H1; subst.
  rewrite 2 app_comm_cons in HP.
  apply Permutation_Type_cons_app_inv in HP.
  list_simpl in HP.
  apply IHpi in HP as [[[N l0] l1] Heq' Htop].
  dichot_elt_app_inf_exec Heq'; subst.
  + now exists (N, l0, l4 ++ neg (wn P) :: l3); list_simpl.
  + now exists (N, l2 ++ neg (wn P) :: l5, l1); list_simpl.
- assert (HP' := HP).
  symmetry in HP'.
  apply Permutation_Type_vs_cons_inv in HP' as ((l2 & l3) & Heq).
  destruct l2; inversion Heq.
  destruct l2; inversion H1; subst.
  rewrite 2 app_comm_cons in HP.
  apply Permutation_Type_cons_app_inv in HP.
  apply (Permutation_Type_cons_app _ _ (neg (wn P))) in HP.
  apply (Permutation_Type_cons_app _ _ (neg (wn P))) in HP.
  list_simpl in HP.
  apply IHpi in HP as [[[N' l0] l1] Heq' Htop].
  dichot_elt_app_inf_exec Heq'; subst.
  + destruct l4; inversion Heq'1; subst.
    * inversion Htop.
    * now exists (N', l2 ++ neg (wn P) :: l4, l1); list_simpl.
  + destruct l5; inversion Heq'1; subst.
    * inversion Htop.
    * now exists (N', l0, l5 ++ neg (wn P) :: l3); list_simpl.
Qed.

Theorem llpol_is_ll_polsequent l : llpol l -> polsequent l -> llpol_ps polsequent_bool l.
Proof.
intros pi; induction pi ; intros Hpol.
- constructor.
  apply (reflectT_iffT (polsequent_spec _)).
  right; exists (covar X :: nil,var X).
  apply Permutation_Type_swap.
- eapply ex_ps_r; [ apply (reflectT_iffT (polsequent_spec _)) | | ]; try eassumption.
  apply IHpi.
  destruct Hpol as [ (l0 & ->) | ((l0 & P) & HP) ].
  + apply Permutation_Type_map_inv in p as [l -> _].
    left; exists l; reflexivity.
  + assert (HP' := HP).
    apply Permutation_Type_vs_cons_inv in HP' as ((l3 & l4) & ->).
    symmetry in HP.
    apply Permutation_Type_cons_app_inv in HP.
    symmetry in HP.
    apply Permutation_Type_map_inv in HP as [l Heq HP].
    symmetry in Heq; decomp_map_inf Heq; cbn in Heq1; cbn in Heq2; subst; cbn in p.
    right; exists (l5 ++ l6, P); cbn.
    etransitivity; [ eassumption | ].
    symmetry; apply Permutation_Type_cons_app; rewrite map_app; reflexivity.
- constructor.
  apply (reflectT_iffT (polsequent_spec _)).
  right; exists (nil, one); reflexivity.
- constructor; [ apply (reflectT_iffT (polsequent_spec _)); assumption | ].
  apply IHpi.
  eapply polsequent_neg_rem; eassumption.
- apply polsequent_pos_rem in Hpol as [l' Heq].
  symmetry in Heq; decomp_map_inf Heq; subst.
  constructor.
  + apply (reflectT_iffT (polsequent_spec _)).
    right; exists (l0 ++ l3, tens P Q); cbn; rewrite map_app; reflexivity.
  + apply IHpi1.
    right; exists (l0, P); reflexivity.
  + apply IHpi2.
    right; exists (l3, Q); reflexivity.
- constructor; [ apply (reflectT_iffT (polsequent_spec _)); assumption | ].
  apply IHpi.
  apply polsequent_neg_add, polsequent_neg_add.
  eapply polsequent_neg_rem; eassumption.
- constructor; apply (reflectT_iffT (polsequent_spec _)); assumption.
- assert (Hpol' := Hpol).
  apply polsequent_pos_rem in Hpol' as [l' ->].
  constructor; [ apply (reflectT_iffT (polsequent_spec _)); assumption | ].
  apply IHpi.
  right; exists (l', P); reflexivity.
- assert (Hpol' := Hpol).
  apply polsequent_pos_rem in Hpol' as [l' ->].
  apply plus_ps_r2; [ apply (reflectT_iffT (polsequent_spec _)); assumption | ].
  apply IHpi.
  right; exists (l', P); reflexivity.
- constructor; [ apply (reflectT_iffT (polsequent_spec _)); assumption | | ].
  + apply IHpi1.
    apply polsequent_neg_add.
    eapply polsequent_neg_rem; eassumption.
  + apply IHpi2.
    apply polsequent_neg_add.
    eapply polsequent_neg_rem; eassumption.
- constructor ; [ apply (reflectT_iffT (polsequent_spec _)); assumption | ].
  apply IHpi.
  left; exists (N :: map wn l); reflexivity.
- destruct Hpol as [ (l0 & Heq) | ((l0 & Q) & HP) ].
  + apply de_ps_r.
    * apply (reflectT_iffT (polsequent_spec _)).
      left; rewrite Heq; exists l0; reflexivity.
    * apply IHpi.
      destruct l0; inversion Heq; subst.
      right; exists (l0, P); reflexivity.
  + destruct (Permutation_Type_vs_cons_inv HP) as [(l2, l3) Heq].
    destruct l2; inversion Heq; subst.
    assert (pi' := pi).
    apply bipos_top_surf with _ P Q (l2 ++ l3) in pi' as [[[N l] l'] Heq' Htop];
      [ | symmetry; apply Permutation_Type_cons, Permutation_Type_cons_app; reflexivity ].
    apply (@ex_r _ (pos P :: pos Q :: l2 ++ l3)) in pi;
      [ | symmetry; apply Permutation_Type_cons, Permutation_Type_cons_app; reflexivity ].
    rewrite Heq' in pi.
    apply (@ex_r _ (neg N :: pos P :: pos Q :: l ++ l')) in pi;
      [ | symmetry; etransitivity;
          [ apply Permutation_Type_cons_app; rewrite ? app_comm_cons | ]; reflexivity ].
    eapply top_imp_top_surf_ps in Htop.
    * apply (@ex_ps_r _ (neg N :: neg (wn P) :: pos Q :: l ++ l')); [ | eassumption | ].
      -- apply (reflectT_iffT (polsequent_spec _)).
         right; eexists; eassumption.
      -- symmetry; etransitivity; [ apply Permutation_Type_middle | ].
         transitivity (neg (wn P) :: pos Q :: l2 ++ l3); [ | rewrite Heq' ].
         ++ symmetry; etransitivity;
              [ apply Permutation_Type_cons_app; rewrite app_comm_cons; reflexivity | ].
            etransitivity; [ apply Permutation_Type_middle | ].
            apply Permutation_Type_app_head, Permutation_Type_swap.
         ++ symmetry; etransitivity;
              [ apply Permutation_Type_cons_app; rewrite ? app_comm_cons | ]; reflexivity.
    * apply polsequent_neg_rem with N.
      right; exists (l0, Q).
      etransitivity; [ | apply HP ].
      transitivity (neg (wn P) :: pos Q :: l2 ++ l3); [ rewrite Heq' | ].
      -- etransitivity; [ apply Permutation_Type_cons_app; rewrite ? app_comm_cons | ]; reflexivity.
      -- apply Permutation_Type_cons, Permutation_Type_cons_app; reflexivity.
- apply wk_ps_r ; [ apply (reflectT_iffT (polsequent_spec _)); assumption | ].
  apply IHpi.
  eapply polsequent_neg_rem; eassumption.
- apply co_ps_r ; [ apply (reflectT_iffT (polsequent_spec _)); assumption | ].
  apply IHpi.
  apply polsequent_neg_add; eassumption.
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

Instance llpolt_perm : Proper ((@Permutation_Type _) ==> arrow) llpolt.
Proof. intros l1 l2 HP pi; eapply ex_rt; eassumption. Qed.

(** For polarized sequents, [llpol] corresponds to [top] rule with at most one positive formula. *)
Theorem llpol_llpolt l : polsequent l -> llpol l -> llpolt l.
Proof.
intros Hpol pi%llpol_is_ll_polsequent; [ | assumption ].
clear Hpol; induction pi; try (now constructor).
- eapply ex_rt; eassumption.
- apply (reflectT_iffT (polsequent_spec _)) in i.
  apply top_rt.
  eapply polsequent_neg_rem; eassumption.
Qed.

Theorem llpolt_llpol l : llpolt l -> (polsequent l * llpol l).
Proof.
intros pi; induction pi; split;
  try (destruct IHpi as [Hpol pi']);
  try (destruct IHpi1 as [Hpol1 pi1']); try (destruct IHpi2 as [Hpol2 pi2']);
  try (now constructor);
  try (apply polsequent_neg_add; assumption).
- right; exists (covar X :: nil,var X); apply Permutation_Type_swap.
- destruct Hpol.
  + destruct s as [l0 ->].
    symmetry in p.
    apply Permutation_Type_map_inv in p as [l3 -> HP].
    left; exists l3; reflexivity.
  + destruct s as ((l0 & P) & H0).
    assert (HP := H0).
    apply Permutation_Type_vs_cons_inv in H0 as ((l3 & l4) & ->).
    symmetry in HP.
    apply Permutation_Type_cons_app_inv in HP.
    right; exists (l0, P).
    symmetry; etransitivity; [ | eassumption ]; cbn.
    apply Permutation_Type_cons_app; assumption.
- eapply ex_r; eassumption.
- right; exists (nil, one); reflexivity.
- apply polsequent_pos_rem in Hpol1 as [l1' ->].
  apply polsequent_pos_rem in Hpol2 as [l2' ->].
  right; exists (l1' ++ l2', tens P Q); cbn; rewrite map_app; reflexivity.
- apply polsequent_neg_rem, polsequent_neg_rem in Hpol.
  apply polsequent_neg_add; assumption.
- apply polsequent_pos_rem in Hpol as [l' ->].
  right; exists (l', aplus P Q); reflexivity.
- apply polsequent_pos_rem in Hpol as [l' ->].
  right; exists (l', aplus Q P); reflexivity.
- apply polsequent_neg_rem in Hpol1.
  apply polsequent_neg_add; assumption.
- right; exists (map wn l, oc N); reflexivity.
- apply polsequent_pos_rem in Hpol as [l' ->].
  left; exists (wn P :: l'); reflexivity.
- eapply polsequent_neg_rem; eassumption.
Qed.

End Atoms.
