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

Coercion pos : pformula >-> formula.
Coercion neg : nformula >-> formula.
Add Printing Coercion pos.
Add Printing Coercion neg.

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

Definition dual A : formula :=
match A with
| pos P => pdual P
| neg N => ndual N
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
- intros x P Heq. destruct P; inversion Heq; reflexivity.
- intros N IH M Heq. destruct M; inversion Heq.
  apply IH in H0. subst; reflexivity.
- intros x N Heq. destruct N; inversion Heq; reflexivity.
- intros P IH Q Heq. destruct Q; inversion Heq.
  apply IH in H0 as ->. reflexivity.
Qed.

Lemma llpol2ll_inj : injective llpol2ll.
Proof.
intros A B Heq. destruct A, B.
- apply billpol2ll_inj in Heq as ->. reflexivity.
- destruct p, n; discriminate Heq.
- destruct p, n; discriminate Heq.
- apply billpol2ll_inj in Heq as ->. reflexivity.
Qed.

Lemma billpol2ll_dual :
     (forall P, formulas.dual (pllpol2ll P) = nllpol2ll (pdual P))
  /\ (forall N, formulas.dual (nllpol2ll N) = pllpol2ll (ndual N)).
Proof. apply polform_ind; intros; cbn; rewrite ? H, ? H0; reflexivity. Qed.

Lemma llpol2ll_dual A : formulas.dual (llpol2ll A) = llpol2ll (dual A).
Proof. destruct A; apply billpol2ll_dual. Qed.

Lemma bidual A : dual (dual A) = A.
Proof. apply llpol2ll_inj. rewrite <- 2 llpol2ll_dual, formulas.bidual. reflexivity. Qed.

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
| ax_r X : llpol (neg (covar X) :: pos (var X) :: nil)
| ex_r l1 l2 : llpol l1 -> Permutation_Type l1 l2 -> llpol l2
| one_r : llpol (pos one :: nil)
| bot_r l : llpol l -> llpol (neg bot :: l)
| tens_r P Q l1 l2 : llpol (pos P :: l1) -> llpol (pos Q :: l2) -> llpol (pos (tens P Q) :: l1 ++ l2)
| parr_r N M l : llpol (neg N :: neg M :: l) -> llpol (neg (parr N M) :: l)
| top_r l : llpol (neg top :: l)
| plus_r1 P Q l : llpol (pos P :: l) -> llpol (pos (aplus P Q) :: l)
| plus_r2 P Q l : llpol (pos P :: l) -> llpol (pos (aplus Q P) :: l)
| with_r N M l : llpol (neg N :: l) -> llpol (neg M :: l) -> llpol (neg (awith N M) :: l)
| oc_r N l : llpol (neg N :: map neg (map wn l)) -> llpol (pos (oc N) :: map neg (map wn l))
| de_r P l : llpol (pos P :: l) -> llpol (neg (wn P) :: l)
| wk_r P l : llpol l -> llpol (neg (wn P) :: l)
| co_r P l : llpol (neg (wn P) :: neg (wn P) :: l) -> llpol (neg (wn P) :: l).

Instance llpol_perm : Proper ((@Permutation_Type _) ==> arrow) llpol.
Proof. intros l1 l2 HP pi. eapply ex_r; eassumption. Qed.


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
| inl _ => True
| inr _ => False
end.

Lemma llpol_is_fragment : ll_prop.fragment llpol_fragment.
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
intros pi. induction pi; try now (constructor; auto).
- eapply ll_def.ex_r; [ eassumption | ].
  apply Permutation_Type_map. assumption.
- eapply ll_def.ex_r.
  + cbn in IHpi1, IHpi2. apply (ll_def.tens_r IHpi1 IHpi2).
  + apply Permutation_Type_cons; [ reflexivity | ].
    fold (map llpol2ll). rewrite map_app.
    apply Permutation_Type_app_comm.
- cbn. rewrite ? map_app, llpol2ll_map_wn.
  apply ll_def.oc_r.
  rewrite <- llpol2ll_map_wn. assumption.
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
            apply IHpi; reflexivity)).
- symmetry in Heql0. decomp_map_inf Heql0. subst.
  destruct l1; inversion Heql4.
  destruct x; inversion Heql2; [ destruct p | destruct n ]; inversion Heql2.
  destruct x0; inversion Heql0; [destruct p | destruct n ]; inversion Heql0; subst.
  apply ax_r.
- cbn in p.
  apply Permutation_Type_map_inv in p as [l'' -> HP].
  symmetry in HP.
  eapply ex_r; [ | eassumption ].
  apply IHpi. reflexivity.
- symmetry in Heql0. decomp_map_inf Heql0. subst. symmetry in Heql0.
  cbn in Heql0. apply llpol2ll_map_wn_inv in Heql0 as [l -> ->].
  apply Permutation_Type_map_inv in p as [l' -> HP].
  apply (Permutation_Type_map wn), (Permutation_Type_map neg) in HP.
  eapply ex_r.
  + rewrite <- llpol2ll_map_wn in IHpi.
    apply IHpi. rewrite <- ? map_app. reflexivity.
  + symmetry. apply Permutation_Type_app_head, Permutation_Type_app_tail. assumption.
- discriminate i.
- destruct l'; inversion Heql0.
  destruct f; inversion H0; [ destruct p | destruct n ]; inversion H0.
  destruct l'; inversion H1.
  apply one_r.
- symmetry in Heql0. decomp_map_inf Heql0. subst.
  destruct x; inversion Heql2; [ destruct p | destruct n ]; inversion Heql2; subst.
  eapply ex_r; [ apply tens_r | ].
  + apply IHpi1. reflexivity.
  + apply IHpi2. reflexivity.
  + apply Permutation_Type_cons, Permutation_Type_app_comm. reflexivity.
- destruct l'; inversion Heql0.
  destruct f; inversion H0 ; [ destruct p | destruct n ]; inversion H0; subst.
  apply with_r; [ apply IHpi1 | apply IHpi2 ]; reflexivity.
- destruct l'; inversion Heql0.
  destruct f; inversion H0; [destruct p | destruct n ]; inversion H0; subst.
  apply llpol2ll_map_wn_inv in H1 as [l'' -> ->].
  apply oc_r, IHpi.
  cbn. rewrite llpol2ll_map_wn. reflexivity.
- discriminate f.
- destruct a.
Qed.


(** ** 6. import properties *)

(** *** axiom expansion *)

Lemma ax_gen_r A : llpol (dual A :: A :: nil).
Proof.
eapply ex_r; [ | apply Permutation_Type_swap ].
apply llpolfrag2llpol.
cbn. rewrite <- llpol2ll_dual. apply ll_def.ax_exp.
Qed.

(** *** cut admissibility *)

Lemma cut_r A l1 l2 : llpol (A :: l1) -> llpol (dual A :: l2) -> llpol (l1 ++ l2).
Proof.
intros pi1%llpol2llpolfrag pi2%llpol2llpolfrag.
cbn in pi1, pi2.
eapply ll_cut.cut_r_axfree in pi1; [ | | rewrite llpol2ll_dual; eassumption ].
- rewrite <- map_app in pi1.
  apply llpolfrag2llpol. assumption.
- intros [].
Qed.


(** ** 7. specific developments *)

Lemma par_inv N M l : llpol (neg (parr N M) :: l) -> llpol (neg N :: neg M :: l).
Proof.
intros pi.
rewrite <- (app_nil_l l).
eapply ex_r; [ | apply Permutation_Type_swap ].
rewrite 2 app_comm_cons. eapply cut_r.
- rewrite <- (app_nil_l (neg N :: nil)), 2 app_comm_cons, <- app_comm_cons.
  apply (@tens_r (ndual M) (ndual N)).
  + change (pos (ndual M)) with (dual (neg M)). apply ax_gen_r.
  + change (pos (ndual N)) with (dual (neg N)). apply ax_gen_r.
- cbn. rewrite 2 (proj2 bipndual). assumption.
Qed.

Lemma with_inv_1 N M l : llpol (neg (awith N M) :: l) ->  llpol (neg N :: l).
Proof.
intros pi.
rewrite <- (app_nil_l l), app_comm_cons. eapply cut_r.
- apply (@plus_r1 (ndual N) (ndual M)).
  change (pos (ndual N)) with (dual (neg N)). apply ax_gen_r.
- cbn. rewrite 2 (proj2 bipndual). assumption.
Qed.

Lemma with_inv_2 N M l : llpol (neg (awith M N) :: l) ->  llpol (neg N :: l).
Proof.
intros pi.
rewrite <- (app_nil_l l), app_comm_cons. eapply cut_r.
- apply (@plus_r2 (ndual N) (ndual M)).
  change (pos (ndual N)) with (dual (neg N)). apply ax_gen_r.
- cbn. rewrite 2 (proj2 bipndual). assumption.
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
  symmetry. assumption.
- exfalso. decomp_map H1. discriminate H1.
Qed.

Lemma Permutation_Type_polsequent l1 l2 : Permutation_Type l1 l2 -> polsequent l1 -> polsequent l2.
Proof.
intros HP [[l ->]|[(l, P) Hpol]].
- left.
  symmetry in HP. apply Permutation_Type_map_inv in HP as [l' -> _].
  exists l'. reflexivity.
- right. exists (l, P).
  symmetry in HP. transitivity l1; assumption.
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
intros [ [l0 ->] | [[l0 P] HP] ].
- left. exists (N :: l0). reflexivity.
- destruct (Permutation_Type_vs_cons_inv HP) as [(l2, l3) ->].
  symmetry in HP. apply Permutation_Type_cons_app_inv in HP. symmetry in HP.
  apply Permutation_Type_map_inv in HP as [l1 Heq' _].
  list_simpl in Heq'. symmetry in Heq'. decomp_map_inf Heq'. subst.
  right. exists (N :: l4 ++ l5, P). cbn. rewrite map_app, app_comm_cons.
  symmetry. apply Permutation_Type_cons_app. reflexivity.
Qed.

Lemma polsequent_neg_rem N l : polsequent (neg N :: l) -> polsequent l.
Proof.
intros [ [l0 Heq] | [[l0 P] HP] ].
- destruct l0; inversion Heq.
  left. exists l0. reflexivity.
- destruct (Permutation_Type_vs_cons_inv HP) as [(l2, l3) Heq].
  destruct l2; inversion Heq; subst.
  symmetry in HP. rewrite app_comm_cons in HP. apply Permutation_Type_cons_app_inv in HP. symmetry in HP.
  apply Permutation_Type_map_inv in HP as [l1 Heq' _].
  list_simpl in Heq'. symmetry in Heq'. decomp_map_inf Heq'. subst.
  right. exists (l5 ++ l6, P). cbn. rewrite map_app.
  symmetry. apply Permutation_Type_middle.
Qed.

Lemma polsequent_pos_rem_strong P l : polsequent (pos P :: l) -> { l' | l = map neg l' }.
Proof.
intros [ [l0 Heq] | [[l0 Q] HP] ].
- symmetry in Heq. decomp_map_inf Heq; discriminate Heq1.
- destruct (Permutation_Type_vs_cons_inv HP) as [(l', l'') Heq].
  destruct l'; inversion Heq; subst.
  + apply Permutation_Type_cons_inv in HP.
    apply Permutation_Type_map_inv in HP as [l' -> _].
    exists l'. reflexivity.
  + exfalso.
    symmetry in HP. rewrite app_comm_cons in HP. apply Permutation_Type_cons_app_inv in HP. symmetry in HP.
    apply Permutation_Type_map_inv in HP as [l2 Heq' _].
    destruct l2; discriminate Heq'.
Qed.

Lemma polsequent_pos_rem_weak P l : polsequent (pos P :: l) -> polsequent l.
Proof. intros [l' ->]%polsequent_pos_rem_strong. left. exists l'. reflexivity. Qed.

Fixpoint Forall_sequent PS l (pi : llpol l) : Type :=
match pi with
| ax_r _ | one_r | top_r _ => PS l
| ex_r pi1 _ | bot_r pi1 | parr_r pi1 | plus_r1 _ pi1 | plus_r2 _ pi1 => Forall_sequent PS pi1 * PS l
| tens_r pi1 pi2 | with_r pi1 pi2 => Forall_sequent PS pi1 * Forall_sequent PS pi2 * PS l
| oc_r _ pi1 | de_r pi1 | wk_r _ pi1 | co_r pi1 => Forall_sequent PS pi1 * PS l
end.

Definition Forall_formula FS := Forall_sequent (Forall_inf FS).

Lemma Forall_sequent_is PS l (pi : llpol l) : Forall_sequent PS pi -> PS l.
Proof. destruct pi; cbn; tauto. Qed.

Lemma Forall_sequent_impl PS QS (HPQ : forall x, PS x -> QS x) l (pi : llpol l) :
  Forall_sequent PS pi -> Forall_sequent QS pi.
Proof.
induction pi;
  try (now cbn; apply HPQ);
  try (now cbn; intros [IH H]; split; auto);
  try (now cbn; intros [[IH1 IH2] H]; split; auto).
Qed.


(** Formulas with [top] below negative connectives only. Such formulas are equivalent to [top]. *)
Inductive top_surf : nformula -> Type :=
| top_s : top_surf top
| par_ls N M : top_surf N -> top_surf (parr N M)
| par_rs N M : top_surf N -> top_surf (parr M N)
| with_s N M : top_surf N -> top_surf M -> top_surf (awith N M).

Lemma top_imp_top_surf_proof N l : top_surf N -> polsequent l ->
  { pi' : llpol (neg N :: l) & Forall_sequent polsequent pi' }.
Proof.
induction N in l |- *; intros Ht Hp; inversion_clear Ht as [ | ? ? Ht' | ? ? Ht' | ? ? Ht' Ht'' ].
- destruct (IHN1 (neg N2 :: l) Ht') as [pi' Hpol'].
  + apply polsequent_neg_add. assumption.
  + exists (parr_r pi'). split; [ assumption | ].
    apply polsequent_neg_add. assumption.
- destruct (IHN2 (neg N1 :: l) Ht') as [pi' Hpol'].
  + apply polsequent_neg_add. assumption.
  + exists (parr_r (ex_r pi' (Permutation_Type_swap _ _ _))). split; [ split; [ assumption | ] | ].
    * apply polsequent_neg_add. apply polsequent_neg_add. assumption.
    * apply polsequent_neg_add. assumption.
- exists (top_r l). apply polsequent_neg_add. assumption.
- destruct (IHN1 l Ht' Hp) as [pi1' Hpol1].
  destruct (IHN2 l Ht'' Hp) as [pi2' Hpol2].
  exists (with_r pi1' pi2'). split; [ split; assumption | ].
  apply polsequent_neg_add. assumption.
Qed.

Lemma bipos_top_surf l (pi : llpol l) P' Q' l' : Permutation_Type l (pos P' :: pos Q' :: l') ->
  {'(N, l1, l2) & l' = l1 ++ neg N :: l2 & top_surf N }.
Proof.
induction pi in P', Q', l' |- *; intros HP.
- apply Permutation_Type_length_2_inv in HP as [ HP | HP ]; discriminate HP.
- eapply IHpi.
  etransitivity; [ apply p | apply HP ].
- apply Permutation_Type_length_1_inv in HP. discriminate HP.
- assert (HP' := HP).
  symmetry in HP'. apply Permutation_Type_vs_cons_inv in HP' as ((l2 & l3) & Heq).
  destruct l2; inversion Heq.
  destruct l2; inversion H1; subst.
  rewrite 2 app_comm_cons in HP. apply Permutation_Type_cons_app_inv in HP. list_simpl in HP.
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
    rewrite Heq' in HP. symmetry in HP.
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

Theorem llpol_is_ll_polsequent l (pi : llpol l) : polsequent l ->
  { pi' : llpol l & Forall_sequent polsequent pi' }.
Proof.
induction pi; cbn; intros Hpol.
- exists (ax_r X). assumption.
- symmetry in p.
  destruct (IHpi (Permutation_Type_polsequent p Hpol)) as [pi' Hpi'].
  symmetry in p.
  exists (ex_r pi' p). split; assumption.
- exists one_r.
  right. exists (nil, one). reflexivity.
- destruct (IHpi (polsequent_neg_rem Hpol)) as [pi' Hpi'].
  exists (bot_r pi'). split; assumption.
- apply polsequent_pos_rem_strong in Hpol as [l' Heq].
  symmetry in Heq. decomp_map_inf Heq. subst.
  assert (polsequent (pos P :: map neg l0)) as [pi1' Hpol1]%IHpi1 by (right; exists (l0, P); reflexivity).
  assert (polsequent (pos Q :: map neg l3)) as [pi2' Hpol2]%IHpi2 by (right; exists (l3, Q); reflexivity).
  exists (tens_r pi1' pi2'). split; [ split; assumption | ].
  right. exists (l0 ++ l3, tens P Q). cbn. rewrite map_app. reflexivity.
- apply polsequent_neg_rem in Hpol.
  destruct (IHpi (polsequent_neg_add N (polsequent_neg_add M Hpol))) as [pi' Hpi'].
  exists (parr_r pi'). split; [ assumption | ].
  apply polsequent_neg_add. assumption.
- exists (top_r l). assumption.
- destruct (polsequent_pos_rem_strong Hpol) as [l' ->].
  assert (polsequent (pos P :: map neg l')) as [pi' Hpol']%IHpi by (right; exists (l', P); reflexivity).
  exists (plus_r1 Q pi'). split; [ assumption | ].
  right. exists (l', aplus P Q). reflexivity.
- destruct (polsequent_pos_rem_strong Hpol) as [l' ->].
  assert (polsequent (pos P :: map neg l')) as [pi' Hpol']%IHpi by (right; exists (l', P); reflexivity).
  exists (plus_r2 Q pi'). split; [ assumption | ].
  right. exists (l', aplus Q P). reflexivity.
- apply polsequent_neg_rem in Hpol.
  destruct (IHpi1 (polsequent_neg_add N Hpol)) as [pi1' Hpol1].
  destruct (IHpi2 (polsequent_neg_add M Hpol)) as [pi2' Hpol2].
  exists (with_r pi1' pi2'). split; [ split; assumption | ].
  apply polsequent_neg_add. assumption.
- assert (polsequent (neg N :: map neg (map wn l))) as [pi' Hpol']%IHpi
    by (left; exists (N :: map wn l); reflexivity).
  exists (oc_r _ pi'). split; [ assumption | ].
  right. exists (map wn l, oc N). reflexivity.
- assert (Hpol' := Hpol).
  destruct Hpol' as [ [l0 Heq] | [[l0 Q] HP] ].
  + symmetry in Heq. decomp_map_inf Heq. subst.
    assert (polsequent (pos P :: map neg l2)) as [pi' Hpol']%IHpi by (right; exists (l2, P); reflexivity).
    exists (de_r pi'). split; [ assumption | ].
    left. exists (wn P :: l2). reflexivity.
  + destruct (Permutation_Type_vs_cons_inv HP) as [(l2, l3) Heq].
    destruct l2; inversion Heq; subst.
    destruct (@bipos_top_surf _ pi P Q (l2 ++ l3)) as [[[N l] l'] Heq' Htop].
    { symmetry. apply Permutation_Type_cons, Permutation_Type_cons_app; reflexivity. }
    assert (Permutation_Type (neg (wn P) :: l2 ++ pos Q :: l3) (pos Q :: neg (wn P) :: l2 ++ l3)) as HP'.
    { symmetry. rewrite ? app_comm_cons. apply Permutation_Type_cons_app. reflexivity. }
    apply (Permutation_Type_polsequent HP') in Hpol.
    apply polsequent_pos_rem_strong in Hpol as [l'' Heq''].
    symmetry in Heq''. decomp_map_inf Heq''. subst.
    rewrite <- map_app in Heq'. decomp_map_inf Heq'. subst.
    injection Heq'3 as [= ->].
    assert (polsequent (pos Q :: neg (wn P) :: map neg l2 ++ map neg l7)) as Hpol.
    { right. exists (wn P :: l2 ++ l7, Q). cbn. rewrite map_app. reflexivity. }
    destruct (top_imp_top_surf_proof Htop Hpol) as [pit Hpolt].
    assert (Permutation_Type (neg N :: pos Q :: neg (wn P) :: map neg l2 ++ map neg l7)
                             (neg (wn P) :: map neg l5 ++ pos Q :: map neg l6)) as HP''.
    { transitivity (pos Q :: neg (wn P) :: map neg l5 ++ map neg l6).
      - rewrite <- ? map_app, <- Heq'. list_simpl.
        rewrite ? (app_comm_cons _ _ (neg (wn P))), ? (app_comm_cons _ _ (pos Q)).
        apply Permutation_Type_cons_app. reflexivity.
      - rewrite ? app_comm_cons. apply Permutation_Type_cons_app. reflexivity. }
    exists (ex_r pit HP''). split; [ assumption | ].
    right. exists (wn P :: l5 ++ l6, Q).
    symmetry. rewrite ? app_comm_cons. apply Permutation_Type_cons_app. cbn. rewrite map_app. reflexivity.
- destruct (IHpi (polsequent_neg_rem Hpol)) as [pi' Hpi'].
  exists (wk_r P pi'). split; assumption.
- apply polsequent_neg_rem in Hpol.
  destruct (IHpi (polsequent_neg_add (wn P) (polsequent_neg_add (wn P) Hpol))) as [pi' Hpi'].
  exists (co_r pi'). split; [ assumption | ].
  apply polsequent_neg_add. assumption.
Qed.

(** [llpol] with [top] rule constrained to at most one positive formula. *)
Inductive llpolt : list formula -> Type :=
| ax_rt X : llpolt (neg (covar X) :: pos (var X) :: nil)
| ex_rt l1 l2 : llpolt l1 -> Permutation_Type l1 l2 -> llpolt l2
| one_rt : llpolt (pos one :: nil)
| bot_rt l : llpolt l -> llpolt (neg bot :: l)
| tens_rt P Q l1 l2 : llpolt (pos P :: l1) -> llpolt (pos Q :: l2) -> llpolt (pos (tens P Q) :: l1 ++ l2)
| parr_rt N M l : llpolt (neg N :: neg M :: l) -> llpolt (neg (parr N M) :: l)
| top_rt l : polsequent l -> llpolt (neg top :: l)
| plus_rt1 P Q l : llpolt (pos P :: l) -> llpolt (pos (aplus P Q) :: l)
| plus_rt2 P Q l : llpolt (pos P :: l) -> llpolt (pos (aplus Q P) :: l)
| with_rt N M l : llpolt (neg N :: l) -> llpolt (neg M :: l) -> llpolt (neg (awith N M) :: l)
| oc_rt N l : llpolt (neg N :: map neg (map wn l)) -> llpolt (pos (oc N) :: map neg (map wn l))
| de_rt P l : llpolt (pos P :: l) -> llpolt (neg (wn P) :: l)
| wk_rt P l : llpolt l -> llpolt (neg (wn P) :: l)
| co_rt P l : llpolt (neg (wn P) :: neg (wn P) :: l) -> llpolt (neg (wn P) :: l).

Instance llpolt_perm : Proper ((@Permutation_Type _) ==> arrow) llpolt.
Proof. intros l1 l2 HP pi. eapply ex_rt; eassumption. Qed.

(** For polarized sequents, [llpol] corresponds to [top] rule with at most one positive formula. *)
Theorem llpol_llpolt l : polsequent l -> llpol l -> llpolt l.
Proof.
intros Hpol [pi Hpol']%llpol_is_ll_polsequent; [ | assumption ].
clear Hpol; induction pi;
  try (now constructor);
  try (now destruct Hpol'; constructor; try apply IHpi; try apply IHpi1; try apply IHpi2; tauto).
- destruct Hpol'.
  eapply ex_rt; try eassumption. auto.
- apply top_rt.
  apply polsequent_neg_rem in Hpol'. assumption.
Qed.

Theorem llpolt_llpol l : llpolt l -> (polsequent l * llpol l).
Proof.
intros pi. induction pi; split;
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
- apply polsequent_pos_rem_strong in Hpol1 as [l1' ->].
  apply polsequent_pos_rem_strong in Hpol2 as [l2' ->].
  right; exists (l1' ++ l2', tens P Q); cbn; rewrite map_app; reflexivity.
- apply polsequent_neg_rem, polsequent_neg_rem in Hpol.
  apply polsequent_neg_add; assumption.
- apply polsequent_pos_rem_strong in Hpol as [l' ->].
  right; exists (l', aplus P Q); reflexivity.
- apply polsequent_pos_rem_strong in Hpol as [l' ->].
  right; exists (l', aplus Q P); reflexivity.
- apply polsequent_neg_rem in Hpol1.
  apply polsequent_neg_add; assumption.
- right; exists (map wn l, oc N); reflexivity.
- apply polsequent_pos_rem_strong in Hpol as [l' ->].
  left; exists (wn P :: l'); reflexivity.
- eapply polsequent_neg_rem; eassumption.
Qed.

End Atoms.
