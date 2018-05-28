Require Import List_more.
Import ListNotations.
Require Import yalla_ax.
Require Import ll.
Require Import ill.
Require Import subs.
Require Import genperm.
Require Import nn.


Definition ipfrag_ill := mk_ipfrag true (fun _ _ => False) true.
Definition ill_ll := ill ipfrag_ill.

(* utf8 *)
Notation "'ν' A" := (ivar A) (at level 12).
Infix "⊗" := itens (at level 40).
Infix "⊕" := iplus (at level 40).
Infix "/&\" := iwith (at level 40).
Infix "⊸" := ilmap (at level 40).
Notation "! A" := (ioc A) (at level 31).
Notation "1" := ione.
Notation "0" := izero.
Notation T := itop.

(* for llprover
Infix "*" := itens.
Infix "\/" := iplus.
Infix "/\" := iwith.
Infix "->" := ilmap.
Notation "! A" := (ioc A) (at level 31).
Notation "1" := ione.
Notation bot := izero.
Notation top := itop.
*)

(* for my mallprover *)
Notation Atom := var.
Notation NegAtom := covar.
Notation One := one.
Notation Bot := bot.
Notation Tens := tens.
Notation Par := parr.
Notation Zero := zero.
Notation Top := top.
Notation Plus := aplus.
Notation With := awith.

Definition X := Some 17.
Definition Y := Some 23.
Definition Z := Some 47.
Notation a := (ivar (a2i 17)).
Notation b := (ivar (a2i 23)).
Notation c := (ivar (a2i 47)).
Notation aa := (ivar X).
Notation bb := (ivar Y).
Notation cc := (ivar Z).

Definition seq1 R F := trans R (dual (unill F)) :: nil.
Definition seq2 R F := trans R (unill F) :: F :: nil.
Definition seq1c R F := map dual (map unill (seq1 R F)).
Definition seq2c R F := map dual (map unill (seq2 R F)).

(* 
(((a -> (a /\ b) -> c) \/ (b -> (a /\ b) -> c)) -> (a /\ b) -> c) * (c -> (a /\ b) -> c), (a /\ b) -> c --> (a /\ b) -> c
not provable *)
Goal (forall F, seq1 F F = F :: nil) ->
     (forall F, seq2 F F = F :: nil) ->
     (forall F, seq1c F F = unill F :: nil) ->
     (forall F, seq2c F F = unill F :: nil) ->
True.
Proof.
intros H1 H2 H1c H2c.
(* remember (ilmap (ivar X) (ione)) as F. *)
(* remember (ioc (ivar X)) as F. *)
(* remember (iwith (ivar X) (ivar Y)) as F. *)
remember (ilmap (iwith (ivar X) (ivar Y)) (ivar Z)) as F.
specialize H1 with F ; specialize H2 with F ;
specialize H1c with F ; specialize H2c with F ; subst.
unfold seq1 in H1 ; simpl in H1 ; unfold negR in H1.
unfold seq2 in H2 ; simpl in H2 ; unfold negR in H2.
unfold seq1c in H1c ; simpl in H1c ; unfold negR in H1c.
unfold seq2c in H2c ; simpl in H2c ; unfold negR in H2c.
constructor.
Qed.

Goal forall R, (forall F, trans R (dual (unill F)) = F) ->
               (forall F, F = negR R (trans R (unill F))) -> True.
Proof.
intros R H1 H2.
remember (itop) as F.
specialize H1 with F ; specialize H2 with F ; subst.
unfold seq1 in H1 ; simpl in H1.
unfold seq2 in H2 ; simpl in H2.
constructor.
Qed.



Definition C := ilpam (ioc (ivar X)) (ivar X).
Definition B := ilpam (itens C C) (ivar X).
Definition A := ilpam (ioc B) (ivar X).

Goal (exists s, ill_ll nil A s).
Proof with try PEperm_solve.
unfold A ; unfold B ; unfold C.
eexists.
apply lpam_irr.
apply de_ilr.
eapply (ex_ir _ ([] ++ [B] ++ nil))...
apply lpam_ilr.
- change (@nil iformula) with ((@nil iformula) ++ nil).
  apply tens_irr.
  + apply lpam_irr.
    apply de_ilr.
    apply ax_ir.
  + apply lpam_irr.
    apply de_ilr.
    apply ax_ir.
- apply ax_ir.
Qed.

Goal (exists s, ill_ll (A :: A :: nil) A s).
Proof with try PEperm_solve.
destruct (@ax_exp_ill ipfrag_ill (!B)) as [sB HaxB].
eexists.
apply lpam_irr.
eapply (ex_ir _ ([A;A] ++ map ioc nil ++ [!B]))...
apply co_ilr.
eapply (ex_ir _ ([A;A;!B] ++ map ioc nil ++ [!B]))...
apply co_ilr.
list_simpl.
eapply (ex_ir _ ([A; A] ++ [! B; ! B; ! B] ++ nil))...
apply de_ilr.
eapply (ex_ir _ (nil ++ B :: ([! B; A] ++ [! B ; A]) ++ nil))...
apply lpam_ilr.
- apply tens_irr.
  + apply lpam_irr.
    apply wk_ilr.
    eapply (ex_ir _ (nil ++ A :: [!B] ++ nil))...
    apply lpam_ilr.
    * apply HaxB.
    * apply ax_ir.
  + apply lpam_irr.
    apply wk_ilr.
    eapply (ex_ir _ (nil ++ A :: [!B] ++ nil))...
    apply lpam_ilr.
    * apply HaxB.
    * apply ax_ir.
- apply ax_ir.
Qed.

Goal (forall F, parr bot F = F) ->
  wn (tens (wn one) (wn one)) = subs bot (i2a X) (ill2ll i2a A).
intros Hsimpl.
assert (forall F, tens F one = F) as Hsimpl2.
{ intros F.
  apply dual_inj.
  simpl.
  rewrite Hsimpl.
  reflexivity. }
simpl.
unfold repl_at.
simpl.
rewrite_all Hsimpl.
rewrite_all Hsimpl2.
reflexivity.
Qed.




