(** * Example of a concrete use of the yalla library: intuitionistic logic*)

From OLlibs Require Import funtheory infinite List_more Permutation_Type_more.


(** ** 0. load the [ill] library *)

From Yalla Require Import atoms.
From Yalla Require ill_cut ill_vs_ll.

Set Implicit Arguments.


Section Atoms.

Context {atom : DecType} {preiatom : DecType}.

(** ** 1. define formulas *)

Inductive iformula :=
| ivar (_ : @iformulas.iatom preiatom)
| itrue | ifalse
| iand (_ _ : iformula) | ior (_ _ : iformula) | imap (_ _ : iformula).

(** ** 2. define proofs *)

(** *** Additive presentation *)
Inductive lj : list iformula -> iformula -> Type :=
| ax_r X l : lj (ivar X :: l) (ivar X)
| ex_r l1 l2 A : lj l1 A -> Permutation_Type l1 l2 -> lj l2 A
| true_r l : lj l itrue
| false_lr C l : lj (ifalse :: l) C
| and_rr A B l : lj l A -> lj l B -> lj l (iand A B)
| and_lr1 A B C l : lj (A :: l) C -> lj (iand A B :: l) C
| and_lr2 A B C l : lj (B :: l) C -> lj (iand A B :: l) C
| or_lr A B C l : lj (A :: l) C -> lj (B :: l) C -> lj (ior A B :: l) C
| or_rr1 A B l : lj l A -> lj l (ior A B)
| or_rr2 A B l : lj l B -> lj l (ior A B)
| map_rr A B l : lj (A :: l) B -> lj l (imap A B)
| map_lr A B C l : lj l A -> lj (B :: l) C -> lj (imap A B :: l) C
| co_lr A C l : lj (A :: A :: l) C -> lj (A :: l) C
| wk_lr A C l : lj l C -> lj (A :: l) C.

Lemma co_list_lr l l0 A : lj (l ++ l ++ l0) A -> lj (l ++ l0) A.
Proof.
induction l as [|a l IHl] in l0, A |- *; intro p; [ exact p | ].
cbn. apply co_lr.
apply ex_r with (l ++ a :: a :: l0);
  [ | symmetry; rewrite app_comm_cons; apply Permutation_Type_cons_app, Permutation_Type_middle ].
apply IHl.
eapply ex_r; [ eassumption | ].
list_simpl. etransitivity; [ apply Permutation_Type_middle | ].
apply Permutation_Type_app_head.
rewrite app_comm_cons; apply Permutation_Type_cons_app, Permutation_Type_middle.
Qed.

Lemma wk_list_lr l0 l A : lj l A -> lj (l0 ++ l) A.
Proof. now induction l0 as [|a l0 IHl0] in l, A |- *; intro p; [ exact p | apply wk_lr, IHl0 ]. Qed.

(** *** Multiplicative presentation *)
Inductive lj_mul : list iformula -> iformula -> Type :=
| max_r X : lj_mul (ivar X :: nil) (ivar X)
| mex_r l1 l2 A : lj_mul l1 A -> Permutation_Type l1 l2 -> lj_mul l2 A
| mtrue_r : lj_mul nil itrue
| mfalse_lr C l : lj_mul (ifalse :: l) C
| mand_rr A B l1 l2 : lj_mul l1 A -> lj_mul l2 B -> lj_mul (l1 ++ l2) (iand A B)
| mand_lr A B C l : lj_mul (A :: B :: l) C -> lj_mul (iand A B :: l) C
| mor_lr A B C l : lj_mul (A :: l) C -> lj_mul (B :: l) C -> lj_mul (ior A B :: l) C
| mor_rr1 A B l : lj_mul l A -> lj_mul l (ior A B)
| mor_rr2 A B l : lj_mul l B -> lj_mul l (ior A B)
| mmap_rr A B l : lj_mul (A :: l) B -> lj_mul l (imap A B)
| mmap_lr A B C l1 l2 : lj_mul l1 A -> lj_mul (B :: l2) C -> lj_mul (imap A B :: l1 ++ l2) C
| mwk_lr A C l : lj_mul l C -> lj_mul (A :: l) C
| mco_lr A C l : lj_mul (A :: A :: l) C -> lj_mul (A :: l) C.

Lemma mco_list_lr l l0 A : lj_mul (l ++ l ++ l0) A -> lj_mul (l ++ l0) A.
Proof.
induction l as [|a l IHl] in l0, A |- *; cbn; intro p; [ exact p | ].
apply mco_lr.
apply mex_r with (l ++ a :: a :: l0);
  [ | symmetry; rewrite app_comm_cons; apply Permutation_Type_cons_app, Permutation_Type_middle ].
apply IHl.
eapply mex_r; [ eassumption | ].
list_simpl. etransitivity; [ apply Permutation_Type_middle | ].
apply Permutation_Type_app_head.
rewrite app_comm_cons; apply Permutation_Type_cons_app, Permutation_Type_middle.
Qed.

Lemma mwk_list_lr l l0 A : lj_mul l0 A -> lj_mul (l ++ l0) A.
Proof. induction l in l0, A |- *; intro p; [ exact p | apply mwk_lr, IHl, p ]. Qed.

(** *** Equivalence of the two presentations *)
Lemma lj_mul2lj l A : lj_mul l A -> lj l A.
Proof.
intros p. induction p; try now constructor.
- eapply ex_r; eassumption.
- apply and_rr.
  + apply ex_r with (l2 ++ l1); [ | apply Permutation_Type_app_comm ].
    apply wk_list_lr. assumption.
  + apply wk_list_lr. assumption.
- apply co_lr, and_lr2.
  apply ex_r with (iand A B :: B :: l); [ | apply Permutation_Type_swap ].
  apply and_lr1. assumption.
- apply map_lr.
  + apply ex_r with (l2 ++ l1); [ | apply Permutation_Type_app_comm ].
    apply wk_list_lr. assumption.
  + apply ex_r with (l1 ++ B :: l2); [ | symmetry; apply Permutation_Type_middle ].
    apply wk_list_lr. assumption.
Qed.

Lemma lj2lj_mul l A : lj l A -> lj_mul l A.
Proof.
intros p. induction p; try now constructor.
- apply mex_r with (l ++ ivar X :: nil); [ | symmetry; apply Permutation_Type_cons_append ].
  apply mwk_list_lr, max_r.
- eapply mex_r; eassumption.
- rewrite <- (app_nil_r _). apply mwk_list_lr, mtrue_r.
- rewrite <- (app_nil_r _). apply mco_list_lr.
  rewrite app_nil_r. apply mand_rr; assumption.
- apply mand_lr.
  apply mex_r with (B :: A :: l); [ | apply Permutation_Type_swap ].
  apply mwk_lr. assumption.
- apply mand_lr, mwk_lr. assumption.
- apply mex_r with (l ++ imap A B :: nil); [ | symmetry; apply Permutation_Type_cons_append ].
  apply mco_list_lr.
  apply mex_r with (imap A B :: l ++ l); [ | rewrite ! app_assoc; apply Permutation_Type_cons_append ].
  apply mmap_lr; assumption.
Qed.

(** ** 3. translation from ill to lj *)

Fixpoint ill2lj A :=
match A with
| iformulas.ivar x => ivar x
| iformulas.ione => itrue
| iformulas.izero => ifalse
| iformulas.itens A B => iand (ill2lj A) (ill2lj B)
| iformulas.iplus A B => ior (ill2lj A) (ill2lj B)
| iformulas.ilmap A B => imap (ill2lj A) (ill2lj B)
| iformulas.ioc A => ill2lj A
| iformulas.iwith A B => iand (ill2lj A) (ill2lj B)
| iformulas.ilpam A B => imap (ill2lj A) (ill2lj B)
| iformulas.ineg A => imap (ill2lj A) (ivar iformulas.atN)
| iformulas.igen A => imap (ill2lj A) (ivar iformulas.atN)
| iformulas.itop => itrue
end.

Lemma skeleton l A : ill_cut.ill_ll l A -> lj (map ill2lj l) (ill2lj A).
Proof.
intros pi. induction pi; cbn;
  try (eapply ex_r with (map ill2lj (_ :: l1 ++ l2));
        [ cbn | apply Permutation_Type_map, Permutation_Type_middle ]);
  try (constructor; assumption);
  try (constructor; eapply ex_r; [ eassumption | rewrite ? map_app; symmetry; apply Permutation_Type_middle ]).
- apply ex_r with (map ill2lj l1); [ | apply Permutation_Type_map ]; assumption.
- eapply ex_r; [ eassumption | ].
  apply Permutation_Type_map, Permutation_Type_app_head,
        Permutation_Type_app_tail, Permutation_Type_map; assumption.
- list_simpl. apply and_rr.
  + apply ex_r with (map ill2lj l2 ++ map ill2lj l1); [ | apply Permutation_Type_app_comm ].
    apply wk_list_lr. assumption.
  + apply wk_list_lr. assumption.
- apply co_lr.
  apply and_lr2.
  apply ex_r with (iand (ill2lj A) (ill2lj B) :: ill2lj B :: map ill2lj (l1 ++ l2));
    [ | apply Permutation_Type_swap ].
  apply and_lr1.
  eapply ex_r; [ eassumption | ].
  list_simpl. symmetry. apply Permutation_Type_cons_app, Permutation_Type_middle.
- constructor. eapply ex_r; [ eassumption | ]. list_simpl. symmetry. apply Permutation_Type_cons_append.
- apply ex_r with (map ill2lj (iformulas.ilpam A B :: l0 ++ l1 ++ l2));
    [ | list_simpl; rewrite app_comm_cons; apply Permutation_Type_app_swap_app ].
  cbn. apply map_lr.
  + apply ex_r with (map ill2lj ((l1 ++ l2) ++ l0)); [ | list_simpl; symmetry; apply Permutation_Type_app_rot ].
    rewrite map_app. apply wk_list_lr. assumption.
  + apply ex_r with (map ill2lj (l0 ++ l1 ++ B :: l2));
      [ | list_simpl; symmetry; rewrite ? app_assoc; apply Permutation_Type_middle ].
    rewrite map_app. apply wk_list_lr. assumption.
- constructor. eapply ex_r; [ eassumption | ]. list_simpl. symmetry. apply Permutation_Type_cons_append.
- apply map_lr; [ assumption | apply ax_r ].
- apply ex_r with (map ill2lj (iformulas.ilmap A B :: l0 ++ l1 ++ l2)).
  2:{ list_simpl. cons2app. rewrite ? app_assoc. apply Permutation_Type_app_tail.
      list_simpl. etransitivity; [ apply Permutation_Type_cons_append | ].
      list_simpl. apply Permutation_Type_app_swap_app. }
  cbn. apply map_lr.
  + apply ex_r with (map ill2lj ((l1 ++ l2) ++ l0)); [ | list_simpl; symmetry; apply Permutation_Type_app_rot ].
    rewrite map_app. apply wk_list_lr. assumption.
  + apply ex_r with (map ill2lj (l0 ++ l1 ++ B :: l2));
      [ | list_simpl; symmetry; rewrite ? app_assoc; apply Permutation_Type_middle ].
    rewrite map_app. apply wk_list_lr. assumption.
- apply ex_r with (map ill2lj (iformulas.ineg A :: l)); [ | list_simpl; apply Permutation_Type_cons_append ].
  apply map_lr; [ assumption | apply ax_r ].
- apply or_lr.
  + eapply ex_r; [ apply IHpi1 | ].
    rewrite <- map_cons. list_simpl. symmetry. apply Permutation_Type_middle.
  + eapply ex_r; [ apply IHpi2 | ].
    rewrite <- map_cons. list_simpl. symmetry. apply Permutation_Type_middle.
- assumption.
- eapply ex_r; [ eassumption | ]. list_simpl. symmetry. apply Permutation_Type_middle.
- constructor. eapply ex_r; [ eassumption | ].
  list_simpl. symmetry. apply Permutation_Type_cons_app, Permutation_Type_middle.
- discriminate f.
- destruct a.
Qed.

(** ** 4. define embedding into [iformulas.iformula] by call-by-value Girard's translation *)

Fixpoint lj2ill_cbv A :=
match A with
| ivar x     => iformulas.ivar x
| itrue      => iformulas.ione
| ifalse     => iformulas.izero
| iand A B   => iformulas.itens (iformulas.ioc (lj2ill_cbv A)) (iformulas.ioc (lj2ill_cbv B))
| ior A B    => iformulas.iplus (iformulas.ioc (lj2ill_cbv A)) (iformulas.ioc (lj2ill_cbv B))
| imap A B   => iformulas.ilmap (iformulas.ioc (lj2ill_cbv A)) (iformulas.ioc (lj2ill_cbv B))
end.

Lemma ill2lj_lj2ill_cbv_id : retract ill2lj lj2ill_cbv.
Proof. intros A. induction A; cbn; rewrite ? IHA1, ? IHA2; reflexivity. Qed.

Lemma lj2ill_cbv_inj : injective lj2ill_cbv.
Proof. eapply section_injective, ill2lj_lj2ill_cbv_id. Qed.

Definition oc_lj2ill_cbv A := iformulas.ioc (lj2ill_cbv A).


(** *** prove equivalence of proof predicates *)
Lemma lj_mul2illfrag_cbv l A : lj_mul l A -> ill_cut.ill_ll (map oc_lj2ill_cbv l) (oc_lj2ill_cbv A).
Proof.
unfold oc_lj2ill_cbv. intros pi. induction pi; cbn.
- change (iformulas.ioc (iformulas.ivar X) :: nil) with (map iformulas.ioc (iformulas.ivar X :: nil)).
  apply ill_def.oc_irr.
  rewrite <- (app_nil_l _). apply ill_def.de_ilr. rewrite app_nil_l.
  apply ill_def.ax_ir.
- apply ill_def.ex_ir with (map oc_lj2ill_cbv l1); [ assumption | ].
  apply Permutation_Type_map. assumption.
- change nil with (map (@iformulas.ioc preiatom) nil).
  apply ill_def.oc_irr, ill_def.one_irr.
- rewrite <- (app_nil_l _). apply ill_def.de_ilr, ill_def.zero_ilr.
- rewrite <- map_map. rewrite <- map_map in IHpi1. rewrite <- map_map in IHpi2.
  apply ill_def.oc_irr.
  rewrite 2 map_app. apply ill_def.tens_irr; assumption.
- rewrite <- (app_nil_l _). apply ill_def.de_ilr, ill_def.tens_ilr; assumption.
- rewrite <- (app_nil_l _). apply ill_def.de_ilr, ill_def.plus_ilr; assumption.
- rewrite <- map_map. rewrite <- map_map in IHpi.
  apply ill_def.oc_irr, ill_def.plus_irr1. assumption.
- rewrite <- map_map. rewrite <- map_map in IHpi.
  apply ill_def.oc_irr, ill_def.plus_irr2. assumption.
- rewrite <- map_map. rewrite <- map_map in IHpi.
  apply ill_def.oc_irr, ill_def.lmap_irr. assumption.
- rewrite <- (app_nil_l _). apply ill_def.de_ilr. rewrite <- map_map.
  apply ill_def.ex_ir
    with (nil ++ map oc_lj2ill_cbv l1 ++ lj2ill_cbv (imap A B) :: (map oc_lj2ill_cbv l2)).
  + apply ill_def.lmap_ilr; assumption.
  + cbn. rewrite map_map. list_simpl. symmetry. apply Permutation_Type_middle.
- rewrite <- (app_nil_l _). apply ill_def.wk_ilr. assumption.
- rewrite <- (app_nil_l _). apply ill_def.co_ilr. assumption.
Qed.

Lemma lj2illfrag_cbv l A : lj l A -> ill_cut.ill_ll (map oc_lj2ill_cbv l) (oc_lj2ill_cbv A).
Proof. intros pi. apply lj_mul2illfrag_cbv, lj2lj_mul, pi. Qed.

Lemma illfrag2lj_cbv l A : ill_cut.ill_ll (map oc_lj2ill_cbv l) (oc_lj2ill_cbv A) -> lj l A.
Proof.
intros pi%skeleton.
cbn in pi. rewrite ill2lj_lj2ill_cbv_id in pi.
replace l with (map ill2lj (map oc_lj2ill_cbv l)); [ assumption | ].
rewrite map_map. rewrite <- (map_id l) at 2.
apply map_ext, ill2lj_lj2ill_cbv_id.
Qed.

End Atoms.

Section Atoms_inj.

Context {atom : InfDecType} {preiatom : DecType} {Atoms : IAtom2AtomType_retract atom preiatom}.

Notation iformula := (@iformula preiatom).
Notation ill2ll := ill_vs_ll.ill2ll.

Lemma lj2ill_cbv_oclpam (A : iformula) : ill_vs_ll.oclpam (lj2ill_cbv A).
Proof. induction A; (try now constructor); cbn; repeat constructor; assumption. Qed.

Lemma lj2llfrag_cbv l A : lj l A ->
  ll_fragments.ll_ll (ill2ll (oc_lj2ill_cbv A) :: rev (map formulas.dual (map ill2ll (map oc_lj2ill_cbv l)))).
Proof.
intros pi%lj2illfrag_cbv.
eapply ill_vs_ll.ill_to_ll in pi.
eapply ll_def.stronger_pfrag; [ | apply pi ].
repeat split.
- intros C. cbn. destruct (ill_vs_ll.ill2ll_inv C) as [x _], (existsb ill_def.ipcut_none (fst x)) eqn:Hb.
  + exfalso. apply existsb_exists in Hb as [z [_ [=]]].
  + apply BoolOrder.false_le.
- intros [].
Qed.

Lemma llfrag2lj_cbv l A :
  ll_fragments.ll_ll (ill2ll (oc_lj2ill_cbv A) :: rev (map formulas.dual (map ill2ll (map oc_lj2ill_cbv l)))) ->
  lj l A.
Proof.
intros pi.
apply illfrag2lj_cbv, ill_vs_ll.ll_to_ill_oclpam_axfree.
- reflexivity.
- intros [].
- constructor; [ constructor; apply lj2ill_cbv_oclpam | ].
  clear pi. induction l; constructor.
  + constructor. apply lj2ill_cbv_oclpam.
  + apply IHl.
- eapply ll_def.stronger_pfrag; [ | apply pi ].
  repeat split. intros [].
Qed.

(** ** 5 define embedding into [iformulas.iformula] by call-by-name Girard's translation with top and with *)
Fixpoint lj2ill_cbn A : (@iformulas.iformula preiatom) :=
match A with
| ivar X => iformulas.ivar X
| itrue => iformulas.itop
| ifalse => iformulas.izero
| imap A B => iformulas.ilmap (iformulas.ioc (lj2ill_cbn A)) (lj2ill_cbn B)
| iand A B => iformulas.iwith (lj2ill_cbn A) (lj2ill_cbn B)
| ior A B => iformulas.iplus (iformulas.ioc (lj2ill_cbn A)) (iformulas.ioc (lj2ill_cbn B))
end.

Lemma ill2lj_lj2ill_cbn_id : retract ill2lj lj2ill_cbn.
Proof. intros A. induction A; cbn; rewrite ? IHA1, ? IHA2; reflexivity. Qed.

Lemma lj2ill_cbn_inj : injective lj2ill_cbn.
Proof. eapply section_injective, ill2lj_lj2ill_cbn_id. Qed.

Definition oc_lj2ill_cbn A := iformulas.ioc (lj2ill_cbn A).


(** *** prove equivalence of proof predicates *)
Lemma lj2illfrag_cbn l A : lj l A -> ill_cut.ill_ll (map oc_lj2ill_cbn l) (lj2ill_cbn A).
Proof.
unfold oc_lj2ill_cbn; intros pi; induction pi; try now constructor.
- rewrite <- map_map.
  apply ill_def.ex_ir with (map iformulas.ioc (map lj2ill_cbn (l ++ ivar X :: nil)));
    [ | list_simpl; symmetry; apply Permutation_Type_cons_append ].
  list_simpl; rewrite <- (app_nil_l _).
  apply ill_def.wk_list_ilr, ill_def.de_ilr, ill_def.ax_ir.
- eapply ill_def.ex_ir with (map _ l1);
    [ eassumption | cbn; apply Permutation_Type_map; assumption ].
- rewrite <- (app_nil_l _).
  apply ill_def.de_ilr, ill_def.zero_ilr.
- rewrite <- map_map; list_simpl; rewrite <- (app_nil_l _).
  change (iformulas.ioc (iformulas.iwith (lj2ill_cbn A) (lj2ill_cbn B))
            :: map iformulas.ioc (map lj2ill_cbn l))
    with (iformulas.ioc (iformulas.iwith (lj2ill_cbn A) (lj2ill_cbn B))
            :: nil ++ (map iformulas.ioc (map lj2ill_cbn l))).
  rewrite <- map_map in IHpi.
  apply (@ill_cut.cut_ll_ir _ (iformulas.ioc (lj2ill_cbn A))
                              (iformulas.ioc (iformulas.iwith (lj2ill_cbn A) (lj2ill_cbn B)) :: nil)), IHpi.
  change (iformulas.ioc (iformulas.iwith (lj2ill_cbn A) (lj2ill_cbn B)) :: nil)
    with (map iformulas.ioc (iformulas.iwith (lj2ill_cbn A) (lj2ill_cbn B) :: nil)).
  apply ill_def.oc_irr.
  rewrite <- (app_nil_l _).
  apply ill_def.de_ilr, ill_def.with_ilr1, ill_def.ax_exp_ill.
- rewrite <- map_map; list_simpl; rewrite <- (app_nil_l _).
  change (iformulas.ioc (iformulas.iwith (lj2ill_cbn A) (lj2ill_cbn B))
            :: map iformulas.ioc (map lj2ill_cbn l))
    with (iformulas.ioc (iformulas.iwith (lj2ill_cbn A) (lj2ill_cbn B))
            :: nil ++ (map iformulas.ioc (map lj2ill_cbn l))).
  rewrite <- map_map in IHpi.
  apply (@ill_cut.cut_ll_ir _ (iformulas.ioc (lj2ill_cbn B))
        (iformulas.ioc (iformulas.iwith (lj2ill_cbn A) (lj2ill_cbn B)) :: nil)), IHpi.
  change (iformulas.ioc (iformulas.iwith (lj2ill_cbn A) (lj2ill_cbn B)) :: nil)
    with (map iformulas.ioc (iformulas.iwith (lj2ill_cbn A) (lj2ill_cbn B) :: nil)).
  apply ill_def.oc_irr.
  rewrite <- (app_nil_l _).
  apply ill_def.de_ilr, ill_def.with_ilr2, ill_def.ax_exp_ill.
- cbn; rewrite <- (app_nil_l _).
  apply ill_def.de_ilr, ill_def.plus_ilr; assumption.
- rewrite <- map_map in *.
  apply ill_def.plus_irr1, ill_def.oc_irr; assumption.
- rewrite <- map_map in *.
  apply ill_def.plus_irr2, ill_def.oc_irr; assumption.
- rewrite <- map_map in *; cbn.
  apply ill_def.ex_ir
    with (nil ++ map iformulas.ioc (map lj2ill_cbn l) ++
              (iformulas.ioc (iformulas.ilmap (iformulas.ioc (lj2ill_cbn A)) (lj2ill_cbn B)) :: nil));
    [ | list_simpl; symmetry; apply Permutation_Type_cons_append ].
  apply ill_def.co_list_ilr.
  apply ill_def.ex_ir
    with (nil ++ (iformulas.ioc (iformulas.ilmap (iformulas.ioc (lj2ill_cbn A)) (lj2ill_cbn B)) ::
                        (map iformulas.ioc (map lj2ill_cbn l))) ++ (map iformulas.ioc (map lj2ill_cbn l)));
    [ | cbn; rewrite ? app_assoc; apply Permutation_Type_cons_append ].
  apply (@ill_cut.cut_ll_ir _ (iformulas.ioc (lj2ill_cbn B))); [ | assumption ].
  rewrite <- map_cons.
  apply ill_def.oc_irr.
  cbn; rewrite <- (app_nil_l _).
  apply ill_def.de_ilr.
  apply ill_def.ex_ir with (nil ++ map iformulas.ioc (map lj2ill_cbn l) ++
                              iformulas.ilmap (iformulas.ioc (lj2ill_cbn A)) (lj2ill_cbn B) :: nil);
    [ | list_simpl; symmetry; apply Permutation_Type_cons_append ].
  apply ill_def.lmap_ilr.
  + apply ill_def.oc_irr; assumption.
  + apply ill_def.ax_exp_ill.
- rewrite <- (app_nil_l _). apply ill_def.co_ilr. assumption.
- rewrite <- (app_nil_l _). apply ill_def.wk_ilr. assumption.
Qed.

Lemma illfrag2lj_cbn l A :   ill_cut.ill_ll (map oc_lj2ill_cbn l) (lj2ill_cbn A) -> lj l A.
Proof.
intros pi%skeleton.
cbn in pi. rewrite ill2lj_lj2ill_cbn_id in pi.
replace l with (map ill2lj (map oc_lj2ill_cbn l)); [ assumption | ].
rewrite map_map. rewrite <- (map_id l) at 2.
apply map_ext, ill2lj_lj2ill_cbn_id.
Qed.

Lemma lj2ill_cbn_oclpam A : ill_vs_ll.oclpam (lj2ill_cbn A).
Proof. induction A; repeat constructor; assumption. Qed.

Lemma lj2llfrag_cbn l A : lj l A ->
  ll_fragments.ll_ll (ill2ll (lj2ill_cbn A) :: rev (map formulas.dual (map ill2ll (map oc_lj2ill_cbn l)))).
Proof.
intros pi%lj2illfrag_cbn.
apply ill_vs_ll.ill_to_ll in pi.
eapply ll_def.stronger_pfrag; [ | apply pi ].
repeat split.
- intros C. cbn. destruct (ill_vs_ll.ill2ll_inv C) as [x _], (existsb ill_def.ipcut_none (fst x)) eqn:Hb.
  + exfalso. apply existsb_exists in Hb as [z [_ Hz]]. discriminate Hz.
  + apply BoolOrder.false_le.
- intros [].
Qed.

Lemma llfrag2lj_cbn l A :
  ll_fragments.ll_ll (ill2ll (lj2ill_cbn A) :: rev (map formulas.dual (map ill2ll (map oc_lj2ill_cbn l)))) ->
  lj l A.
Proof.
intros pi.
apply illfrag2lj_cbn, ill_vs_ll.ll_to_ill_oclpam_axfree.
- reflexivity.
- intros [].
- constructor; [ apply lj2ill_cbn_oclpam | ].
  clear pi. induction l as [|C l IHl]; constructor.
  + constructor. apply lj2ill_cbn_oclpam.
  + apply IHl.
- eapply ll_def.stronger_pfrag; [ | apply pi ].
  repeat split. intros [].
Qed.


(** ** 6 Import properties *)

Lemma ax_gen_r (A : iformula) : lj (A :: nil) A.
Proof. apply illfrag2lj_cbv, ill_def.ax_exp_ill. Qed.

Lemma cut_ir (A : iformula) l1 l2 C : lj l1 A -> lj (A :: l2) C -> lj (l1 ++ l2) C.
Proof.
intros pi1%lj2illfrag_cbv pi2%lj2illfrag_cbv.
apply illfrag2lj_cbv.
list_simpl. rewrite <- (app_nil_l _). list_simpl in pi2. rewrite <- (app_nil_l _) in pi2.
apply ill_cut.cut_ll_ir with (oc_lj2ill_cbv A); assumption.
Qed.


(** ** 7 Specific developments *)

Lemma disjunction_property (A B : iformula) : lj nil (ior A B) -> lj nil A + lj nil B.
Proof.
intros pi.
remember nil as l eqn:Heql. remember (ior A B) as C eqn:HeqC.
induction pi; inversion Heql; inversion HeqC; subst; [ | left; assumption | right; assumption ].
symmetry in p. apply Permutation_Type_nil in p as ->.
apply IHpi; reflexivity.
Qed.

End Atoms_inj.
