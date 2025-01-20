(** * Comparison between Intuitionistic Linear Logic and Linear Logic *)

From OLlibs Require Import Datatypes_more funtheory infinite List_more Permutation_Type_more GPermutation_Type.
From Yalla Require Import ll_fragments.
From Yalla Require Export ill_prop.

Set Default Proof Using "Type".
Set Implicit Arguments.


Section Atoms.

Context {atom : InfDecType} {preiatom : DecType} {Atoms : IAtom2AtomType_fin atom preiatom}.
Notation iatom := (option preiatom).
Notation formula := (@formula atom).
Notation iformula := (@iformula preiatom).
Notation i2a := IAtom2Atom_fin_base.
Notation i2a_inv := IAtom2Atom_fin.


(** ** Characterization of [ill] as a fragment of [ll] *)

(** *** Embedding of [ill] into [ll] *)

Fixpoint ill2ll A :=
match A with
| ivar x    => var (i2a x)
| ione      => one
| itens A B => tens (ill2ll A) (ill2ll B)
| ilpam A B => parr (ill2ll B) (dual (ill2ll A))
| igen A    => parr (var (i2a atN)) (dual (ill2ll A))
| ilmap A B => parr (dual (ill2ll A)) (ill2ll B)
| ineg A    => parr (dual (ill2ll A)) (var (i2a atN))
| itop      => top
| iwith A B => awith (ill2ll A) (ill2ll B)
| izero     => zero
| iplus A B => aplus (ill2ll A) (ill2ll B)
| ioc A     => oc (ill2ll A)
end.

Lemma ill2ll_map_ioc l : map dual (map ill2ll (map ioc l)) = map wn (map dual (map ill2ll l)).
Proof. induction l as [ | a l IHl ]; [ | list_simpl; cbn in IHl; rewrite IHl ]; reflexivity. Qed.

Lemma ill2ll_map_ioc_inv l1 l2 : map wn l1 = map dual (map ill2ll l2) ->
  { l2' | l2 = map ioc l2' & l1 = map dual (map ill2ll l2') }.
Proof.
induction l2 as [|a l2 IHl2] in l1 |- *; intros Heq; destruct l1; inversion Heq as [[Heq' Heq'']].
- exists nil; reflexivity.
- destruct a; inversion_clear Heq'.
  apply IHl2 in Heq'' as [l0 -> ->].
  exists (a :: l0); reflexivity.
Qed.

Lemma ill2ll_inv A : {'(l,lop) & forall B, iffT (A = ill2ll B) (In_inf B l)
                               & forall B, iffT (A = dual (ill2ll B)) (In_inf B lop) }.
Proof.
destruct (i2a_inv (i2a atN)) as [lN HlN].
induction A.
- destruct (i2a_inv c) as [lc Hc].
  exists (map ivar lc, nil); split; intros Himg.
  + destruct B; inversion Himg as [Himg']. subst.
    apply in_inf_map, Hc. reflexivity.
  + apply in_inf_map_inv in Himg as [i Himg].
    destruct B; inversion Himg as [Himg']. subst.
    cbn. f_equal. apply Hc. assumption.
  + destruct B; discriminate Himg.
  + destruct Himg.
- destruct (i2a_inv c) as [lc Hc].
  exists (nil, map ivar lc); split; intros Himg.
  + destruct B; discriminate Himg.
  + destruct Himg.
  + destruct B; inversion Himg as [Himg']. subst.
    apply in_inf_map, Hc. reflexivity.
  + apply in_inf_map_inv in Himg as [i Himg].
    destruct B; inversion Himg as [Himg']. subst.
    cbn. f_equal. apply Hc. assumption.
- exists (ione :: nil, nil); intros B; split; intros Himg.
  + destruct B; inversion Himg. apply in_inf_eq.
  + destruct Himg as [<-|[]]; reflexivity.
  + destruct B; discriminate Himg.
  + destruct Himg.
- exists (nil, ione :: nil); intros B; split; intros Himg.
  + destruct B; discriminate Himg.
  + destruct Himg.
  + destruct B; inversion Himg. apply in_inf_eq.
  + destruct Himg as [<-|[]]; reflexivity.
- destruct IHA1 as [(l1, l1op) H1 H1op].
  destruct IHA2 as [(l2, l2op) H2 H2op].
  destruct (@eq_dt_dec formulas_dectype A1 (covar (i2a atN)));
    destruct (@eq_dt_dec formulas_dectype A2 (covar (i2a atN))).
  + subst. exists (nil, nil); intros B; split; intros Himg.
    * destruct B; inversion Himg as [[Himg1 Himg2]]. destruct B1; discriminate Himg1.
    * destruct Himg.
    * destruct B; inversion Himg as [[Himg1 Himg2]].
      -- destruct B1; discriminate Himg1.
      -- destruct B; discriminate Himg1.
      -- destruct B1; discriminate Himg2.
      -- destruct B; discriminate Himg1.
    * destruct Himg.
  + subst. exists (nil, map (fun '(x, y) => ilmap x (ivar y)) (list_prod l2 lN) ++ map ineg l2);
      intros B; split; intros Himg.
    * destruct B; inversion Himg as [[Himg1 Himg2]]. destruct B1; discriminate Himg1.
    * destruct Himg.
    * destruct B; inversion Himg as [[Himg1 Himg2]].
      -- destruct B1; discriminate Himg1.
      -- contradiction.
      -- subst. destruct B2; inversion Himg1 as [Hi].
         apply HlN in Hi.
         apply in_inf_or_app. left.
         change (ilmap B1 (ivar i)) with ((fun '(x, y) => ilmap x (ivar y)) (B1, i)).
         apply in_inf_map, in_inf_prod; [ apply H2, bidual | apply Hi ].
      -- inversion Himg1 as [Hi]. rewrite bidual in Hi.
         apply in_inf_or_app. right.
         apply in_inf_map, H2, Hi.
    * apply in_inf_app_or in Himg as [Himg|Himg].
      -- apply in_inf_map_inv in Himg as [(B', i) <- [Hin Hi]%in_inf_prod_inv].
         cbn. rewrite bidual. f_equal; [f_equal | ].
         ++ apply HlN, Hi.
         ++ apply H2, Hin.
      -- apply in_inf_map_inv in Himg as [B' <- ->%H2].
         simpl ill2ll. simpl dual. rewrite bidual. reflexivity.
  + subst. exists (nil, map (fun '(x, y) => ilpam x (ivar y)) (list_prod l1 lN) ++ map igen l1);
      intros B; split; intros Himg.
    * destruct B; inversion Himg as [[Himg1 Himg2]]. destruct B2; discriminate Himg2.
    * destruct Himg.
    * destruct B; inversion Himg as [[Himg1 Himg2]].
      -- subst. destruct B2; inversion Himg2 as [Hi].
         apply HlN in Hi.
         apply in_inf_or_app. left.
         change (ilpam B1 (ivar i)) with ((fun '(x, y) => ilpam x (ivar y)) (B1, i)).
         apply in_inf_map, in_inf_prod; [ apply H1, bidual | apply Hi ].
      -- inversion Himg1 as [Hi]. rewrite bidual in Hi.
         apply in_inf_or_app. right.
         apply in_inf_map, H1, Hi.
      -- destruct B1; discriminate Himg2.
      -- destruct B; discriminate Himg2.
    * apply in_inf_app_or in Himg as [Himg|Himg].
      -- apply in_inf_map_inv in Himg as [(B', i) <- [Hin Hi]%in_inf_prod_inv].
         cbn. rewrite bidual. f_equal; [ | f_equal ].
         ++ apply H1, Hin.
         ++ apply HlN, Hi.
      -- apply in_inf_map_inv in Himg as [B' <- ->%H1].
         simpl ill2ll. simpl dual. rewrite bidual. reflexivity.
  + exists (map (fun '(x, y) => itens x y) (list_prod l1 l2),
            map (fun '(x, y) => ilpam x y) (list_prod l1 l2op) ++
            map (fun '(x, y) => ilmap x y) (list_prod l2 l1op));
      intros B; split; intros Himg.
    * destruct B; inversion Himg as [[Himg1 Himg2]].
      change (itens B1 B2) with ((fun '(x, y) => itens x y) (B1, B2)).
      apply in_inf_map, in_inf_prod.
      -- apply H1. assumption.
      -- apply H2. assumption.
    * apply in_inf_map_inv in Himg as [(B1, B2) <- [Hin1 Hin2]%in_inf_prod_inv].
      cbn. f_equal.
      -- apply H1. assumption.
      -- apply H2. assumption.
    * destruct B; inversion Himg as [[Himg1 Himg2]].
      -- apply in_inf_or_app. left.
         change (ilpam B1 B2) with ((fun '(x, y) => ilpam x y) (B1, B2)).
         apply in_inf_map, in_inf_prod.
         ++ apply H1. rewrite <- (bidual (ill2ll B1)). assumption.
         ++ apply H2op. assumption.
      -- contradiction.
      -- apply in_inf_or_app. right.
         change (ilmap B1 B2) with ((fun '(x, y) => ilmap x y) (B1, B2)).
         apply in_inf_map, in_inf_prod.
         ++ apply H2. rewrite <- (bidual (ill2ll B1)). assumption.
         ++ apply H1op. assumption.
      -- contradiction.
    * apply in_inf_app_or in Himg as [Hin|Hin].
      -- apply in_inf_map_inv in Hin as [(B1, B2) <- [Hin1 Hin2]%in_inf_prod_inv].
         cbn. f_equal.
         ++ rewrite bidual. apply H1. assumption.
         ++ apply H2op. assumption.
      -- apply in_inf_map_inv in Hin as [(B1, B2) <- [Hin1 Hin2]%in_inf_prod_inv].
         cbn. f_equal.
         ++ apply H1op. assumption.
         ++ rewrite bidual. apply H2. assumption.
- destruct IHA1 as [(l1, l1op) H1 H1op].
  destruct IHA2 as [(l2, l2op) H2 H2op].
  destruct (@eq_dt_dec formulas_dectype A1 (var (i2a atN))), (@eq_dt_dec formulas_dectype A2 (var (i2a atN))).
  + subst. exists (nil, nil); intros B; split; intros Himg.
    * destruct B; inversion Himg as [[Himg1 Himg2]].
      -- destruct B1; discriminate Himg2.
      -- destruct B; discriminate Himg1.
      -- destruct B1; discriminate Himg1.
      -- destruct B; discriminate Himg1.
    * destruct Himg.
    * destruct B; inversion Himg as [[Himg1 Himg2]]. destruct B1; discriminate Himg2.
    * destruct Himg.
  + subst. exists (map (fun '(x, y) => ilpam x (ivar y)) (list_prod l2op lN) ++ map igen l2op, nil);
      intros B; split; intros Himg.
    * destruct B; inversion Himg as [[Himg1 Himg2]].
      -- subst. destruct B2; inversion Himg1 as [Hi].
         apply HlN in Hi.
         apply in_inf_or_app. left.
         change (ilpam B1 (ivar i)) with ((fun '(x, y) => ilpam x (ivar y)) (B1, i)).
         apply in_inf_map, in_inf_prod; [ apply H2op; reflexivity | apply Hi ].
      -- inversion Himg1 as [Hi].
         apply in_inf_or_app. right.
         apply in_inf_map, H2op, Hi.
      -- destruct B1; discriminate Himg1.
      -- contradiction n.
    * apply in_inf_app_or in Himg as [Himg|Himg].
      -- apply in_inf_map_inv in Himg as [(B1, B2) <- [Hin Hi]%in_inf_prod_inv].
         cbn. f_equal; [ f_equal | ].
         ++ apply HlN, Hi.
         ++ apply H2op, Hin.
      -- apply in_inf_map_inv in Himg as [B' <- ->%H2op].
         reflexivity.
    * destruct B; inversion Himg as [[Himg1 Himg2]]. destruct B2; discriminate Himg1.
    * destruct Himg.
  + subst. exists (map (fun '(x, y) => ilmap x (ivar y)) (list_prod l1op lN) ++ map ineg l1op, nil);
      intros B; split; intros Himg.
    * destruct B; inversion Himg as [[Himg1 Himg2]].
      -- destruct B1; discriminate Himg2.
      -- destruct B; discriminate Himg2.
      -- subst. destruct B2; inversion Himg2 as [Hi].
         apply HlN in Hi.
         apply in_inf_or_app. left.
         change (ilmap B1 (ivar i)) with ((fun '(x, y) => ilmap x (ivar y)) (B1, i)).
         apply in_inf_map, in_inf_prod; [ apply H1op; reflexivity | apply Hi ].
      -- inversion Himg1 as [Hi].
         apply in_inf_or_app. right.
         apply in_inf_map, H1op, Hi.
    * apply in_inf_app_or in Himg as [Himg|Himg].
      -- apply in_inf_map_inv in Himg as [(B1, B2) <- [Hin Hi]%in_inf_prod_inv].
         cbn. f_equal; [ | f_equal ].
         ++ apply H1op, Hin.
         ++ apply HlN, Hi.
      -- apply in_inf_map_inv in Himg as [B' <- ->%H1op].
         reflexivity.
    * destruct B; inversion Himg as [[Himg1 Himg2]]. destruct B1; discriminate Himg2.
    * destruct Himg.
  + exists (map (fun '(x, y) => ilpam x y) (list_prod l2op l1) ++
            map (fun '(x, y) => ilmap x y) (list_prod l1op l2),
            map (fun '(x, y) => itens x y) (list_prod l2op l1op));
      intros B; split; intros Himg.
    * destruct B; inversion Himg as [[Himg1 Himg2]].
      -- apply in_inf_or_app. left.
         change (ilpam B1 B2) with ((fun '(x, y) => ilpam x y) (B1, B2)).
         apply in_inf_map, in_inf_prod.
         ++ apply H2op. assumption.
         ++ apply H1. assumption.
      -- contradiction n.
      -- apply in_inf_or_app. right.
         change (ilmap B1 B2) with ((fun '(x, y) => ilmap x y) (B1, B2)).
         apply in_inf_map, in_inf_prod.
         ++ apply H1op. assumption.
         ++ apply H2. assumption.
      -- contradiction n0.
    * apply in_inf_app_or in Himg as [Hin|Hin].
      -- apply in_inf_map_inv in Hin as [(B1, B2) <- [Hin1 Hin2]%in_inf_prod_inv].
         cbn. f_equal.
         ++ apply H1. assumption.
         ++ apply H2op. assumption.
      -- apply in_inf_map_inv in Hin as [(B1, B2) <- [Hin1 Hin2]%in_inf_prod_inv].
         cbn. f_equal.
         ++ apply H1op. assumption.
         ++ apply H2. assumption.
    * destruct B; inversion Himg as [[Himg1 Himg2]].
      change (itens B1 B2) with ((fun '(x, y) => itens x y) (B1, B2)).
      apply in_inf_map, in_inf_prod.
      -- apply H2op. assumption.
      -- apply H1op. assumption.
    * apply in_inf_map_inv in Himg as [(B1, B2) <- [Hin1 Hin2]%in_inf_prod_inv].
      cbn. f_equal.
      -- apply H1op. assumption.
      -- apply H2op. assumption.
- exists (izero :: nil, itop :: nil); intros B; split; intros Himg.
  + destruct B; inversion Himg. apply in_inf_eq.
  + destruct Himg as [<-|[]]. reflexivity.
  + destruct B; inversion Himg. apply in_inf_eq.
  + destruct Himg as [<-|[]]. reflexivity.
- exists (itop :: nil, izero :: nil); intros B; split; intros Himg.
  + destruct B; inversion Himg. apply in_inf_eq.
  + destruct Himg as [<-|[]]. reflexivity.
  + destruct B; inversion Himg. apply in_inf_eq.
  + destruct Himg as [<-|[]]. reflexivity.
- destruct IHA1 as [(l1, l1op) H1 H1op].
  destruct IHA2 as [(l2, l2op) H2 H2op].
  exists (map (fun '(x, y) => iplus x y) (list_prod l1 l2),
          map (fun '(x, y) => iwith x y) (list_prod l1op l2op));
    intros B; split; intros Himg.
  + destruct B; inversion Himg as [[Himg1 Himg2]].
    change (iplus B1 B2) with ((fun '(x, y) => iplus x y) (B1, B2)).
    apply in_inf_map, in_inf_prod.
    * apply H1. assumption.
    * apply H2. assumption.
  + apply in_inf_map_inv in Himg as [(B1, B2) <- [Hin1 Hin2]%in_inf_prod_inv].
    cbn. f_equal.
    * apply H1. assumption.
    * apply H2. assumption.
  + destruct B; inversion Himg as [[Himg1 Himg2]].
    change (iwith B1 B2) with ((fun '(x, y) => iwith x y) (B1, B2)).
    apply in_inf_map, in_inf_prod.
    * apply H1op. assumption.
    * apply H2op. assumption.
  + apply in_inf_map_inv in Himg as [(B1, B2) <- [Hin1 Hin2]%in_inf_prod_inv].
    cbn. f_equal.
    * apply H1op. assumption.
    * apply H2op. assumption.
- destruct IHA1 as [(l1, l1op) H1 H1op].
  destruct IHA2 as [(l2, l2op) H2 H2op].
  exists (map (fun '(x, y) => iwith x y) (list_prod l1 l2),
          map (fun '(x, y) => iplus x y) (list_prod l1op l2op));
    intros B; split; intros Himg.
  + destruct B; inversion Himg as [[Himg1 Himg2]].
    change (iwith B1 B2) with ((fun '(x, y) => iwith x y) (B1, B2)).
    apply in_inf_map, in_inf_prod.
    * apply H1. assumption.
    * apply H2. assumption.
  + apply in_inf_map_inv in Himg as [(B1, B2) <- [Hin1 Hin2]%in_inf_prod_inv].
    cbn. f_equal.
    * apply H1. assumption.
    * apply H2. assumption.
  + destruct B; inversion Himg as [[Himg1 Himg2]].
    change (iplus B1 B2) with ((fun '(x, y) => iplus x y) (B1, B2)).
    apply in_inf_map, in_inf_prod.
    * apply H1op. assumption.
    * apply H2op. assumption.
  + apply in_inf_map_inv in Himg as [(B1, B2) <- [Hin1 Hin2]%in_inf_prod_inv].
    cbn. f_equal.
    * apply H1op. assumption.
    * apply H2op. assumption.
- destruct IHA as [(l1, l1op) H1 H1op].
  exists (map ioc l1, nil); intros B; split; intros Himg.
  + destruct B; inversion Himg as [Himg1].
    apply in_inf_map, H1. assumption.
  + apply in_inf_map_inv in Himg as [B1 <- Hin].
    cbn. f_equal.
    apply H1. assumption.
  + destruct B; discriminate Himg.
  + destruct Himg.
- destruct IHA as [(l1, l1op) H1 H1op].
  exists (nil, map ioc l1op); intros B; split; intros Himg.
  + destruct B; discriminate Himg.
  + destruct Himg.
  + destruct B; inversion Himg as [Himg1].
    apply in_inf_map, H1op. assumption.
  + apply in_inf_map_inv in Himg as [B1 <- Hin].
    cbn. f_equal.
    apply H1op. assumption.
Defined.

Lemma ill2ll_not_inj : ill2ll (ilmap itop itop) = ill2ll (ilpam izero izero).
Proof. reflexivity. Qed.

Lemma ill2ll_dec A : {B | A = ill2ll B} + (forall B, A <> ill2ll B).
Proof.
destruct (ill2ll_inv A) as [([|B l], _) HB _].
- right. intros B ->. destruct (fst (HB B) eq_refl).
- left. exists B. apply HB, in_inf_eq.
Qed.


(** Translation of proof fragments *)
Definition i2pfrag P := {|
  pcut := fun A => existsb (ipcut P) (fst (projT1 (sigT_of_sigT2 (ill2ll_inv A))));
  pgax := existT (fun x => x -> _) _
                 (fun a => ill2ll (snd (projT2 (ipgax P) a))
                             :: rev (map dual (map ill2ll (fst (projT2 (ipgax P) a)))));
  pmix := pmix_none;
  pperm := ipperm P |}.

Lemma cutrm_i2pfrag P : le_pfrag (cutrm_pfrag (i2pfrag P)) (i2pfrag (cutrm_ipfrag P)).
Proof. repeat split; [ intro a; exists a | ]; reflexivity. Qed.

Lemma i2pfrag_ill_ll : le_pfrag (i2pfrag (ipfrag_ill)) pfrag_ll.
Proof.
repeat split.
- intro A. cbn.
  remember (fst (let (a, _, _) := ill2ll_inv A in a)) as l.
  clear. now induction l as [|C l IHl]; cbn.
- intros [].
Qed.

Lemma ill_to_ll P l C : ill P l C -> ll (i2pfrag P) (ill2ll C :: rev (map dual (map ill2ll l))).
Proof.
intros Hill. induction Hill; list_simpl;
  try list_simpl in IHHill; try list_simpl in IHHill1; try list_simpl in IHHill2.
- eapply ex_r, PCPermutation_Type_swap. apply ax_r.
- eapply ex_r; [ eassumption | ].
  apply PEPermutation_PCPermutation_Type_cons; [ reflexivity | ].
  apply PEPermutation_Type_map, PEPermutation_Type_map, PEPermutation_Type_rev, p.
- rewrite ? ill2ll_map_ioc, ? app_comm_cons in *.
  apply Permutation_Type_rev' in p. do 2 eapply Permutation_Type_map in p.
  eapply ex_wn_r; eassumption.
- apply one_r.
- rewrite app_comm_cons.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply bot_r.
  eapply ex_r; [ eassumption | ].
  rewrite ? app_comm_cons.
  apply PCPermutation_Type_app_comm.
- apply tens_r; assumption.
- rewrite app_comm_cons.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply parr_r.
  eapply ex_r; [ eassumption | ].
  rewrite ? app_comm_cons.
  apply PCPermutation_Type_app_comm.
- apply parr_r. assumption.
- rewrite app_comm_cons, app_assoc.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  rewrite bidual, ? app_assoc, <- ? app_comm_cons.
  apply tens_r; [ assumption | ].
  eapply ex_r; [ eassumption | ].
  rewrite ? app_comm_cons.
  apply PCPermutation_Type_app_comm.
- apply parr_r. assumption.
- rewrite app_comm_cons.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  list_simpl.
  change (var (i2a atN) :: map dual (map ill2ll (rev l)))
    with ((var (i2a atN) :: nil) ++ map dual (map ill2ll (rev l))).
  apply tens_r.
  + rewrite bidual. assumption.
  + apply ax_r.
- apply parr_r.
  eapply ex_r; [ eassumption | ].
  symmetry. rewrite (app_comm_cons _ _ (ill2ll B)).
  apply PCPermutation_Type_cons_append.
- rewrite app_comm_cons.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  rewrite <- ? app_comm_cons, <- ? app_assoc, bidual.
  apply tens_r; [ | assumption ].
  eapply ex_r; [ eassumption | ].
  rewrite ? app_comm_cons.
  apply PCPermutation_Type_app_comm.
- apply parr_r.
  eapply ex_r; [ eassumption | ].
  symmetry. rewrite (app_comm_cons _ _ (ill2ll N)).
  apply PCPermutation_Type_cons_append.
- cons2app.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  rewrite <- ? app_comm_cons, <- ? app_assoc, bidual.
  list_simpl.
  apply tens_r; [ | assumption ].
  apply ax_r.
- apply top_r.
- apply with_r; assumption.
- rewrite ? app_comm_cons.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply plus_r1.
  eapply ex_r; [ eassumption | ].
  rewrite ? app_comm_cons.
  apply PCPermutation_Type_app_comm.
- rewrite ? app_comm_cons.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply plus_r2.
  eapply ex_r; [ eassumption | ].
  rewrite ? app_comm_cons.
  apply PCPermutation_Type_app_comm.
- rewrite ? app_comm_cons.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply top_r.
- apply plus_r1. assumption.
- apply plus_r2. assumption.
- rewrite ? app_comm_cons.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply with_r.
  + eapply ex_r; [ apply IHHill1 | ].
    rewrite ? app_comm_cons.
    apply PCPermutation_Type_app_comm.
  + eapply ex_r; [ apply IHHill2 | ].
    rewrite ? app_comm_cons.
    apply PCPermutation_Type_app_comm.
- rewrite ? ill2ll_map_ioc in *. apply oc_r. assumption.
- rewrite ? app_comm_cons.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply de_r.
  eapply ex_r; [ eassumption | ].
  rewrite ? app_comm_cons.
  apply PCPermutation_Type_app_comm.
- rewrite app_comm_cons.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  rewrite <- ? app_comm_cons.
  apply wk_r.
  eapply ex_r; [ eassumption | ].
  rewrite ? app_comm_cons.
  apply PCPermutation_Type_app_comm.
- rewrite app_comm_cons.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  rewrite <- app_comm_cons.
  apply co_r.
  eapply ex_r; [ eassumption | ].
  rewrite ? app_comm_cons.
  apply PCPermutation_Type_app_comm.
- rewrite app_comm_cons.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  rewrite <- app_assoc.
  assert (pcut (i2pfrag P) (ill2ll A) = true) as fc.
  { cbn. destruct (ill2ll_inv (ill2ll A)) as [(l, lop) Hl _]. cbn.
    assert (Hin := fst (Hl A) eq_refl).
    apply (exists_existsb_inf _ _ A); assumption. }
  eapply (cut_r _ fc); [ | eassumption ].
  eapply ex_r; [ eassumption | ].
  rewrite ? app_comm_cons.
  apply PCPermutation_Type_app_comm.
- enough (ll (i2pfrag P) (projT2 (pgax (i2pfrag P)) a)) as pi.
  { cbn in pi. rewrite 2 map_rev. exact pi. }
  apply gax_r.
Qed.


(** ** Non conservativity of [ll] over [ill]. *)

Lemma no_at_prove_ill (x : iatom) : notT (ill_ll nil (ivar x)).
Proof.
intros pi.
remember (ivar x) as C eqn:HeqC. remember nil as l eqn:Heql.
induction pi in Heql, HeqC |- *; subst;
  try discriminate;
  try now (destruct l1; discriminate Heql).
- symmetry in p.
  apply PEPermutation_Type_nil in p. now apply IHpi.
- apply app_eq_nil in Heql as [-> [->%map_eq_nil ->]%app_eq_nil].
  symmetry in p. apply Permutation_Type_nil in p as ->. apply IHpi; reflexivity.
- apply app_eq_nil in Heql as [_ [_ [=]]%app_eq_nil].
- apply app_eq_nil in Heql as [_ [=]].
- destruct a.
Qed.

Lemma no_biat_prove_ill (x y : iatom) : ill_ll (ivar x :: nil) (ivar y) -> x = y.
Proof.
intros pi.
remember (ivar y) as C eqn:HeqC. remember (ivar x :: nil) as l eqn:Heql.
induction pi in Heql, HeqC |- *; subst;
  (try now (inversion Heql));
  (try now (inversion HeqC));
  try now (destruct l1; inversion Heql; destruct l1; discriminate).
- injection HeqC as [= ->]. injection Heql as [= ->]. reflexivity.
- symmetry in p. apply PEPermutation_Type_length_1_inv in p. now apply IHpi.
- destruct l1; inversion Heql; subst.
  + destruct lw'; inversion H0.
    cbn in H. subst.
    symmetry in p. apply Permutation_Type_nil in p as ->. apply IHpi; reflexivity.
  + apply app_eq_nil in H1 as [-> [->%map_eq_nil ->]%app_eq_nil].
    symmetry in p. apply Permutation_Type_nil in p as ->. apply IHpi; reflexivity.
- destruct l1 as [|? l1], l0 as [|? l0]; inversion Heql; try destruct l0; try destruct l1; discriminate Heql.
- destruct l; inversion Heql; destruct l; discriminate.
Qed.

Lemma no_biat_map_prove_ill (x y : iatom) : ill_ll nil (ilpam (ivar x) (ivar y)) -> x = y.
Proof. intros pi%ilpam_rev_noax; [ | intros []]. apply no_biat_prove_ill, pi. Qed.

Section Non_Conservativity_Atoms.

Variable x y z : iatom.

(** Counter example from Schellinx-Lafont *)
Notation cons_counter_ex := (ilpam (ilpam (ilpam (ivar x) (ivar y)) izero)
                                   (itens (ivar x) (ilpam izero (ivar z)))).

Lemma counter_ll_prove : ll_ll (ill2ll cons_counter_ex :: nil).
Proof.
cbn. apply parr_r.
ll_swap. rewrite <- (app_nil_l (tens (var _) _ :: _)). apply tens_r.
- apply parr_r.
  eapply ex_r; [ | symmetry; apply Permutation_Type_cons_append ].
  eapply ex_r; [ | symmetry; apply Permutation_Type_cons_append ].
  apply tens_r.
  + ll_swap. apply ax_r.
  + apply parr_r.
    eapply ex_r; [ | symmetry; apply Permutation_Type_cons_append ].
    apply top_r.
- apply top_r.
Qed.

Lemma pre_pre_counter_ex_ill : ill_ll (ilpam (ilpam (ivar x) (ivar y)) izero :: nil) (ivar x) -> x = y.
Proof.
intros pi.
remember (ilpam (ilpam (ivar x) (ivar y)) izero :: nil) as l. remember (ivar x) as C.
induction pi in Heql, HeqC |- *; subst;
  try discriminate;
  try now (destruct l1 as [|? l1]; inversion Heql; destruct l1; discriminate).
- symmetry in p.
  apply PEPermutation_Type_length_1_inv in p as ->. apply IHpi; reflexivity.
- destruct l1; inversion Heql; subst.
  + destruct lw'; inversion H0.
    cbn in H. subst.
    symmetry in p. apply Permutation_Type_nil in p as ->. apply IHpi; reflexivity.
  + apply app_eq_nil in H1 as [-> [->%map_eq_nil ->]%app_eq_nil].
    symmetry in p. apply Permutation_Type_nil in p as ->. apply IHpi; reflexivity.
- destruct l1; inversion Heql; try rewrite app_nil_l in Heql; subst.
  + apply app_eq_nil in H2 as [-> ->].
    apply no_biat_map_prove_ill. assumption.
  + apply app_eq_nil in H1 as [_ [=]].
- destruct l1 as [|? l1], l0 as [|? l0]; inversion Heql; try destruct l0; try destruct l1; discriminate.
- destruct l; inversion Heql. destruct l; discriminate.
- destruct a.
Qed.

Lemma pre_counter_ex_ill :
  ill_ll (ilpam (ilpam (ivar x) (ivar y)) izero :: nil) (itens (ivar x) (ilpam izero (ivar z))) -> x = y.
Proof.
intros pi.
remember (ilpam (ilpam (ivar x) (ivar y)) izero :: nil) as l.
remember (itens (ivar x) (ilpam izero (ivar z))) as C.
induction pi in Heql, HeqC |- *; subst;
  try discriminate;
  try now (destruct l1; inversion Heql; destruct l1; discriminate).
- symmetry in p.
  apply PEPermutation_Type_length_1_inv in p. now apply IHpi.
- destruct l1; inversion Heql; subst.
  + destruct lw'; inversion H0.
    cbn in H. subst.
    symmetry in p. apply Permutation_Type_nil in p as ->. apply IHpi; reflexivity.
  + apply app_eq_nil in H1 as [-> [Heq ->]%app_eq_nil].
    destruct lw'; inversion Heq.
    symmetry in p. apply Permutation_Type_nil in p as ->. apply IHpi; reflexivity.
- destruct l1; inversion Heql; inversion HeqC; try rewrite app_nil_l in Heql; subst.
  + contradiction (no_at_prove_ill pi1).
  + apply app_eq_nil in H1 as [-> ->].
    apply (pre_pre_counter_ex_ill pi1).
- destruct l1; inversion Heql; subst.
  + apply app_eq_nil in H2 as [-> ->].
    apply (no_biat_map_prove_ill pi1).
  + destruct l1; discriminate H1.
- destruct l1 as [|? l1], l0 as [|? l0]; inversion Heql; try destruct l0; try destruct l1; discriminate.
- destruct a.
Qed.

Lemma counter_ex_ill : ill_ll nil cons_counter_ex -> x = y.
Proof. intro pi. apply ilpam_rev_noax in pi; [ | intros [] ]. apply (pre_counter_ex_ill pi). Qed.

End Non_Conservativity_Atoms.


(** Counter example from Jui-Hsuan Wu *)
Notation cons_counter_ex_atfree := (ilpam (ilpam (ilpam (ilpam (ilpam izero ione) ione) izero) izero) ione).

Lemma counter_atfree_ll_prove : ll_ll (ill2ll cons_counter_ex_atfree :: nil).
Proof.
cbn. apply parr_r.
eapply ex_r; [ | symmetry; apply Permutation_Type_cons_append ].
apply tens_r.
- apply parr_r.
  eapply ex_r; [ | symmetry; apply Permutation_Type_cons_append ].
  apply tens_r.
  + apply parr_r.
    eapply ex_r; [ | symmetry; apply Permutation_Type_cons_append ].
    apply top_r.
  + apply bot_r, one_r.
- apply top_r.
Qed.

Lemma counter_ex_atfree_ill : notT (@ill_ll preiatom nil cons_counter_ex_atfree).
Proof.
intros pi.
apply ilpam_rev_noax in pi; [ | intros [] ].
remember (nil ++ ilpam (ilpam (ilpam (ilpam izero ione) ione) izero) izero :: nil) as l. remember ione as C.
induction pi in Heql, HeqC |- *; subst;
  try discriminate;
  try now (destruct l1; inversion Heql; destruct l1; discriminate).
- cbn in p. symmetry in p.
  apply Permutation_Type_length_1_inv in p as ->.
  apply IHpi; reflexivity.
- apply IHpi; [ reflexivity | ].
  destruct l1; inversion Heql.
  + destruct lw'; inversion H0.
    symmetry in p. apply Permutation_Type_nil in p as ->. assumption.
  + apply app_eq_nil in H1 as [-> [H1 ->]%app_eq_nil].
    destruct lw'; inversion H1.
    symmetry in p. apply Permutation_Type_nil in p as ->. reflexivity.
- destruct l1; inversion Heql; subst.
  + apply app_eq_nil in H2 as [-> ->]. clear - pi1.
    apply ilpam_rev_noax in pi1; [ | intros [] ].
    remember (nil ++ ilpam (ilpam izero ione) ione :: nil) as l. remember izero as C.
    induction pi1 in Heql, HeqC |- *; subst;
      try discriminate;
      try now (destruct l1; inversion Heql; destruct l1; discriminate).
    * cbn in p. symmetry in p.
      apply Permutation_Type_length_1_inv in p as ->. apply IHpi1; reflexivity.
    * apply IHpi1; [ reflexivity | ].
      destruct l1; inversion Heql.
      -- destruct lw'; inversion H0.
         symmetry in p. apply Permutation_Type_nil in p as ->. assumption.
      -- apply app_eq_nil in H1 as [-> [H1 ->]%app_eq_nil].
         destruct lw'; inversion H1.
         symmetry in p. apply Permutation_Type_nil in p as ->. reflexivity.
    * destruct l1; inversion Heql; subst.
      -- apply app_eq_nil in H2 as [-> ->]. clear - pi1_2.
         remember (nil ++ ione :: nil) as l. remember izero as C.
         induction pi1_2 in Heql, HeqC |- *; subst;
           try discriminate;
           try now (destruct l1; inversion Heql; destruct l1; discriminate).
         ++ cbn in p. symmetry in p.
            apply Permutation_Type_length_1_inv in p as ->.
            apply IHpi1_2; reflexivity.
         ++ apply IHpi1_2; [ | reflexivity ].
            destruct l1; inversion Heql.
            ** destruct lw'; inversion H0.
               symmetry in p. apply Permutation_Type_nil in p as ->. assumption.
            ** apply app_eq_nil in H1 as [-> [H1 ->]%app_eq_nil].
               destruct lw'; inversion H1.
               symmetry in p. apply Permutation_Type_nil in p as ->. reflexivity.
         ++ destruct l1; inversion Heql; subst.
            ** clear - pi1_2.
               remember (nil ++ nil) as l. remember izero as C.
               induction pi1_2 in Heql, HeqC |- *; subst;
                 try discriminate;
                 try now (destruct l1; inversion Heql; destruct l1; discriminate).
               --- symmetry in p. apply Permutation_Type_nil in p as ->.
                   apply IHpi1_2; reflexivity.
               --- apply app_eq_nil in Heql as [-> [Heql ->]%app_eq_nil].
                   destruct lw'; inversion Heql.
                   symmetry in p. apply Permutation_Type_nil in p as ->.
                   apply IHpi1_2; reflexivity.
               --- destruct l1, l0; discriminate Heql.
               --- destruct a.
            ** destruct l1; discriminate.
         ++ destruct l1; inversion Heql.
            ** destruct l0 as [|? l0]; inversion H0. destruct l0; discriminate.
            ** destruct l1, l0; discriminate.
         ++ destruct a.
      -- destruct l1; discriminate.
    * destruct l1; inversion Heql.
      -- destruct l0 as [|? l0]; inversion H0. destruct l0; discriminate.
      -- destruct l1, l0; discriminate.
    * destruct a.
  + destruct l1; discriminate.
- destruct l1; inversion Heql.
  + destruct l0 as [|? l0]; inversion H0. destruct l0; discriminate.
  + destruct l1, l0; discriminate.
- destruct a.
Qed.

End Atoms.


(** ** Conservativity results for [ll] over [ill] *)

Section Conservativity_Atoms.

(** Embedding of [IAtom] into [Atom] *)

Context {atom : InfDecType} {preiatom : DecType} {Atoms : IAtom2AtomType_retract atom preiatom}.
Notation formula := (@formula atom).
Notation iformula := (@iformula preiatom).
Notation i2a := IAtom2Atom_retract_base.
Notation i2a_inj := (section_injective IAtom2Atom_retract).


(** *** Comparisons between [ll] connectives and [ill] *)

Lemma wn_not_idefin A F : notT (ll_mix0 (dual (ill2ll A) :: nil) * ll_mix0 (oc F :: ill2ll A :: nil)).
Proof.
cut (forall l2, ll_mix0 (dual (ill2ll A) :: nil) ->
  Permutation_Type (oc F :: ill2ll A :: nil) l2 -> notT (ll_mix0 l2)).
{ intros H [pi1 pi2]. eapply H; [ eassumption | reflexivity | eassumption ]. }
induction A in F |- *; cbn; intros l2 pi1 HP2 pi2.
- remember (covar (i2a i) :: nil) as l1. revert Heql1. clear - pi1.
  induction pi1; intros Heql1; try (now inversion Heql1); subst.
  + symmetry in p; apply Permutation_Type_length_1_inv in p.
    apply IHpi1; assumption.
  + destruct l1; inversion Heql1; destruct lw'; inversion H0.
    * symmetry in p. now apply Permutation_Type_nil in p as ->.
    * symmetry in p. now apply Permutation_Type_nil in p as ->.
    * destruct l1; discriminate H1.
  + destruct L; try inversion Heql1; discriminate f.
- revert HP2. clear - pi2. induction pi2; intros HP2;
    try (apply Permutation_Type_length in HP2; discriminate HP2);
    try now apply Permutation_Type_length_2_inv in HP2 as [ | ].
  + apply IHpi2.
    symmetry in p. transitivity l2; assumption.
  + apply IHpi2.
    etransitivity; [ apply HP2 | symmetry ].
    apply Permutation_Type_app_head, Permutation_Type_app_tail, Permutation_Type_map, p.
  + destruct L; [ | discriminate f ].
    apply Permutation_Type_sym, Permutation_Type_nil_cons in HP2 as [].
  + apply Permutation_Type_length_2_inv in HP2.
    destruct HP2; inversion e.
    destruct l; discriminate H1.
- rewrite <- (app_nil_l (parr _ _ :: _)) in pi1.
  eapply parr_rev in pi1; [ | intros [] ].
  rewrite app_nil_l in pi1.
  assert ((ll_mix0 (oc F :: ill2ll A1 :: nil) * ll_mix0 (ill2ll A2 :: nil))
        + (ll_mix0 (ill2ll A1 :: nil) * ll_mix0 (oc F :: ill2ll A2 :: nil)))
    as [[pi2' pi2''] | [pi2' pi2'']].
  { revert HP2. clear - pi2; induction pi2; intros HP2;
      try (apply Permutation_Type_length in HP2; discriminate HP2);
      try now apply Permutation_Type_length_2_inv in HP2 as [ | ].
    - apply IHpi2.
      cbn in p. symmetry in p. etransitivity; [ exact HP2 | exact p ].
    - apply IHpi2.
      etransitivity; [ exact HP2 | ].
      symmetry in p. apply Permutation_Type_app_head, Permutation_Type_app_tail, Permutation_Type_map, p.
    - destruct L; [ | discriminate f ].
      apply Permutation_Type_sym, Permutation_Type_nil_cons in HP2 as [].
    - apply Permutation_Type_length_2_inv in HP2.
      destruct HP2; inversion e; subst.
      destruct l2; inversion H2; subst.
      + destruct l1; inversion H2; subst.
        left. split; [ | assumption ].
        eapply ex_r; [ apply pi2_1 | apply Permutation_Type_swap ].
      + apply app_eq_nil in H1 as [-> ->].
        right. split; [ assumption | ].
        eapply ex_r; [ apply pi2_2 | apply Permutation_Type_swap ].
    - apply Permutation_Type_length_2_inv in HP2.
      destruct HP2; inversion e.
      destruct l; inversion H1. }
  + eapply cut_mix0_r in pi1; [ | rewrite bidual; eassumption ].
    eapply IHA1; [ apply pi1 | reflexivity | eassumption ].
  + eapply ex_r in pi1; [ | apply Permutation_Type_swap ].
    eapply cut_mix0_r in pi1; [ | rewrite bidual; eassumption ].
    eapply IHA2; [ apply pi1 | reflexivity | eassumption ].
- eapply tens_rev in pi1; [ | intros [] | intro; reflexivity ].
  cons2app in HP2.
  assert (Heq2 := HP2).
  symmetry in Heq2; apply Permutation_Type_vs_elt_inv in Heq2 as [(l', l'') ->].
  assert (ll_mix0 (l' ++ ill2ll A2 :: dual (ill2ll A1) :: l'')) as pi2'
    by (apply parr_rev; [ intros [] | assumption ]).
  destruct pi1 as [pi1' pi1''].
  rewrite bidual in pi1'.
  eapply (@cut_mix0_r _ _ (l' ++ ill2ll A2 :: l'')) in pi1';
    [ | eapply ex_r; [ apply pi2' | ] ].
  2:{ cbn. clear. symmetry. etransitivity; [ apply Permutation_Type_middle | ].
      apply Permutation_Type_app_head, Permutation_Type_swap. }
  eapply IHA2.
  + assumption.
  + apply Permutation_Type_swap.
  + eapply ex_r; [ apply pi1' | ].
    list_simpl in HP2; cons2app in HP2; apply Permutation_Type_app_inv in HP2.
    list_simpl; etransitivity; [ symmetry; apply Permutation_Type_middle | ].
    symmetry; apply Permutation_Type_cons, HP2; reflexivity.
- eapply tens_rev in pi1; [ | intros [] | intro; reflexivity ].
  destruct pi1 as [_ pi1'].
  clear - pi1'.
  assert ({ l & Permutation_Type (covar (i2a atN) :: nil) l }) as [l HP] by (eexists; reflexivity).
  eapply ex_r in pi1'; [ | apply HP ].
  revert HP; induction pi1'; intros HP;
    try (now (apply Permutation_Type_length in HP; inversion HP));
    try (now (apply Permutation_Type_length_1_inv in HP; inversion HP)).
  + apply IHpi1'.
    symmetry in p. etransitivity; [ exact HP | exact p ].
  + apply IHpi1'.
    symmetry in p. etransitivity; [ exact HP | ].
    apply Permutation_Type_app_head, Permutation_Type_app_tail, Permutation_Type_map, p.
  + destruct L; [ | discriminate f ].
    apply Permutation_Type_sym, Permutation_Type_nil_cons in HP as [].
- eapply tens_rev in pi1; [ | intros [] | intro; reflexivity ].
  cons2app in HP2.
  assert (Heq2 := HP2).
  symmetry in Heq2. apply Permutation_Type_vs_elt_inv in Heq2 as [(l', l'') ->].
  eapply parr_rev in pi2; [ | intros [] ].
  destruct pi1 as [pi1' pi1'']. rewrite bidual in pi1''.
  eapply (@cut_mix0_r _ _ (l' ++ ill2ll A2 :: l'')) in pi1'';
    [ | eapply ex_r; [ apply pi2 | symmetry; apply Permutation_Type_middle ]].
  eapply IHA2.
  + eassumption.
  + apply Permutation_Type_swap.
  + eapply ex_r; [ apply pi1'' | ].
    list_simpl in HP2. cons2app in HP2. apply Permutation_Type_app_inv in HP2.
    list_simpl. etransitivity; [ symmetry; apply Permutation_Type_middle | ].
    symmetry. apply Permutation_Type_cons, HP2; reflexivity.
- eapply tens_rev in pi1; [ | intros [] | intro; reflexivity ].
  destruct pi1 as [pi1' _]. clear - pi1'.
  assert ({ l & Permutation_Type (covar (i2a atN) :: nil) l })
    as [l HP] by (eexists; reflexivity).
  eapply ex_r in pi1'; [ | apply HP ].
  induction pi1' in HP |- *;
    try (apply Permutation_Type_length in HP; discriminate HP);
    try now apply Permutation_Type_length_1_inv in HP.
  + apply IHpi1'.
    symmetry in p. etransitivity; [ exact HP | exact p ].
  + apply IHpi1'.
    symmetry in p. etransitivity; [ exact HP | ].
    apply Permutation_Type_app_head, Permutation_Type_app_tail, Permutation_Type_map, p.
  + destruct L; [ | discriminate f ].
    apply Permutation_Type_sym, Permutation_Type_nil_cons in HP as [].
- remember (zero :: nil) as l1. revert Heql1. clear - pi1.
  induction pi1; intros Heql1; try (now inversion Heql1); subst.
  + symmetry in p. apply Permutation_Type_length_1_inv in p.
    apply IHpi1. assumption.
  + destruct l1; inversion Heql1; destruct lw'; inversion H0.
    * symmetry in p. now apply Permutation_Type_nil in p as ->.
    * symmetry in p. now apply Permutation_Type_nil in p as ->.
    * destruct l1; discriminate H1.
  + destruct L; discriminate.
- eapply plus_rev in pi1; [ | intros [] | intro; reflexivity ].
  destruct pi1 as [ pi1 | pi1 ].
  + cons2app in HP2.
    assert (Heq2 := HP2).
    symmetry in Heq2. apply Permutation_Type_vs_elt_inv in Heq2 as [(l', l'') ->].
    eapply with_rev1 in pi2; [ | intros [] ].
    eapply IHA1.
    * eassumption.
    * apply Permutation_Type_swap.
    * eapply ex_r; [ apply pi2 | ].
      list_simpl in HP2. cons2app in HP2. apply Permutation_Type_app_inv in HP2.
      list_simpl. etransitivity; [ symmetry; apply Permutation_Type_middle | ].
      symmetry. apply Permutation_Type_cons, HP2. reflexivity.
  + cons2app in HP2.
    assert (Heq2 := HP2).
    symmetry in Heq2. apply Permutation_Type_vs_elt_inv in Heq2 as [(l', l'') ->].
    eapply with_rev2 in pi2; [ | intros [] ].
    eapply IHA2.
    * eassumption.
    * apply Permutation_Type_swap.
    * eapply ex_r; [ apply pi2 | ].
      list_simpl in HP2. cons2app in HP2. apply Permutation_Type_app_inv in HP2.
      list_simpl. etransitivity; [ symmetry; apply Permutation_Type_middle | ].
      symmetry. apply Permutation_Type_cons, HP2. reflexivity.
- revert HP2. clear - pi2. induction pi2; intros HP2;
    try (apply Permutation_Type_length in HP2; discriminate HP2);
    try now apply Permutation_Type_length_2_inv in HP2 as [ | ].
  + apply IHpi2.
    symmetry in p. etransitivity; [ exact HP2 | exact p ].
  + apply IHpi2.
    symmetry in p. etransitivity; [ exact HP2 | ].
    apply Permutation_Type_app_head, Permutation_Type_app_tail, Permutation_Type_map, p.
  + destruct L; [ | discriminate f ].
    apply Permutation_Type_sym, Permutation_Type_nil_cons in HP2 as [].
  + apply Permutation_Type_length_2_inv in HP2 as [ | ]; inversion e.
    destruct l; discriminate H1.
- assert (pi0 := pi1).
  rewrite <- (app_nil_l _) in pi1; eapply with_rev1 in pi1; [ | intros [] ].
  rewrite <- (app_nil_l _) in pi0; eapply with_rev2 in pi0; [ | intros [] ].
  assert (ll_mix0 (oc F :: ill2ll A1 :: nil) + ll_mix0 (oc F :: ill2ll A2 :: nil)) as [ pi2' | pi2' ].
  { revert HP2. clear - pi2. induction pi2; intros HP2;
      try (apply Permutation_Type_length in HP2; discriminate HP2);
      try now apply Permutation_Type_length_2_inv in HP2 as [ | ].
    - apply IHpi2.
      symmetry in p. etransitivity; [ exact HP2 | exact p ].
    - apply IHpi2.
      symmetry in p. etransitivity; [ exact HP2 | ].
      apply Permutation_Type_app_head, Permutation_Type_app_tail, Permutation_Type_map, p.
    - destruct L; [ | discriminate f ].
      apply Permutation_Type_sym, Permutation_Type_nil_cons in HP2 as [].
    - apply Permutation_Type_length_2_inv in HP2 as [ | ]; inversion e. subst.
      left. eapply ex_r; [ apply pi2 | ]. cons2app. apply PCPermutation_Type_app_comm.
    - apply Permutation_Type_length_2_inv in HP2 as [ | ]; inversion e. subst.
      right. eapply ex_r; [ apply pi2 | ]. cons2app. apply PCPermutation_Type_app_comm.
    - apply Permutation_Type_length_2_inv in HP2 as [ | ]; inversion e.
      destruct l; discriminate H1. }
  + eapply IHA1; try eassumption; reflexivity.
  + eapply IHA2; try eassumption; reflexivity.
- revert HP2. clear - pi2. induction pi2; intros HP2;
    try (apply Permutation_Type_length in HP2; discriminate HP2);
    try now apply Permutation_Type_length_2_inv in HP2 as [ | ].
  + apply IHpi2.
    symmetry in p. etransitivity; [ exact HP2 | exact p ].
  + apply IHpi2.
    symmetry in p. etransitivity; [ exact HP2 | ].
    apply Permutation_Type_app_head, Permutation_Type_app_tail, Permutation_Type_map, p.
  + destruct L; [ | discriminate f ].
    apply Permutation_Type_sym, Permutation_Type_nil_cons in HP2 as [].
  + apply Permutation_Type_length_2_inv in HP2 as [ | ]; inversion e; destruct l; discriminate H1.
Qed.

Lemma bot_not_idefin A : notT (ll_mix0 (dual (ill2ll A) :: nil) * ll_mix0 (one :: ill2ll A :: nil)).
Proof.
intros [pi1 pi2].
eapply cut_mix0_r in pi2.
- list_simpl in pi2. eapply ex_r in pi2; [ | apply Permutation_Type_swap ].
  eapply wn_not_idefin. split; eassumption.
- apply bot_r.
  change nil with (map (@wn atom) nil).
  apply oc_r, one_r.
Qed.

Lemma wn_one_not_idefin A :
  notT (ll_mix0 (wn one :: dual (ill2ll A) :: nil) * ll_mix0 (oc bot :: ill2ll A :: nil)).
Proof.
intros [pi1 pi2].
eapply cut_mix0_r in pi1.
- list_simpl in pi1.
  eapply wn_not_idefin. split; eassumption.
- change nil with (map (@wn atom) nil).
  apply oc_r, bot_r.
  change (map wn nil) with (concat (@nil (list formula))).
  apply mix_r; constructor.
Qed.

Lemma oc_bot_not_idefin A :
  notT (ll_ll (oc bot :: dual (ill2ll A) :: nil) * ll_mix0 (wn one :: ill2ll A :: nil)).
Proof.
enough (forall l, ll_ll (map dual (map ill2ll l)) ->
          (Forall_inf (fun F => ll_mix0 (ill2ll F :: nil)) l) -> False)
  as Hgen.
{ intros [pi1 pi2].
  eapply cut_ll_r in pi1.
  eapply cut_mix0_r in pi2.
  - change (dual (ill2ll A) :: nil)
      with (map dual (map ill2ll (A :: nil))) in pi1.
    rewrite app_nil_r in pi1.
    list_simpl in pi2.
    eapply Hgen; [ eassumption | ].
    constructor; [ eassumption | constructor ].
  - change nil with (map (@wn atom) nil).
    apply oc_r, bot_r.
    change (map wn nil) with (concat (@nil (list formula))).
    apply mix_r; constructor.
  - apply de_r, one_r. }
intros l pi.
remember (map dual (map ill2ll l)) as l0.
revert l Heql0; induction pi; intros l' Heq HF; subst; try discriminate f.
- destruct l'; inversion Heq.
  destruct l'; inversion Heq.
  destruct i0; inversion H3.
- apply PCPermutation_Type_map_inv in p as [ l1' -> HP ].
  symmetry in HP.
  apply PCPermutation_Type_map_inv in HP as [ l1'' -> HP ].
  eapply IHpi; [ reflexivity | ].
  eapply Permutation_Type_Forall_inf; [ apply HP | eassumption ].
- decomp_map Heq eqn:Heq'. decomp_map Heq. subst.
  symmetry in Heq'. destruct (ill2ll_map_ioc_inv _ _ Heq') as [l' -> ->].
  rewrite map_map in p. apply Permutation_Type_map_inv in p as [l'' -> p].
  rewrite <- (map_map _ _ l''), <- ill2ll_map_ioc, <- ? map_app in IHpi.
  eapply IHpi; [ reflexivity | ].
  assert (HF1 := Forall_inf_app_l _ _ HF).
  assert (HF2 := Forall_inf_app_r _ _ HF).
  assert (HF3 := Forall_inf_app_l _ _ HF2).
  assert (HF4 := Forall_inf_app_r _ _ HF2).
  apply Forall_inf_app; [ assumption | ].
  apply Forall_inf_app; [ | assumption ].
  apply (Permutation_Type_map ioc) in p.
  eapply Permutation_Type_Forall_inf; eassumption.
- destruct l'; inversion Heq.
  destruct i; inversion H0.
- destruct l'; inversion Heq; subst.
  inversion HF.
  eapply IHpi; [ reflexivity | eassumption ].
- destruct l'; inversion Heq.
  symmetry in H1. decomp_map H1. symmetry in H1. decomp_map H1. subst.
  destruct i; inversion H0. subst.
  + inversion HF. subst.
    cbn in X. rewrite <- (app_nil_l _) in X. eapply parr_rev in X; [ | intros [] ].
    list_simpl in X.
    assert (X1 := Forall_inf_app_l _ _ X0).
    assert (X2 := Forall_inf_app_r _ _ X0).
    rewrite bidual in pi1.
    assert (ll_mix0 (ill2ll i1 :: nil)) as pi0.
    { eapply (stronger_pfrag _ pfrag_mix0) in pi1; [ | repeat split; intros [] ].
      revert pi1 X2. clear. induction l1 as [|? ? IHl1]; intros pi HF.
      - assumption.
      - inversion HF. subst.
        cbn in pi. eapply ex_r in pi; [ | apply Permutation_Type_swap ].
        apply (cut_mix0_r pi) in X.
        apply IHl1; assumption. }
    eapply ex_r in X; [ | apply Permutation_Type_swap ].
    apply (cut_mix0_r X) in pi0.
    apply (IHpi2 (i2 :: l2)); constructor; assumption.
  + inversion HF. subst.
    cbn in X. rewrite <- (app_nil_l _) in X; eapply parr_rev in X; [ | intros [] ].
    list_simpl in X.
    assert (X1 := Forall_inf_app_l _ _ X0).
    assert (X2 := Forall_inf_app_r _ _ X0).
    rewrite bidual in pi1.
    assert (ll_mix0 (ill2ll i :: nil)) as pi0.
    { eapply (stronger_pfrag _ pfrag_mix0) in pi1; [ | repeat split; intros [] ].
      revert pi1 X2. clear. induction l1 as [|? ? IHl1]; intros pi HF.
      - assumption.
      - inversion HF. subst.
        cbn in pi. eapply ex_r in pi; [ | apply Permutation_Type_swap ].
        apply (cut_mix0_r pi) in X.
        apply IHl1; assumption. }
    eapply ex_r in X; [ | apply Permutation_Type_swap ].
    apply (cut_mix0_r X) in pi0.
    apply (IHpi2 (ivar atN  :: l2)); constructor; assumption.
  + inversion HF; subst.
    cbn in X; rewrite <- (app_nil_l _) in X; eapply parr_rev in X; [ | intros [] ].
    list_simpl in X.
    assert (X1 := Forall_inf_app_l _ _ X0).
    assert (X2 := Forall_inf_app_r _ _ X0).
    rewrite bidual in pi2.
    assert (ll_mix0 (ill2ll i1 :: nil)) as pi0.
    { eapply (stronger_pfrag _ pfrag_mix0) in pi2; [ | repeat split; intros [] ].
      revert pi2 X1. clear. induction l2 as [|? ? IHl2]; intros pi HF.
      - assumption.
      - inversion HF. subst.
        cbn in pi. eapply ex_r in pi; [ | apply Permutation_Type_swap ].
        apply (cut_mix0_r pi) in X.
        apply IHl2; assumption. }
    apply (cut_mix0_r X) in pi0.
    apply (IHpi1 (i2 :: l1)); constructor; assumption.
  + inversion HF; subst.
    cbn in X; rewrite <- (app_nil_l _) in X; eapply parr_rev in X; [ | intros [] ].
    list_simpl in X.
    assert (X1 := Forall_inf_app_l _ _ X0).
    assert (X2 := Forall_inf_app_r _ _ X0).
    rewrite bidual in pi2.
    assert (ll_mix0 (ill2ll i :: nil)) as pi0.
    { eapply (stronger_pfrag _ pfrag_mix0) in pi2; [ | repeat split; intros [] ].
      revert pi2 X1. clear. induction l2 as [|? ? IHl2]; intros pi HF.
      - assumption.
      - inversion HF. subst.
        cbn in pi. eapply ex_r in pi; [ | apply Permutation_Type_swap ].
        apply (cut_mix0_r pi) in X.
        apply IHl2; assumption. }
    apply (cut_mix0_r X) in pi0.
    apply (IHpi1 (ivar atN :: l1)); constructor; assumption.
- destruct l'; inversion Heq.
  destruct i; inversion H0. subst.
  inversion HF. subst.
  cbn in X. eapply tens_rev in X as [pi1 pi2]; [ | intros [] | intro; reflexivity ].
  apply (IHpi (i2 :: i1 :: l')); constructor; [ | constructor ]; assumption.
- destruct l'; inversion Heq.
  destruct i; inversion H0. subst.
  inversion HF. subst.
  clear - X.
  assert ({ l & Permutation_Type (ill2ll izero :: nil) l }) as [l HP]
    by (eexists; reflexivity).
  eapply ex_r in X; [ | apply HP ].
  revert HP; clear - X; induction X; intros HP;
    try (now apply Permutation_Type_length in HP; inversion HP);
    try (now apply Permutation_Type_length_1_inv in HP; inversion HP).
  + apply IHX.
    symmetry in p. etransitivity; [ exact HP | exact p ].
  + apply IHX.
    symmetry in p. etransitivity; [ exact HP | ].
    apply Permutation_Type_app_head, Permutation_Type_app_tail, Permutation_Type_map, p.
  + destruct L; [ | discriminate f ].
    apply Permutation_Type_sym, Permutation_Type_nil_cons in HP as [].
- destruct l'; inversion Heq.
  destruct i; inversion H0. subst.
  inversion HF. subst.
  cbn in X. rewrite <- (app_nil_l (awith _ _ :: _)) in X.
  eapply with_rev1 in X; [ | intros [] ].
  apply (IHpi (i1 :: l')); constructor; assumption.
- destruct l'; inversion Heq.
  destruct i; inversion H0. subst.
  inversion HF. subst.
  cbn in X. rewrite <- (app_nil_l (awith _ _ :: _)) in X.
  eapply with_rev2 in X; [ | intros [] ].
  apply (IHpi (i2 :: l')); constructor; assumption.
- destruct l'; inversion Heq.
  destruct i; inversion H0. subst.
  inversion HF. subst.
  cbn in X. eapply plus_rev in X as [pi | pi]; [ | | intros [] | intro; reflexivity ].
  + apply (IHpi1 (i1 :: l')); constructor; assumption.
  + apply (IHpi2 (i2 :: l')); constructor; assumption.
- destruct l'; inversion Heq.
  destruct i; discriminate H0.
- destruct l'; inversion Heq.
  destruct i; inversion H0. subst.
  inversion HF. subst.
  cbn in X. rewrite <- (app_nil_l (oc _ :: _)) in X.
  eapply oc_rev in X; [ | intros [] ].
  apply (IHpi (i :: l')); constructor; assumption.
- destruct l'; inversion Heq.
  destruct i; inversion H0. subst.
  inversion HF. subst.
  cbn in X. rewrite <- (app_nil_l (oc _ :: _)) in X.
  eapply oc_rev in X; [ | intros [] ].
  apply (IHpi l'); [ reflexivity | assumption ].
- destruct l'; inversion Heq.
  destruct i; inversion H0. subst.
  apply (IHpi (ioc i :: ioc i :: l')); [ reflexivity | ].
  inversion HF. constructor; assumption.
- destruct a.
Qed.


(** ** Characterization of [ill] as a fragment of [ll] *)

(** *** Conservativity with constraints on [izero] *)

(** Constraints on the presence of [izero] for conservativity *)
Inductive zeropos : iformula -> Type :=
| zp_izero : zeropos izero
| zp_itens_l A B : zeropos A -> zeropos (itens A B)
| zp_itens_r A B : zeropos A -> zeropos (itens B A)
| zp_iwith_l A B : zeropos A -> zeropos (iwith A B)
| zp_iwith_r A B : zeropos A -> zeropos (iwith B A)
| zp_iplus A B : zeropos A -> zeropos B -> zeropos (iplus A B)
| zp_ioc A : zeropos A -> zeropos (ioc A).

Lemma zeropos_ilr P D (Hz : zeropos D) l1 l2 C : ill P (l1 ++ D :: l2) C.
Proof.
induction Hz in l1, l2 |- *; try now constructor.
apply tens_ilr. cons2app. rewrite app_assoc. apply IHHz.
Qed.

Lemma ill2ll_zeropos C D : zeropos C -> ill2ll C = ill2ll D -> zeropos D.
Proof.
intros Hz. induction Hz in D |- *; intros Heq; destruct D; inversion Heq;
  try apply IHHz in H0; try apply IHHz in H1; try now constructor.
constructor; [ exact (IHHz1 _ H0) | exact (IHHz2 _ H1) ].
Qed.

Inductive nonzerospos : iformula -> Type :=
| nzsp_ivar x : nonzerospos (ivar x)
| nzsp_ione : nonzerospos ione
| nzsp_itens A B : nonzerospos A -> nonzerospos B -> nonzerospos (itens A B)
| nzsp_ilpam A B : nonzerospos A -> nonzerospos B -> notT (zeropos B) -> nonzerospos (ilpam A B)
| nzsp_igen A : nonzerospos A -> nonzerospos (igen A)
| nzsp_ilmap A B : nonzerospos A -> nonzerospos B -> notT (zeropos B) -> nonzerospos (ilmap A B)
| nzsp_ineg A : nonzerospos A -> nonzerospos (ineg A)
| nzsp_itop : nonzerospos itop
| nzsp_iwith A B : nonzerospos A -> nonzerospos B -> nonzerospos (iwith A B)
| nzsp_izero : nonzerospos izero
| nzsp_iplus A B : nonzerospos A -> nonzerospos B -> nonzerospos (iplus A B)
| nzsp_ioc A : nonzerospos A -> nonzerospos (ioc A).

Definition easyipgax_nzeropos P := forall a,
  (forall D, ill2ll (snd (projT2 (ipgax P) a)) = dual (ill2ll D) ->
     {'(Z, Zl1, Zl2) & zeropos Z & D :: (fst (projT2 (ipgax P) a)) = Zl1 ++ Z :: Zl2 })
* (forall l C,
     PCPermutation_Type (ipperm P)
           (ill2ll (snd (projT2 (ipgax P) a)) :: rev (map dual (map ill2ll (fst (projT2 (ipgax P) a)))))
           (ill2ll C :: rev (map dual (map ill2ll l)))
       -> ill P l C)
* notT (In_inf N (fst (projT2 (ipgax P) a))).

Lemma dual_jfragment_zeropos P (Hcut : no_icut P) (Hgax : easyipgax_nzeropos P) l0 :
  Forall_inf nonzerospos l0 -> ll (i2pfrag P) (map dual (map ill2ll l0)) ->
  {'(C, Cl1, Cl2) & zeropos C & l0 = Cl1 ++ C :: Cl2 }.
Proof.
intros Hnzsp Hll.
remember (map dual (map ill2ll l0)) as l.
revert l0 Hnzsp Heql.
induction Hll; intros l0 Hnzsp HP.
- exfalso.
  destruct l0; inversion HP.
  destruct l0; inversion HP.
  destruct i0; inversion H3.
- subst.
  rewrite map_map in p.
  apply PCPermutation_Type_map_inv in p as [l' -> HP].
  apply PCPermutation_Permutation_Type in HP; unfold id in HP.
  apply (Permutation_Type_Forall_inf HP) in Hnzsp.
  apply IHHll in Hnzsp as [[[C l1] l2] Hz ->]; [ | rewrite <- map_map; reflexivity ].
  apply Permutation_Type_vs_elt_inv in HP as [(l', l'') ->].
  exists (C, l', l''); [ assumption | reflexivity ].
- decomp_map HP eqn:Heq. decomp_map HP. subst.
  symmetry in Heq. apply ill2ll_map_ioc_inv in Heq as [lw'' -> ->].
  rewrite map_map in p.
  apply Permutation_Type_map_inv in p as [lw''' -> p].
  assert (Forall_inf nonzerospos (l1 ++ map ioc lw''' ++ l2)) as HF.
  { assert (HF1 := Forall_inf_app_l _ _ Hnzsp).
    assert (HF2 := Forall_inf_app_r _ _ Hnzsp).
    assert (HF3 := Forall_inf_app_l _ _ HF2).
    assert (HF4 := Forall_inf_app_r _ _ HF2).
    apply Forall_inf_app; [ assumption | ].
    apply Forall_inf_app; [ | assumption ].
    apply (Permutation_Type_map ioc) in p.
    eapply Permutation_Type_Forall_inf; [ exact p | assumption ]. }
  apply IHHll in HF as [[[C l1'] l2'] Hz Heq];
    [ | list_simpl; rewrite ill2ll_map_ioc, <- (map_map _ _ lw'''); reflexivity ].
  dichot_elt_app_inf_exec Heq; subst.
  + exists (C, l1', l ++ map ioc lw'' ++ l2); list_simpl; [ assumption | reflexivity ].
  + dichot_elt_app_inf_exec Heq1; subst; cbn.
    * apply (Permutation_Type_map ioc) in p. rewrite <- Heq0 in p.
      apply Permutation_Type_vs_elt_inv in p as [(llw1, llw2) ->].
      list_simpl. rewrite app_assoc. exists (C, l1 ++ llw1, llw2 ++ l2); [ assumption | reflexivity ].
    * rewrite 2 app_assoc. exists (C, (l1 ++ map ioc lw'') ++ l0, l2'); [ assumption | reflexivity ].
- discriminate f.
- destruct l0; inversion HP.
  destruct i; discriminate H0.
- rewrite map_map in HP. decomp_map HP. subst.
  rewrite <- map_map in IHHll.
  inversion_clear Hnzsp as [ | ? ? ? HF].
  apply IHHll in HF as [[[C l1'] l2'] Hzp ->]; [ | reflexivity ].
  exists (C, x :: l1', l2'); [ assumption | reflexivity ].
- rewrite map_map in HP. decomp_map HP eqn:Heq. subst.
  destruct x; inversion Heq; subst.
  + rewrite <- map_map in IHHll2.
    assert (Forall_inf nonzerospos (x2 :: l2)) as Hnzsp'.
    { inversion_clear Hnzsp as [ | ? ? Hnzsp' HF].
      apply Forall_inf_app_l in HF.
      inversion Hnzsp'.
      constructor; assumption. }
    apply IHHll2 in Hnzsp' as [[[C l1'] l2'] Hzp Heq2]; [ | reflexivity ].
    destruct l1'; inversion Heq2; subst.
    * exfalso. inversion_clear Hnzsp as [ | ? ? Hnzsp' ]. inversion Hnzsp'.
      apply H0; assumption.
    * exists (C, ilpam x1 i :: l1', l2' ++ l1); [ assumption | list_simpl; reflexivity ].
  + assert (Forall_inf nonzerospos (N :: l2)) as Hnzsp'.
    { inversion_clear Hnzsp as [ | ? ? Hnzsp' HF ]. inversion Hnzsp'.
      apply Forall_inf_app_l in HF.
      constructor; [ constructor | assumption ]. }
    rewrite <- map_map in IHHll2.
    apply IHHll2 in Hnzsp' as [[[C l1'] l2'] Hzp Heq2]; [ | reflexivity ].
    destruct l1'; inversion Heq2; subst.
    * exfalso. inversion Hzp.
    * exists (C, igen x :: l1', l2' ++ l1); [ assumption | list_simpl; reflexivity ].
  + assert (Forall_inf nonzerospos (x2 :: l1)) as Hnzsp'.
    { inversion_clear Hnzsp as [ | ? ? Hnzsp' HF ].
      apply Forall_inf_app_r in HF.
      inversion Hnzsp'.
      constructor; assumption. }
    rewrite <- map_map in IHHll1.
    apply IHHll1 in Hnzsp' as [[[C l1'] l2'] Hzp Heq2]; [ | reflexivity ].
    destruct l1'; inversion Heq2; subst.
    * exfalso. inversion_clear Hnzsp as [ | ? ? Hnzsp' ]. inversion Hnzsp'.
      apply H0; assumption.
    * exists (C, ilmap x1 i :: l2 ++ l1', l2'); [ assumption | list_simpl; reflexivity ].
  + assert (Forall_inf nonzerospos (N :: l1)) as Hnzsp'.
    { inversion_clear Hnzsp as [ | ? ? Hnzsp' HF ].
      apply Forall_inf_app_r in HF.
      inversion Hnzsp'.
      constructor; [ constructor | assumption ]. }
    rewrite <- map_map in IHHll1.
    apply IHHll1 in Hnzsp'; [ | reflexivity ].
    destruct Hnzsp' as [[[C l1'] l2'] Hzp Heq2].
    destruct l1'; inversion Heq2; subst.
    * exfalso. inversion Hzp.
    * exists (C, ineg x :: l2 ++ l1', l2'); [ assumption | list_simpl; reflexivity ].
- rewrite map_map in HP. decomp_map HP eqn:Heq. subst.
  destruct x; inversion Heq. subst.
  rewrite <- map_map in IHHll.
  assert (Forall_inf nonzerospos (x2 :: x1 :: l)) as Hnzsp'.
  { inversion_clear Hnzsp as [ | ? ? Hnzsp' ]. inversion_clear Hnzsp'.
    constructor; [ | constructor ]; assumption. }
  apply IHHll in Hnzsp' as [[[C l1'] l2'] Hzp Heq2]; [ | reflexivity ].
  destruct l1'; inversion Heq2; [ | destruct l1'; inversion Heq2 ]; subst.
  + exists (itens x1 C, nil, l); [ | reflexivity ].
    apply zp_itens_r. assumption.
  + exists (itens C i, nil, l2'); [ | reflexivity ].
    apply zp_itens_l. assumption.
  + exists (C, itens i0 i :: l1', l2'); [ assumption | reflexivity ].
- decomp_map HP eqn:Ht. decomp_map HP. subst.
  destruct x; inversion Ht.
  exists (izero, nil, l); constructor.
- rewrite map_map in HP. decomp_map HP eqn:Hp. subst.
  destruct x; inversion Hp. subst.
  rewrite <- map_map in IHHll.
  assert (Forall_inf nonzerospos (x1 :: l)) as Hnzsp'.
  { inversion_clear Hnzsp as [ | ? ? Hnzsp' ]. inversion_clear Hnzsp'.
    constructor; assumption. }
  apply IHHll in Hnzsp' as [[[C l1'] l2'] Hzp Heq2]; [ | reflexivity ].
  destruct l1'; inversion Heq2; subst.
  + exists (iwith C x2, nil, l2'); [ | reflexivity ].
    apply zp_iwith_l. assumption.
  + exists (C, iwith i x2 :: l1', l2'); [ assumption | reflexivity ].
- rewrite map_map in HP. decomp_map HP eqn:Hp. subst.
  destruct x; inversion Hp. subst.
  rewrite <- map_map in IHHll.
  assert (Forall_inf nonzerospos (x2 :: l)) as Hnzsp'.
  { inversion_clear Hnzsp as [ | ? ? Hnzsp' ]. inversion_clear Hnzsp'.
    constructor; assumption. }
  apply IHHll in Hnzsp' as [[[C l1'] l2'] Hzp Heq2]; [ | reflexivity ].
  destruct l1'; inversion Heq2; subst.
  + exists (iwith x1 C, nil, l2'); [ | reflexivity ].
    apply zp_iwith_r. assumption.
  + exists (C, iwith x1 i :: l1', l2'); [ assumption | reflexivity ].
- rewrite map_map in HP. decomp_map HP eqn:Hw. subst.
  destruct x; inversion Hw. subst.
  rewrite <- map_map in IHHll2.
  assert (Forall_inf nonzerospos (x2 :: l)) as Hnzsp'.
  { inversion_clear Hnzsp as [ | ? ? Hnzsp' ]. inversion_clear Hnzsp'.
    constructor; assumption. }
  apply IHHll2 in Hnzsp' as [[[C l1'] l2'] Hzp Heq2]; [ | reflexivity ].
  destruct l1'; inversion Heq2; subst.
  + assert (Forall_inf nonzerospos (x1 :: l2')) as Hnzsp''.
    { inversion_clear Hnzsp as [ | ? ? Hnzsp' ]. inversion_clear Hnzsp'.
      constructor; assumption. }
    rewrite <- map_map in IHHll1.
    apply IHHll1 in Hnzsp'' as [[[C' l1''] l2''] Hzp' Heq3]; [ | reflexivity ].
    destruct l1''; inversion Heq3; subst.
    * exists (iplus C' C, nil, l2''); constructor; assumption.
    * exists (C', iplus i C :: l1'', l2''); [ assumption | reflexivity ].
  + exists (C, iplus x1 i :: l1', l2'); [ assumption | reflexivity ].
- exfalso.
  destruct l0; inversion HP.
  destruct i; inversion H0.
- rewrite map_map in HP. decomp_map HP eqn:Hwn. subst.
  destruct x; inversion Hwn. subst.
  rewrite <- map_map in IHHll.
  assert (Forall_inf nonzerospos (x :: l)) as Hnzsp'.
  { inversion_clear Hnzsp as [ | ? ? Hnzsp' ]. inversion_clear Hnzsp'.
    constructor; assumption. }
  apply IHHll in Hnzsp' as [[[C l1'] l2'] Hzp Heq2]; [ | reflexivity ].
  destruct l1'; inversion Heq2; subst.
  + exists (ioc C, nil, l2'); constructor; assumption.
  + exists (C, ioc i :: l1', l2'); [ assumption | reflexivity ].
- rewrite map_map in HP. decomp_map HP. subst.
  rewrite <- map_map in IHHll.
  inversion Hnzsp as [ | ? ? ? HF ]. subst.
  apply IHHll in HF as [[[C l1'] l2'] Hzp ->]; [ | reflexivity ].
  exists (C, x :: l1', l2'); [ assumption | reflexivity ].
- rewrite map_map in HP. decomp_map HP eqn:Hwn. subst.
  destruct x; inversion Hwn. subst.
  assert (Forall_inf nonzerospos (ioc x :: ioc x :: l)) as Hnzsp'.
  { inversion Hnzsp. subst. constructor; assumption. }
  rewrite <- (map_map _ _ l) in IHHll.
  apply IHHll in Hnzsp' as [[[C l1'] l2'] Hzp Heq2]; [ | reflexivity ].
  destruct l1'; inversion Heq2; subst.
  + exists (ioc x, nil, l); [ assumption | reflexivity ].
  + destruct l1'; inversion H1; subst.
    * exists (ioc x, nil, l2'); [ assumption | reflexivity ].
    * exists (C, ioc x :: l1', l2'); [ assumption | reflexivity ].
- exfalso. clear - f Hcut. cbn in f.
  destruct (ill2ll_inv A) as [[l ?] _ _].
  apply existsb_exists in f as [B [Hin Hcut']].
  rewrite Hcut in Hcut'. discriminate Hcut'.
- unfold i2pfrag in HP. cbn in HP.
  destruct l0; inversion HP.
  apply (fst (Hgax a)) in H0 as [[[Z lz1] lz2] Hz Heq].
  destruct lz1; inversion Heq; subst.
  + exists (Z, nil, l0); [ assumption | reflexivity ].
  + list_simpl in H1. rewrite H2 in H1. list_simpl in H1.
    decomp_map H1 eqn:Hd. destruct Hd as [Hd1 [Hd2 Hd3]]. apply dual_inj in Hd2 as ->.
    decomp_map H1 eqn:Hxz. subst. symmetry in Hxz. apply (ill2ll_zeropos _ Hz) in Hxz.
    rewrite app_comm_cons. exists (x, i0 :: l, l2); [ assumption | reflexivity ].
Qed.

(** Cut-free conservativity *)
Lemma ll_to_ill_nzeropos_cutfree P (Hcut : no_icut P) (Hgax : easyipgax_nzeropos P) l :
  ll (i2pfrag P) l -> forall l0 C, Forall_inf nonzerospos (C :: l0) ->
  PCPermutation_Type (pperm (i2pfrag P)) l (ill2ll C :: rev (map dual (map ill2ll l0))) ->
  ill P l0 C.
Proof.
intros Hll. induction Hll; intros l0 C Hnzsp HP.
- apply PCPermutation_Type_length_2_inv in HP as [HP | HP]; inversion HP; destruct C; inversion H0.
  destruct l0 using rev_rect; inversion H1.
  list_simpl in H3. inversion H3.
  destruct l0 using rev_rect; list_simpl in H5; inversion H5.
  destruct x; inversion H4.
  rewrite <- H2 in H6. apply i2a_inj in H6 as ->.
  apply ax_ir.
- apply IHHll; [ | etransitivity ]; eassumption.
- apply PCPermutation_Type_vs_cons_inv in HP as [[l1' l2'] HP Heq].
  dichot_elt_app_inf_exec Heq; subst.
  + apply PEPermutation_Type_rev in HP. rewrite rev_involutive in HP.
    rewrite ? rev_app_distr, <- map_rev, <- ? app_assoc, map_map in HP.
    symmetry in HP. apply PEPermutation_Type_map_inv in HP as [l' Heq HP].
    decomp_map Heq eqn:Heq'. subst. destruct Heq' as [Heq0 [Heq1 [Heq2 Heq3]]].
    rewrite <- map_map in Heq2. symmetry in Heq2.
    apply ill2ll_map_ioc_inv in Heq2 as [l' -> Heq].
    symmetry in HP. eapply ex_ir; [ | apply HP ]; cbn.
    rewrite app_assoc. apply Permutation_Type_rev' in p. rewrite Heq, map_map in p.
    apply Permutation_Type_map_inv in p as [lw'' Heq' p].
    symmetry in p. eapply ex_oc_ir; [ | eassumption ].
    apply IHHll.
    * inversion_clear Hnzsp as [ | ? ? ? HF ].
      cbn in HP. symmetry in HP.
      apply (PEPermutation_Type_Forall_inf _ _ HP) in HF.
      assert (HF1:= Forall_inf_app_l _ _ HF).
      assert (HF2:= Forall_inf_app_r _ _ HF).
      assert (HF3:= Forall_inf_app_l _ _ HF2).
      assert (HF4:= Forall_inf_app_r _ _ HF2).
      assert (HF5:= Forall_inf_app_l _ _ HF4).
      assert (HF6:= Forall_inf_app_r _ _ HF4).
      constructor; [ assumption | ].
      apply Forall_inf_app; apply Forall_inf_app; try assumption.
      symmetry in p. apply (Permutation_Type_map ioc) in p.
      eapply Permutation_Type_Forall_inf; eassumption.
    * list_simpl. cbn in HP.
      apply (f_equal (@rev _)) in Heq0. rewrite rev_involutive in Heq0. subst.
      apply (f_equal (@rev _)) in Heq1. rewrite rev_involutive in Heq1. subst.
      apply (f_equal (@rev _)) in Heq3. rewrite rev_involutive in Heq3. subst.
      apply (f_equal (@rev _)) in Heq'. rewrite rev_involutive in Heq'. subst.
      list_simpl.
      rewrite <- (map_map _ _ (rev l1)), <- (map_map _ _ (rev l4)), <- (map_map _ _ (rev l6)),
              <- (map_map _ _ (rev lw'')), ill2ll_map_ioc.
      etransitivity; [ apply PCPermutation_Type_app_comm | list_simpl; reflexivity ].
  + dichot_elt_app_inf_exec Heq1; subst;
      [ exfalso; symmetry in Heq0; decomp_map Heq0 eqn:Heq'; destruct C; inversion Heq' | ].
    apply PEPermutation_Type_rev in HP. rewrite rev_involutive in HP. list_simpl in HP. rewrite map_map in HP.
    symmetry in HP. apply PEPermutation_Type_map_inv in HP as [l' Heq HP].
    decomp_map Heq eqn:Heq'. subst. destruct Heq' as [Heq1 [Heq2 [Heq3 Heq4]]].
    rewrite <- map_map in Heq2. symmetry in Heq2. apply ill2ll_map_ioc_inv in Heq2 as [l' -> Heq].
    symmetry in HP. eapply ex_ir; [ cbn | apply HP ].
    apply Permutation_Type_rev' in p. rewrite Heq, map_map in p.
    apply Permutation_Type_map_inv in p as [lw'' Heq' p].
    symmetry in p. eapply ex_oc_ir; [ | eassumption ].
    apply IHHll.
    * inversion_clear Hnzsp as [ | ? ? ? HF ].
      cbn in HP. symmetry in HP.
      apply (PEPermutation_Type_Forall_inf _ _ HP) in HF.
      assert (HF1:= Forall_inf_app_l _ _ HF).
      assert (HF2:= Forall_inf_app_r _ _ HF).
      assert (HF3:= Forall_inf_app_l _ _ HF2).
      assert (HF4:= Forall_inf_app_r _ _ HF2).
      assert (HF5:= Forall_inf_app_l _ _ HF4).
      assert (HF6:= Forall_inf_app_r _ _ HF4).
      constructor; [ assumption | ].
      rewrite app_assoc. apply Forall_inf_app; apply Forall_inf_app; try assumption.
      symmetry in p. apply (Permutation_Type_map ioc) in p.
      eapply Permutation_Type_Forall_inf; eassumption.
    * list_simpl. cbn in HP.
      apply (f_equal (@rev _)) in Heq1. rewrite rev_involutive in Heq1.
      apply (f_equal (@rev _)) in Heq3. rewrite rev_involutive in Heq3.
      apply (f_equal (@rev _)) in Heq4. rewrite rev_involutive in Heq4.
      apply (f_equal (@rev _)) in Heq'. rewrite rev_involutive in Heq'.
      subst. list_simpl.
      rewrite <- (map_map _ _ (rev l)), <- (map_map _ _ (rev l2)), <- (map_map _ _ (rev l6)),
              <- (map_map _ _ (rev lw'')), ill2ll_map_ioc, app_comm_cons.
      symmetry. etransitivity; [ apply PCPermutation_Type_app_comm | list_simpl; reflexivity ].
- discriminate f.
- apply PCPermutation_Type_length_1_inv in HP as [= HP1 HP2].
  destruct C; inversion HP1.
  destruct l0 using rev_rect; [ | list_simpl in HP2; discriminate HP2 ].
  apply one_irr.
- list_simpl in HP. symmetry in HP.
  apply PCPermutation_Type_vs_cons_inv in HP as [(l', l'') HP Heq].
  destruct l'; inversion Heq.
  + destruct C; discriminate H0.
  + decomp_map H1 eqn:Hx. decomp_map H1. subst.
    apply (f_equal (@rev _)) in H1.
    rewrite rev_involutive in H1. subst.
    destruct x; destr_eq Hx.
    list_simpl. apply one_ilr, IHHll.
    * inversion Hnzsp as [ | ? ? ? HF ].
      constructor; [ assumption | ].
      list_simpl in HF.
      assert (H3l := Forall_inf_app_l _ _ HF).
      assert (H3r := Forall_inf_app_r _ _ HF).
      inversion H3r.
      apply Forall_inf_app; assumption.
    * list_simpl.
      apply PEPermutation_PCPermutation_Type in HP. unfold id in HP. cbn in HP.
      etransitivity; [ apply HP | rewrite app_comm_cons; apply PCPermutation_Type_app_comm ].
- list_simpl in HP. symmetry in HP.
  apply PCPermutation_Type_vs_cons_inv in HP as [(l', l'') HP Heq].
  destruct l'; inversion Heq.
  + destruct C; inversion H0. subst.
    list_simpl in HP. rewrite map_map in HP.
    apply PEPermutation_Type_map_inv in HP as [l3 Heq' HP].
    rewrite <- map_map in Heq'. decomp_map Heq'. decomp_map Heq'. subst.
    inversion_clear Hnzsp as [ | ? ? Hnzsp' HF ]. inversion_clear Hnzsp'.
    apply Forall_inf_rev, (PEPermutation_Type_Forall_inf _ _ HP) in HF.
    assert (H3l := Forall_inf_app_l _ _ HF).
    assert (H3r := Forall_inf_app_r _ _ HF).
    apply PEPermutation_Type_rev in HP. list_simpl in HP. symmetry in HP.
    eapply ex_ir; [ | exact HP ].
    apply tens_irr.
    * apply IHHll1.
      -- constructor; [ | apply Forall_inf_rev ]; assumption.
      -- list_simpl. reflexivity.
    * apply IHHll2.
      -- constructor; [ | apply Forall_inf_rev ]; assumption.
      -- list_simpl. reflexivity.
  + decomp_map H1 eqn:Ht. decomp_map H1. subst.
    inversion_clear Hnzsp as [ | ? ? ? HF ].
    apply Forall_inf_rev in HF. rewrite H1 in HF.
    assert (H3l := Forall_inf_app_l _ _ HF).
    assert (H3r := Forall_inf_app_r _ _ HF).
    inversion H3r as [ | ? ? Hnzsp' HF']. subst.
    apply (Forall_inf_app HF') in H3l.
    assert ({'(ll, lr) & 
       PEPermutation_Type (ipperm P) (l'' ++ l') (ll ++ lr) &
       l2 ++ l1 = map dual (map ill2ll ll)
                         ++ ill2ll C :: map dual (map ill2ll lr) /\
       (ipperm P = false -> l'' = ll /\ l' = lr) }) as [(ll, lr) HP0 [Heq' HPeq]].
    { clear - HP.
      destruct (ipperm P).
      - apply PEPermutation_Type_vs_elt_inv in HP.
        destruct HP as [(ll & lr) HP0 Heq]. cbn in HP0.
        rewrite <- 2 map_app, map_map in HP0. symmetry in HP0.
        apply Permutation_Type_map_inv in HP0 as [l3 Heq1 HP].
        rewrite <- map_map in Heq1. decomp_map Heq1. decomp_map Heq1. subst.
        exists (ll, lr); [ | split ]; [ assumption | assumption | ].
        intros [=].
      - cbn in HP. exists (l'', l'); cbn; [ | repeat split ]; [ reflexivity | assumption ]. }
    dichot_elt_app_inf_exec Heq'; subst.
    * decomp_map Heq'1. decomp_map Heq'1. subst.
      apply (PEPermutation_Type_Forall_inf _ _ HP0) in H3l. cbn in H3l.
      destruct x; inversion Hnzsp'; inversion Ht; subst.
      -- apply (f_equal (@rev _)) in H1. rewrite rev_involutive in H1. subst.
         list_simpl. apply (ex_ir (rev ll ++ ilpam x1 x2 :: rev l1 ++ rev l)).
         ++ apply lpam_ilr.
            ** apply IHHll1.
               --- constructor; [ assumption | ].
                   apply Forall_inf_app_r, Forall_inf_app_r in H3l.
                   apply Forall_inf_rev. assumption.
               --- rewrite bidual. list_simpl. reflexivity.
            ** apply IHHll2.
               --- constructor; [ assumption | ].
                   assert (H3l' := Forall_inf_app_l _ _ H3l).
                   assert (H3l'' := Forall_inf_app_r _ _ H3l).
                   apply Forall_inf_app_l, Forall_inf_rev in H3l''.
                   apply Forall_inf_rev in H3l'.
                   apply Forall_inf_app; [ assumption | ].
                   constructor; assumption.
               --- list_simpl. rewrite ? app_comm_cons. apply PCPermutation_Type_app_comm.
         ++ destruct (ipperm P).
            ** clear - HP0.
               apply Permutation_Type_rev' in HP0.
               list_simpl in HP0. list_simpl.
               apply Permutation_Type_elt.
               symmetry. etransitivity; [ apply Permutation_Type_app_comm | ].
               etransitivity; [ exact HP0 | ].
               etransitivity; [ | apply Permutation_Type_app_comm ]. rewrite app_assoc. reflexivity.
            ** destruct (HPeq eq_refl) as [-> ->]. list_simpl. reflexivity.
      -- apply (f_equal (@rev _)) in H1. rewrite rev_involutive in H1. subst.
         list_simpl. apply (ex_ir (rev ll ++ igen x :: rev l1 ++ rev l)).
         ++ apply gen_pam_rule.
            ** intro. apply Hgax.
            ** apply IHHll1.
               --- constructor; [ assumption | ].
                   apply Forall_inf_app_r in H3l.
                   apply Forall_inf_app_r in H3l.
                   apply Forall_inf_rev. assumption.
               --- rewrite bidual. list_simpl. reflexivity.
            ** apply IHHll2.
               --- constructor; [ assumption | ].
                   assert (H3l' := Forall_inf_app_l _ _ H3l).
                   assert (H3l'' := Forall_inf_app_r _ _ H3l).
                   apply Forall_inf_app_l in H3l''.
                   apply Forall_inf_rev in H3l'.
                   apply Forall_inf_rev in H3l''.
                   apply Forall_inf_app; [ | constructor; [ constructor | ] ]; assumption.
               --- list_simpl. rewrite ? app_comm_cons. apply PCPermutation_Type_app_comm.
         ++ destruct (ipperm P).
            ** clear - HP0.
               apply Permutation_Type_rev' in HP0.
               list_simpl in HP0. list_simpl.
               apply Permutation_Type_elt.
               symmetry. etransitivity; [ apply Permutation_Type_app_comm | ].
               etransitivity; [ exact HP0 | rewrite app_assoc; apply Permutation_Type_app_comm ].
            ** destruct (HPeq eq_refl). subst. list_simpl. reflexivity.
      -- change (dual (ill2ll x2) :: map dual (map ill2ll l1))
           with (map dual (map ill2ll (x2 :: l1))) in Hll1.
         apply dual_jfragment_zeropos in Hll1; [ | assumption .. | ].
         ++ destruct Hll1 as [[[C1 [|]] lz2] HzC1 Heq1]; inversion Heq1; subst.
            ** contradiction HzC1.
            ** apply (f_equal (@rev _)) in H1. rewrite rev_involutive in H1. subst.
               rewrite ? app_assoc in HP0.
               apply PEPermutation_Type_vs_elt_inv in HP0 as [(ll1, lr1) _ HP0].
               dichot_elt_app_inf_exec HP0; subst; list_simpl.
               --- apply zeropos_ilr. assumption.
               --- rewrite ? app_comm_cons, ? app_assoc. apply zeropos_ilr. assumption.
         ++ constructor; [ assumption | ].
            apply Forall_inf_app_r in H3l.
            apply Forall_inf_app_r in H3l. assumption.
      -- change (covar (i2a atN) :: map dual (map ill2ll l1))
           with (map dual (map ill2ll (N :: l1))) in Hll1.
         apply dual_jfragment_zeropos in Hll1; [ | assumption .. | ].
         ++ destruct Hll1 as [[[C1 [|]] lz2] HzC1 Heq1]; inversion Heq1; subst.
            ** inversion HzC1.
            ** apply (f_equal (@rev _)) in H1. rewrite rev_involutive in H1. subst.
               cbn in HP0; rewrite ? app_assoc in HP0.
               apply PEPermutation_Type_vs_elt_inv in HP0 as [(ll1, lr1) _ Heq0].
               dichot_elt_app_inf_exec Heq0; subst; list_simpl.
               --- apply zeropos_ilr. assumption.
               --- rewrite ? app_comm_cons, ? app_assoc. apply zeropos_ilr. assumption.
         ++ constructor.
            --- constructor.
            --- apply Forall_inf_app_r in H3l.
                apply Forall_inf_app_r in H3l; assumption.
    * decomp_map Heq'0. decomp_map Heq'0. subst.
      apply (PEPermutation_Type_Forall_inf _ _ HP0) in H3l.
      destruct x; inversion Hnzsp'; inversion Ht; subst.
      -- change (dual (ill2ll x2) :: map dual (map ill2ll l2))
           with (map dual (map ill2ll (x2 :: l2))) in Hll2.
         apply dual_jfragment_zeropos in Hll2; [ | assumption .. | ].
         ++ destruct Hll2 as [[[C1 [|]] lz2] HzC1 Heq1]; inversion Heq1; subst.
            ** contradiction HzC1.
            ** apply (f_equal (@rev _)) in H1. rewrite rev_involutive in H1. subst.
               list_simpl in HP0. apply PEPermutation_Type_vs_elt_inv in HP0 as [(ll1, lr1) _ Heq0].
               dichot_elt_app_inf_exec Heq0; subst; list_simpl.
               --- apply zeropos_ilr. assumption.
               --- rewrite ? app_comm_cons, ? app_assoc. apply zeropos_ilr. assumption.
         ++ constructor; [ assumption | ].
            apply Forall_inf_app_l, Forall_inf_app_l in H3l. assumption.
      -- change (covar (i2a atN) :: map dual (map ill2ll l2))
           with (map dual (map ill2ll (N :: l2))) in Hll2.
         apply dual_jfragment_zeropos in Hll2; [ | assumption .. | ].
         ++ destruct Hll2 as [[[C1 [|]] lz2] HzC1 Heq1]; inversion Heq1; subst.
            ** inversion HzC1.
            ** apply (f_equal (@rev _)) in H1. rewrite rev_involutive in H1. subst.
               list_simpl in HP0. apply PEPermutation_Type_vs_elt_inv in HP0 as [(ll1, lr1) _ Heq0].
               dichot_elt_app_inf_exec Heq0; subst; list_simpl.
               --- apply zeropos_ilr. assumption.
               --- rewrite ? app_comm_cons, ? app_assoc. apply zeropos_ilr. assumption.
         ++ constructor; [ constructor | ].
            apply Forall_inf_app_l, Forall_inf_app_l in H3l. assumption.
      -- apply (f_equal (@rev _)) in H1. rewrite rev_involutive in H1. subst.
         list_simpl. apply (ex_ir (rev l ++ rev l2 ++ ilmap x1 x2 :: rev lr)).
         ++ apply lmap_ilr.
            ** apply IHHll2.
               --- constructor; [ assumption | ].
                   apply Forall_inf_app_l in H3l.
                   apply Forall_inf_app_l in H3l.
                   apply Forall_inf_rev; assumption.
               --- rewrite bidual; list_simpl; reflexivity.
            ** apply IHHll1.
               --- constructor; [ assumption | ].
                   assert (H3l' := Forall_inf_app_l _ _ H3l).
                   assert (H3l'' := Forall_inf_app_r _ _ H3l).
                   apply Forall_inf_app_r in H3l'.
                   apply Forall_inf_rev in H3l'.
                   apply Forall_inf_rev in H3l''.
                   apply Forall_inf_app; [ assumption | ].
                   constructor; assumption.
               --- list_simpl. rewrite ? app_comm_cons. apply PCPermutation_Type_app_comm.
         ++ destruct (ipperm P) eqn:Hperm.
            ** clear - HP0.
               apply Permutation_Type_rev' in HP0.
               list_simpl in HP0. list_simpl. rewrite app_assoc.
               apply Permutation_Type_elt.
               etransitivity; [ apply Permutation_Type_app_comm | ].
               symmetry. etransitivity; [ apply Permutation_Type_app_comm | exact HP0 ].
            ** destruct (HPeq eq_refl). subst. list_simpl. reflexivity.
      -- apply (f_equal (@rev _)) in H1. rewrite rev_involutive in H1. subst.
         list_simpl. apply (ex_ir (rev l ++ rev l2 ++ ineg x :: rev lr)).
         ++ apply neg_map_rule.
            ** intro. apply Hgax.
            ** apply IHHll2.
               --- constructor; [ assumption | ].
                   apply Forall_inf_app_l in H3l.
                   apply Forall_inf_app_l in H3l.
                   apply Forall_inf_rev; assumption.
               --- rewrite bidual; list_simpl; reflexivity.
            ** apply IHHll1.
               --- constructor; [ assumption | ].
                   assert (H3l' := Forall_inf_app_l _ _ H3l).
                   assert (H3l'' := Forall_inf_app_r _ _ H3l).
                   apply Forall_inf_app_r in H3l'.
                   apply Forall_inf_rev in H3l'.
                   apply Forall_inf_rev in H3l''.
                   apply Forall_inf_app; [ assumption | ].
                   constructor; [ constructor | assumption ].
               --- list_simpl. rewrite ? app_comm_cons. apply PCPermutation_Type_app_comm.
         ++ destruct (ipperm P) eqn:Hperm.
            ** clear - HP0. apply Permutation_Type_rev' in HP0.
               list_simpl in HP0. list_simpl. rewrite app_assoc.
               apply Permutation_Type_elt.
               etransitivity; [ apply Permutation_Type_app_comm | ].
               symmetry. etransitivity; [ apply Permutation_Type_app_comm | exact HP0 ].
            ** destruct (HPeq eq_refl). subst. list_simpl. reflexivity.
- list_simpl in HP. symmetry in HP.
  apply PCPermutation_Type_vs_cons_inv in HP as [([|] & l'') HP Heq].
  + inversion Heq as [ Heq0 ]; subst.
    list_simpl in HP.
    rewrite map_map in HP.
    apply PEPermutation_Type_map_inv in HP.
    destruct HP as [l3 Heq' HP].
    rewrite <- map_map in Heq'. subst.
    inversion_clear Hnzsp as [ | ? ? Hnzsp' HF ].
    apply Forall_inf_rev in HF.
    apply (PEPermutation_Type_Forall_inf _ _ HP) in HF.
    destruct C; inversion Hnzsp'; inversion Heq0; subst.
    * apply lpam_irr.
      symmetry in HP.
      apply PEPermutation_Type_rev in HP.
      rewrite rev_involutive in HP.
      apply (ex_ir (rev l3 ++ C1 :: nil));
        [ | apply PEPermutation_Type_add_inside; [ assumption | reflexivity ] ].
      apply IHHll.
      -- constructor; [ assumption | ].
         apply Forall_inf_app; [ | constructor ]; try constructor; [ | assumption ].
         apply Forall_inf_rev; assumption.
      -- list_simpl; reflexivity.
    * apply gen_irr.
      symmetry in HP.
      apply PEPermutation_Type_rev in HP.
      rewrite rev_involutive in HP.
      apply (ex_ir (rev l3 ++ C :: nil));
        [ | apply PEPermutation_Type_app; [ assumption | reflexivity ] ].
      apply IHHll.
      -- constructor; [ constructor | ].
         apply Forall_inf_app; [ | constructor; [ | constructor ] ]; [ | assumption ].
         apply Forall_inf_rev. assumption.
      -- list_simpl. reflexivity.
    * apply lmap_irr.
      symmetry in HP.
      apply PEPermutation_Type_rev in HP.
      rewrite rev_involutive in HP.
      apply (ex_ir (C1 :: rev l3)); [ | apply PEPermutation_Type_cons, HP; reflexivity ].
      apply IHHll.
      -- constructor; [ assumption | constructor; [ assumption | ] ].
         apply Forall_inf_rev. assumption.
      -- list_simpl. symmetry. rewrite app_comm_cons.
         etransitivity; [ apply PCPermutation_Type_app_comm | reflexivity ].
    * apply neg_irr.
      symmetry in HP.
      apply PEPermutation_Type_rev in HP.
      rewrite rev_involutive in HP.
      apply (ex_ir (C :: rev l3)); [ | apply PEPermutation_Type_cons, HP; reflexivity ].
      apply IHHll.
      -- constructor; [ constructor | ].
         constructor; [ assumption | ].
         apply Forall_inf_rev. assumption.
      -- list_simpl. rewrite app_comm_cons.
         symmetry. etransitivity; [ apply PCPermutation_Type_app_comm | reflexivity ].
  + inversion Heq as [[Heq0 Heq1]]. subst.
    decomp_map Heq1 eqn:Heq0. decomp_map Heq1. subst.
    apply (f_equal (@rev _)) in Heq1. rewrite rev_involutive in Heq1. subst.
    destruct x; inversion Heq0. subst.
    list_simpl. apply tens_ilr, IHHll.
    * inversion Hnzsp as [ | ? ? ? HF ].
      constructor; [ assumption | ].
      list_simpl in HF.
      assert (H3l := Forall_inf_app_l _ _ HF).
      assert (H3r := Forall_inf_app_r _ _ HF).
      inversion H3r as [ | ? ? Hnzsp' ].
      inversion_clear Hnzsp'.
      apply Forall_inf_app; [ assumption | ].
      constructor; [ | constructor ]; assumption.
    * list_simpl.
      etransitivity; [ | rewrite ? app_comm_cons; apply PCPermutation_Type_app_comm].
      apply PEPermutation_PCPermutation_Type.
      apply PEPermutation_Type_cons; [ reflexivity | ].
      apply PEPermutation_Type_cons; [ reflexivity | exact HP ].
- list_simpl in HP. symmetry in HP.
  apply PCPermutation_Type_vs_cons_inv in HP as [([|] & l'') HP Heq]; inversion Heq; subst.
  + destruct C; inversion H0.
    apply top_irr.
  + decomp_map H1 eqn:Hx. decomp_map H1. subst.
    apply (f_equal (@rev _)) in H1. rewrite rev_involutive in H1. subst.
    destruct x; destr_eq Hx.
    list_simpl. apply zero_ilr.
- list_simpl in HP. symmetry in HP.
  apply PCPermutation_Type_vs_cons_inv in HP as [([|] & l'') HP Heq]; inversion Heq; subst.
  + list_simpl in HP. rewrite map_map in HP. apply PEPermutation_Type_map_inv in HP as [l3 Heq' HP].
    rewrite <- map_map in Heq'. subst.
    inversion_clear Hnzsp as [ | ? ? Hnzsp' HF].
    apply Forall_inf_rev in HF.
    apply (PEPermutation_Type_Forall_inf _ _ HP) in HF.
    destruct C; inversion H0. subst.
    inversion Hnzsp'. subst.
    symmetry in HP. apply PEPermutation_Type_rev in HP. rewrite rev_involutive in HP.
    apply (ex_ir (rev l3)); [ | apply HP ].
    apply plus_irr1, IHHll.
    * constructor; [ assumption | ].
      apply Forall_inf_rev; assumption.
    * list_simpl. reflexivity.
  + decomp_map H1 eqn:Hx. decomp_map H1.
    apply (f_equal (@rev _)) in H1. rewrite rev_involutive in H1.
    destruct x; destr_eq Hx. subst. list_simpl.
    apply with_ilr1, IHHll.
    * inversion Hnzsp as [ | ? ? ? HF ].
      constructor; [ assumption | ].
      list_simpl in HF.
      assert (H3l := Forall_inf_app_l _ _ HF).
      assert (H3r := Forall_inf_app_r _ _ HF).
      inversion H3r as [ | ? ? Hnzsp' ].
      inversion_clear Hnzsp'.
      apply Forall_inf_app; [ assumption | ].
      constructor; assumption.
    * list_simpl. rewrite HP. rewrite ? app_comm_cons. apply PCPermutation_Type_app_comm.
- list_simpl in HP. symmetry in HP.
  apply PCPermutation_Type_vs_cons_inv in HP as [([|] & l'') HP Heq]; inversion Heq; subst.
  + list_simpl in HP. rewrite map_map in HP. apply PEPermutation_Type_map_inv in HP as [l3 Heq' HP].
    rewrite <- map_map in Heq'. subst.
    inversion_clear Hnzsp as [ | ? ? Hnzsp' HF ].
    apply Forall_inf_rev in HF.
    apply (PEPermutation_Type_Forall_inf _ _ HP) in HF.
    destruct C; inversion H0. subst.
    inversion_clear Hnzsp'.
    symmetry in HP. apply PEPermutation_Type_rev in HP. rewrite rev_involutive in HP.
    apply (ex_ir (rev l3)); [ | apply HP ].
    apply plus_irr2, IHHll.
    * constructor; [ assumption | ].
      apply Forall_inf_rev; assumption.
    * list_simpl; reflexivity.
  + decomp_map H1 eqn:Hx. decomp_map H1. subst.
    apply (f_equal (@rev _)) in H1. rewrite rev_involutive in H1. subst.
    destruct x; destr_eq Hx. subst.
    list_simpl. apply with_ilr2, IHHll.
    * inversion Hnzsp as [ | ? ? ? HF ].
      constructor; [ assumption | ].
      list_simpl in HF.
      assert (H3l := Forall_inf_app_l _ _ HF).
      assert (H3r := Forall_inf_app_r _ _ HF).
      inversion H3r as [ | ? ? Hnzsp' ].
      inversion_clear Hnzsp'.
      apply Forall_inf_app; [ | constructor ]; assumption.
    * list_simpl. rewrite HP. rewrite ? app_comm_cons. apply PCPermutation_Type_app_comm.
- list_simpl in HP. symmetry in HP.
  apply PCPermutation_Type_vs_cons_inv in HP as [([|], l'') HP Heq]; inversion Heq; subst.
  + list_simpl in HP. rewrite map_map in HP. apply PEPermutation_Type_map_inv in HP as [l3 Heq' HP].
    rewrite <- map_map in Heq'. subst.
    inversion_clear Hnzsp as [ | ? ? Hnzsp' HF ].
    apply Forall_inf_rev in HF.
    apply (PEPermutation_Type_Forall_inf _ _ HP) in HF.
    destruct C; inversion H0. subst.
    inversion_clear Hnzsp'.
    symmetry in HP. apply PEPermutation_Type_rev in HP. rewrite rev_involutive in HP.
    apply (ex_ir (rev l3)); [ | apply HP ].
    apply with_irr.
    * apply IHHll1.
      -- constructor; [ assumption | ].
         apply Forall_inf_rev; assumption.
      -- list_simpl; reflexivity.
    * apply IHHll2.
      -- constructor; [ assumption | ].
         apply Forall_inf_rev; assumption.
      -- list_simpl; reflexivity.
  + decomp_map H1 eqn:Hx. decomp_map H1. subst.
    apply (f_equal (@rev _)) in H1. rewrite rev_involutive in H1. subst.
    destruct x; destr_eq Hx. subst.
    list_simpl. apply plus_ilr.
    * apply IHHll1.
      -- inversion Hnzsp as [ | ? ? ? HF ].
         constructor; [ assumption | ].
         list_simpl in HF.
         assert (H3l := Forall_inf_app_l _ _ HF).
         assert (H3r := Forall_inf_app_r _ _ HF).
         inversion H3r as [ | ? ? Hnzsp' ].
         inversion_clear Hnzsp'.
         apply Forall_inf_app; [ | constructor ]; assumption.
      -- list_simpl. rewrite HP. rewrite ? app_comm_cons. apply PCPermutation_Type_app_comm.
    * apply IHHll2.
      -- inversion Hnzsp as [ | ? ? ? HF ].
         constructor; [ assumption | ].
         list_simpl in HF.
         assert (H3l := Forall_inf_app_l _ _ HF).
         assert (H3r := Forall_inf_app_r _ _ HF).
         inversion H3r as [ | ? ? Hnzsp' ].
         inversion_clear Hnzsp'.
         apply Forall_inf_app; [ | constructor ]; assumption.
      -- list_simpl. rewrite HP. rewrite ? app_comm_cons. apply PCPermutation_Type_app_comm.
- list_simpl in HP. symmetry in HP.
  apply PCPermutation_Type_vs_cons_inv in HP as [([|], l'') HP Heq]; inversion Heq; subst.
  + list_simpl in HP. rewrite map_map in HP. apply PEPermutation_Type_map_inv in HP as [l3 Heq' HP].
    rewrite <- (map_map _ _ l3) in Heq'.
    destruct (ill2ll_map_ioc_inv _ _ Heq') as [l0' -> _].
    inversion_clear Hnzsp as [ | ? ? Hnzsp' HF ].
    apply Forall_inf_rev in HF.
    apply (PEPermutation_Type_Forall_inf _ _ HP) in HF.
    destruct C; inversion H0. subst.
    inversion_clear Hnzsp'.
    symmetry in HP. apply PEPermutation_Type_rev in HP. rewrite rev_involutive in HP.
    apply (ex_ir (rev (map ioc l0'))); [ | apply HP ].
    list_simpl. apply oc_irr, IHHll.
    * constructor; [ assumption | ].
      apply Forall_inf_rev in HF; list_simpl in HF; assumption.
    * rewrite Heq'. list_simpl. reflexivity.
  + decomp_map H1 eqn:Hx. decomp_map H1. subst.
    destruct x; destr_eq Hx.
- list_simpl in HP. symmetry in HP.
  apply PCPermutation_Type_vs_cons_inv in HP as [([|], l'') HP Heq]; inversion Heq; subst.
  + destruct C; discriminate H0.
  + decomp_map H1 eqn:Hx. decomp_map H1. subst.
    apply (f_equal (@rev _)) in H1. rewrite rev_involutive in H1. subst.
    destruct x; destr_eq Hx. subst.
    list_simpl. apply de_ilr, IHHll.
    * inversion Hnzsp as [ | ? ? ? HF ].
      constructor; [ assumption | ].
      list_simpl in HF.
      assert (H3l := Forall_inf_app_l _ _ HF).
      assert (H3r := Forall_inf_app_r _ _ HF).
      inversion H3r as [ | ? ? Hnzsp' ].
      inversion_clear Hnzsp'.
      apply Forall_inf_app; [ | constructor ]; assumption.
    * list_simpl. rewrite HP, ? app_comm_cons. apply PCPermutation_Type_app_comm.
- list_simpl in HP. symmetry in HP.
  apply PCPermutation_Type_vs_cons_inv in HP as [([|], l'') HP Heq]; inversion Heq; subst.
  + destruct C; discriminate H0.
  + decomp_map H1 eqn:Hx. decomp_map H1. subst.
    apply (f_equal (@rev _)) in H1. rewrite rev_involutive in H1. subst.
    destruct x; destr_eq Hx. subst.
    list_simpl.
    apply wk_ilr, IHHll.
    * inversion Hnzsp as [ | ? ? ? HF ].
      constructor; [ assumption | ].
      list_simpl in HF.
      assert (H3l := Forall_inf_app_l _ _ HF).
      assert (H3r := Forall_inf_app_r _ _ HF).
      inversion H3r as [ | ? ? Hnzsp' ].
      inversion_clear Hnzsp'.
      apply Forall_inf_app; assumption.
    * list_simpl.
      apply PEPermutation_PCPermutation_Type in HP. unfold id in HP.
      etransitivity; [ exact HP | rewrite app_comm_cons; apply PCPermutation_Type_app_comm ].
- list_simpl in HP. symmetry in HP.
  apply PCPermutation_Type_vs_cons_inv in HP as [([|], l'') HP Heq]; inversion Heq; subst.
  + destruct C; discriminate H0.
  + decomp_map H1 eqn:Hx. decomp_map H1. subst.
    apply (f_equal (@rev _)) in H1. rewrite rev_involutive in H1. subst.
    destruct x; destr_eq Hx. subst.
    list_simpl. apply co_ilr, IHHll.
    * inversion_clear Hnzsp as [ | ? ? ? HF ].
      list_simpl in HF.
      assert (HF1 := Forall_inf_app_l _ _ HF).
      assert (HF2 := Forall_inf_app_r _ _ HF).
      inversion HF2. subst.
      constructor; [ assumption | ].
      apply Forall_inf_app; [ | constructor ]; assumption.
    * apply (PEPermutation_Type_cons _ (eq_refl (wn (dual (ill2ll x))))) in HP.
      apply (PEPermutation_Type_cons _ (eq_refl (wn (dual (ill2ll x))))) in HP.
      apply PEPermutation_PCPermutation_Type in HP. unfold id in HP.
      etransitivity; try eassumption.
      list_simpl. rewrite ? app_comm_cons. apply PCPermutation_Type_app_comm.
- exfalso. clear - f Hcut. cbn in f.
  destruct (ill2ll_inv A) as [[l ?] _ _].
  apply existsb_exists in f as [B [Hin Hcut']].
  rewrite Hcut in Hcut'. discriminate Hcut'.
- apply (Hgax a). assumption.
Qed.

(** Axiom-free conservativity *)
Lemma ll_to_ill_nzeropos_axfree P (P_axfree : no_iax P) l C :
  Forall_inf nonzerospos (C :: l) -> ll (i2pfrag P) (ill2ll C :: rev (map dual (map ill2ll l))) -> ill P l C.
Proof.
intros Hnz pi.
apply cut_admissible_axfree in pi; [ | assumption ].
apply (stronger_pfrag _ _ (cutrm_i2pfrag P)) in pi.
eapply ll_to_ill_nzeropos_cutfree in pi; [ | | | eassumption | reflexivity ].
- apply (stronger_ipfrag (cutrm_ipfrag_le P)), pi.
- apply noicut_cutrm.
- intro. contradiction P_axfree.
Qed.


(** *** Conservativity with constraints on the left of [ilpam] *)

(** Constraints on the left of [ilpam] for conservativity *)
Inductive oclike : iformula -> Type :=
| ocl_ivar X : oclike (ivar X)
| ocl_ione : oclike ione
| ocl_itens A B : oclike A -> oclike B -> oclike (itens A B)
| ocl_iwith_l A B : oclike A -> oclike (iwith A B)
| ocl_iwith_r A B : oclike A -> oclike (iwith B A)
| ocl_izero : oclike izero
| ocl_iplus A B : oclike A -> oclike B -> oclike (iplus A B)
| ocl_ioc A : oclike (ioc A).

Inductive oclpam : iformula -> Type :=
| oclm_ivar x : oclpam (ivar x)
| oclm_ione : oclpam ione
| oclm_itens A B : oclpam A -> oclpam B -> oclpam (itens A B)
| oclm_ilpam A B : oclike A -> oclpam A -> oclpam B -> oclpam (ilpam A B)
| oclm_igen A : oclike A -> oclpam A -> oclpam (igen A)
| oclm_ilmap A B : oclike A -> oclpam A -> oclpam B -> oclpam (ilmap A B)
| oclm_ineg A : oclike A -> oclpam A -> oclpam (ineg A)
| oclm_itop : oclpam itop
| oclm_iwith A B : oclpam A -> oclpam B -> oclpam (iwith A B)
| oclm_izero : oclpam izero
| oclm_iplus A B : oclpam A -> oclpam B -> oclpam (iplus A B)
| oclm_ioc A : oclpam A -> oclpam (ioc A).

Definition easyipgax_oclmap P := forall a,
  (forall A, In_inf (dual (ill2ll A)) (map ill2ll (fst (projT2 (ipgax P) a))) -> notT (oclike A))
* (forall A, ill2ll A = ill2ll (snd (projT2 (ipgax P) a)) -> notT (oclike A))
* (forall l C,
     PCPermutation_Type (ipperm P) (ill2ll (snd (projT2 (ipgax P) a))
                         :: rev (map dual (map ill2ll (fst (projT2 (ipgax P) a)))))
                       (ill2ll C :: rev (map dual (map ill2ll l)))
       -> ill P l C)
* notT (In_inf N (fst (projT2 (ipgax P) a))).

(** Cut-free conservativity *)
Lemma ll_to_ill_oclpam_cutfree P (P_perm : ipperm P = true) (P_cut : no_icut P) (Hgax : easyipgax_oclmap P) l :
  ll (i2pfrag P) l -> forall l0 l1 C, Forall_inf oclpam (C :: l0) ->
    Forall_inf oclike l1 ->
    PCPermutation_Type (pperm (i2pfrag P)) l
                (ill2ll C :: map ill2ll l1 ++ rev (map dual (map ill2ll l0))) ->
      ill P l0 C
   *  (l1 <> nil -> forall l2, ill P (l0 ++ l2) C).
Proof.
intros Hll. induction Hll; intros l0 lo C Hoclm Hocl HP; try discriminate.
- apply PCPermutation_Type_length_2_inv in HP.
  destruct HP as [HP | HP]; inversion HP; destruct C; inversion H0. subst.
  destruct lo; list_simpl in H1; inversion H1.
  + induction l0 using rev_rect; list_simpl in H2; inversion H2.
    induction l0 using rev_rect; list_simpl in H4; inversion H4.
    destruct x; inversion H3.
    apply i2a_inj in H5. subst.
    split.
    * apply ax_ir.
    * intros Hnil. contradiction Hnil. reflexivity.
  + destruct i0; discriminate H2.
- rewrite HP in p. apply IHHll in p; assumption.
- assert (PCPermutation_Type (pperm (i2pfrag P)) (l1 ++ map wn lw ++ l2)
       (ill2ll C :: map ill2ll lo ++ rev (map dual (map ill2ll l0))))
    as HP'.
  { cbn in HP. rewrite P_perm in HP. cbn in HP. cbn. rewrite P_perm. cbn.
    etransitivity; [ | exact HP ].
    apply Permutation_Type_app_head, Permutation_Type_app_tail, Permutation_Type_map, p. }
  apply IHHll in HP'; assumption.
- apply PCPermutation_Type_length_1_inv in HP.
  inversion HP; destruct C; inversion H0. subst.
  destruct lo; inversion H1.
  induction l0 using rev_rect; list_simpl in H1; inversion H1.
  split.
  + apply one_irr.
  + intros Hnil. contradiction Hnil. reflexivity.
- symmetry in HP. apply PCPermutation_Type_vs_cons_inv in HP as [(l', l'') HP Heq].
  destruct l'; inversion Heq; [ destruct C; inversion H0 | ]. subst.
  symmetry in H1. dichot_elt_app_inf_exec H1; subst.
  { decomp_map H0 eqn:Hx. destruct x; destr_eq Hx. }
  list_simpl in H2. decomp_map H2 eqn:Hx. decomp_map H2.
  apply (f_equal (@rev _)) in H2. list_simpl in H2. subst.
  destruct x; destr_eq Hx.
  apply PEPermutation_PCPermutation_Type in HP. unfold id in HP.
  assert (HP' := PCPermutation_Type_trans _ _ _ _ HP (PCPermutation_Type_app_comm _ _ _)).
  specialize IHHll with (rev l'' ++ rev l1) lo C.
  list_simpl in IHHll. list_simpl in HP'. apply IHHll in HP'; [ | | assumption ].
  + destruct HP' as [IH1 IH2]; split.
    * apply one_ilr. assumption.
    * intros Hnil l2.
      list_simpl. apply one_ilr.
      rewrite app_assoc. apply (IH2 Hnil).
  + inversion Hoclm as [ | ? ? ? HF ]; constructor; [ assumption | ].
    assert (Hl := Forall_inf_app_l _ _ HF).
    assert (Hr := Forall_inf_app_r _ _ HF). inversion_clear Hr.
    apply Forall_inf_app; assumption.
- symmetry in HP. apply PCPermutation_Type_vs_cons_inv in HP as [(l', l'') HP Heq].
  cbn in HP. rewrite P_perm in HP. cbn in HP.
  apply Permutation_Type_app_app_inv in HP as [[[[l3' l3''] l4'] l4''] [[HP1 HP2] [HP3 HP4]]].
  destruct l'; inversion Heq; [ destruct C; inversion H0 | ]; subst.
  + apply Permutation_Type_nil in HP4. apply app_eq_nil in HP4 as [-> ->].
    list_simpl in HP1. symmetry in HP1.
    list_simpl in HP2. symmetry in HP2.
    apply (@Permutation_Type_trans _ _ _ (l2 ++ l1)) in HP3;
      [ | apply Permutation_Type_app ]; try assumption.
    clear l3' l3'' HP1 HP2.
    apply Permutation_Type_app_app_inv in HP3 as [[[[l3' l3''] l4'] l4''] [[HP1 HP2] [HP3 HP4]]].
    symmetry in HP1. apply Permutation_Type_map_inv in HP1 as [l3 Heq1 HP1].
    decomp_map Heq1. subst.
    list_simpl in HP2. rewrite map_map in HP2.
    symmetry in HP2. apply Permutation_Type_map_inv in HP2 as [l3 Heq2 HP2].
    apply Permutation_Type_rev' in HP2. rewrite rev_involutive in HP2.
    rewrite <- map_map in Heq2. decomp_map Heq2. decomp_map Heq2. subst.
    specialize IHHll1 with (rev l4'') l4' C1.
    specialize IHHll2 with (rev l3'') l3' C2.
    apply (Permutation_Type_Forall_inf HP1) in Hocl.
    assert (Hocl2 := Forall_inf_app_l _ _ Hocl).
    assert (Hocl1 := Forall_inf_app_r _ _ Hocl).
    apply IHHll1 in Hocl1; [ apply IHHll2 in Hocl2 | | ].
    * destruct Hocl1 as [IH1 IH2].
      destruct Hocl2 as [IH3 IH4].
      split.
      -- eapply ex_ir; [ apply tens_irr; eassumption | ].
         list_simpl in HP2.
         rewrite P_perm. cbn. symmetry. assumption.
      -- intros Hnil lw.
         destruct lo; [ contradiction Hnil; reflexivity | ].
         symmetry in HP1. apply Permutation_Type_vs_cons_inv in HP1 as [(ll, lr) Heq3].
         dichot_elt_app_inf_exec Heq3; subst.
         ++ assert (ll ++ i :: l <> nil) as Hnil2
              by (clear; intro H; destruct ll; inversion H).
            assert (IH := IH4 Hnil2 lw).
            eapply ex_ir; [apply tens_irr; eassumption | ].
            list_simpl in HP2.
            rewrite P_perm. cbn. rewrite app_assoc. apply Permutation_Type_app_tail. symmetry. assumption.
         ++ assert (l ++ i :: lr <> nil) as Hnil2
              by (clear; intros H; destruct l; inversion H).
            assert (IH := IH2 Hnil2 lw).
            eapply ex_ir; [apply tens_irr; eassumption | ].
            list_simpl in HP2.
            rewrite P_perm. cbn. etransitivity; [ apply Permutation_Type_app_comm | ].
            rewrite app_assoc. apply Permutation_Type_app_tail.
            symmetry. etransitivity; [ exact HP2 | apply Permutation_Type_app_comm ].
    * inversion_clear Hoclm as [ | ? ? Hoclm' HF ].
      inversion_clear Hoclm'.
      constructor; try assumption.
      list_simpl in HP2.
      apply (Permutation_Type_Forall_inf HP2) in HF.
      apply Forall_inf_app_r in HF; assumption.
    * now cbn; rewrite P_perm; list_simpl; apply Permutation_Type_cons.
    * inversion Hoclm as [ | ? ? Hoclm' HF ].
      inversion Hoclm'.
      constructor; try assumption.
      list_simpl in HP2.
      apply (Permutation_Type_Forall_inf HP2) in HF.
      apply Forall_inf_app_l in HF; assumption.
    * now cbn; rewrite P_perm; list_simpl; apply Permutation_Type_cons.
  + dichot_elt_app_inf_exec H1; subst.
    * decomp_map H0 eqn:Hx. subst.
      destruct x; destr_eq Hx. subst.
      assert (HP4' := HP4).
      symmetry in HP4'. apply Permutation_Type_vs_cons_inv in HP4' as [(ll, lr) Heq'].
      apply Permutation_Type_app_app_inv in HP3 as [[[[l3l l3r] l4l] l4r] [[HP3' HP3''] [HP3''' HP3'''']]].
      symmetry in HP3'. apply Permutation_Type_map_inv in HP3' as [l3 Heq'' HP3'].
      decomp_map Heq''. subst.
      list_simpl in HP3''. rewrite map_map in HP3''. symmetry in HP3''.
      apply Permutation_Type_map_inv in HP3'' as [l3 Heq'' HP3''].
      apply Permutation_Type_rev' in HP3''. rewrite rev_involutive in HP3''.
      rewrite <- map_map in Heq''.
      decomp_map Heq''. decomp_map Heq''. subst.
      apply (Permutation_Type_app_tail l4') in HP3'''.
      assert (HP1' := Permutation_Type_trans HP1 HP3''').
      apply (Permutation_Type_app_tail l4'') in HP3''''.
      assert (HP2' := Permutation_Type_trans HP2 HP3'''').
      dichot_elt_app_inf_exec Heq'; subst.
      -- list_simpl in HP4. apply Permutation_Type_cons_app_inv in HP4.
         symmetry in HP4. apply Permutation_Type_map_inv in HP4 as [l5 Heq' HP].
         decomp_map Heq'. subst.
         specialize IHHll2 with (rev l3r) (x2 :: l3l ++ ll ++ l3) C.
         assert (Forall_inf oclike (x2 :: l3l ++ ll ++ l3)) as Hocl'.
         { assert (Hocl2 := Forall_inf_app_l _ _ Hocl).
           assert (Hocl1 := Forall_inf_app_r _ _ Hocl).
           apply (Permutation_Type_Forall_inf HP) in Hocl2.
           inversion Hocl1 as [ | ? ? Hocl1' HF ].
           inversion_clear Hocl1'.
           constructor; [ assumption | ].
           cbn in HP3'. apply (Permutation_Type_Forall_inf HP3') in HF.
           assert (HF1 := Forall_inf_app_l _ _ HF).
           assert (HF2 := Forall_inf_app_r _ _ HF).
           apply Forall_inf_app; [ assumption | ].
           rewrite app_assoc in Hocl2.
           assert (Hocl3 := Forall_inf_app_l _ _ Hocl2).
           assert (Hocl4 := Forall_inf_app_r _ _ Hocl2). assumption. }
         apply IHHll2 in Hocl'.
         ++ destruct Hocl' as [_ Hocl'].
            assert (x2 :: l3l ++ ll ++ l3 <> nil) as Hnil by intros [=].
            split.
            ** eapply Hocl' in Hnil.
               eapply ex_ir; [ apply Hnil | ].
               cbn in HP3''. symmetry in HP3''.
               rewrite P_perm. cbn. etransitivity; [ | apply HP3'' ].
               rewrite rev_app_distr. apply Permutation_Type_app_comm.
            ** intros Hnil' l''.
               eapply Hocl' in Hnil.
               eapply ex_ir; [ apply Hnil | ].
               symmetry in HP3''. apply (Permutation_Type_app_tail l'') in HP3''.
               rewrite P_perm. cbn. etransitivity; [ | apply HP3'' ].
               rewrite rev_app_distr, <- app_assoc.
               etransitivity; [ apply Permutation_Type_app_rot | apply Permutation_Type_app_rot ].
         ++ inversion Hoclm as [ | ? ? ? HF ]; constructor; try assumption.
            cbn in HP3''.
            apply (Permutation_Type_Forall_inf HP3'') in HF.
            list_simpl in HF; apply Forall_inf_app_r in HF; apply HF.
         ++ list_simpl. rewrite P_perm. cbn.
            cons2app. rewrite <- (app_comm_cons _ _ (ill2ll x2)). apply Permutation_Type_cons_app.
            list_simpl. etransitivity; [ apply HP1' | ].
            rewrite app_assoc. symmetry. apply Permutation_Type_cons_app.
            list_simpl. apply Permutation_Type_app_head.
            symmetry. apply Permutation_Type_app_rot.
      -- list_simpl in HP4. rewrite app_assoc in HP4. apply Permutation_Type_cons_app_inv in HP4.
         symmetry in HP4. apply Permutation_Type_map_inv in HP4 as [l'' Heq' HP].
         list_simpl in Heq'. decomp_map Heq'. subst.
         specialize IHHll1 with (rev l4r) (x1 :: l4l ++ l3 ++ lr) C.
         assert (Forall_inf oclike (x1 :: l4l ++ l3 ++ lr)) as Hocl'.
         { cbn in HP. cbn in Hocl.
           assert (Hocl2 := Forall_inf_app_l _ _ Hocl).
           assert (Hocl1 := Forall_inf_app_r _ _ Hocl).
           apply (Permutation_Type_Forall_inf HP) in Hocl2.
           inversion Hocl1 as [ | ? ? Hocl1' HF ].
           inversion_clear Hocl1'.
           constructor; try assumption.
           apply (Permutation_Type_Forall_inf HP3') in HF.
           apply Forall_inf_app_r in HF; apply Forall_inf_app; try assumption.
           apply Forall_inf_app_r in Hocl2; assumption. }
         apply IHHll1 in Hocl'.
         ++ destruct Hocl' as [_ Hocl'].
            assert (x1 :: l4l ++ l3 ++ lr <> nil) as Hnil by intros [=].
            split.
            ** eapply Hocl' in Hnil.
               eapply ex_ir; [ apply Hnil | ].
               symmetry in HP3''. rewrite P_perm. cbn. etransitivity; [ | apply HP3'' ].
               rewrite rev_app_distr. reflexivity.
            ** intros Hnil' l''.
               eapply Hocl' in Hnil.
               eapply ex_ir; [ apply Hnil | ].
               symmetry in HP3''. apply (Permutation_Type_app_tail l'') in HP3''.
               rewrite P_perm. cbn. etransitivity; [ | apply HP3'' ].
               rewrite rev_app_distr, <- app_assoc. reflexivity.
         ++ inversion Hoclm as [ | ? ? ? HF ]; constructor; try assumption.
            apply (Permutation_Type_Forall_inf HP3'') in HF.
            list_simpl in HF. apply Forall_inf_app_l in HF. apply HF.
         ++ list_simpl. rewrite P_perm. cbn.
            cons2app. rewrite <- (app_comm_cons _ _ (ill2ll x1)). apply Permutation_Type_cons_app.
            list_simpl. etransitivity; [ apply HP2' | ].
            rewrite app_assoc. symmetry. apply Permutation_Type_cons_app.
            list_simpl. apply Permutation_Type_app_head. symmetry. apply Permutation_Type_app_rot.
    * list_simpl in H2. decomp_map H2 eqn:Hx. decomp_map H2. subst.
      apply (f_equal (@rev _)) in H2. list_simpl in H2. subst.
      destruct x; destr_eq Hx. subst.
      -- assert (HP4' := HP4).
         symmetry in HP4'. apply Permutation_Type_vs_cons_inv in HP4' as [(l4a & l4b) Heq'].
         dichot_elt_app_inf_exec Heq'; subst.
         ++ rewrite map_map in HP3. symmetry in HP3. apply Permutation_Type_map_inv in HP3 as [l3''' Heq' HP3].
            decomp_map Heq'. subst.
            rewrite <- map_map in HP1, HP2.
            list_simpl in HP4. apply Permutation_Type_cons_app_inv in HP4.
            apply Permutation_Type_app_app_inv in HP4 as [[[[l3a l3b] l3c] l3d] [[HP4' HP4''] [HP4''' HP4'''']]].
            apply Permutation_Type_app_app_inv in HP4'''' as [[[[l3e l3f] l3g] l3h] [[HP4a HP4b] [HP4c HP4d]]].
            assert (Permutation_Type l2 (map dual (map ill2ll l3') ++ (l3a ++ l3b) ++ ill2ll C :: l3e ++ l3g))
              as HP'.
            { etransitivity; [ apply HP1 | ].
              now apply Permutation_Type_app_head, Permutation_Type_app, Permutation_Type_cons. }
            symmetry in HP4'. apply Permutation_Type_map_inv in HP4'.
            destruct HP4' as [l4 Heq' HP4'].
            decomp_map Heq'. subst.
            apply (Permutation_Type_app_head l3b) in HP4d.
            assert (HP'' := Permutation_Type_trans HP4'' HP4d).
            rewrite map_map in HP''.
            symmetry in HP''. apply Permutation_Type_map_inv in HP''.
            clear HP4''. destruct HP'' as [l4' Heq' HP4''].
            decomp_map Heq'. subst.
            rewrite <- (map_map _ _ l3b) in HP'.
            rewrite <- (map_map _ _ l3g) in HP'.
            symmetry in HP4c. apply Permutation_Type_map_inv in HP4c as [l4' Heq' HP4c].
            decomp_map Heq'. subst.
            rewrite <- (map_map _ _ l3h) in HP4b.
            apply (Permutation_Type_app_head (map dual (map ill2ll l3''))) in HP4b.
            assert (HP'' := Permutation_Type_trans HP2 HP4b).
            specialize IHHll2 with (rev (x2 :: l3' ++ l3b ++ l3g)) (l3a ++ l3e) C.
            apply (Permutation_Type_Forall_inf HP4') in Hocl.
            assert (Hocl1 := Forall_inf_app_l _ _ Hocl).
            assert (Hocl2 := Forall_inf_app_r _ _ Hocl).
            specialize IHHll1 with (rev (l3'' ++ l3h)) l3f x1.
            apply (Permutation_Type_Forall_inf HP4c) in Hocl2.
            assert (Hocl2' := Forall_inf_app_l _ _ Hocl2).
            assert (Hocl3 := Forall_inf_app_r _ _ Hocl2).
            assert (Hocl4 := Forall_inf_app Hocl1 Hocl2').
            apply IHHll2 in Hocl4; [ apply IHHll1 in Hocl3 | | ].
            ** split.
               --- destruct Hocl4 as [Hocl4 _].
                   destruct Hocl3 as [Hocl3 _].
                   apply (ex_ir (rev (l3' ++ l3b ++ l3g) ++
                                   ilpam x1 x2 :: rev (l3'' ++ l3h) ++ nil)).
                   +++ apply lpam_ilr; assumption.
                   +++ apply Permutation_Type_rev' in HP3 .
                       apply Permutation_Type_rev' in HP4''.
                       list_simpl in HP3. list_simpl in HP4''. symmetry in HP4''.
                       rewrite P_perm. list_simpl.
                       etransitivity;
                         [ | apply Permutation_Type_app_head, Permutation_Type_cons, HP4''; reflexivity ].
                       rewrite app_assoc. etransitivity; [ apply Permutation_Type_app_comm | ].
                       rewrite ? app_comm_cons, ? app_assoc.
                       apply Permutation_Type_app_tail, Permutation_Type_app_tail.
                       list_simpl.
                       symmetry. etransitivity; [ apply Permutation_Type_app_tail, HP3 | ].
                       list_simpl. rewrite app_comm_cons, (app_assoc (rev l3')).
                       apply Permutation_Type_app_comm.
               --- intros Hnil lw; destruct lo; [ contradiction Hnil; reflexivity | ].
                   apply (Permutation_Type_app_head l3a) in HP4c.
                   assert (HP''' := Permutation_Type_trans HP4' HP4c).
                   symmetry in HP'''. apply Permutation_Type_vs_cons_inv in HP''' as [(l4l & l4r) Heq'].
                   cbn in Heq'. rewrite app_assoc in Heq'. dichot_elt_app_inf_exec Heq'; subst.
                   +++ rewrite <- Heq'0 in Hocl4.
                       assert (l4l ++ i :: l3 <> nil) as Hnil'
                         by (intros Hnil'; destruct l4l; discriminate Hnil').
                       apply (snd Hocl4) with lw in Hnil'.
                       destruct Hocl3 as [Hocl3 _].
                       apply (ex_ir (rev (l3' ++ l3b ++ l3g) ++
                                       ilpam x1 x2 :: rev (l3'' ++ l3h) ++ lw)).
                       *** apply lpam_ilr; try assumption.
                           eapply ex_ir; [ apply Hnil' | ].
                           rewrite P_perm. list_simpl. reflexivity.
                       *** apply Permutation_Type_rev' in HP3 .
                           apply Permutation_Type_rev' in HP4''.
                           list_simpl in HP3. list_simpl in HP4''.
                           rewrite P_perm. list_simpl.
                           rewrite ? app_comm_cons, ? app_assoc. apply Permutation_Type_app_tail.
                           list_simpl. symmetry. etransitivity; [ apply Permutation_Type_app_tail, HP3 | ].
                           etransitivity;
                             [ apply Permutation_Type_app_head, Permutation_Type_cons, HP4''; reflexivity | ].
                           list_simpl. etransitivity; [ apply Permutation_Type_app_comm | ].
                           rewrite ? app_comm_cons, ? app_assoc. apply Permutation_Type_app_tail.
                           list_simpl. etransitivity; [ apply Permutation_Type_app_comm | ].
                           list_simpl. rewrite ? (app_assoc (rev l3g)), ? (app_assoc _ (rev l3')).
                           apply Permutation_Type_cons_app, Permutation_Type_app_comm.
                   +++ assert (l3 ++ i :: l4r <> nil) as Hnil'
                         by (intros Hnil'; destruct l3; discriminate Hnil').
                       apply (snd Hocl3) with lw in Hnil'.
                       destruct Hocl4 as [Hocl4 _].
                       apply (ex_ir (rev (l3' ++ l3b ++ l3g) ++
                                      ilpam x1 x2 :: (rev (l3'' ++ l3h) ++ lw) ++ nil)).
                       *** apply lpam_ilr; assumption.
                       *** apply Permutation_Type_rev' in HP3 . list_simpl in HP3.
                           apply Permutation_Type_rev' in HP4''. list_simpl in HP4''.
                           rewrite P_perm. list_simpl.
                           rewrite ? app_comm_cons, ? app_assoc. apply Permutation_Type_app_tail.
                           list_simpl. symmetry. etransitivity; [ apply Permutation_Type_app_tail, HP3 | ].
                           etransitivity;
                             [ apply Permutation_Type_app_head, Permutation_Type_cons, HP4''; reflexivity | ].
                           list_simpl. etransitivity; [ apply Permutation_Type_app_comm | ].
                           rewrite ? app_comm_cons, ? app_assoc. apply Permutation_Type_app_tail.
                           list_simpl. etransitivity; [ apply Permutation_Type_app_comm | ].
                           list_simpl. rewrite ? (app_assoc (rev l3g)), ? (app_assoc _ (rev l3')).
                           apply Permutation_Type_cons_app, Permutation_Type_app_comm.
            ** inversion_clear Hoclm as [ | ? ? ? HF ].
               assert (Hoclm1 := Forall_inf_app_l _ _ HF).
               assert (Hoclm2 := Forall_inf_app_r _ _ HF).
               inversion_clear Hoclm2 as [ | ? ? Hoclm3 HF'].
               inversion Hoclm3; constructor; try assumption.
               apply Permutation_Type_rev' in HP3.
               apply (Permutation_Type_Forall_inf HP3) in Hoclm1. list_simpl in Hoclm1.
               assert (Hoclm1' := Forall_inf_app_l _ _ Hoclm1).
               assert (Hoclm2' := Forall_inf_app_r _ _ Hoclm1).
               apply Permutation_Type_rev' in HP4''.
               apply (Permutation_Type_Forall_inf HP4'') in HF'. list_simpl in HF'.
               apply Forall_inf_app_l in HF'. list_simpl. apply Forall_inf_app; assumption.
            ** cbn. rewrite P_perm, bidual. list_simpl.
               apply Permutation_Type_cons; [ reflexivity | ].
               etransitivity; [ exact HP'' | apply Permutation_Type_app_swap_app ].
            ** inversion_clear Hoclm as [ | ? ? ? HF ]; constructor; try assumption.
               assert (Hoclm1 := Forall_inf_app_l _ _ HF).
               assert (Hoclm2 := Forall_inf_app_r _ _ HF).
               inversion_clear Hoclm2 as [ | ? ? Hoclm2' HF' ].
               apply Permutation_Type_rev' in HP4''.
               apply (Permutation_Type_Forall_inf HP4'') in HF'. list_simpl in HF'.
               apply Forall_inf_app_r in HF'.
               assert (H4l := Forall_inf_app_l _ _ HF').
               assert (H4r := Forall_inf_app_r _ _ HF').
               list_simpl.
               apply Forall_inf_app; [ exact H4l | ].
               apply Forall_inf_app; [ exact H4r | ].
               apply Permutation_Type_rev' in HP3.
               apply (Permutation_Type_Forall_inf HP3) in Hoclm1. list_simpl in Hoclm1.
               apply Forall_inf_app_r in Hoclm1.
               inversion Hoclm2'.
               apply Forall_inf_app; [ | constructor; [assumption | constructor] ]; assumption.
            ** list_simpl. rewrite P_perm. cbn.
               rewrite app_comm_cons, 2 app_assoc. apply Permutation_Type_cons_app.
               etransitivity; [ exact HP' | ].
               rewrite ? app_comm_cons, ? app_assoc. apply Permutation_Type_app_tail. list_simpl.
               symmetry. rewrite ? app_assoc. apply Permutation_Type_cons_app. list_simpl.
               symmetry. etransitivity; [ apply Permutation_Type_app_swap_app | ].
               symmetry. apply Permutation_Type_app_head, Permutation_Type_app_rot.
         ++ cbn in HP3. rewrite map_map in HP3.
            symmetry in HP3. apply Permutation_Type_map_inv in HP3 as [l3''' Heq' HP3].
            decomp_map Heq'. subst.
            rewrite <- map_map in HP1, HP2.
            rewrite app_assoc in HP4. apply Permutation_Type_cons_app_inv in HP4.
            list_simpl in HP4. apply Permutation_Type_app_app_inv in HP4.
            destruct HP4 as [[[[l3a l3b] l3c] l3d] [[HP4' HP4''] [HP4''' HP4'''']]].
            apply Permutation_Type_app_app_inv in HP4''''.
            destruct HP4'''' as [[[[l3e l3f] l3g] l3h] [[HP4a HP4b] [HP4c HP4d]]].
            symmetry in HP4'. apply Permutation_Type_map_inv in HP4' as [l4 Heq' HP4'].
            decomp_map Heq'. subst.
            apply (Permutation_Type_app_head l3b) in HP4d.
            assert (HP' := Permutation_Type_trans HP4'' HP4d).
            rewrite map_map in HP'.
            symmetry in HP'. apply Permutation_Type_map_inv in HP'.
            clear HP4''. destruct HP' as [l4'' Heq' HP4''].
            decomp_map Heq'. subst.
            apply (Permutation_Type_app_tail (ill2ll C :: l4b)) in HP4a.
            apply (Permutation_Type_app_head (map dual (map ill2ll l3''))) in HP4a.
            assert (HP' := Permutation_Type_trans HP2 HP4a).
            rewrite <- (map_map _ _ l3g) in HP'.
            symmetry in HP4c. apply Permutation_Type_map_inv in HP4c as [l4'' Heq' HP4c].
            decomp_map Heq'. subst.
            rewrite <- (map_map _ _ l3h) in HP4b.
            apply (@Permutation_Type_cons _ (ill2ll C) _ eq_refl) in HP4b.
            apply (Permutation_Type_app_head (map dual (map ill2ll l3'')
              ++ (map ill2ll l3e ++ map dual (map ill2ll l3g)))) in HP4b.
            rewrite <- app_assoc in HP4b.
            assert (HP'' := Permutation_Type_trans HP' HP4b).
            specialize IHHll1 with (rev (l3g ++ l3'' ++ l3h)) (x1 :: l3e ++ l3f) C.
            assert (x1 :: l3e ++ l3f <> nil) as Hnil by (intros Hnil; inversion Hnil).
            inversion_clear Hoclm as [ | ? ? ? HF ].
            assert (Hoclm1 := Forall_inf_app_l _ _ HF).
            assert (Hoclm2 := Forall_inf_app_r _ _ HF).
            inversion_clear Hoclm2 as [ | ? ? Hoclm2' ].
            inversion_clear Hoclm2'.
            apply (Permutation_Type_Forall_inf HP4') in Hocl.
            apply (Permutation_Type_app_head l3a) in HP4c.
            apply (Permutation_Type_Forall_inf HP4c) in Hocl.
            apply Forall_inf_app_r in Hocl.
            assert (Hocl' := Forall_inf_cons _ X1 Hocl).
            apply IHHll1 in Hocl'; [ split | | ].
            ** apply (snd Hocl') with (ilpam x1 x2 :: rev l3' ++ rev l3b) in Hnil.
               eapply ex_ir; [ apply Hnil | ].
               cbn. rewrite P_perm. cbn.
               apply Permutation_Type_rev' in HP3. list_simpl in HP3.
               apply Permutation_Type_rev' in HP4''. list_simpl in HP4''.
               symmetry. etransitivity; [ apply Permutation_Type_app_tail, HP3 | ].
               etransitivity;
                 [ apply Permutation_Type_app_head, Permutation_Type_cons; [ reflexivity | apply HP4''] | ].
               list_simpl. rewrite ? app_comm_cons, ? app_assoc. apply Permutation_Type_app_tail.
               list_simpl. rewrite app_assoc. etransitivity; [ apply Permutation_Type_app_comm | ].
               cons2app. rewrite ? app_assoc. apply Permutation_Type_app_tail.
               list_simpl. rewrite ? app_assoc. apply Permutation_Type_cons_app.
               list_simpl. apply Permutation_Type_app_head, Permutation_Type_app_comm.
            ** intros Hnil' lw.
               apply (snd Hocl') with (ilpam x1 x2 :: rev l3' ++ rev l3b ++ lw) in Hnil.
               eapply ex_ir; [ apply Hnil | ].
               cbn. rewrite P_perm. cbn.
               apply Permutation_Type_rev' in HP3. list_simpl in HP3.
               apply Permutation_Type_rev' in HP4''. list_simpl in HP4''.
               list_simpl. symmetry. etransitivity; [ apply Permutation_Type_app_tail, HP3 | ].
               rewrite ? app_comm_cons, ? app_assoc. apply Permutation_Type_app_tail.
               etransitivity;
                 [ apply Permutation_Type_app_head, Permutation_Type_cons; [ reflexivity | apply HP4''] | ].
               list_simpl. rewrite ? app_comm_cons, ? app_assoc. apply Permutation_Type_app_tail.
               list_simpl. rewrite app_assoc. etransitivity; [ apply Permutation_Type_app_comm | ].
               cons2app. rewrite ? app_assoc. apply Permutation_Type_app_tail.
               list_simpl. rewrite ? app_assoc. apply Permutation_Type_cons_app.
               list_simpl. apply Permutation_Type_app_head, Permutation_Type_app_comm.
            ** constructor; try assumption.
               apply Permutation_Type_rev' in HP4''. list_simpl in HP4''.
               apply (Permutation_Type_Forall_inf HP4'') in X0.
               rewrite app_assoc in X0. apply Forall_inf_app_l in X0.
               assert (H4l := Forall_inf_app_l _ _ X0).
               assert (H4r := Forall_inf_app_r _ _ X0).
               apply Permutation_Type_rev' in HP3. list_simpl in HP3.
               apply (Permutation_Type_Forall_inf HP3) in Hoclm1.
               apply Forall_inf_app_l in Hoclm1.
               list_simpl. apply Forall_inf_app; [ | apply Forall_inf_app ]; assumption.
            ** list_simpl. rewrite P_perm, bidual. list_simpl.
               cons2app. rewrite <- (app_comm_cons _ _ (ill2ll x1)).
               apply Permutation_Type_cons_app.
               list_simpl; etransitivity; [ apply HP'' | ].
               rewrite ? app_comm_cons, ? app_assoc. apply Permutation_Type_app_tail. list_simpl.
               etransitivity; [ apply Permutation_Type_app_comm | ].
               rewrite ? app_comm_cons, ? app_assoc. apply Permutation_Type_app_tail. list_simpl.
               symmetry. rewrite ? app_assoc. apply Permutation_Type_cons_app.
               list_simpl. apply Permutation_Type_app_head, Permutation_Type_app_comm.
      -- assert (HP4' := HP4).
         symmetry in HP4'. apply Permutation_Type_vs_cons_inv in HP4' as [(l4a, l4b) Heq'].
         dichot_elt_app_inf_exec Heq'; subst.
         ++ rewrite map_map in HP3.
            symmetry in HP3. apply Permutation_Type_map_inv in HP3 as [l3''' Heq' HP3].
            decomp_map Heq'. subst.
            rewrite <- map_map in HP1, HP2.
            list_simpl in HP4. apply Permutation_Type_cons_app_inv in HP4.
            apply Permutation_Type_app_app_inv in HP4 as [[[[l3a l3b] l3c] l3d] [[HP4' HP4''] [HP4''' HP4'''']]].
            apply Permutation_Type_app_app_inv in HP4'''' as [[[[l3e l3f] l3g] l3h] [[HP4a HP4b] [HP4c HP4d]]].
            assert (Permutation_Type l2 (map dual (map ill2ll l3') ++ (l3a ++ l3b) ++ ill2ll C :: l3e ++ l3g))
              as HP'.
            { etransitivity; [ apply HP1 | ].
              apply Permutation_Type_app_head, Permutation_Type_app; auto. }
            symmetry in HP4'. apply Permutation_Type_map_inv in HP4' as [l4 Heq' HP4'].
            decomp_map Heq'. subst.
            apply (Permutation_Type_app_head l3b) in HP4d.
            assert (HP'' := Permutation_Type_trans HP4'' HP4d).
            rewrite map_map in HP''.
            symmetry in HP''. apply Permutation_Type_map_inv in HP''.
            clear HP4''. destruct HP'' as [l4' Heq' HP4''].
            decomp_map Heq'. subst.
            rewrite <- (map_map _ _ l3b), <- (map_map _ _ l3g) in HP'.
            symmetry in HP4c. apply Permutation_Type_map_inv in HP4c as [l4' Heq' HP4c].
            decomp_map Heq'. subst.
            rewrite <- (map_map _ _ l3h) in HP4b.
            apply (Permutation_Type_app_head (map dual (map ill2ll l3''))) in HP4b.
            assert (HP'' := Permutation_Type_trans HP2 HP4b).
            specialize IHHll2 with (rev (N :: l3' ++ l3b ++ l3g)) (l3a ++ l3e) C.
            apply (Permutation_Type_Forall_inf HP4') in Hocl.
            assert (Hocl1 := Forall_inf_app_l _ _ Hocl).
            assert (Hocl2 := Forall_inf_app_r _ _ Hocl).
            specialize IHHll1 with (rev (l3'' ++ l3h)) l3f x.
            apply (Permutation_Type_Forall_inf HP4c) in Hocl2.
            assert (Hocl2' := Forall_inf_app_l _ _ Hocl2).
            assert (Hocl3 := Forall_inf_app_r _ _ Hocl2).
            assert (Hocl4 := Forall_inf_app Hocl1 Hocl2').
            apply IHHll2 in Hocl4; [ apply IHHll1 in Hocl3 | | ].
            ** split.
               --- destruct Hocl4 as [Hocl4 _].
                   destruct Hocl3 as [Hocl3 _].
                   apply (ex_ir (rev (l3' ++ l3b ++ l3g) ++ igen x :: rev (l3'' ++ l3h) ++ nil)).
                   +++ apply gen_pam_rule; [ | assumption .. ].
                       intros a. apply Hgax.
                   +++ apply Permutation_Type_rev' in HP3 . list_simpl in HP3.
                       apply Permutation_Type_rev' in HP4''. list_simpl in HP4''.
                       rewrite P_perm. list_simpl.
                       symmetry. etransitivity; [ apply Permutation_Type_app_tail, HP3 | ].
                       etransitivity; [ apply Permutation_Type_app_head, Permutation_Type_cons;
                                          [ reflexivity | apply HP4''] | ].
                       list_simpl. rewrite app_assoc. etransitivity; [ apply Permutation_Type_app_comm | ].
                       list_simpl. rewrite ? app_assoc. apply Permutation_Type_cons_app.
                       list_simpl. etransitivity; [ apply Permutation_Type_app_comm | ].
                       list_simpl. rewrite ? (app_assoc (rev l3g)). apply Permutation_Type_app_head.
                       rewrite (app_assoc (rev l3')). apply Permutation_Type_app_comm.
               --- intros Hnil lw. destruct lo; [ contradiction Hnil; reflexivity | ].
                   apply (Permutation_Type_app_head l3a) in HP4c.
                   assert (HP''' := Permutation_Type_trans HP4' HP4c).
                   symmetry in HP'''. apply Permutation_Type_vs_cons_inv in HP''' as [(l4l, l4r) Heq'].
                   rewrite app_assoc in Heq'. dichot_elt_app_inf_exec Heq'; subst.
                   +++ rewrite <- Heq'0 in Hocl4.
                       assert (l4l ++ i :: l3 <> nil) as Hnil'
                         by (intros Hnil'; destruct l4l; discriminate Hnil').
                       apply (snd Hocl4) with lw in Hnil'.
                       destruct Hocl3 as [Hocl3 _].
                       apply (ex_ir (rev (l3' ++ l3b ++ l3g) ++ igen x :: rev (l3'' ++ l3h) ++ lw)).
                       *** apply gen_pam_rule; [ | assumption | ].
                           ---- intro. apply Hgax.
                           ---- eapply ex_ir; [ apply Hnil' | ].
                                rewrite P_perm. cbn. cons2app. rewrite ? app_assoc. reflexivity.
                       *** apply Permutation_Type_rev' in HP3 . list_simpl in HP3.
                           apply Permutation_Type_rev' in HP4''. list_simpl in HP4''.
                           rewrite P_perm. list_simpl.
                           rewrite ? app_comm_cons, ? app_assoc. apply Permutation_Type_app_tail.
                           symmetry. etransitivity; [ apply Permutation_Type_app_tail, HP3 | ].
                           etransitivity; [ apply Permutation_Type_app_head, Permutation_Type_cons;
                                              [ reflexivity | apply HP4''] | ].
                           list_simpl. rewrite app_assoc. etransitivity; [ apply Permutation_Type_app_comm | ].
                           list_simpl. rewrite ? app_assoc. apply Permutation_Type_cons_app.
                           list_simpl. etransitivity; [ apply Permutation_Type_app_comm | ].
                           list_simpl. rewrite ? (app_assoc (rev l3g)). apply Permutation_Type_app_head.
                           rewrite (app_assoc (rev l3')). apply Permutation_Type_app_comm.
                   +++ assert (l3 ++ i :: l4r <> nil) as Hnil'
                         by (intros Hnil'; destruct l3; discriminate Hnil').
                       apply (snd Hocl3) with lw in Hnil'.
                       destruct Hocl4 as [Hocl4 _].
                       apply (ex_ir (rev (l3' ++ l3b ++ l3g) ++ igen x :: (rev (l3'' ++ l3h) ++ lw) ++ nil)).
                       *** apply gen_pam_rule; [ | assumption .. ].
                           intro. apply Hgax.
                       *** apply Permutation_Type_rev' in HP3. list_simpl in HP3.
                           apply Permutation_Type_rev' in HP4''. list_simpl in HP4''.
                           rewrite P_perm. list_simpl.
                           rewrite ? app_comm_cons, ? app_assoc. apply Permutation_Type_app_tail.
                           symmetry. etransitivity; [ apply Permutation_Type_app_tail, HP3 | ].
                           etransitivity; [ apply Permutation_Type_app_head, Permutation_Type_cons;
                                              [ reflexivity | apply HP4''] | ].
                           list_simpl. rewrite app_assoc. etransitivity; [ apply Permutation_Type_app_comm | ].
                           list_simpl. rewrite ? app_assoc. apply Permutation_Type_cons_app.
                           list_simpl. etransitivity; [ apply Permutation_Type_app_comm | ].
                           list_simpl. rewrite ? (app_assoc (rev l3g)). apply Permutation_Type_app_head.
                           rewrite (app_assoc (rev l3')). apply Permutation_Type_app_comm.
            ** inversion_clear Hoclm as [ | ? ? ? HF ].
               assert (Hoclm1 := Forall_inf_app_l _ _ HF).
               assert (Hoclm2 := Forall_inf_app_r _ _ HF).
               inversion_clear Hoclm2 as [ | ? ? Hoclm2' HF' ].
               inversion Hoclm2'; constructor; try assumption.
               apply Permutation_Type_rev' in HP3.
               apply (Permutation_Type_Forall_inf HP3) in Hoclm1.
               list_simpl in Hoclm1. list_simpl.
               assert (Hoclm1' := Forall_inf_app_l _ _ Hoclm1).
               assert (Hoclm1'' := Forall_inf_app_r _ _ Hoclm1).
               apply Permutation_Type_rev' in HP4''.
               apply (Permutation_Type_Forall_inf HP4'') in HF'. list_simpl in HF'.
               apply Forall_inf_app_l in HF'. apply Forall_inf_app; assumption.
            ** cbn. rewrite P_perm, bidual. list_simpl.
               apply Permutation_Type_cons; [ reflexivity | ].
               etransitivity; [ exact HP'' | ].
               list_simpl. apply Permutation_Type_app_swap_app.
            ** inversion_clear Hoclm as [ | ? ? ? HF ]; constructor; try assumption.
               list_simpl.
               assert (Hoclm1 := Forall_inf_app_l _ _ HF).
               assert (Hoclm2 := Forall_inf_app_r _ _ HF).
               inversion_clear Hoclm2 as [ | ? ? Hoclm2' HF' ].
               apply Permutation_Type_rev' in HP4''.
               apply (Permutation_Type_Forall_inf HP4'') in HF'. list_simpl in HF'.
               assert (H4l := Forall_inf_app_l _ _ HF').
               assert (H4r := Forall_inf_app_r _ _ HF').
               assert (H4r1 := Forall_inf_app_l _ _ H4r).
               assert (H4r2 := Forall_inf_app_r _ _ H4r).
               apply Forall_inf_app; [ apply H4r1 | ].
               apply Forall_inf_app; [ apply H4r2 | ].
               apply Permutation_Type_rev' in HP3.
               apply (Permutation_Type_Forall_inf HP3) in Hoclm1.
               list_simpl in Hoclm1. apply Forall_inf_app_r in Hoclm1.
               inversion Hoclm2'.
               list_simpl. apply Forall_inf_app; [ | constructor; [ constructor | constructor] ]; assumption.
            ** cbn. rewrite P_perm. list_simpl.
               rewrite app_comm_cons, 2 app_assoc. apply Permutation_Type_cons_app.
               etransitivity; [ exact HP1 | ].
               etransitivity; [ apply Permutation_Type_app_head, Permutation_Type_app_head,
                                      Permutation_Type_cons, HP4a; reflexivity | ].
               list_simpl. rewrite app_assoc. symmetry. apply Permutation_Type_cons_app.
               rewrite ? map_map. rewrite ? app_assoc. apply Permutation_Type_app_tail.
               list_simpl. symmetry in HP4'''.
               etransitivity; [ | apply Permutation_Type_app_head, Permutation_Type_app_tail, HP4''' ].
               etransitivity; [ | apply Permutation_Type_app_swap_app ].
               list_simpl. apply Permutation_Type_app_head.
               etransitivity; [ | apply Permutation_Type_app_comm ].
               rewrite ? app_assoc. apply Permutation_Type_app_tail, Permutation_Type_app_comm.
         ++ rewrite map_map in HP3. symmetry in HP3. apply Permutation_Type_map_inv in HP3 as [l3''' Heq' HP3].
            decomp_map Heq'. subst.
            rewrite <- map_map in HP1, HP2.
            rewrite app_assoc in HP4. apply Permutation_Type_cons_app_inv in HP4.
            list_simpl in HP4.
            apply Permutation_Type_app_app_inv in HP4 as [[[[l3a l3b] l3c] l3d] [[HP4' HP4''] [HP4''' HP4'''']]].
            apply Permutation_Type_app_app_inv in HP4'''' as [[[[l3e l3f] l3g] l3h] [[HP4a HP4b] [HP4c HP4d]]].
            symmetry in HP4'. apply Permutation_Type_map_inv in HP4' as [l4 Heq' HP4'].
            decomp_map Heq'. subst.
            apply (Permutation_Type_app_head l3b) in HP4d.
            assert (HP' := Permutation_Type_trans HP4'' HP4d).
            rewrite map_map in HP'. symmetry in HP'.
            clear HP4''. apply Permutation_Type_map_inv in HP' as [l4'' Heq' HP4''].
            decomp_map Heq'. subst.
            apply (Permutation_Type_app_tail (ill2ll C :: l4b)) in HP4a.
            apply (Permutation_Type_app_head (map dual (map ill2ll l3''))) in HP4a.
            assert (HP' := Permutation_Type_trans HP2 HP4a). rewrite <- (map_map _ _ l3g) in HP'.
            symmetry in HP4c. apply Permutation_Type_map_inv in HP4c as [l4'' Heq' HP4c].
            decomp_map Heq'. subst.
            rewrite <- (map_map _ _ l3h) in HP4b.
            apply (@Permutation_Type_cons _ (ill2ll C) _ eq_refl) in HP4b.
            apply (Permutation_Type_app_head (map dual (map ill2ll l3'')
              ++ (map ill2ll l3e ++ map dual (map ill2ll l3g)))) in HP4b.
            rewrite <- app_assoc in HP4b.
            assert (HP'' := Permutation_Type_trans HP' HP4b).
            specialize IHHll1 with (rev (l3g ++ l3'' ++ l3h)) (x :: l3e ++ l3f) C.
            assert (x :: l3e ++ l3f <> nil) as Hnil by (intros [=]).
            inversion_clear Hoclm as [ | ? ? ? HF ].
            assert (Hoclm1 := Forall_inf_app_l _ _ HF).
            assert (Hoclm2 := Forall_inf_app_r _ _ HF).
            inversion_clear Hoclm2 as [ | ? ? Hoclm2' HF' ].
            inversion_clear Hoclm2'.
            apply (Permutation_Type_Forall_inf HP4') in Hocl.
            apply (Permutation_Type_app_head l3a) in HP4c.
            apply (Permutation_Type_Forall_inf HP4c) in Hocl.
            apply Forall_inf_app_r in Hocl.
            assert (Hocl' := Forall_inf_cons _ X0 Hocl).
            apply IHHll1 in Hocl'; [ split | | ].
            ** apply (snd Hocl') with (igen x :: rev l3' ++ rev l3b) in Hnil.
               eapply ex_ir; [ apply Hnil | ].
               cbn. rewrite P_perm. cbn.
               apply Permutation_Type_rev' in HP3. list_simpl in HP3.
               apply Permutation_Type_rev' in HP4''. list_simpl in HP4''.
               list_simpl. symmetry. etransitivity; [ apply Permutation_Type_app_tail, HP3 | ].
                           etransitivity; [ apply Permutation_Type_app_head, Permutation_Type_cons;
                                              [ reflexivity | apply HP4''] | ].
                           list_simpl. rewrite app_assoc. etransitivity; [ apply Permutation_Type_app_comm | ].
                           list_simpl. rewrite ? app_assoc. apply Permutation_Type_cons_app.
                           list_simpl. etransitivity; [ apply Permutation_Type_app_comm | ].
               etransitivity; [ apply Permutation_Type_app_comm | ].
               apply Permutation_Type_app_head.
               rewrite app_assoc. etransitivity; [ apply Permutation_Type_app_comm | ].
               list_simpl. apply Permutation_Type_app_head.
               rewrite ? app_assoc. apply Permutation_Type_app_tail, Permutation_Type_app_comm.
            ** intros Hnil' lw.
               apply (snd Hocl') with (igen x :: rev l3' ++ rev l3b ++ lw) in Hnil.
               eapply ex_ir; [ apply Hnil | ].
               cbn. rewrite P_perm. cbn.
               apply Permutation_Type_rev' in HP3. list_simpl in HP3.
               apply Permutation_Type_rev' in HP4''. list_simpl in HP4''.
               list_simpl. rewrite ? app_comm_cons, ? app_assoc. apply Permutation_Type_app_tail.
               list_simpl. symmetry. etransitivity; [ apply Permutation_Type_app_tail, HP3 | ].
                           etransitivity; [ apply Permutation_Type_app_head, Permutation_Type_cons;
                                              [ reflexivity | apply HP4''] | ].
                           list_simpl. rewrite app_assoc. etransitivity; [ apply Permutation_Type_app_comm | ].
                           list_simpl. rewrite ? app_assoc. apply Permutation_Type_cons_app.
                           list_simpl. etransitivity; [ apply Permutation_Type_app_comm | ].
               etransitivity; [ apply Permutation_Type_app_comm | ].
               apply Permutation_Type_app_head.
               rewrite app_assoc. etransitivity; [ apply Permutation_Type_app_comm | ].
               list_simpl. apply Permutation_Type_app_head.
               rewrite ? app_assoc. apply Permutation_Type_app_tail, Permutation_Type_app_comm.
            ** constructor; try assumption.
               apply Permutation_Type_rev' in HP4''. list_simpl in HP4''.
               apply (Permutation_Type_Forall_inf HP4'') in HF'.
               rewrite app_assoc in HF'. apply Forall_inf_app_l in HF'.
               assert (H4l := Forall_inf_app_l _ _ HF').
               assert (H4r := Forall_inf_app_r _ _ HF').
               apply Permutation_Type_rev' in HP3. list_simpl in HP3.
               apply (Permutation_Type_Forall_inf HP3) in Hoclm1.
               list_simpl in Hoclm1. apply Forall_inf_app_l in Hoclm1.
               list_simpl. apply Forall_inf_app; [ assumption | ].
               apply Forall_inf_app; assumption.
            ** list_simpl. rewrite P_perm, bidual; list_simpl.
               cons2app. rewrite <- (app_comm_cons _ _ (ill2ll x)). apply Permutation_Type_cons_app.
               etransitivity; [ apply HP'' | ].
               cons2app. rewrite ? app_assoc. apply Permutation_Type_app_tail.
               list_simpl. etransitivity; [ apply Permutation_Type_app_comm | ].
               rewrite ? app_comm_cons, ? app_assoc. apply Permutation_Type_app_tail.
               list_simpl. symmetry. rewrite (app_assoc (map ill2ll l3e) (map dual (map ill2ll l3g))).
               apply Permutation_Type_cons_app. list_simpl. apply Permutation_Type_app_head.
               apply Permutation_Type_app_comm.
      -- assert (HP4' := HP4).
         symmetry in HP4'. apply Permutation_Type_vs_cons_inv in HP4' as [(l4a, l4b) Heq'].
         dichot_elt_app_inf_exec Heq'. subst.
         ++ cbn in HP3. rewrite map_map in HP3.
            symmetry in HP3. apply Permutation_Type_map_inv in HP3 as [l3''' Heq' HP3].
            decomp_map Heq'. subst.
            rewrite <- map_map in HP1.
            list_simpl in HP4. apply Permutation_Type_cons_app_inv in HP4.
            apply Permutation_Type_app_app_inv in HP4 as [[[[l3a l3b] l3c] l3d] [[HP4' HP4''] [HP4''' HP4'''']]].
            apply Permutation_Type_app_app_inv in HP4'''' as [[[[l3e l3f] l3g] l3h] [[HP4a HP4b] [HP4c HP4d]]].
            apply (@Permutation_Type_cons _ (ill2ll C) _ eq_refl) in HP4a.
            apply (Permutation_Type_app HP4''') in HP4a.
            apply (Permutation_Type_app_head (map dual (map ill2ll l3'))) in HP4a.
            assert (HP' := Permutation_Type_trans HP1 HP4a).
            symmetry in HP4'. apply Permutation_Type_map_inv in HP4' as [l4 Heq' HP4'].
            decomp_map Heq'. subst.
            apply (Permutation_Type_app_head l3b) in HP4d.
            assert (HP'' := Permutation_Type_trans HP4'' HP4d).
            rewrite map_map in HP''. symmetry in HP''. apply Permutation_Type_map_inv in HP''.
            clear HP4''. destruct HP'' as [l4' Heq' HP4''].
            decomp_map Heq'. subst.
            rewrite <- (map_map _ _ l3b), <- (map_map _ _ l3g) in HP'.
            symmetry in HP4c. apply Permutation_Type_map_inv in HP4c as [l4' Heq' HP4c].
            decomp_map Heq'. subst.
            specialize IHHll2 with (rev (l3' ++ l3b ++ l3g)) (x1 :: l3a ++ l3e) C.
            apply (Permutation_Type_Forall_inf HP4') in Hocl.
            assert (Hocl1 := Forall_inf_app_l _ _ Hocl).
            assert (Hocl2 := Forall_inf_app_r _ _ Hocl).
            apply (Permutation_Type_Forall_inf HP4c) in Hocl2.
            apply Forall_inf_app_l in Hocl2.
            assert (Hocl3 := Forall_inf_app Hocl1 Hocl2).
            inversion Hoclm as [ | ? ? ? HF ].
            apply Forall_inf_app_r in HF.
            inversion HF as [ | ? ? Hoclm' HF']; inversion_clear Hoclm'.
            assert (Hocl4 := Forall_inf_cons _ X0 Hocl3).
            apply IHHll2 in Hocl4.
            ** assert (x1 :: l3a ++ l3e <> nil) as Hnil by intros [=].
               split.
               --- apply (snd Hocl4) with (ilmap x1 x2 :: rev l3'' ++ rev l3h) in Hnil.
                   eapply ex_ir; [ apply Hnil | ].
                   rewrite P_perm. cbn.
                   apply Permutation_Type_elt.
                   apply Permutation_Type_rev' in HP3. list_simpl in HP3.
                   apply Permutation_Type_rev' in HP4''. list_simpl in HP4''.
                   list_simpl. symmetry. etransitivity; [ apply Permutation_Type_app_tail, HP3 | ].
                   etransitivity; [ apply Permutation_Type_app_head, HP4'' | ].
                   list_simpl. rewrite 2 app_assoc. etransitivity; [ apply Permutation_Type_app_comm | ].
                   rewrite ? app_assoc. apply Permutation_Type_app_tail.
                   etransitivity; [ apply Permutation_Type_app_comm | ].
                   rewrite ? app_assoc. apply Permutation_Type_app_tail.
                   list_simpl. apply Permutation_Type_app_rot.
               --- intros Hnil' lw.
                   apply (snd Hocl4) with (ilmap x1 x2 :: lw ++ rev l3'' ++ rev l3h) in Hnil.
                   eapply ex_ir; [ apply Hnil | ].
                   rewrite P_perm. cbn.
                   rewrite <- app_assoc, <- app_comm_cons. apply Permutation_Type_elt.
                   apply Permutation_Type_rev' in HP3. list_simpl in HP3.
                   apply Permutation_Type_rev' in HP4''. list_simpl in HP4''.
                   list_simpl. symmetry. etransitivity; [ apply Permutation_Type_app_tail, HP3 | ].
                   etransitivity; [ apply Permutation_Type_app_head, Permutation_Type_app_tail, HP4'' | ].
                   list_simpl. rewrite 2 app_assoc. etransitivity; [ apply Permutation_Type_app_comm | ].
                   rewrite ? app_assoc. apply Permutation_Type_app_tail.
                   etransitivity; [ apply Permutation_Type_app_comm | ].
                   rewrite ? app_assoc. apply Permutation_Type_app_tail, Permutation_Type_app_tail.
                   list_simpl. apply Permutation_Type_app_rot.
            ** constructor; [ assumption | ].
               cbn in HP4''.
               apply Permutation_Type_rev' in HP4''.
               apply (Permutation_Type_Forall_inf HP4'') in HF'.
               list_simpl in HF'.
               apply Forall_inf_app_r in HF' as Hoclm1.
               inversion Hoclm as [ | ? ? ? HF'' ].
               apply Forall_inf_app_l in HF'' as Hoclm2.
               cbn in HP3.
               apply Permutation_Type_rev' in HP3.
               apply (Permutation_Type_Forall_inf HP3) in Hoclm2.
               list_simpl in Hoclm2.
               apply Forall_inf_app_r in Hoclm2.
               rewrite rev_app_distr.
               apply Forall_inf_app; list_simpl; assumption.
            ** cbn. rewrite P_perm, bidual. list_simpl.
               cons2app. rewrite <- (app_comm_cons _ _ (ill2ll x1)). apply Permutation_Type_cons_app.
               list_simpl. etransitivity; [ exact HP' | ].
               rewrite 2 app_assoc. symmetry. apply Permutation_Type_cons_app.
               rewrite ? app_assoc. apply Permutation_Type_app_tail.
               etransitivity; [ | apply Permutation_Type_app_comm ].
               rewrite ? app_assoc. apply Permutation_Type_app_tail.
               list_simpl. apply Permutation_Type_app_rot.
         ++ cbn in HP3. rewrite map_map in HP3.
            symmetry in HP3. apply Permutation_Type_map_inv in HP3 as [l3''' Heq' HP3].
            decomp_map Heq'. subst.
            rewrite <- map_map in HP1, HP2.
            rewrite app_assoc in HP4; apply Permutation_Type_cons_app_inv in HP4.
            apply Permutation_Type_app_app_inv in HP4.
            destruct HP4 as [[[[l3a l3b] l3c] l3d] [[HP4' HP4''] [HP4''' HP4'''']]];
              cbn in HP4', HP4'', HP4''', HP4''''.
            apply Permutation_Type_app_app_inv in HP4'''.
            destruct HP4''' as [[[[l3e l3f] l3g] l3h] [[HP4a HP4b] [HP4c HP4d]]];
              cbn in HP4a, HP4b, HP4c, HP4d, HP1.
            apply (Permutation_Type_app_head (map dual (map ill2ll l3'))) in HP4a.
            assert (HP' := Permutation_Type_trans HP1 HP4a).
            symmetry in HP4'. apply Permutation_Type_map_inv in HP4' as [l4 Heq' HP4'].
            decomp_map Heq'. subst.
            apply (Permutation_Type_app_tail l3d) in HP4d.
            assert (HP'' := Permutation_Type_trans HP4'' HP4d).
            rewrite map_map in HP''.
            symmetry in HP''. apply Permutation_Type_map_inv in HP''.
            clear HP4''. destruct HP'' as [l4'' Heq' HP4''].
            decomp_map Heq'. subst.
            rewrite <- (map_map _ _ l3g) in HP'.
            symmetry in HP4c. apply Permutation_Type_map_inv in HP4c as [l4'' Heq' HP4c].
            decomp_map Heq'. subst.
            rewrite <- (map_map _ _ l3h) in HP4b.
            apply (@Permutation_Type_cons _ (ill2ll C) _ eq_refl) in HP4''''.
            apply (Permutation_Type_app HP4b) in HP4''''.
            apply (Permutation_Type_app_head (map dual (map ill2ll l3''))) in HP4''''.
            assert (HP'' := Permutation_Type_trans HP2 HP4'''').
            specialize IHHll2 with (rev (l3' ++ l3g)) l3e x1.
            apply (Permutation_Type_Forall_inf HP4') in Hocl.
            assert (Hocl1 := Forall_inf_app_l _ _ Hocl).
            assert (Hocl2 := Forall_inf_app_r _ _ Hocl).
            rewrite <- (map_map _ _ l3d) in HP''.
            specialize IHHll1 with (rev (x2 :: l3'' ++ l3h ++ l3d)) (l3c ++ l3f) C.
            apply (Permutation_Type_Forall_inf HP4c) in Hocl1.
            assert (Hocl3 := Forall_inf_app_l _ _ Hocl1).
            assert (Hocl4 := Forall_inf_app_r _ _ Hocl1).
            assert (Hocl5 := Forall_inf_app Hocl2 Hocl4).
            apply IHHll2 in Hocl3; [ apply IHHll1 in Hocl5 | | ].
            ** split.
               --- destruct Hocl5 as [Hocl5 _].
                   destruct Hocl3 as [Hocl3 _].
                   apply (ex_ir (nil ++ rev (l3' ++ l3g) ++
                                   ilmap x1 x2 :: rev (l3'' ++ l3h ++ l3d))).
                   +++ apply lmap_ilr; try assumption.
                       eapply ex_ir; [ apply Hocl5 | ].
                       rewrite P_perm. cbn. cons2app. apply Permutation_Type_app_comm.
                   +++ rewrite P_perm. cbn.
                       apply Permutation_Type_rev' in HP3. list_simpl in HP3.
                       apply Permutation_Type_rev' in HP4''. list_simpl in HP4''.
                       list_simpl. symmetry. etransitivity; [ apply Permutation_Type_app_tail, HP3 | ].
                       etransitivity;
                         [ apply Permutation_Type_app_head, Permutation_Type_cons, HP4''; reflexivity | ].
                       list_simpl. rewrite 2 app_assoc. etransitivity; [ apply Permutation_Type_app_comm | ].
                       list_simpl. rewrite ? (app_assoc (rev l3g)). apply Permutation_Type_cons_app.
                       rewrite app_assoc. etransitivity; [ apply Permutation_Type_app_comm | ].
                       list_simpl. apply Permutation_Type_app_head.
                       etransitivity; [ apply Permutation_Type_app_comm | list_simpl; reflexivity ].
               --- intros Hnil lw. destruct lo; [ contradiction Hnil; reflexivity | ].
                   apply (Permutation_Type_app_tail l3c) in HP4c.
                   assert (HP''' := Permutation_Type_trans HP4' HP4c).
                   symmetry in HP'''. apply Permutation_Type_vs_cons_inv in HP''' as [(l4l & l4r) Heq'].
                   rewrite <- app_assoc in Heq'. dichot_elt_app_inf_exec Heq'; subst.
                   +++ assert (l4l ++ i :: l3 <> nil) as Hnil'
                         by (intros Hnil'; destruct l4l; discriminate Hnil').
                       apply (snd Hocl3) with lw in Hnil'.
                       destruct Hocl5 as [Hocl5 _].
                       apply (ex_ir (nil ++ (rev (l3' ++ l3g) ++ lw) ++
                                      ilmap x1 x2 :: rev (l3'' ++ l3h ++ l3d))).
                       *** apply lmap_ilr; try assumption.
                           eapply ex_ir; [ apply Hocl5 | ].
                           rewrite P_perm. cbn. symmetry. apply Permutation_Type_cons_append.
                       *** rewrite P_perm. cbn.
                           apply Permutation_Type_rev' in HP3; list_simpl in HP3.
                           apply Permutation_Type_rev' in HP4''. list_simpl in HP4''.
                           list_simpl. symmetry. etransitivity; [ apply Permutation_Type_app_tail, HP3 | ].
                           etransitivity; [ apply Permutation_Type_app_head, Permutation_Type_cons,
                                     Permutation_Type_app_tail, HP4''; reflexivity | ].
                           list_simpl. rewrite 2 app_assoc. etransitivity; [ apply Permutation_Type_app_comm | ].
                           list_simpl. rewrite ? (app_assoc (rev l3g)), ? (app_assoc _ lw).
                           apply Permutation_Type_cons_app.
                           rewrite app_assoc. etransitivity; [ apply Permutation_Type_app_comm | ].
                           list_simpl. apply Permutation_Type_app_head.
                           symmetry. etransitivity; [ apply Permutation_Type_app_comm | ].
                           list_simpl. apply Permutation_Type_app_head.
                           rewrite app_assoc.
                           etransitivity; [ apply Permutation_Type_app_comm | list_simpl; reflexivity ].
                   +++ assert (l3 ++ i :: l4r <> nil) as Hnil'
                         by (intros Hnil'; destruct l3; discriminate Hnil').
                       rewrite Heq'1 in Hnil'.
                       assert (l3c ++ l3f <> nil) as Hnil''.
                       { intros Hnil''. apply Hnil'.
                         clear - Hnil''. apply app_eq_nil in Hnil'' as [-> ->]. reflexivity. }
                       apply (snd Hocl5) with lw in Hnil''.
                       destruct Hocl3 as [Hocl3 _].
                       apply (ex_ir (lw ++ rev (l3' ++ l3g) ++
                                       ilmap x1 x2 :: rev (l3'' ++ l3h ++ l3d))).
                       *** apply lmap_ilr; [ assumption | ].
                           eapply ex_ir; [ apply Hnil'' | ].
                           rewrite P_perm. cbn. etransitivity; [ apply Permutation_Type_app_comm | ].
                           apply Permutation_Type_app_head.
                           symmetry. etransitivity; [ | apply Permutation_Type_middle ].
                           list_simpl. reflexivity.
                       *** rewrite P_perm. cbn.
                           apply Permutation_Type_rev' in HP3. list_simpl in HP3.
                           apply Permutation_Type_rev' in HP4''. list_simpl in HP4''.
                           list_simpl. etransitivity; [ apply Permutation_Type_app_comm | ].
                           rewrite ? app_comm_cons, ? app_assoc. apply Permutation_Type_app_tail.
                           list_simpl. symmetry. etransitivity; [ apply Permutation_Type_app_tail, HP3 | ].
                           etransitivity;
                             [ apply Permutation_Type_app_head, Permutation_Type_cons, HP4''; reflexivity | ].
                           list_simpl. rewrite 2 app_assoc. etransitivity; [ apply Permutation_Type_app_comm | ].
                           list_simpl. rewrite ? (app_assoc (rev l3g)). apply Permutation_Type_cons_app.
                           rewrite app_assoc. etransitivity; [ apply Permutation_Type_app_comm | ].
                           list_simpl. apply Permutation_Type_app_head.
                           etransitivity; [ apply Permutation_Type_app_comm | list_simpl; reflexivity ].
            ** inversion_clear Hoclm as [ | ? ? ? HF ].
               assert (Hoclm1 := Forall_inf_app_l _ _ HF).
               assert (Hoclm2 := Forall_inf_app_r _ _ HF).
               inversion_clear Hoclm2 as [ | ? ? Hoclm2' HF' ].
               inversion Hoclm2'; constructor; try assumption.
               apply Permutation_Type_rev' in HP3.
               apply (Permutation_Type_Forall_inf HP3) in Hoclm1.
               apply Forall_inf_rev.
               constructor; try assumption.
               apply Forall_inf_app.
               --- list_simpl in Hoclm1. apply Forall_inf_app_l in Hoclm1.
                   rewrite <- rev_involutive.
                   apply Forall_inf_rev, Hoclm1.
               --- apply Permutation_Type_rev' in HP4''.
                   apply (Permutation_Type_Forall_inf HP4'') in HF'.
                   list_simpl in HF'.
                   assert (H4l := Forall_inf_app_l _ _ HF').
                   assert (H4r := Forall_inf_app_r _ _ HF').
                   apply Forall_inf_rev in H4l.
                   rewrite rev_involutive in H4l.
                   apply Forall_inf_app; [ | assumption ].
                   apply Forall_inf_app_l in H4r.
                   apply Forall_inf_rev in H4r.
                   rewrite rev_involutive in H4r; assumption.
            ** cbn. rewrite P_perm. list_simpl.
               rewrite app_comm_cons, 2 app_assoc. apply Permutation_Type_cons_app.
               list_simpl. etransitivity; [ exact HP'' | ].
               rewrite app_assoc. symmetry. apply Permutation_Type_cons_app.
               list_simpl. rewrite ? app_assoc. apply Permutation_Type_app_tail.
               list_simpl. etransitivity; [ apply Permutation_Type_app_comm | ].
               rewrite ? app_assoc.
               apply Permutation_Type_app_tail, Permutation_Type_app_tail, Permutation_Type_app_comm.
            ** inversion_clear Hoclm as [ | ? ? ? HF ].
               assert (Hoclm1 := Forall_inf_app_l _ _ HF).
               assert (Hoclm2 := Forall_inf_app_r _ _ HF).
               inversion_clear Hoclm2 as [ | ? ?  Hoclm2' HF' ].
               cbn in HP4''.
               apply Permutation_Type_rev' in HP4''.
               apply (Permutation_Type_Forall_inf HP4'') in HF'.
               list_simpl in HF'.
               assert (H4l := Forall_inf_app_l _ _ HF').
               assert (H4r := Forall_inf_app_r _ _ HF').
               apply Forall_inf_app_r in H4r.
               inversion_clear Hoclm2'; constructor; try assumption.
               list_simpl; apply Forall_inf_app; try assumption.
               cbn in HP3.
               apply Permutation_Type_rev' in HP3.
               apply (Permutation_Type_Forall_inf HP3) in Hoclm1.
               list_simpl in Hoclm1; apply Forall_inf_app_r in Hoclm1.
               apply Hoclm1.
            ** list_simpl. rewrite P_perm, bidual. list_simpl.
               apply Permutation_Type_cons; [ reflexivity | ].
               etransitivity; [ exact HP1 | ].
               etransitivity; [ exact HP4a | ].
               rewrite ? map_map. apply Permutation_Type_app_swap_app.
      -- assert (HP4' := HP4).
         symmetry in HP4'. apply Permutation_Type_vs_cons_inv in HP4' as [(l4a & l4b) Heq'].
         dichot_elt_app_inf_exec Heq'; subst.
         ++ rewrite map_map in HP3.
            symmetry in HP3. apply Permutation_Type_map_inv in HP3 as [l3''' Heq' HP3].
            decomp_map Heq'. subst.
            rewrite <- map_map in HP1.
            list_simpl in HP4. apply Permutation_Type_cons_app_inv in HP4.
            apply Permutation_Type_app_app_inv in HP4 as [[[[l3a l3b] l3c] l3d] [[HP4' HP4''] [HP4''' HP4'''']]].
            apply Permutation_Type_app_app_inv in HP4'''' as [[[[l3e l3f] l3g] l3h] [[HP4a HP4b] [HP4c HP4d]]].
            apply (@Permutation_Type_cons _ (ill2ll C) _ eq_refl) in HP4a.
            apply (Permutation_Type_app HP4''') in HP4a.
            apply (Permutation_Type_app_head (map dual (map ill2ll l3'))) in HP4a.
            assert (HP' := Permutation_Type_trans HP1 HP4a).
            symmetry in HP4'. apply Permutation_Type_map_inv in HP4' as [l4 Heq' HP4'].
            decomp_map Heq'. subst.
            apply (Permutation_Type_app_head l3b) in HP4d.
            assert (HP'' := Permutation_Type_trans HP4'' HP4d).
            rewrite map_map in HP''. symmetry in HP''. apply Permutation_Type_map_inv in HP''.
            clear HP4''. destruct HP'' as [l4' Heq' HP4''].
            decomp_map Heq'. subst.
            rewrite <- (map_map _ _ l3b), <- (map_map _ _ l3g) in HP'.
            symmetry in HP4c. apply Permutation_Type_map_inv in HP4c as [l4' Heq' HP4c].
            decomp_map Heq'. subst.
            specialize IHHll2 with (rev (l3' ++ l3b ++ l3g)) (x :: l3a ++ l3e) C.
            apply (Permutation_Type_Forall_inf HP4') in Hocl.
            assert (Hocl1 := Forall_inf_app_l _ _ Hocl).
            assert (Hocl2 := Forall_inf_app_r _ _ Hocl).
            apply (Permutation_Type_Forall_inf HP4c) in Hocl2.
            apply Forall_inf_app_l in Hocl2.
            assert (Hocl3 := Forall_inf_app Hocl1 Hocl2).
            inversion_clear Hoclm as [ | ? ? ? HF ].
            assert (HF'' := Forall_inf_app_l _ _ HF).
            apply Forall_inf_app_r in HF.
            inversion HF as [ | ? ? Hoclm' HF' ]; inversion_clear Hoclm'.
            assert (Hocl4 := Forall_inf_cons _ X0 Hocl3).
            apply IHHll2 in Hocl4.
            ** assert (x :: l3a ++ l3e <> nil) as Hnil by intros [=].
               split.
               --- apply (snd Hocl4) with (ineg x :: rev l3'' ++ rev l3h) in Hnil.
                   eapply ex_ir; [ apply Hnil | ].
                   rewrite P_perm. cbn. apply Permutation_Type_elt.
                   cbn in HP3. apply Permutation_Type_rev' in HP3. list_simpl in HP3.
                   cbn in HP4''. apply Permutation_Type_rev' in HP4''. list_simpl in HP4''.
                   list_simpl. symmetry.
                   etransitivity; [ apply Permutation_Type_app_tail, HP3 | ].
                   etransitivity; [ apply Permutation_Type_app_head, HP4'' | ].
                   symmetry. rewrite app_assoc. etransitivity; [ apply Permutation_Type_app_comm | ].
                   rewrite ? app_assoc. apply Permutation_Type_app_tail, Permutation_Type_app_tail.
                   list_simpl. apply Permutation_Type_app_swap_app.
               --- intros Hnil' lw.
                   apply (snd Hocl4) with (ineg x :: lw ++ rev l3'' ++ rev l3h) in Hnil.
                   eapply ex_ir; [ apply Hnil | ].
                   rewrite P_perm. cbn.
                   rewrite <- app_assoc, <- app_comm_cons. apply Permutation_Type_elt.
                   cbn in HP3. apply Permutation_Type_rev' in HP3. list_simpl in HP3.
                   cbn in HP4''. apply Permutation_Type_rev' in HP4''. list_simpl in HP4''.
                   list_simpl. symmetry.
                   etransitivity; [ apply Permutation_Type_app_tail, HP3 | ].
                   etransitivity; [ apply Permutation_Type_app_head, Permutation_Type_app_tail, HP4'' | ].
                   list_simpl. rewrite 2 app_assoc. etransitivity; [ apply Permutation_Type_app_comm | ].
                   rewrite ? app_assoc. apply Permutation_Type_app_tail.
                   etransitivity; [ apply Permutation_Type_app_comm | ].
                   rewrite ? app_assoc. apply Permutation_Type_app_tail, Permutation_Type_app_tail.
                   list_simpl. apply Permutation_Type_app_rot.
            ** constructor; try assumption.
               cbn in HP4''.
               apply Permutation_Type_rev' in HP4''.
               apply (Permutation_Type_Forall_inf HP4'') in HF'.
               list_simpl in HF'.
               apply Forall_inf_app_r in HF' as Hoclm1.
               apply Permutation_Type_rev' in HP3.
               apply (Permutation_Type_Forall_inf HP3) in HF''.
               list_simpl in HF''. apply Forall_inf_app_r in HF''.
               rewrite rev_app_distr. apply Forall_inf_app; list_simpl; assumption.
            ** cbn. rewrite P_perm, bidual. list_simpl.
               cons2app. rewrite <- (app_comm_cons _ _ (ill2ll x)). apply Permutation_Type_cons_app.
               list_simpl. etransitivity; [ exact HP' | ].
               symmetry. rewrite ? app_assoc. apply Permutation_Type_cons_app.
               rewrite ? app_assoc. apply Permutation_Type_app_tail.
               list_simpl. etransitivity; [ | apply Permutation_Type_app_swap_app ].
               apply Permutation_Type_app_head, Permutation_Type_app_rot.
         ++ rewrite map_map in HP3.
            symmetry in HP3. apply Permutation_Type_map_inv in HP3 as [l3''' Heq' HP3].
            decomp_map Heq'. subst.
            rewrite <- map_map in HP1, HP2.
            rewrite app_assoc in HP4. apply Permutation_Type_cons_app_inv in HP4.
            apply Permutation_Type_app_app_inv in HP4.
            destruct HP4 as [[[[l3a l3b] l3c] l3d] [[HP4' HP4''] [HP4''' HP4'''']]].
            apply Permutation_Type_app_app_inv in HP4'''.
            destruct HP4''' as [[[[l3e l3f] l3g] l3h] [[HP4a HP4b] [HP4c HP4d]]].
            apply (Permutation_Type_app_head (map dual (map ill2ll l3'))) in HP4a.
            assert (HP' := Permutation_Type_trans HP1 HP4a).
            symmetry in HP4'. apply Permutation_Type_map_inv in HP4' as [l4 Heq' HP4'].
            decomp_map Heq'. subst.
            apply (Permutation_Type_app_tail l3d) in HP4d.
            assert (HP'' := Permutation_Type_trans HP4'' HP4d).
            clear HP4''. rewrite map_map in HP''. symmetry in HP''.
            apply Permutation_Type_map_inv in HP'' as [l4'' Heq' HP4''].
            decomp_map Heq'. subst.
            rewrite <- (map_map _ _ l3g) in HP'.
            symmetry in HP4c. apply Permutation_Type_map_inv in HP4c as [l4'' Heq' HP4c].
            decomp_map Heq'. subst.
            rewrite <- (map_map _ _ l3h) in HP4b.
            apply (@Permutation_Type_cons _ (ill2ll C) _ eq_refl) in HP4''''.
            apply (Permutation_Type_app HP4b) in HP4''''.
            apply (Permutation_Type_app_head (map dual (map ill2ll l3''))) in HP4''''.
            assert (HP'' := Permutation_Type_trans HP2 HP4'''').
            specialize IHHll2 with (rev (l3' ++ l3g)) l3e x.
            apply (Permutation_Type_Forall_inf HP4') in Hocl.
            assert (Hocl1 := Forall_inf_app_l _ _ Hocl).
            assert (Hocl2 := Forall_inf_app_r _ _ Hocl).
            rewrite <- (map_map _ _ l3d) in HP''.
            specialize IHHll1 with (rev (ivar atN :: l3'' ++ l3h ++ l3d)) (l3c ++ l3f) C.
            apply (Permutation_Type_Forall_inf HP4c) in Hocl1.
            assert (Hocl3 := Forall_inf_app_l _ _ Hocl1).
            assert (Hocl4 := Forall_inf_app_r _ _ Hocl1).
            assert (Hocl5 := Forall_inf_app Hocl2 Hocl4).
            apply IHHll2 in Hocl3; [ apply IHHll1 in Hocl5 | | ].
            ** split.
               --- destruct Hocl5 as [Hocl5 _].
                   destruct Hocl3 as [Hocl3 _].
                   apply neg_map_rule with _ _ (rev l3'' ++ rev l3h) (rev l3d) _ C in Hocl3.
                   +++ eapply ex_ir; [ apply Hocl3 | ].
                       rewrite P_perm. cbn.
                       rewrite app_assoc. apply Permutation_Type_elt.
                       apply Permutation_Type_rev' in HP3. list_simpl in HP3.
                       apply Permutation_Type_rev' in HP4''. list_simpl in HP4''.
                       list_simpl. symmetry. etransitivity; [ apply Permutation_Type_app_tail, HP3 | ].
                       etransitivity; [ apply Permutation_Type_app_head, HP4'' | ].
                       list_simpl. apply Permutation_Type_app_head.
                       rewrite app_assoc.
                       etransitivity; [ apply Permutation_Type_app_comm | list_simpl; reflexivity ].
                   +++ intros a Ha. apply (snd (Hgax a) Ha).
                   +++ eapply ex_ir; [ apply Hocl5 | ].
                       rewrite P_perm. cbn.
                       etransitivity; [ | apply Permutation_Type_app_comm ].
                       list_simpl. rewrite 2 app_assoc. symmetry. apply Permutation_Type_cons_app.
                       list_simpl. apply Permutation_Type_app_head, Permutation_Type_app_comm.
               --- intros Hnil lw. destruct lo; [ contradiction Hnil; reflexivity | ].
                   apply (Permutation_Type_app_tail l3c) in HP4c.
                   assert (HP''' := Permutation_Type_trans HP4' HP4c).
                   symmetry in HP'''. apply Permutation_Type_vs_cons_inv in HP''' as [(l4l, l4r) Heq'].
                   rewrite <- app_assoc in Heq'. cbn in Heq'. dichot_elt_app_inf_exec Heq'; subst.
                   +++ assert (l4l ++ i :: l3 <> nil) as Hnil'
                         by (intros Hnil'; destruct l4l; discriminate Hnil').
                       apply (snd Hocl3) with lw in Hnil'.
                       destruct Hocl5 as [Hocl5 _].
                       apply neg_map_rule with _ _ (rev l3'' ++ rev l3h) (rev l3d) _ C in Hnil'.
                       *** eapply ex_ir; [ apply Hnil' | ].
                           rewrite P_perm. list_simpl. rewrite 4 app_assoc.
                           apply Permutation_Type_elt.
                           apply Permutation_Type_rev' in HP3. list_simpl in HP3.
                           apply Permutation_Type_rev' in HP4''. list_simpl in HP4''.
                           list_simpl. symmetry.
                           etransitivity; [ apply Permutation_Type_app_tail, HP3 | ].
                           etransitivity;
                             [ apply Permutation_Type_app_head, Permutation_Type_app_tail, HP4'' | ].
                           list_simpl. apply Permutation_Type_app_head.
                           symmetry. rewrite app_assoc. etransitivity; [ apply Permutation_Type_app_comm |  ].
                           list_simpl. apply Permutation_Type_app_head.
                           etransitivity; [ apply Permutation_Type_app_comm | list_simpl; reflexivity ].
                       *** intros a Ha. apply (snd (Hgax a) Ha).
                       *** eapply ex_ir; [ apply Hocl5 | ].
                           rewrite P_perm. list_simpl.
                           cons2app. etransitivity; [ apply Permutation_Type_app_comm | ].
                           rewrite ? app_assoc. apply Permutation_Type_app_tail.
                           list_simpl. apply Permutation_Type_app_swap_app.
                   +++ assert (l3 ++ i :: l4r <> nil) as Hnil'
                         by (intros Hnil'; destruct l3; inversion Hnil').
                       rewrite Heq'1 in Hnil'.
                       assert (l3c ++ l3f <> nil) as Hnil''.
                       { intros Hnil''. apply Hnil'. apply app_eq_nil in Hnil'' as [-> ->]. reflexivity. }
                       apply (snd Hocl5) with lw in Hnil''.
                       destruct Hocl3 as [Hocl3 _].
                       apply neg_map_rule with _ _ (rev l3'' ++ rev l3h) (rev l3d ++ lw) _ C in Hocl3.
                       *** eapply ex_ir; [ apply Hocl3 | ].
                           rewrite P_perm. list_simpl.
                           rewrite 3 app_assoc. apply Permutation_Type_elt.
                           apply Permutation_Type_rev' in HP3. list_simpl in HP3.
                           apply Permutation_Type_rev' in HP4''. list_simpl in HP4''.
                           list_simpl. rewrite ? app_assoc. apply Permutation_Type_app_tail.
                           symmetry. etransitivity; [ apply Permutation_Type_app_tail, HP3 | ].
                           etransitivity; [ apply Permutation_Type_app_head, HP4'' | ].
                           list_simpl. apply Permutation_Type_app_head.
                           rewrite app_assoc.
                           etransitivity; [ apply Permutation_Type_app_comm | list_simpl; reflexivity ].
                       *** intros a Ha. apply (snd (Hgax a) Ha).
                       *** eapply ex_ir; [ apply Hnil'' | ].
                           rewrite P_perm. cbn.
                           rewrite ? app_comm_cons, ? app_assoc. apply Permutation_Type_app_tail.
                           list_simpl. etransitivity; [ apply Permutation_Type_app_comm | ].
                           list_simpl. apply Permutation_Type_app_swap_app.
            ** inversion_clear Hoclm as [ | ? ? ? HF ].
               assert (Hoclm1 := Forall_inf_app_l _ _ HF).
               assert (Hoclm2 := Forall_inf_app_r _ _ HF).
               inversion_clear Hoclm2 as [ | ? ? Hoclm2' HF' ].
               inversion Hoclm2'; constructor; try assumption.
               apply Permutation_Type_rev' in HP3.
               apply (Permutation_Type_Forall_inf HP3) in Hoclm1.
               apply Forall_inf_rev.
               constructor; [ | apply Forall_inf_app ].
               --- constructor.
               --- list_simpl in Hoclm1. apply Forall_inf_app_l in Hoclm1.
                   rewrite <- rev_involutive. apply Forall_inf_rev, Hoclm1.
               --- apply Permutation_Type_rev' in HP4''.
                   apply (Permutation_Type_Forall_inf HP4'') in HF'. list_simpl in HF'.
                   assert (H4l := Forall_inf_app_l _ _ HF').
                   assert (H4r := Forall_inf_app_r _ _ HF').
                   apply Forall_inf_rev in H4l. rewrite rev_involutive in H4l.
                   apply Forall_inf_app; [ | assumption ].
                   apply Forall_inf_app_l in H4r.
                   apply Forall_inf_rev in H4r.
                   rewrite rev_involutive in H4r. assumption.
            ** cbn. rewrite P_perm. list_simpl.
               rewrite app_comm_cons, 2 app_assoc. apply Permutation_Type_cons_app.
               etransitivity; [ exact HP'' | ].
               rewrite ? app_comm_cons, ? app_assoc. apply Permutation_Type_app_tail.
               list_simpl. symmetry. rewrite app_comm_cons. etransitivity; [ apply Permutation_Type_app_comm | ].
               rewrite ? app_assoc. apply Permutation_Type_app_tail.
               list_simpl. apply Permutation_Type_app_swap_app.
            ** inversion_clear Hoclm as [ | ? ? ? HF ].
               assert (Hoclm1 := Forall_inf_app_l _ _ HF).
               assert (Hoclm2 := Forall_inf_app_r _ _ HF).
               inversion_clear Hoclm2 as [ | ? ? Hoclm2' HF' ].
               cbn in HP4''; apply Permutation_Type_rev' in HP4''.
               apply (Permutation_Type_Forall_inf HP4'') in HF'.
               list_simpl in HF'.
               assert (H4l := Forall_inf_app_l _ _ HF').
               assert (H4r := Forall_inf_app_r _ _ HF').
               apply Forall_inf_app_r in H4r.
               inversion_clear Hoclm2'; constructor; try assumption.
               list_simpl. apply Forall_inf_app; try assumption.
               apply Permutation_Type_rev' in HP3.
               apply (Permutation_Type_Forall_inf HP3) in Hoclm1.
               list_simpl in Hoclm1. apply Forall_inf_app_r in Hoclm1. apply Hoclm1.
            ** list_simpl. rewrite P_perm. cbn. rewrite bidual.
               apply Permutation_Type_cons; [ reflexivity | ].
               etransitivity; [ exact HP' | apply Permutation_Type_app_swap_app ].
- symmetry in HP; apply PCPermutation_Type_vs_cons_inv in HP as [(l', l'') HP Heq]; cbn in Heq, HP.
  destruct l'; inversion Heq; [ destruct C; inversion H0 | ]; subst.
  + specialize IHHll with (l0 ++ C1 :: nil) lo C2.
    apply IHHll in Hocl.
    * destruct Hocl as [IH1 IH2].
      split.
      -- apply lpam_irr. assumption.
      -- intros Hnil l2.
         assert (IH := IH2 Hnil l2).
         list_simpl in IH.
         list_simpl. apply lpam_irr.
         eapply ex_ir; [ eassumption | ].
         rewrite P_perm. list_simpl. apply Permutation_Type_app_head, Permutation_Type_cons_append.
    * inversion_clear Hoclm as [ | ? ?  Hoclm' ]. inversion_clear Hoclm'.
      constructor; try assumption.
      apply Forall_inf_app; [ assumption | ].
      constructor; [ assumption | constructor ].
    * rewrite P_perm in HP. cbn in HP. rewrite app_nil_r in HP.
      cbn. rewrite P_perm. cbn.
      apply Permutation_Type_cons; [ reflexivity | ].
      list_simpl. apply Permutation_Type_cons_app. rewrite ! map_rev. assumption.
  + specialize IHHll with (l0 ++ C :: nil) lo N.
    apply IHHll in Hocl.
    * destruct Hocl as [IH1 IH2].
      split.
      -- apply gen_irr. assumption.
      -- intros Hnil l2.
         assert (IH := IH2 Hnil l2).
         list_simpl in IH.
         list_simpl. apply gen_irr.
         eapply ex_ir; [ eassumption | ].
         rewrite P_perm. list_simpl.
         apply Permutation_Type_app_head, Permutation_Type_cons_append.
    * inversion_clear Hoclm as [ | ? ? Hoclm' ].
      inversion_clear Hoclm'.
      constructor; try assumption.
      -- constructor.
      -- apply Forall_inf_app; try assumption.
         constructor; [ | constructor ]; assumption.
    * rewrite P_perm in HP. cbn in HP. rewrite app_nil_r in HP.
      cbn. rewrite P_perm.
      apply Permutation_Type_cons; [ reflexivity | ].
      list_simpl. apply Permutation_Type_cons_app. rewrite ! map_rev. assumption.
  + specialize IHHll with (C1 :: l0) lo C2.
    apply IHHll in Hocl.
    * destruct Hocl as [IH1 IH2].
      split.
      -- apply lmap_irr; assumption.
      -- intros Hnil l2.
         assert (IH := IH2 Hnil l2).
         list_simpl in IH. list_simpl. apply lmap_irr; assumption.
    * inversion_clear Hoclm as [ | ? ? Hoclm' ].
      inversion_clear Hoclm'.
      constructor; [ assumption | ].
      constructor; assumption.
    * cbn in HP. rewrite P_perm in HP. cbn in HP.
      cbn. rewrite P_perm. cbn.
      rewrite app_comm_cons, app_assoc. apply Permutation_Type_cons_app.
      now apply Permutation_Type_cons.
  + specialize IHHll with (C :: l0) lo N.
    apply IHHll in Hocl.
    * destruct Hocl as [IH1 IH2].
      split.
      -- apply neg_irr; assumption.
      -- intros Hnil l2.
         assert (IH := IH2 Hnil l2).
         list_simpl in IH.
         list_simpl. apply neg_irr. assumption.
    * inversion_clear Hoclm as [ | ? ? Hoclm' ].
      inversion_clear Hoclm'.
      constructor; try assumption.
      -- constructor.
      -- constructor; assumption.
    * cbn in HP. rewrite P_perm in HP. cbn in HP.
      cbn. rewrite P_perm. cbn.
      rewrite app_comm_cons, app_assoc; apply Permutation_Type_cons_app.
      now apply Permutation_Type_cons.
  + dichot_elt_app_inf_exec H1; subst;
      [ decomp_map H0 eqn:Hx
      | list_simpl in H2; decomp_map H2 eqn:Hx; decomp_map H2 ];
      destruct x; destr_eq Hx; subst;
      [ exfalso; apply Forall_inf_app_r in Hocl; inversion Hocl as [ | ? ? Hocl'];
        inversion Hocl' .. | ].
    apply (f_equal (@rev _)) in H2. list_simpl in H2. subst.
    apply (PEPermutation_Type_cons _ (eq_refl (dual (ill2ll x1)))) in HP.
    apply (PEPermutation_Type_cons _ (eq_refl (dual (ill2ll x2)))) in HP.
    apply PEPermutation_PCPermutation_Type in HP. unfold id in HP. rewrite 2 app_comm_cons in HP.
    assert (HP' := PCPermutation_Type_trans _ _ _ _ HP (PCPermutation_Type_app_comm _ _ _)).
    specialize IHHll with (rev (x2 :: x1 :: l'') ++ rev l1) lo C.
    list_simpl in IHHll. list_simpl in HP'. apply IHHll in HP'; [ | | assumption ].
    * destruct HP' as [IH1 IH2].
      split.
      -- apply tens_ilr; assumption.
      -- intros Hnil l2.
         assert (IH := IH2 Hnil l2).
         list_simpl in IH. list_simpl. apply tens_ilr. assumption.
    * inversion Hoclm as [ | ? ? ? HF ]; constructor; try assumption.
      assert (Hl := Forall_inf_app_l _ _ HF).
      assert (Hr := Forall_inf_app_r _ _ HF).
      apply Forall_inf_app; [ assumption | ].
      inversion Hr as [ | ? ? Hr' ].
      inversion Hr'.
      constructor; [ | constructor ]; assumption.
- symmetry in HP. apply PCPermutation_Type_vs_cons_inv in HP as [(l', l'') HP Heq].
  destruct l'; inversion Heq; [ destruct C; inversion H0 | ]; subst.
  + split; intros; apply top_irr.
  + symmetry in H1. dichot_elt_app_inf_exec H1; subst;
      [ decomp_map H0 eqn:Hx
      | list_simpl in H2; decomp_map H2 eqn:Hx; decomp_map H2 ];
      destruct x; destr_eq Hx; subst.
    * exfalso.
      apply Forall_inf_app_r in Hocl. inversion Hocl as [ | ? ?  Hocl' ]. inversion Hocl'.
    * apply (f_equal (@rev _)) in H2. list_simpl in H2. subst.
      split; intros; list_simpl; apply zero_ilr.
- symmetry in HP. apply PCPermutation_Type_vs_cons_inv in HP as [([|], l'') HP Heq];
    inversion Heq; [ destruct C; inversion H0 | ]; subst.
  + apply (PEPermutation_Type_cons _ (eq_refl (ill2ll C1))) in HP.
    apply PEPermutation_PCPermutation_Type in HP. unfold id in HP. rewrite app_comm_cons in HP.
    assert (HP' := PCPermutation_Type_trans _ _ _ _ HP (PCPermutation_Type_app_comm _ _ _)).
    specialize IHHll with l0 lo C1.
    list_simpl in IHHll. list_simpl in HP'. apply IHHll in HP'; [ | | assumption ].
    * destruct HP' as [IH1 IH2].
      split.
      -- apply plus_irr1. assumption.
      -- intros Hnil l2.
         assert (IH := IH2 Hnil l2).
         list_simpl in IH. list_simpl. apply plus_irr1. assumption.
    * inversion_clear Hoclm as [ | ? ? Hoclm' ].
      inversion_clear Hoclm'.
      constructor; assumption.
  + symmetry in H1. dichot_elt_app_inf_exec H1; subst;
      [ decomp_map H0 eqn:Hx
      | list_simpl in H2; decomp_map H2 eqn:Hx; decomp_map H2 ];
      destruct x; destr_eq Hx; subst.
    * apply (PEPermutation_Type_cons _ (eq_refl (ill2ll x1))) in HP.
      apply PEPermutation_PCPermutation_Type in HP. unfold id in HP. rewrite app_comm_cons in HP.
      assert (HP' := PCPermutation_Type_trans _ _ _ _ HP (PCPermutation_Type_app_comm _ _ _)).
      specialize IHHll with l0 (l1 ++ x1 :: l2) C.
      list_simpl in IHHll. list_simpl in HP'. apply IHHll in HP'; try assumption.
      -- destruct HP' as [IH1 IH2].
         split; [ assumption | intros _ ? ].
         apply IH2.
         intro Hnil. nil_vs_elt_inv Hnil.
      -- assert (Hocll := Forall_inf_app_l _ _ Hocl).
         assert (Hoclr := Forall_inf_app_r _ _ Hocl).
         apply Forall_inf_app; [ assumption | ].
         inversion Hoclr as [ | ? ? Hocl'].
         inversion Hocl'.
         constructor; assumption.
    * apply (f_equal (@rev _)) in H2. list_simpl in H2. subst.
      apply (PEPermutation_Type_cons _ (eq_refl (dual (ill2ll x1)))) in HP.
      apply PEPermutation_PCPermutation_Type in HP. unfold id in HP. rewrite app_comm_cons in HP.
      assert (HP' := PCPermutation_Type_trans _ _ _ _ HP (PCPermutation_Type_app_comm _ _ _)).
      specialize IHHll with (rev (x1 :: l'') ++ rev l2) lo C.
      list_simpl in IHHll. list_simpl in HP'. apply IHHll in HP'; [ | | assumption ].
      -- destruct HP' as [IH1 IH2]. split.
         ++ apply with_ilr1. assumption.
         ++ intros Hnil l'. list_simpl.
            assert (IH := IH2 Hnil l'). list_simpl in IH.
            apply with_ilr1. assumption.
      -- inversion_clear Hoclm as [ | ? ? ? HF ]; constructor; try assumption.
         assert (Hl := Forall_inf_app_l _ _ HF).
         assert (Hr := Forall_inf_app_r _ _ HF).
         apply Forall_inf_app; [ assumption | ].
         inversion Hr as [ | ? ? Hr' ]. inversion Hr'.
         constructor; assumption.
- symmetry in HP; apply PCPermutation_Type_vs_cons_inv in HP as [(l', l'') HP Heq].
  destruct l'; inversion Heq; [ destruct C; inversion H0 | ]; subst.
  + apply (PEPermutation_Type_cons _ (eq_refl (ill2ll C2))) in HP.
    apply PEPermutation_PCPermutation_Type in HP. unfold id in HP. rewrite app_comm_cons in HP.
    assert (HP' := PCPermutation_Type_trans _ _ _ _ HP (PCPermutation_Type_app_comm _ _ _)).
    specialize IHHll with l0 lo C2.
    list_simpl in IHHll. list_simpl in HP'. apply IHHll in HP'; try assumption.
    * destruct HP' as [IH1 IH2]. split.
      -- apply plus_irr2. assumption.
      -- intros Hnil l2. list_simpl.
         assert (IH := IH2 Hnil l2). list_simpl in IH.
         apply plus_irr2. assumption.
    * inversion_clear Hoclm as [ | ? ? Hoclm' ]. inversion_clear Hoclm'.
      constructor; assumption.
  + symmetry in H1. dichot_elt_app_inf_exec H1; subst;
      [ decomp_map H0 eqn:Hx
      | list_simpl in H2; decomp_map H2 eqn:Hx; decomp_map H2 ];
      destruct x; destr_eq Hx; subst.
    * apply (PEPermutation_Type_cons _ (eq_refl (ill2ll x2))) in HP.
      apply PEPermutation_PCPermutation_Type in HP. unfold id in HP. rewrite app_comm_cons in HP.
      assert (HP' := PCPermutation_Type_trans _ _ _ _ HP (PCPermutation_Type_app_comm _ _ _)).
      specialize IHHll with l0 (l' ++ x2 :: l1) C.
      list_simpl in IHHll. list_simpl in HP'. apply IHHll in HP'; [ | assumption | ].
      -- destruct HP' as [IH1 IH2].
         split; [ assumption | intros _ ? ].
         apply IH2.
         intro Hnil. nil_vs_elt_inv Hnil.
      -- assert (Hocll := Forall_inf_app_l _ _ Hocl).
         assert (Hoclr := Forall_inf_app_r _ _ Hocl).
         apply Forall_inf_app; [ assumption | ].
         inversion Hoclr as [ | ? ?  Hoclr' ]. inversion Hoclr'.
         constructor; assumption.
    * apply (f_equal (@rev _)) in H2. list_simpl in H2. subst.
      apply (PEPermutation_Type_cons _ (eq_refl (dual (ill2ll x2)))) in HP.
      apply PEPermutation_PCPermutation_Type in HP. unfold id in HP. rewrite app_comm_cons in HP.
      assert (HP' := PCPermutation_Type_trans _ _ _ _ HP (PCPermutation_Type_app_comm _ _ _)).
      specialize IHHll with (rev (x2 :: l'') ++ rev l1) lo C.
      list_simpl in IHHll. list_simpl in HP'. apply IHHll in HP'; [ | | assumption ].
      -- destruct HP' as [IH1 IH2]. split.
         ++ apply with_ilr2. assumption.
         ++ intros Hnil l2. list_simpl.
            assert (IH := IH2 Hnil l2). list_simpl in IH.
            apply with_ilr2. assumption.
      -- inversion_clear Hoclm as [ | ? ? ? HF ]; constructor; try assumption.
         assert (Hl := Forall_inf_app_l _ _ HF).
         assert (Hr := Forall_inf_app_r _ _ HF).
         apply Forall_inf_app; [ assumption | ].
         inversion Hr as [ | ? ? Hr' ]. inversion Hr'.
         constructor; assumption.
- symmetry in HP; apply PCPermutation_Type_vs_cons_inv in HP as [(l', l'') HP Heq].
  destruct l'; inversion Heq; [ destruct C; inversion H0 | ]; subst.
  + assert (HP1 := HP).
    apply (PEPermutation_Type_cons _ (eq_refl (ill2ll C1))) in HP1.
    apply PEPermutation_PCPermutation_Type in HP1. unfold id in HP1. rewrite app_comm_cons in HP1.
    assert (HP1' := PCPermutation_Type_trans _ _ _ _ HP1 (PCPermutation_Type_app_comm _ _ _)).
    specialize IHHll1 with l0 lo C1.
    list_simpl in IHHll1. list_simpl in HP1'. apply IHHll1 in HP1'; [ | |  assumption ].
    * destruct HP1' as [IH1 IH2].
      apply (PEPermutation_Type_cons _ (eq_refl (ill2ll C2))) in HP.
      apply PEPermutation_PCPermutation_Type in HP. unfold id in HP. rewrite app_comm_cons in HP.
      assert (HP2' := PCPermutation_Type_trans _ _ _ _ HP (PCPermutation_Type_app_comm _ _ _)).
      specialize IHHll2 with l0 lo C2.
      list_simpl in IHHll2. list_simpl in HP2'. apply IHHll2 in HP2'; [ | | assumption ].
      -- destruct HP2' as [IH3 IH4]. split.
         ++ apply with_irr; assumption.
         ++ intros Hnil l2. list_simpl.
            assert (IH := IH2 Hnil l2). list_simpl in IH.
            assert (IH' := IH4 Hnil l2). list_simpl in IH'.
            apply with_irr; assumption.
      -- inversion_clear Hoclm as [ | ? ? Hoclm' ]. inversion_clear Hoclm'.
         constructor; assumption.
    * inversion_clear Hoclm as [ | ? ? Hoclm' ]. inversion_clear Hoclm'.
      constructor; assumption.
  + symmetry in H1. dichot_elt_app_inf_exec H1; subst;
      [ decomp_map H0 eqn:Hx
      | list_simpl in H2; decomp_map H2 eqn:Hx; decomp_map H2 ];
      destruct x; destr_eq Hx; subst.
    * assert (Hocll := Forall_inf_app_l _ _ Hocl).
      assert (Hoclr := Forall_inf_app_r _ _ Hocl).
      inversion Hoclr as [ | ? ? Hoclr' ].
      inversion Hoclr'.
      -- apply (PEPermutation_Type_cons _ (eq_refl (ill2ll x1))) in HP.
         apply PEPermutation_PCPermutation_Type in HP. unfold id in HP. rewrite app_comm_cons in HP.
         assert (HP' := PCPermutation_Type_trans _ _ _ _ HP (PCPermutation_Type_app_comm _ _ _)).
         specialize IHHll1 with l0 (l' ++ x1 :: l1) C.
         list_simpl in IHHll1. list_simpl in HP'. apply IHHll1 in HP'; try assumption.
         ++ destruct HP' as [IH1 IH2].
            split; [ assumption | intros _ ? ].
            apply IH2.
            intro Hnil. nil_vs_elt_inv Hnil.
         ++ apply Forall_inf_app; [ | constructor ]; assumption.
      -- apply (PEPermutation_Type_cons _ (eq_refl (ill2ll x2))) in HP.
         apply PEPermutation_PCPermutation_Type in HP. unfold id in HP. rewrite app_comm_cons in HP.
         assert (HP' := PCPermutation_Type_trans _ _ _ _ HP (PCPermutation_Type_app_comm _ _ _)).
         specialize IHHll2 with l0 (l' ++ x2 :: l1) C.
         list_simpl in IHHll2. list_simpl in HP'. apply IHHll2 in HP'; [ | assumption | ].
         ++ destruct HP' as [IH1 IH2].
            split; [ assumption | ].
            intros _ ?.
            apply IH2.
            intros Hnil. destruct l'; discriminate Hnil.
         ++ apply Forall_inf_app; [ | constructor ]; assumption.
    * apply (f_equal (@rev _)) in H2. list_simpl in H2. subst.
      assert (HP1 := HP).
      apply (PEPermutation_Type_cons _ (eq_refl (dual (ill2ll x1)))) in HP1.
      apply PEPermutation_PCPermutation_Type in HP1. unfold id in HP1. rewrite app_comm_cons in HP1.
      assert (HP1' := PCPermutation_Type_trans _ _ _ _ HP1 (PCPermutation_Type_app_comm _ _ _)).
      specialize IHHll1 with (rev (x1 :: l'') ++ rev l1) lo C.
      list_simpl in IHHll1. list_simpl in HP1'. apply IHHll1 in HP1'; [ | | assumption ].
      -- destruct HP1' as [IH1 IH2].
         apply (PEPermutation_Type_cons _ (eq_refl (dual (ill2ll x2)))) in HP.
         apply PEPermutation_PCPermutation_Type in HP. unfold id in HP. rewrite app_comm_cons in HP.
         assert (HP2' := PCPermutation_Type_trans _ _ _ _ HP (PCPermutation_Type_app_comm _ _ _)).
         specialize IHHll2 with (rev (x2 :: l'') ++ rev l1) lo C.
         list_simpl in IHHll2. list_simpl in HP2'. apply IHHll2 in HP2'; [ | | assumption ].
         ++ destruct HP2' as [IH3 IH4]. split.
            ** apply plus_ilr; assumption.
            ** intros Hnil l2. list_simpl.
               assert (IH5 := IH2 Hnil l2). list_simpl in IH5.
               assert (IH6 := IH4 Hnil l2). list_simpl in IH6.
               apply plus_ilr; assumption.
         ++ inversion Hoclm as [ | ? ? ? HF]; constructor; [ assumption | ].
            assert (Hl := Forall_inf_app_l _ _ HF).
            assert (Hr := Forall_inf_app_r _ _ HF).
            apply Forall_inf_app; [ assumption | ].
            inversion Hr as [ | ? ? Hr' ]. inversion Hr'.
            constructor; assumption.
      -- inversion Hoclm as [ | ? ? ? HF ]; constructor; [ assumption | ].
         assert (Hl := Forall_inf_app_l _ _ HF).
         assert (Hr := Forall_inf_app_r _ _ HF).
         apply Forall_inf_app; [ assumption | ].
         inversion Hr as [ | ? ? Hr' ]. inversion Hr'.
         constructor; assumption.
- symmetry in HP. apply PCPermutation_Type_vs_cons_inv in HP as [(l', l'') HP Heq].
  destruct l'; inversion Heq; [ destruct C; inversion H0 | ]; subst.
  + symmetry in HP. apply PEPermutation_Type_map_inv in HP as [l'' Heq' HPE]. list_simpl in Heq'.
    decomp_map Heq' eqn:HH. destruct HH as [Heq1 Heq2].
    destruct lo, l1; inversion Heq1; subst.
    * split.
      -- list_simpl in Heq2.
         apply ill2ll_map_ioc_inv in Heq2 as [l2' Heq' Heq'']. subst.
         apply (f_equal (@rev _)) in Heq'. list_simpl in Heq'. subst.
         apply (IHHll ((rev (map ioc l2'))) nil C) in Hocl.
         ++ list_simpl in Hocl. destruct Hocl as [Hocl _].
            apply oc_irr. assumption.
         ++ inversion_clear Hoclm as [ | ? ? Hoclm' ]. inversion_clear Hoclm'.
            list_simpl. constructor; assumption.
         ++ etransitivity.
            ** apply PEPermutation_PCPermutation_Type.
               list_simpl in HPE. apply (PEPermutation_Type_map _ wn) in HPE.
               apply PEPermutation_Type_cons; [reflexivity | eassumption].
            ** list_simpl. rewrite ill2ll_map_ioc. reflexivity.
      -- intros Hnil. contradiction Hnil. reflexivity.
    * exfalso. destruct i; discriminate H1.
  + exfalso.
    symmetry in H1. dichot_elt_app_inf_exec H1; subst;
      [ decomp_map H0 eqn:Hx
      | list_simpl in H2; decomp_map H2 eqn:Hx; decomp_map H2 ];
      destruct x; destr_eq Hx; subst.
    symmetry in HP. apply PEPermutation_Type_map_inv in HP as [l'' Heq' _].
    decomp_map Heq' eqn:HH. destruct HH as [_ [HH _]].
    destruct C; discriminate HH.
- symmetry in HP. apply PCPermutation_Type_vs_cons_inv in HP as [(l', l'') HP Heq].
  destruct l'; inversion Heq; [ destruct C; inversion H0 | ]. subst.
  symmetry in H1. dichot_elt_app_inf_exec H1; subst;
    [ decomp_map H0 eqn:Hx
    | list_simpl in H2; decomp_map H2 eqn:Hx; decomp_map H2 ];
    destruct x; destr_eq Hx; cbn in Hx, H2; subst.
  apply (f_equal (@rev _)) in H2. list_simpl in H2. subst.
  apply (PEPermutation_Type_cons _ (eq_refl (dual (ill2ll x)))) in HP.
  apply PEPermutation_PCPermutation_Type in HP. unfold id in HP. rewrite app_comm_cons in HP.
  assert (HP' := PCPermutation_Type_trans _ _ _ _ HP (PCPermutation_Type_app_comm _ _ _)).
  specialize IHHll with (rev (x :: l'') ++ rev l1) lo C.
  list_simpl in IHHll. list_simpl in HP'. apply IHHll in HP'; [ | | assumption ].
  + destruct HP' as [IH1 IH2]. split.
    * apply de_ilr. assumption.
    * intros Hnil l2.
      assert (IH := IH2 Hnil l2).
      list_simpl in IH. list_simpl. apply de_ilr. assumption.
  + inversion Hoclm as [ | ? ? ? HF ]. constructor; [ assumption | ].
    assert (Hl := Forall_inf_app_l _ _ HF).
    assert (Hr := Forall_inf_app_r _ _ HF).
    apply Forall_inf_app; [ assumption | ].
    inversion Hr as [ | ? ? Hr' ]. inversion Hr'.
    constructor; assumption.
- symmetry in HP. apply PCPermutation_Type_vs_cons_inv in HP as [(l', l'') HP Heq].
  destruct l'; inversion Heq; [ destruct C; inversion H0 | ]. subst.
  symmetry in H1. dichot_elt_app_inf_exec H1; subst;
    [ decomp_map H0 eqn:Hx
    | list_simpl in H2; decomp_map H2 eqn:Hx; decomp_map H2 ];
    destruct x; destr_eq Hx; cbn in Hx; cbn in H2; subst.
  apply (f_equal (@rev _)) in H2. list_simpl in H2. subst.
  apply PEPermutation_PCPermutation_Type in HP. unfold id in HP. rewrite app_comm_cons in HP.
  assert (HP' := PCPermutation_Type_trans _ _ _ _ HP (PCPermutation_Type_app_comm _ _ _)).
  specialize IHHll with (rev l'' ++ rev l1) lo C.
  list_simpl in IHHll. list_simpl in HP'. apply IHHll in HP'; [ | | assumption ].
  + destruct HP' as [IH1 IH2]. split.
    * apply wk_ilr. assumption.
    * intros Hnil l2.
      assert (IH := IH2 Hnil l2).
      list_simpl in IH. list_simpl. apply wk_ilr. assumption.
  + inversion Hoclm as [ | ? ? ? HF ]. constructor; [ assumption | ].
    assert (Hl := Forall_inf_app_l _ _ HF).
    assert (Hr := Forall_inf_app_r _ _ HF).
    apply Forall_inf_app; [ assumption | ].
    inversion Hr. assumption.
- symmetry in HP. apply PCPermutation_Type_vs_cons_inv in HP as [([|], l'') HP Heq];
   inversion Heq; [ destruct C; inversion H0 | ]; subst.
  symmetry in H1. dichot_elt_app_inf_exec H1; subst;
    [ decomp_map H0 eqn:Hx
    | list_simpl in H2; decomp_map H2 eqn:Hx; decomp_map H2 ];
    destruct x; destr_eq Hx; cbn in Hx; cbn in H2; subst.
  apply (f_equal (@rev _)) in H2. list_simpl in H2. subst.
  assert (PCPermutation_Type (ipperm P) (wn (dual (ill2ll x)) :: wn (dual (ill2ll x)) :: l)
         (ill2ll C :: map ill2ll lo
          ++ map dual (map ill2ll (l2 ++ ioc x :: ioc x :: l'')))) as HP'.
  { apply (PEPermutation_Type_cons _ (eq_refl (wn (dual (ill2ll x))))) in HP.
    apply (PEPermutation_Type_cons _ (eq_refl (wn (dual (ill2ll x))))) in HP.
    apply PEPermutation_PCPermutation_Type in HP. unfold id in HP. cbn in HP.
    etransitivity; [ apply HP | ].
    list_simpl. rewrite ? app_comm_cons.
    etransitivity; [ apply PCPermutation_Type_app_comm | list_simpl; reflexivity ]. }
  specialize IHHll with (rev (ioc x :: ioc x :: l'') ++ rev l2) lo C.
  list_simpl in IHHll. list_simpl in HP'. apply IHHll in HP'; [ | | assumption ].
  + destruct HP' as [IH1 IH2].
    split.
    * eapply ex_ir; [ apply co_ilr | ].
      -- rewrite app_nil_l.
         eapply ex_ir; [ apply IH1 | ].
         rewrite P_perm. cbn. symmetry. apply Permutation_Type_cons_app, Permutation_Type_middle.
      -- rewrite P_perm. cbn. apply Permutation_Type_middle.
    * intros Hnil l3.
      assert (IH := IH2 Hnil l3).
      list_simpl in IH.
      eapply ex_ir; [ apply co_ilr | ].
      -- rewrite app_nil_l. eapply ex_ir; [ apply IH | ].
         rewrite P_perm. cbn. symmetry. apply Permutation_Type_cons_app, Permutation_Type_middle.
      -- rewrite P_perm. cbn. rewrite app_comm_cons, app_assoc.
         apply Permutation_Type_app_tail, Permutation_Type_middle.
  + inversion Hoclm as [ | ? ? ? HF ]. constructor; [ assumption | ].
    assert (Hl := Forall_inf_app_l _ _ HF).
    assert (Hr := Forall_inf_app_r _ _ HF).
    apply Forall_inf_app; [ assumption | ].
    inversion Hr. constructor; assumption.
- exfalso. clear - f P_cut. cbn in f.
  destruct (ill2ll_inv A) as [[l ?] _ _].
  apply existsb_exists in f as [B [Hin Hcut]].
  rewrite P_cut in Hcut. discriminate Hcut.
- destruct lo.
  + apply (snd (fst (Hgax a))) in HP.
    split; [ assumption | ].
    intros Hnil. contradiction Hnil. reflexivity.
  + exfalso.
    inversion_clear Hocl as [ | ? ? ? HF ].
    cbn in HP. rewrite <- (app_nil_l (ill2ll i :: _)), app_comm_cons in HP.
    apply PCPermutation_Type_vs_elt_inv in HP as [(l1,l2) _ Heq].
    destruct l1; inversion Heq as [[Heq' Heq'']].
    * symmetry in Heq'. apply (snd (fst (fst (Hgax a))) i); assumption.
    * apply (f_equal (@rev _)) in Heq''.
      rewrite rev_involutive in Heq''. list_simpl in Heq''. rewrite map_map in Heq''.
      decomp_map Heq'' eqn:HH. destruct HH as [Heq1 [Heq2 Heq3]].
      apply (fst (fst (fst (Hgax a))) i); [ | assumption ].
      apply (f_equal dual) in Heq2. rewrite bidual in Heq2.
      rewrite Heq''. list_simpl. rewrite Heq2. apply in_inf_elt.
Qed.

Lemma ll_to_ill_oclpam_axfree P (P_perm : ipperm P = true) (P_axfree : no_iax P) l C :
  Forall_inf oclpam (C :: l) -> ll (i2pfrag P) (ill2ll C :: rev (map dual (map ill2ll l))) -> ill P l C.
Proof.
intros Hoclm pi.
apply cut_admissible_axfree in pi; [ | assumption ].
apply (stronger_pfrag _ _ (cutrm_i2pfrag P)) in pi.
eapply ll_to_ill_oclpam_cutfree in pi; [ | eassumption | | | eassumption | | ].
- apply (stronger_ipfrag (cutrm_ipfrag_le P)), pi.
- apply noicut_cutrm.
- intro. contradiction P_axfree.
- apply Forall_inf_nil.
- reflexivity.
Qed.

End Conservativity_Atoms.
