From Yalla Require Import List_more Permutation_Type_more CPermutation_Type GPermutation_Type ll_def.
Import ListNotations.

Section CyclicExchange.

Definition exc := forall P l1 l2, ll P l1 -> CPermutation_Type l1 l2 -> ll P l2.
Definition excl := forall P A l, ll P (l ++ [A]) -> ll P (A :: l).
Definition excr := forall P A l, ll P (A :: l) -> ll P (l ++ [A]).

Lemma exc_excl : exc -> excl.
Proof.
intros exc_r P A l pi.
eapply exc_r; [ eassumption | ].
symmetry. apply CPermutation_Type_cons_append.
Qed.

Lemma exc_excr : exc -> excr.
Proof.
intros exc_r P A l pi.
eapply exc_r; [ eassumption | ].
apply CPermutation_Type_cons_append.
Qed.

Lemma excl_exc : excl -> exc.
Proof.
intros exl_r P l1 l2 pi HC. destruct HC.
induction l2 as [ | A l2 IH ] in l1, pi |- *.
- list_simpl in pi. assumption.
- list_simpl. apply exl_r.
  rewrite <- app_assoc. apply IH.
  list_simpl. assumption.
Qed.

Lemma excr_exc : excr -> exc.
Proof.
intros exr_r P l1 l2 pi HC. destruct HC.
induction l1 as [ | A l1 IH ] in l2, pi |- *.
- list_simpl. assumption.
- change (l2 ++ A :: l1) with (l2 ++ [A] ++ l1).
  rewrite app_assoc. apply IH.
  rewrite app_assoc. apply exr_r. assumption.
Qed.

End CyclicExchange.


Section Exchange.

Definition ex := forall P l1 l2, ll P l1 -> Permutation_Type l1 l2 -> ll P l2.
Definition ext := forall P A B l1 l2, ll P (l1 ++ A :: B :: l2) -> ll P (l1 ++ B :: A :: l2).
Definition extl := forall P A B l, ll P (A :: B :: l) -> ll P (B :: A :: l).

Lemma ex_ext : ex -> ext.
Proof.
intros ex_fr P A B l1 l2 pi.
apply (ex_fr _ _ _ pi).
apply Permutation_Type_app_head, Permutation_Type_swap.
Qed.

Lemma ext_extl : ext -> extl.
Proof. intros ext_r P A B l pi. apply (ext_r _ _ _ nil _ pi). Qed.

Lemma extl_ex : extl -> ex.
Proof.
intros extl_r P l1 l2 pi HP%perm_perm_t_Type.
induction HP as [ | | ? ? ? ? IH1 ? IH2 ].
- assumption.
- eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  cbn. apply extl_r. rewrite 2 app_comm_cons.
  eapply ex_r; [ | apply PCPermutation_Type_app_comm ].
  assumption.
- apply IH2, IH1, pi.
Qed.

End Exchange.
