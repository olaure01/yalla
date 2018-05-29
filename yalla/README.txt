The files have to be compiled with Coq version 8.7.1
Simply use: make


Links from the paper "Around Classical and Intuitionistic Linear Logics":


Lemma 2.1 (i)  = nn.v / Lemma neg_tens_propag
          (ii) = nn.v / Lemma neg_plus_propag

Definition 2.2 = nn.v / Fixpoint trans

Lemme 2.3 = nn.v / Lemma trans_dual

Proposition 2.4 = nn.v / Theorem ll_to_ill_trans

Lemma 2.5 (n=0,n=2) = nn.v / Theorem ll_to_ill_trans

Lemma 2.6 = ll_fragments.v / Lemma subs_llR

Lemma 2.7 (=>) = ll_fragments.v / Lemma llR_to_ll
          (<=) = ll_fragments.v / Lemma ll_wn_wn_to_llR

Lemma 2.8 (=>) = ll_fragments.v / Lemma llwnR_to_ll
          (<=) = ll_fragments.v / Lemma ll_wn_to_llwnR

Lemma 2.9 = nn.v / Lemma back_to_llR

Proposition 2.10 = nn.v / Lemma ill_trans_to_llR

Lemma 2.11 (i)  = nn.v / Lemma ie_dual
           (ii) = nn.v / Lemma ie_ie

Proposition 2.12 (<=) = nn.v / Proposition llR_ie_to_ill_trans

Lemma 2.13 = nn.v / Lemma ll_mix02_to_ill_trans_gen

Proposition 2.14 (i) => (ii)   = nn.v / Theorem ll_mix02_to_ill_trans
                 (ii) => (iii) = nn.v / Lemma ill_trans_to_llR_one
                 (iii) => (i)  = nn.v / Theorem llR_one_to_ll_mix02

Proposition 2.16 (i) => (ii) = nn.v / Theorem ll_ll_to_ill_trans
                 (ii) => (v) = nn.v / Theorem ill_trans_to_llR_bot
                 (v) => (i)  = nn.v / Theorem llR_bot_to_ll

Lemma 2.18 = ill.v / Lemma wn_not_idefin

Lemma 2.19 = ill.v / Lemma bot_not_idefin

Lemma 2.20 = ill.v / Lemma wn_one_not_idefin

Proposition 2.21 (i) => (ii)  = nn.v / Theorem ll_mix0_to_ill_trans
                 (ii) => (v)  = nn.v / Theorem ill_trans_to_llR_wn_one
                 (v) => (i)   = nn.v / Theorem llR_wn_one_to_ll_mix0
                 (i) <=> (vi) = ll_fragments.v / Lemma mix0_wn_one

Lemma 2.22 (included in ill.v / Lemma oc_bot_not_idefin)

Lemma 2.23 = ill.v / Lemma oc_bot_not_idefin

Lemma 2.24 = bbb.v / Lemma bbb_to_mix02

Proposition 2.25 = bbb.v / Lemma cut_bbb_r

Proposition 2.26 (i) => (ii) = nn.v / Theorem ll_bbb_to_ill_trans
                 (ii) => (v) = nn.v / Theorem ill_trans_to_llR_oc_bot
                 (v) => (i)  = bbb.v / Theorem bb_to_bbb

Proposition 2.27 (n=2) (i) => (vi) = ll_fragments.v / Lemma mix2_to_ll
                 (n=2) (vi) => (i) = ll_fragments.v / Lemma ll_to_mix2
                 (v) => (vi) = ll_fragments.v / Lemma llwnR_to_ll
                 (vi) => (v) = ll_fragments.v / Lemma ll_wn_to_llwnR

Proposition 2.28 (i) => (v) = ll_fragments.v / Lemma mix02_to_ll
                 (v) => (i) = ll_fragments.v / Lemma ll_to_mix02





Lemma 3.2 = ill.v / Theorem ll_to_ill_oclmap_cutfree

Theorem 3.3 (=>) = ill.v / Proposition ll_to_ill_oclmap_axfree

Definition 3.5 = ill.v / Inductive zeropos

Lemma 3.6 (Z |- 0) = ill.v / Lemma zeropos_ilr

Definition 3.7 = ill.v / Inductive nonzerospos

Lemma 3.8 = ill.v / Lemma dual_jfragment_zeropos

Theorem 3.9 (=>) = ill.v / Theorem ll_to_ill_nzeropos_cutfree

Theorem 3.11 = tl.v / Theorem ll_is_tl_axfree





Lemma 4.1 = nnfoc.v / Lemma pntrans_dual

Lemma 4.2 = nnfoc.v / Lemma ntrans_to_trans

Theorem 4.3 = nnfoc.v / Proposition ll_to_tl

Lemma 4.4 (Pi empty) = nnfoc.v / Lemma tl_to_otl

Theorem 4.5 = nnfoc.v / Theorem otl_to_llfoc

Corollary 4.6 = nnfoc.v / Theorem weak_focusing





Lemma 5.1 (partial) = nn.v / Lemma trans_subs

