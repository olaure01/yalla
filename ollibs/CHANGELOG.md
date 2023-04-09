# Versions 2.0.x

## Version 2.0.4

* rename `fresh_prop` into `fresh_spec`
* correct arguments in tactic `case_analysis`
* turn some `_ -> False` into `notT _`
* add `PCPermutation_Type_app_flat_map`, `injective_neq` and `section_coimage_option`
* add results on `filter` and `partition`
* add automatic tactics `in_solve` and `Forall_inf_cbn_hyp` for lists
* create `Datatypes_more.v`
    * add `iffT`, `prod_map` and `prod_map2`
* create `Bool_more.v`
    * add `reflectT` and associated results
	* add `reflect_neg`, `Forall_forallb_reflect` and some results from `ssr.ssrbool`
* integrate material for dealing with [Issue #12394](https://github.com/coq/coq/issues/12394) in file `issue12394.v`
* adapt to Coq v8.17.0
    * clean uses of tactic `intuition`
    * remove `Forall2_length` (integrated in the standard library in [PR #15986](https://github.com/coq/coq/pull/15986))

## Version 2.0.3

* `arrow`
    * do not export `Program.Basics` in `funtheory` anymore
    * rely on `Classes.CRelationClasses.arrow` rather than `Program.Basics.arrow` for `Proper` instances in `Type`
* turn `#[global]` instances into `#[export]` ones
* rename `wf_prod.v` into `Wf_nat_more.v`
    * use the non-dependent product order from Coq stdlib (introduced in [PR #14809](https://github.com/coq/coq/pull/14809))
* create separated file `inhabited_Type.v`
* add `option_test`, `Permutation_vs_elt_subst`, `decidable_image` (and associated properties), `in_inf_prod_inv` and `eqb_sym`
* simplify `cpair_surj` hypothesis in `nattree.v`
* adapt to Coq v8.16
    * setoid_rewriting is more powerful (not backward compatible)

## Version 2.0.2

* add function constructions for `Empty_set` and `option` in `funtheory`
* adapt to Coq v8.14 and v8.15
    * add locality attributes to `Instance` commands

## Version 2.0.1

* proof scripts more robust with respect to automatically generated names
* slightly more powerful `unit_vs_elt_inv` tactic
* adapt to Coq v8.13.0
    * remove statements about `repeat` (moved into Coq stdlib: [PR #12799](https://github.com/coq/coq/pull/12799))
    * add locality attributes to `Hint` commands

## Version 2.0.0

First Opam-released version.

It coincides with incorporation of part of previous content into the standard library of Coq v8.12.0.
