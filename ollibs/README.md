# OLlibs
Add-ons for the Coq Standard Library

Working with `Coq 8.12.0`

## Extensions of Standard Library

* `List_more`       : add-ons for standard library List
* `funtheory`       : properties of functions
* `dectype`         : types with decidable/Boolean equality (using records rather than modules)
* `infinite`        : infinite types
* `BOrders`         : `Orders` with output in `bool`
* `ComparisonOrder` : order structure on `comparison`
* `List_assoc`      : some operations on association lists
* `AFC`             : finite versions of the axiom of choice
* `nattree`         : nat-labelled trees and coding into nat
* `wf_prod`         : well-founded order on product (application to `nat`)

## Around Finite Multisets

* `fmsetlist`               : finite multisets with Coq equality
* `fmsetoidlist`            : finite multisets as setoid
* `fmsetlist_Type`          : `fmsetlist` with output in `Type`
* `fmsetoidlist_Type`       : `fmsetoidlist` with output in `Type`

## Around Permutations

* `Permutation_more`        : add-ons for standard library Permutation
* `CPermutation_more`       : add-ons for standard library CPermutation
* `GPermutation`            : factorized common properties of
    * permutation and cyclic permutation
    * permutation and equality
* `transp_perm`             : transpositions
* `Permutation_Type`        : `Permutation` with output in `Type`
* `Permutation_Type_more`   : `Permutation_more` with output in `Type`
* `CPermutation_Type`       : `CyclicPerm` with output in `Type`
* `GPermutation_Type`       : `genperm` with output in `Type`
* `PermutationPropify`      : turn `Permutation_Type` into `Permutation` for types with decidable equality
* `Permutation_solve`  : automatic tactic for permutation goals
* `CPermutation_solve` : automatic tactic for cyclic permutation goals
* `Permutation_Type_solve`  : `Permutation_solve` with output in `Type`
* `CPermutation_Type_solve` : `CPermutation_solve` with output in `Type`

## Misc

* `flat_map_more`           : decomposition properties for `flat_map`
* `Dependent_Forall_Type`   : generalization of `Forall_Type` to dependent product

