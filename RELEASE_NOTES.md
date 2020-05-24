# YALLA: an LL library for Coq

## v 2.x

Modifications in definitions leading to possible incompatibilities with version 2.0:

* generalized mix rules
    (no real impact if mix rules are not used except that the `mix0` and `mix2` rules are replaced by a single rule)
* output of `atomic` is now in `Type` (only requires simple updates if `atomic` is used, it is also possible to use the previous version under the name `atomic_Prop`)
* results are now parametrized over atom sets (this increases the number of implicit parameters of objects)

New results added, including:

* results about the generalized `mix` rule
* consistency properties
* additional counter-examples to conservativity of `ill` over `ll`
* simplified definition of `micro_ll` and new `nano_ll`
* decidability of equality on formulas
* Girard's translations into intuitionistic logic

Tested with Coq version 8.12.0.

## v 2.0 (2019/01/23)

This major revision is based on a representation of proofs in `Type` rather than `Prop`.
For this reason it is *not compatible with version 1.0*.

Many results have been added, including:

* general cut admissibility proof for Intuitionistic Linear Logic
* more general conservativity results for Classical Linear Logic over Intuitionistic Linear Logic
* theory of focusing
* example files for additional related systems
* definition of the microyalla kernel

Tested with Coq version 8.9.0.

## v 1.0 (2017/07/18)

First public release.

