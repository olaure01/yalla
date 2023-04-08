# YALLA: an LL library for Coq

## Version 2.x

Modifications in definitions leading to possible incompatibilities with version 2.0.*:

* generalized mix rules
    (no real impact if mix rules are not used except that the `mix0` and `mix2` rules are replaced by a single rule);
* output of `atomic` is now in `Type` (only requires simple updates if `atomic` is used);
* results are now parametrized over atom sets (this increases the number of implicit parameters of objects);
* introduction of `Forall_sequent` to deal with properties of sequents inside proofs rather than `ll_ps` (and similarly for the other systems);
* parameter `pcut` for cut-rules is now of type `formula -> bool`.

New results added, including:

* results about the generalized `mix` rule;
* consistency properties;
* additional counter-examples to conservativity of `ill` over `ll`;
* simplified definition of `micro_ll` and new `nano_ll`;
* decidability of equality on formulas;
* Girard's translations of intuitionistic logic;
* more on focusing (Andreoli's triadic system).

*Tested with Coq v8.17.0.*

## Version 2.0.3 (2022/02/06)

This is mostly an adaptation of v2.0 to Coq v8.15.0 and OLlibs v2.0.2.

*Tested with Coq v8.15.0.*

## Version 2.0.2 (2021/01/13)

This is mostly an adaptation of v2.0 to Coq v8.13.0 and OLlibs v2.0.1.

*Tested with Coq v8.13.0.*

## Version 2.0.1 (2020/08/07)

This is mostly an adaptation of v2.0 to Coq v8.12.0 and OLlibs v2.0.0.

*Tested with Coq v8.12.0.*

## Version 2.0 (2019/01/23)

This major revision is based on a representation of proofs in `Type` rather than `Prop`.
For this reason it is *not compatible with v1.0*.

Many results have been added, including:

* general cut admissibility proof for Intuitionistic Linear Logic;
* more general conservativity results for Classical Linear Logic over Intuitionistic Linear Logic;
* theory of focusing;
* example files for additional related systems;
* definition of the microyalla kernel.

*Tested with Coq v8.9.0.*

## Version 1.0 (2017/07/18)

First public release.

