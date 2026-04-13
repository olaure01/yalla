# YALLA: an LL library for Rocq

## Version 2.1.0

This major revision introduces modifications in definitions leading to possible incompatibilities with versions 2.0.*:

* generalized mix rules
    (no real impact if mix rules are not used except that the `mix0` and `mix2` rules are replaced by a single rule);
* output of `atomic` is now in `Type` (only requires simple updates if `atomic` is used);
* results are now parameterized over atom sets (this increases the number of implicit parameters of objects);
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

[OLlibs](https://github.com/olaure01/ollibs) v2.1 is now required as an external dependency.

*Tested with Rocq v9.2.*

## Version 2.0.7 (2025/03/26)

This is mostly an adaptation of v2.0 to Rocq v9.0 and OLlibs v2.0.7.

*Tested with Rocq v9.0-9.2.*

## Version 2.0.6 (2024/09/16)

This is mostly an adaptation of v2.0 to Coq v8.20 and OLlibs v2.0.7.

*Tested with Coq v8.20.*

## Version 2.0.5 (2024/09/15)

This is mostly an adaptation of v2.0 to Coq v8.19 and OLlibs v2.0.6.

*Tested with Coq v8.19.*

## Version 2.0.4 (2023/04/09)

This is mostly an adaptation of v2.0 to Coq v8.17.0 and OLlibs v2.0.4.

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

