# YALLA: an LL library for Coq

## Yet Another deep embedding of Linear Logic in Coq



If you have any trouble, question or request for extension, if you need help to write interfaces,
please contact:  `Olivier.Laurent@ens-lyon.fr`


This library defines notions of proofs for various fragments of linear logic.
It provides some general results such as cut admissibility.

The formalisation is based on sequents as lists together with an explicit exchange rule.
This allows us to provide a study of proofs which is compatible with the computational interpretation of proofs.

Parameters in the definition of proofs allow the user:

* to include the `mix0` rule or not;
* to include the `mix2` rule or not;
* to define arbitrary axioms
     (which allows in particular to work with open proofs);
* to use the usual exchange rule (arbitrary permutations)
   or to restrict to cyclic linear logic (cyclic permutations only).

This library is probably not so appropriate to build LL proofs by hands, but is more dedicated to the study of meta-properties of linear logic fragments.

Because of the parameters, the proof predicates defined in the library should not be used directly.
We recommend the user to define his own objects (inductive types for formulas and proofs) and to interface them with the library in order to then import the results of the library in his lighter setting (examples of such interfaces are provided in the files mell2.v and lambek.v).
It is possible to hide the explicit exchange rule by introducing multisets for sequents (see mell_mset.v).



Main files:

* formulas.v(o):
    definition of (classical) linear logic formulas
* fmformulas.v(o):
    additional structure on formulas (order, multiset)
* ll_def.v(o):
    main definitions for classical linear logic (LL)
    and properties not requiring cut admissibility
* subs.v(o):
    susbtitution for LL
* ll_cut.v(o):
    cut admissibility properties for LL
* ll_prop.v(o):
    properties of LL relying on cut admissibility
* ll_fragments.v(o):
    definitions of some common fragments of LL
* iformulas.v(o):
    definition of intuitionistic linear logic formulas
* fmiformulas.v(o):
    additional structure on intuitionistic formulas (order, multiset)
* ill_def.v(o):
    main defintions for intuitionistic linear logic (ILL)
    (Lambek calculus included when permutation is equality:
       ipperm P = false)
* isubs.v(o):
    susbtitution for ILL
* ill_cut.v(o):
    cut admissibility properties for ILL
* ill_prop.v(o):
    properties of ILL relying on cut admissibility
* ill_vs_ll.v(o):
    relations between ILL and LL
* nn_def.v(o):
    main properties of double-negation translations from LL to ILL
* nn_prop.v(o):
    properties of double-negation translations from LL to ILL
    related to expressiveness analysis
* llfoc.v(o):
    definitions of focused systems
    and proof of strong focusing from weak focusing
* nn_foc.v(o):
    double-negation-based proof of weak focusing

Example files for interfaces:

* mell2.v(o):
    unit-free MELL with mix2
* mell_Prop.v(o):
    unit-free MELL with proofs in Prop (i.e. provability only)
* lambek.v(o):
    a variant of Lambek calculus
* mell_mset.v(o):
    multiset-based MELL (no exchange rule)
* mell_msetoid.v(o):
    setoid multiset-based MELL
* llpol.v(o):
    polarized fragment of LL
* tl.v(o):
    tensor logic
* ll_smp.v(o):
    interface with the microyalla self-contained version of LL
* ill_smp.v(o):
    interface with the microyalla self-contained version of ILL

Other files:

* bbb.v(o):
    study of LL extended with the equation: bot = oc bot
* yalla_ax.v(o):
    specific instances of axioms on atoms used in the library
    (this guarantees consistency of this set of axioms)

The precise file dependencies are pictured in the [dependency graph](dependencies.png).

