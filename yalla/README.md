# YALLA: an LL library for Coq

## Yet Another deep embedding of Linear Logic in Coq



*If you have any trouble, question or request for extension, if you need help to write interfaces,
please contact:  `Olivier.Laurent@ens-lyon.fr`*


This library defines notions of proofs for various fragments of linear logic.
It provides some general results such as cut admissibility.

The formalisation is based on sequents as lists together with an explicit exchange rule.
This allows us to provide a study of proofs which is compatible with the computational interpretation of proofs.

Parameters in the definition of proofs allow the user:

* to include some `mix` rules or not;
* to define arbitrary axioms
     (which allows in particular to work with open proofs);
* to use the usual exchange rule (arbitrary permutations)
   or to restrict to cyclic linear logic (cyclic permutations only).

This library is probably not so appropriate to build LL proofs by hands, but is more dedicated to the study of meta-properties of linear logic fragments.

Because of the parameters, the proof predicates defined in the library should not be used directly.
We recommend the user to define his own objects (inductive types for formulas and proofs) and to interface them with the library in order to then import the results of the library in his lighter setting (examples of such interfaces are provided in the files mell2.v and lambek.v).
It is possible to hide the explicit exchange rule by introducing multisets for sequents (see mell_mset.v).



Main files:

* formulas.v:
    definition of (classical) linear logic formulas
* fmformulas.v:
    additional structure on formulas (order, multiset)
* ll_def.v:
    main definitions for classical linear logic (LL)
    and properties not requiring cut admissibility
* subs.v:
    susbtitution for LL
* ll_cut_at.v:
    cut admissibility for atomic cut formulas in LL
* ll_cut.v:
    cut admissibility properties for LL
* ll_prop.v:
    properties of LL relying on cut admissibility
* ll_fragments.v:
    definitions of some common fragments of LL
* iformulas.v:
    definition of intuitionistic linear logic formulas
* fmiformulas.v:
    additional structure on intuitionistic formulas (order, multiset)
* ill_def.v:
    main defintions for intuitionistic linear logic (ILL)
    (Lambek calculus included when permutation is equality:
       ipperm P = false)
* isubs.v:
    susbtitution for ILL
* ill_cut.v:
    cut admissibility properties for ILL
* ill_prop.v:
    properties of ILL relying on cut admissibility
* ill_vs_ll.v:
    relations between ILL and LL
* nn_def.v:
    main properties of double-negation translations from LL to ILL
* nn_prop.v:
    properties of double-negation translations from LL to ILL
    related to expressiveness analysis
* llfoc.v:
    definitions of focused systems
    and proof of strong focusing from weak focusing
* nn_foc.v:
    double-negation-based proof of weak focusing

Example files for interfaces:

* mell2.v:
    unit-free MELL with mix2
* mell_Prop.v:
    unit-free MELL with proofs in Prop (i.e. provability only)
* lambek.v:
    a variant of Lambek calculus
* mell_mset.v:
    multiset-based MELL (no exchange rule)
* mell_msetoid.v:
    setoid multiset-based MELL
* llpol.v:
    polarized fragment of LL
* tl.v:
    tensor logic
* ll_smp.v:
    interface for the standard version of LL
* ill_smp.v:
    interface for the standard version of ILL

Other files:

* bbb.v:
    study of LL extended with the equation: bot = oc bot
* yalla_ax.v:
    specific instances of axioms on atoms used in the library
    (this guarantees consistency of this set of axioms)
* basic_misc.v:
    basic definitions and tactics

The precise file dependencies are pictured in the [dependency graph](dependencies.png).

