# Record 1930: sparse source support instantiated in the finite-basis selector

Date: 2026-09-24

## Result

The abstract finite-dimensional minimum-coefficient selector is now attached to
the actual sparse source support.  For a sparse correction `c`, its finite
support `c.support` is used as the coefficient index type, and the existing
`windowedFiniteMellinVector` family is used as the finite source basis.

`exists_min_norm_on_sparse_source_support` proves:

- every attainable finite Mellin target has a coefficient vector in
  `EuclideanSpace Complex c.support`;
- the vector is represented by the original sparse correction on its support;
- among all coefficient vectors producing the same finite target, the selected
  vector has minimum Euclidean coefficient norm.

The proof is an actual instantiation: the original evaluation equation is
rewritten as the finite sum over `c.support`, then transported to the subtype
sum used by the Euclidean finite-dimensional theorem.  It does not add a
positivity or residual-sign premise.

## Verification

The owning module and its audit module build successfully in focused build
`20260924_sparse_min_selector19.log` (3663 jobs).  The audited declaration has
only the standard Lean axioms `[propext, Classical.choice, Quot.sound]` and no
`sorryAx`.

## Independent grouped-residual sign

This record does not claim the strict grouped-residual margin.  The selector
only minimizes coefficient norm, while the residual is an actual signed
physical-kernel pairing.  The existing derivative transport supplies an upper
bound, not a lower bound or a sign.  The exact remaining obligation is still a
strict owner-specific inequality for the grouped finite aggregate.  Treating
the minimum-norm property as that inequality would be a logical gap.

Status: sparse-support instantiation FORMAL; strict grouped-residual margin
OPEN.
