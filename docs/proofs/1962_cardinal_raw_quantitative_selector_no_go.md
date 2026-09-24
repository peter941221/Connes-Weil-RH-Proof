# Proof Record 1962: cardinalRaw quantitative selector no-go

## Audit result

The live explicit correction uses

```text
cardinalRaw nodes seed z
  = product over t in nodes.erase z of derivativeShift(_, t)
    applied to exponentialWeight(seed, -z)
```

The correction L1 envelope from Record 1961 therefore requires quantitative
bounds for the L1 mass of this iterated derivative object.

The Mathlib `ContDiffBump` interface currently used by the committed seed
contains only:

```text
rIn, rOut, 0 < rIn, rIn < rOut
```

Its generated function exposes smoothness, support, nonnegativity, and the
unit plateau, but no explicit bound for `deriv`, higher derivatives, or their
L1 masses. The repository's `baseBump` is a noncomputable instance of this
interface, so its derivative profile is not available as an exact numerical
certificate.

## Consequence

The current explicit finite-node correction can prove interpolation and support
preservation, but it cannot yet produce the quantitative `cardinalRaw` mass /
node-product budget required by Map 106. A generic existence theorem for a
finite derivative bound is insufficient for the signed determinant target: the
bound must be connected to an explicit margin and actual owner data.

This is a scoped no-go for the current selector-plus-`ContDiffBump` API, not a
no-go for all possible selectors.

## Minimal ways forward

1. Introduce a concrete analytic seed with explicit derivative and L1 bounds,
   then rebuild the correction around that seed.
2. Extend the selector contract with certified seminorm fields for every
   derivative order needed by the finite node set, and prove the correction
   budget from those fields.
3. Replace high-order differential shifts by a quantitative interpolation
   basis whose L1 norms are directly certified.

Option 1 has the smallest proof surface if the concrete seed can retain the
existing support and nonvanishing Laplace requirements. Option 2 preserves the
current owner but requires a new public selector contract. Option 3 changes the
construction more substantially.

## Status

No determinant sign, producer witness, or RH conclusion follows from the
current API. Map 106 remains OPEN at the actual signed-moment and tail budget
stage.