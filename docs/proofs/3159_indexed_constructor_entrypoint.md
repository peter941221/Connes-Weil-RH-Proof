# 3159: indexed CCM25 constructor entrypoint

Date: 2026-10-28.

Status: Lean-verified API migration step. This record does not claim SourceRH
or RH.

## Change

`SourceWeilFormData.toIndexedCCM25SourceArithmeticConstructorInput` now maps a
source Weil-form model plus
`FixedLambdaIndexedArithmeticSourceTestCertificatesForAllTests` into the
indexed CCM25 constructor boundary.

The constructor preserves the existing global, restricted, and pole rows and
stores finite-prime arithmetic only through the indexed certificate family.
`IndexedCCM25SourceArithmeticConstructorInput.finite_prime_normalization`
readbacks the finite-prime normalization statement through
`ConcreteCCM25IndexedArithmeticRows`.

## Boundary

This is an API entrypoint, not a producer. It still requires the indexed
certificates as an explicit input. It does not cast or derive them from the
inconsistent legacy root.

```text
SourceWeilFormData
        + indexed certificates
        -> IndexedCCM25SourceArithmeticConstructorInput
        -> indexed CCM25 rows
        -> CCM25SourceModel
```

## Verification

```text
lake env lean ConnesWeilRH/Source/CCM25TheoremBase.lean
lake build ConnesWeilRH.Route.RouteTheorem
```