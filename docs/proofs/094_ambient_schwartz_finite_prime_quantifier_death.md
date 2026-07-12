# 094 Ambient Schwartz Broad Finite-Prime Quantifier Death

Date: 2026-07-12

## Exact interface evidence

`SourceFinitePrimeExactSupportData` in
`ConnesWeilRH/Source/AnalyticCore.lean` requires a global carrier

```text
globalPrimeIndexCarrier : { carrier : Finset ℕ //
  ∀ F : A.Test, ∀ n, n ∈ carrier -> sourceFinitePrimeTerm n F ≠ 0 }
```

and a converse field saying every nonzero source term lies in that same finite
carrier. The quantifier ranges over all `F : A.Test`, not only compact-support
witnesses or tests inside one fixed window.

## Conflict with the ambient escape

The proposed owner sets `A.Test = TestFunction = SchwartzMap ℝ ℂ`. For genuine
prime translations/evaluations, a general Schwartz test is not compactly
supported and can have nonzero values at arbitrarily many prime-power
coordinates. Therefore no single finite `Finset ℕ` can be exact for all ambient
Schwartz tests.

The existing finite-support data survives only because the current toy source
terms are artificially zero outside a finite model. Reusing that data with the
genuine convolution changes the arithmetic object; defining genuine prime
terms makes the universal finite-support field false.

## Scope correction

This verdict applies to the broad `SourceWeilFormData`/
`SourceFinitePrimeData` core interface only. The route-facing
`ConcreteCCM25ArithmeticPackage W f lambda` is indexed by one fixed common
test at the outer level, but its internal `rows` field still requires the
universal `ForAllTests` certificate. Proof 095 records that hidden quantifier;
the package rescue in Plan 027 is therefore killed as well. Only the direct
fixed-detector consumer in Plan 028 remains open.

## Decision

```text
ambient Schwartz convolution probe: passes
ambient SourceTestAlgebra type: passes
ambient genuine finite-prime package: rejected by quantifier shape
Plan 026 broad source-core replacement: dead
Plan 027 per-detector arithmetic package: dead (proof 095)
Plan 028 direct fixed-detector certificate: open
```

Reopening the broad core requires finite support indexed by a compact-support /
cutoff witness and a separately proved tail. The existing per-detector package
must bypass the package rows entirely; see Plan 028.
