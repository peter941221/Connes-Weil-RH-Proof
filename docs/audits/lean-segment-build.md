# Lean Segment Build Plan

Status: active build strategy.

The Connes-Weil route is built as a separate lightweight Lake target:

```text
ConnesWeilRH
```

Use this target for current work:

```text
lake build ConnesWeilRH
```

Verified result on the WSL ext4 mirror `~/projects/Connes-Weil-RH-Proof`:

```text
lake build ConnesWeilRH
Build completed successfully.
elapsed: about 56 seconds
```

Latest verified result:

```text
lake build ConnesWeilRH
Build completed successfully (2909 jobs).
elapsed: about 49 seconds
```

This build verified the CC20 finite-vanishing exit refactor. The final route now
consumes `inputs.cc20.finiteVanishingRhExit`, a field of
`ConnesWeilRH.Source.CC20Interface`, instead of a route-local RH exit field.

Latest CC20 trace-interface verification:

```text
lake build ConnesWeilRH.Source.CC20
Build completed successfully (2899 jobs).
elapsed: about 51 seconds

lake build ConnesWeilRH.Route.RouteTheorem
Build completed successfully (2907 jobs).
elapsed: about 10 seconds

lake build ConnesWeilRH
Build completed successfully (2909 jobs).
elapsed: about 3 seconds
```

This build verified the replacement of CC20 trace, trace-class, Mellin, and sign
`statement := True` placeholders with statements over
`ConnesWeilRH.ArchimedeanTraceSymbols`.

Latest CCM24 semilocal-interface verification:

```text
lake build ConnesWeilRH.Source.CCM24
Build completed successfully (2899 jobs).
elapsed: about 55 seconds

lake build ConnesWeilRH.Route.RouteTheorem
Build completed successfully (2907 jobs).
elapsed: about 48 seconds

lake build ConnesWeilRH
Build completed successfully (2909 jobs).
elapsed: about 3 seconds
```

This build verified the replacement of CCM24 `statement := True` placeholders
with statements over `ConnesWeilRH.SemilocalModelSymbols`. A scan of
`ConnesWeilRH/Source` found no remaining `statement := True`.

Latest route-bridge verification:

```text
lake build ConnesWeilRH.Basic
Build completed successfully (2898 jobs).
elapsed: about 52 seconds

lake build ConnesWeilRH.Route.Definitions
Build completed successfully (2902 jobs).
elapsed: about 4 seconds

lake build ConnesWeilRH.Route.AdmissibleWindow
Build completed successfully (2903 jobs).
elapsed: about 3 seconds

lake build ConnesWeilRH.Route.RouteTheorem
Build completed successfully (2907 jobs).
elapsed: about 9 seconds

lake build ConnesWeilRH
Build completed successfully (2909 jobs).
elapsed: about 3 seconds
```

This build verified that `RouteCertificate` consumes
`ConnesWeilRH.Route.SourceBackedFixedSTest` and derives
`AdmissibleForTheorem1` through
`ConnesWeilRH.Route.admissible_for_theorem1_of_source_backed`.
It also verified the CCM25 finite-prime bridge:
`finite_prime_visibility_statement_of_source_backed` derives
`WeilFormSymbols.FinitePrimeVisibilityStatement` from
`inputs.ccm25.finitePrimeNormalization`, and
`finite_primes_visible_of_source_backed` applies the route bridge to obtain
`test.finitePrimesVisible`.

Latest full-positivity bridge verification:

```text
lake build ConnesWeilRH.Route.Exhaustion
Build completed successfully (2906 jobs).
elapsed: about 46 seconds

lake build ConnesWeilRH.Route.RouteTheorem
Build completed successfully (2907 jobs).
elapsed: about 3 seconds

lake build ConnesWeilRH
Build completed successfully (2909 jobs).
elapsed: about 3 seconds
```

This build verified that `RouteCertificate` consumes
`ConnesWeilRH.Route.SourceBackedFullPositivity`. The final route theorem now
gets `FullWeilPositivity` through
`ConnesWeilRH.Route.full_weil_positivity_of_source_backed`, which uses the CC20
trace-class and trace-square contracts plus the CCM25 Weil-form read-off bridge.

Latest ledger-bridge verification:

```text
lake build ConnesWeilRH.Route.Ledger
Build completed successfully (2904 jobs).
elapsed: about 50 seconds

lake build ConnesWeilRH.Route.Exhaustion
Build completed successfully (2906 jobs).
elapsed: about 54 seconds

lake build ConnesWeilRH.Route.RouteTheorem
Build completed successfully (2907 jobs).
elapsed: about 3 seconds

lake build ConnesWeilRH
Build completed successfully (2909 jobs).
elapsed: about 3 seconds
```

This build verified that `SourceBackedFullPositivity` consumes
`ConnesWeilRH.Route.SourceBackedLedgers`, and that `LedgersCleared` is obtained
through `ConnesWeilRH.Route.ledgers_cleared_of_source_backed`.

Latest triple-vanishing bridge verification:

```text
lake build ConnesWeilRH.Basic
Build completed successfully (2898 jobs).
elapsed: about 47 seconds

lake build ConnesWeilRH.Route.Definitions
Build completed successfully (2902 jobs).
elapsed: about 52 seconds

lake build ConnesWeilRH.Route.AdmissibleWindow
Build completed successfully (2903 jobs).
elapsed: about 5 seconds

lake build ConnesWeilRH.Route.Exhaustion
Build completed successfully (2906 jobs).
elapsed: about 5 seconds

lake build ConnesWeilRH.Route.RouteTheorem
Build completed successfully (2907 jobs).
elapsed: about 5 seconds

lake build ConnesWeilRH
Build completed successfully (2909 jobs).
elapsed: about 3 seconds
```

This build verified the explicit triple-vanishing bridge through
`ConnesWeilRH.CriticalVanishingPoint`,
`ConnesWeilRH.TripleVanishingSymbols`, and
`ConnesWeilRH.Route.triple_vanishing_of_source_backed`.

Latest trace-read-off split verification:

```text
lake build ConnesWeilRH.Route.Theorem1
Build completed successfully (2905 jobs).
elapsed: about 45 seconds

lake build ConnesWeilRH.Route.Exhaustion
Build completed successfully (2906 jobs).
elapsed: about 3 seconds

lake build ConnesWeilRH.Route.RouteTheorem
Build completed successfully (2907 jobs).
elapsed: about 3 seconds

lake build ConnesWeilRH
Build completed successfully (2909 jobs).
elapsed: about 3 seconds
```

This build verified `ConnesWeilRH.Route.SourceTraceReadOffData` and the updated
`fixed_s_read_off_of_source_backed_full_positivity` path.

Latest fixed-S trace output hardening:

```text
lake build ConnesWeilRH.Route.Theorem1
Build completed successfully (2905 jobs).
elapsed: about 49 seconds

lake build ConnesWeilRH.Route.Exhaustion
Build completed successfully (2906 jobs).
elapsed: about 29 seconds

lake build ConnesWeilRH.Route.RouteTheorem
Build completed successfully (2907 jobs).
elapsed: about 1 second

lake build ConnesWeilRH
Build completed successfully (2909 jobs).
elapsed: about 1 second

#print axioms ConnesWeilRH.Route.final_connes_weil_rh
[propext, Classical.choice, Quot.sound]
```

This build verified that `FixedSPositiveTraceReadOff` is no longer definitionally
equal to `AdmissibleForTheorem1`. The theorem now produces an existential
package containing trace legality, no-defect source read-off, Weil
identification, and positive-trace nonnegativity evidence.

Latest CC20 trace-gate ownership verification:

```text
lake build ConnesWeilRH.Route.Theorem1
Build completed successfully (2905 jobs).
elapsed: about 37 seconds

lake build ConnesWeilRH.Route.Exhaustion
Build completed successfully (2906 jobs).
elapsed: about 1 second

lake build ConnesWeilRH.Route.RouteTheorem
Build completed successfully (2907 jobs).
elapsed: about 1 second

lake build ConnesWeilRH
Build completed successfully (2909 jobs).
elapsed: about 1 second

#print axioms ConnesWeilRH.Route.final_connes_weil_rh
[propext, Classical.choice, Quot.sound]
```

This build verified that `SourceTraceReadOffData` owns the CC20 archimedean
test object and Hilbert-Schmidt gate. The trace legality and trace-square
read-off are derived inside the Theorem 1 segment from the CC20 interface,
rather than being supplied by `SourceBackedFullPositivity`.

Latest CCM25 read-off hardening:

```text
lake build ConnesWeilRH.Route.Theorem1
Build completed successfully (2905 jobs).
elapsed: about 32 seconds

lake build ConnesWeilRH.Route.Exhaustion
Build completed successfully (2906 jobs).
elapsed: about 1 second

lake build ConnesWeilRH.Route.RouteTheorem
Build completed successfully (2907 jobs).
elapsed: about 1 second

lake build ConnesWeilRH
Build completed successfully (2909 jobs).
elapsed: about 1 second

#print axioms ConnesWeilRH.Route.final_connes_weil_rh
[propext, Classical.choice, Quot.sound]
```

This build verified `ConnesWeilRH.Route.CCM25WeilFormReadOff`. The route no
longer carries a loose `weilFormReadOff : Prop` field or a free read-off bridge
on `SourceBackedFullPositivity`.

Latest trace-Weil compatibility split:

```text
lake build ConnesWeilRH.Route.Theorem1
Build completed successfully (2905 jobs).
elapsed: about 31 seconds

lake build ConnesWeilRH.Route.Exhaustion
Build completed successfully (2906 jobs).
elapsed: about 1 second

lake build ConnesWeilRH.Route.RouteTheorem
Build completed successfully (2907 jobs).
elapsed: about 1 second

lake build ConnesWeilRH
Build completed successfully (2909 jobs).
elapsed: about 1 second

#print axioms ConnesWeilRH.Route.final_connes_weil_rh
[propext, Classical.choice, Quot.sound]
```

This build verified `ConnesWeilRH.Route.TraceWeilCompatibility` and the split
from trace-Weil compatibility to final Weil identification.

Latest lambda/window compatibility binding:

```text
lake build ConnesWeilRH.Basic
Build completed successfully (2898 jobs).
elapsed: about 32 seconds

lake build ConnesWeilRH.Route.Definitions
Build completed successfully (2902 jobs).
elapsed: about 1 second

lake build ConnesWeilRH.Route.AdmissibleWindow
Build completed successfully (2903 jobs).
elapsed: about 1 second

lake build ConnesWeilRH.Route.Theorem1
Build completed successfully (2905 jobs).
elapsed: about 33 seconds

lake build ConnesWeilRH.Route.Exhaustion
Build completed successfully (2906 jobs).
elapsed: about 1 second

lake build ConnesWeilRH.Route.RouteTheorem
Build completed successfully (2907 jobs).
elapsed: about 1 second

lake build ConnesWeilRH
Build completed successfully (2909 jobs).
elapsed: about 1 second

#print axioms ConnesWeilRH.Route.final_connes_weil_rh
[propext, Classical.choice, Quot.sound]
```

This build verified `ConnesWeilRH.Route.WindowLambdaCompatibility` and
`ConnesWeilRH.Route.lambda_compatible_of_source_backed`. The restricted
parameter `lambda` in `CCM25WeilFormReadOff` now carries both `1 < lambda` and
CCM24 window compatibility.

Latest trace-Weil read-off equality hardening:

```text
lake build ConnesWeilRH.Route.Theorem1
Build completed successfully (2905 jobs).
elapsed: about 33 seconds

lake build ConnesWeilRH.Route.Exhaustion
Build completed successfully (2906 jobs).
elapsed: about 1 second

lake build ConnesWeilRH.Route.RouteTheorem
Build completed successfully (2907 jobs).
elapsed: about 1 second

lake build ConnesWeilRH
Build completed successfully (2909 jobs).
elapsed: about 1 second

#print axioms ConnesWeilRH.Route.final_connes_weil_rh
[propext, Classical.choice, Quot.sound]
```

This build verified that `TraceWeilCompatibility` carries the named
`fullTraceReadOff` and `restrictedTraceReadOff` equalities before final Weil
identification.

Latest source-backed read-off equality bridge:

```text
lake build ConnesWeilRH.Route.Theorem1
Build completed successfully (2905 jobs).
elapsed: about 33 seconds

lake build ConnesWeilRH.Route.Exhaustion
Build completed successfully (2906 jobs).
elapsed: about 1 second

lake build ConnesWeilRH.Route.RouteTheorem
Build completed successfully (2907 jobs).
elapsed: about 1 second

lake build ConnesWeilRH
Build completed successfully (2909 jobs).
elapsed: about 1 second

#print axioms ConnesWeilRH.Route.final_connes_weil_rh
[propext, Classical.choice, Quot.sound]
```

This build verified that `SourceTraceReadOffData` derives the named read-off
equalities through `FullTraceReadOffSource` and `RestrictedTraceReadOffSource`
bridges instead of accepting direct equality proof fields.

Latest direct-leg read-off bridge tightening:

```text
lake build ConnesWeilRH.Route.Theorem1
Build completed successfully (2905 jobs).
elapsed: about 37 seconds

lake build ConnesWeilRH.Route.Exhaustion
Build completed successfully (2906 jobs).
elapsed: about 1 second

lake build ConnesWeilRH.Route.RouteTheorem
Build completed successfully (2907 jobs).
elapsed: about 1 second

lake build ConnesWeilRH
Build completed successfully (2909 jobs).
elapsed: about 1 second

#print axioms ConnesWeilRH.Route.final_connes_weil_rh
[propext, Classical.choice, Quot.sound]
```

This build verified that `fullTraceReadOffBridge` consumes
`CC20NoDefectSourceReadOff`, and `restrictedTraceReadOffBridge` consumes
`CCM25WeilFormReadOff`. The route no longer carries arbitrary source Prop fields
for those two read-off legs.

Latest read-off equality factoring:

```text
lake build ConnesWeilRH.Route.Theorem1
Build completed successfully (2905 jobs).
elapsed: about 31 seconds

lake build ConnesWeilRH.Route.Exhaustion
Build completed successfully (2906 jobs).
elapsed: about 1 second

lake build ConnesWeilRH.Route.RouteTheorem
Build completed successfully (2907 jobs).
elapsed: about 1 second

lake build ConnesWeilRH
Build completed successfully (2909 jobs).
elapsed: about 1 second

#print axioms ConnesWeilRH.Route.final_connes_weil_rh
[propext, Classical.choice, Quot.sound]
```

This build verified `FullTraceReadOffEquality` and
`RestrictedTraceReadOffEquality`, separating the equality targets from the
source-leg bundles.

Latest CCM25 full/restricted read-off split:

```text
lake build ConnesWeilRH.Route.Theorem1
Build completed successfully (2905 jobs).
elapsed: about 37 seconds

lake build ConnesWeilRH.Route.Exhaustion
Build completed successfully (2906 jobs).
elapsed: about 1 second

lake build ConnesWeilRH.Route.RouteTheorem
Build completed successfully (2907 jobs).
elapsed: about 1 second

lake build ConnesWeilRH
Build completed successfully (2909 jobs).
elapsed: about 1 second

#print axioms ConnesWeilRH.Route.final_connes_weil_rh
[propext, Classical.choice, Quot.sound]
```

This build verified `CCM25FullQWReadOff` and `CCM25RestrictedQWReadOff`. The
full leg is derived from `inputs.ccm25.qwDefinition`; the restricted leg is
derived from `inputs.ccm25.qwLambdaFormula` and
`inputs.ccm25.poleNormalization`.

Latest CCM25 sub-leg and window-containment verification:

```text
lake build ConnesWeilRH.Basic
Build completed successfully (2898 jobs).
elapsed: about 31 seconds

lake build ConnesWeilRH.Route.Definitions
Build completed successfully (2902 jobs).
elapsed: about 1 second

lake build ConnesWeilRH.Route.AdmissibleWindow
Build completed successfully (2903 jobs).
elapsed: about 1 second

lake build ConnesWeilRH.Route.Theorem1
Build completed successfully (2905 jobs).
elapsed: about 1 second

lake build ConnesWeilRH.Route.Exhaustion
Build completed successfully (2906 jobs).
elapsed: about 1 second

lake build ConnesWeilRH.Route.RouteTheorem
Build completed successfully (2907 jobs).
elapsed: about 1 second

lake build ConnesWeilRH
Build completed successfully (2909 jobs).

#print axioms ConnesWeilRH.Route.final_connes_weil_rh
[propext, Classical.choice, Quot.sound]
```

This build verified the finer CCM25 split:
`CCM25FullQWReadOff` now contains `CCM25QWDefinitionReadOff` and
`CCM25PsiSignReadOff`, while `CCM25RestrictedQWReadOff` contains
`WindowLambdaCompatibility`, `CCM25QWLambdaFormulaReadOff`, and
`CCM25PoleNormalizationReadOff`.

It also verified `WindowSupportContainment`. The restricted `lambda` leg now
exposes support in the CCM24 window, Fourier support in the same window,
convolution-support transport, and `windowContainedInLambda window lambda`
before deriving `lambdaCompatible window lambda`.

Latest CCM25 finite-prime index-set verification:

```text
lake build ConnesWeilRH.Basic
Build completed successfully (2898 jobs).

lake build ConnesWeilRH.Source.CCM25
Build completed successfully (2899 jobs).

lake build ConnesWeilRH.Route.Theorem1
Build completed successfully (2905 jobs).
elapsed: about 31 seconds

lake build ConnesWeilRH.Route.Exhaustion
Build completed successfully (2906 jobs).

lake build ConnesWeilRH.Route.RouteTheorem
Build completed successfully (2907 jobs).

lake build ConnesWeilRH
Build completed successfully (2909 jobs).

#print axioms ConnesWeilRH.Route.final_connes_weil_rh
[propext, Classical.choice, Quot.sound]
```

This build verified that the CCM25 symbolic formulas no longer use
`Finset.range 0` as an empty finite-prime placeholder. The full formula is
indexed by `WeilFormSymbols.globalPrimeIndexSet`, and the restricted formula is
indexed by `WeilFormSymbols.restrictedPrimeIndexSet lambda`.

## Segment Order

```text
ConnesWeilRH.Basic
  |
  v
ConnesWeilRH.Source.CCM24
ConnesWeilRH.Source.CCM25
ConnesWeilRH.Source.CC20
  |
  v
ConnesWeilRH.Route.Definitions
  |
  v
ConnesWeilRH.Route.AdmissibleWindow
  |
  v
ConnesWeilRH.Route.Ledger
  |
  v
ConnesWeilRH.Route.Theorem1
  |
  v
ConnesWeilRH.Route.Exhaustion
  |
  v
ConnesWeilRH.Route.RouteTheorem
```

Each segment should build before moving to the next one.

For edit loops, use the smallest segment that contains the changed interface:

| changed area | first build target |
|---|---|
| final RH target, common source-obligation records, symbolic formula records | `lake build ConnesWeilRH.Basic` |
| source-paper interface declarations | `lake build ConnesWeilRH.Source.CCM24`, `CCM25`, or `CC20` |
| bundled route objects and admissibility predicates | `lake build ConnesWeilRH.Route.Definitions` or `AdmissibleWindow` |
| ledger and fixed-S theorem interface | `lake build ConnesWeilRH.Route.Ledger` or `Theorem1` |
| full positivity bridge | `lake build ConnesWeilRH.Route.Exhaustion` |
| final composition into Mathlib RH | `lake build ConnesWeilRH.Route.RouteTheorem` |

Run `lake build ConnesWeilRH` after the smallest target passes.

## Axiom Audit Rule

The current route skeleton should not introduce project axioms. Check the final
theorem with:

```text
#print axioms ConnesWeilRH.Route.final_connes_weil_rh
```

Verified output:

```text
'ConnesWeilRH.Route.final_connes_weil_rh' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

No project-local axiom appears in the current route skeleton.
