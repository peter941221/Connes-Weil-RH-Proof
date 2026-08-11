# 981 — R1 Step3-upstream: CC20 archimedean symbols on CompactLog, non-L^2 obligations closed

Status: execution record.  RH NOT claimed.

## Goal
`SourceRouteTraceData`/`CC20Interface` needs an `ArchimedeanTraceSymbols` on the
route carrier.  R1 Step2 (980) proved the operator gate is uniform over
`CompactLogTest`.  This step upgrades that to a full `ArchimedeanTraceSymbols` on
the CompactLog carrier and proves the five CC20 archimedean obligations except the
arithmetic one.

## Result — axiom-clean
`Dev/R1Step3Probe981.lean` (build 3210 jobs green, `#print axioms` =
`[propext, Classical.choice, Quot.sound]`, 0 sorry):

- `R1ArchimedeanSymbols : ArchimedeanTraceSymbols` with
  `Test := CompactLogTest`, `positiveTrace := (Re arch)^2`,
  `hilbertSchmidtGate := IsSelfAdjoint (windowedDetector g 1 1) ∧ ∃global basis`.
- `R1_posTrace_nonneg` : `0 ≤ positiveTrace g` for all g (square).
- `R1_posTrace_strict_pos_bump` : `positiveTrace bumpPlateauTest > 0` STRICT (Wall-A).
- `R1_cc20_trace_square` : `support = noDefect ∧ 0 ≤ positive`.
- `R1_cc20_oid_trace_support_square` : `positive = support` (r to def).
- `R1_cc20_trace_class_template` : `gate → traceClass ∧ cyclicLegal`.
- `R1_cc20_mellin_` / `_signs_normalizations` : the `True` conventions.

## The key design decision: positiveTrace = (Re arch)^2
`TraceSquareStatement` is `∀ g, ... 0 ≤ positiveTrace g` for ALL tests.  Plain
`positiveTrace := Re(arch g)` is NOT universally nonnegative (only at the bump is it
> 0).  By using the SQUARE, `0 ≤` holds for every g while strict `> 0` holds at the
bump — and it's exactly the `positiveTrace = traceAmplitude²` convention the
`AnalyticCore.SourceTraceScaleData` already uses (AnalyticCore:8167-8175). So this
is not ad-hoc: it matches the repo's own trace-scale semantics.

## Honest scope
- The `ccm25ArithmeticPackage` (L2 arithmetic) is NOT here. It is the genuine
  arithmetic bottom (memory 916: L653) separate from this archimedean-interface step.
- `mellinHalfDensityMatched`/`uInfinityNormalized`/`qduNormalized` are the `True`
  conventions the route's own arch symbols use (no arithmetic at this layer).
- This works at `ArchimedeanTraceSymbols` level directly (as 979 did) — it does NOT
  build a `SourceTestAlgebra` on `CompactLogTest` (which would need the `LegacyTestEquiv`
  `decode : TestFunction → CompactLogTest`, requiring compact support from any Schwartz
  function — not always true).

## Lean gotchas
- `ArchimedeanTraceSymbols` fields via `simp [R1ArchimedeanSymbols]` (not `unfold`'s
  `rfl`) because structure projections don't always see the abbrev.
- `sq_nonneg`/`sq_pos_of_ne_zero` for square positivity; `ne_of_gt` to get the base
  nonzero.

## Next
R1 Step3-core: build `RouteInputs`/`CC20Interface` on `R1ArchimedeanSymbols`,
`testAndQuotientCompatibility`, `fixedSSupportSquareTransport` — then the ONLY
genuine arithmetic opening is `ccm25ArithmeticPackage` = L2/L653. That is the
frontier where R1 meets real arithmetic.