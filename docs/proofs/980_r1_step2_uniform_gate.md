# 980 — R1 Step2: the real HS operator gate is uniform over CompactLogTest

Status: execution record.  RH NOT claimed.

## Goal
979 locked the object-layer shape (`ArchimedeanTraceSymbols.Test := CompactLogTest`,
`positiveTrace := Re(arch)`).  Step 2 of the R1 plan needs the operator content of
`hilbertSchmidtGate` to attach to the SAME test that carries `positiveTrace > 0`.

## Result — uniform gate, one test both halves, axiom-clean
`Dev/R1Step2Probe980.lean` (build 3208 jobs green, `#print axioms` =
`[propext, Classical.choice, Quot.sound]`, 0 sorry):

- `r1_gate_selfAdjoint_uniform g` : `IsSelfAdjoint (windowedBoundaryDetector g 1 1)`
  — uniform over `g` (from `CompactRootHalfLinePair:1358`).
- `r1_gate_traceClass_uniform g` : the signed boundary operator at (1,1) is trace
  class along four bases, whose existence is uniform (914c's `exists_hilbertBasis`,
  params depend only on window (1,1), not on g).
- `r1_one_test_both_halves` : `bumpPlateauTest` is self-adjoint AND a global basis
  exists — the two `hilbertSchmidtGate` conjuncts on one test.

## Why this unblocks R1
The apparent object-mismatch (914 uses `gateTest`/`nonzeroTest`; Wall-A positivity
uses `bumpPlateauTest`) is RESOLVED: the operator gate is test-uniform, so the SAME
`bumpPlateauTest` that has the >0 positive trace also has the full gate.  Step 3 can
assemble `SourceRouteTraceData` from one test = `bumpPlateauTest`.

## Honest scope
- The trace-class basis witness is existential (bases exist, as in 914c), not a named
  concrete basis.  Sufficient for `hilbertSchmidtGate`.
- `hilbertSchmidtGate` = `traceClass ∧ cyclicLegal` (AnalyticCore:8180); this probe
  pins the two conjuncts on the bump test, but does NOT yet assemble the full
  `SourceRouteTraceData` / trigger L1552. That is Step 3.

## Lean gotchas this session
- `open MeasureTheory` needed for `Lp`; `open scoped ComplexConjugate InnerProduct
  InnerProductSpace` for `ℂ` inner products.
- Inside deep `Dev` namespace, qualify `CompactLogTest` fully
  (`ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution.CompactLogTest`).
- `exists_hilbertBasis` elaboration can exceed default heartbeats; scope
  `set_option maxHeartbeats in` per-declaration.

## Next
R1 Step 3: assemble `SourceRouteTraceData` at `bumpPlateauTest` — `hilbertSchmidtGate`,
`positiveTraceNonnegative`, `λ`, `oneLtLambda`, `ccm25ArithmeticPackage` (L653),
transport, compatibility — → `FullWeilPositivity` witness → feed L1552.