# 922 — L653 reduce: concrete assembly notes (read-off all rfl-level)

Status: reduce path fully mapped; read-offs verified rfl-level; a first
axiom-clean bridge committed (d481d50). Full L653 `CommonFinitePrimeArithmeticSourceData`
construction is a large mechanical assembly, not a one-def proof.

## The wall (restated)
`CommonFinitePrimeArithmeticSourceData` -> `finitePrimeData.certificateData`
(∀ f g λ 1<λ …) -> each `FixedLambdaArithmeticCertificateSourceTestData`
-> `atoms : SourceFinitePrimeArithmeticNormalizationForSourceTest` =
`∀ n : ℕ → DataForSourceTest`, whose leaf needs `IsPrimePow n` = False at
composites/1. A forall-n normalization is uninhabitable for any W. Definitional
(quantifier-scope) wall, not a missing real-analysis lemma. Do NOT attack at
composites.

## Why on-index-set re-type is the win (bridge, committed)
`FixedLambdaArithmeticCertificateSourceTestData.sourceGlobalArithmeticData`
(FinitePrimeSourceData.lean:263) projects visible arithmetic data onto
`SourceGlobalFinitePrimeArithmeticData` (on-`globalPrimeIndexSet`). Membership
witness downgraded via `globalIndexData -> .atomVisible ->
route_visibility_iff_source_visibility`. #print axioms = [propext, Classical.choice, Quot.sound].
Build green 4146. This is the Level-1 projection primitive.

## The real reduce lane (NOT the bridge)
`SourceFinitePrimeArithmeticDataOnIndexSet.ofSourceEvaluationData`
(PrimePowerArithmeticBridge.lean:504) builds on-index arithmetic straight from
`E : AnalyticCore.SourceEvaluationData`, needs only per-n:
- `sourcePrimePowerIndex : IsPrimePow n`  (n=2: capable)
- `visible : finitePrimeAtomVisible n`     (has: term_two_pos -> termHeaderCell ne 0)
- `pairingReadOff : W.primePowerPairing = (1/root n)(valueAt + valueAt inv)`
- `weightReadOff : W.vonMang t)
- `termReadOff  : W.finitePrimeTerm = vonManGold n * (1/root n)(valueAt+valueAt)`

## Why assembly is mechanical (all refl/simp)
AnalyticCore defines on the concrete data:
- `vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n` (AnalyticCore:7598) -> weightReadOff = rfl
- `sourceFinitePrimeTerm` = `vonMangGold n * (1/sqrt n)(valueFwd+valueInv)` (AnalyticCoreBase:303-307)
- `sourcePrimePowerPairing` = `(1/sqrt n)(valueAt sq n + valueAt sq inv)` (AnalyticCoreBase:297)
- `toWeilFormSymbols.primePowerPairing = sourcePrimePowerPairing`,
  `.finitePrimeTerm = sourceFinitePrimeTerm` (AnalyticCore:7693 etc.)
So `pairingReadOff` / `termReadOff` reduce to `simp [..] = rfl` lemmas. No new
real analysis required.

## Known-good concrete carriers (ConcreteP1SupportProbe)
- `concreteEval : SourceEvaluationData concreteTestAlgebra` (mk)
- `commonBump : TestFunction` compact support in Icc 3/2 5/2, value 1 at 2
- `term_two_pos : 0 < concreteEval.sourceFinitePrimeTerm 2 commonBump`
- `perCommonSupport.globalIndexSet = {2}` exactly
- `concreteWeilForm : SourceWeilFormData concreteTestAlgebra`

## Compute only.
Need: `W = concreteWeilForm.toWeilFormSymbols`; `common = concreteCommonSourceTest W commonBump`.
The tricky one is `visible : W.finitePrimeAtomVisible 2 (W.convolutionStar g g)`
where `sourceFinitePrimeTerm ≠ 0` (via concrete `term_two_pos`), and `common`
passes through `route_visibility_iff_visibility`.

## Why we stopped — not a one-edit diff
Assembling a `SourceFinitePrimeArithmeticDataOnIndexSet` under the full
`ofSourceEvaluationData` signature (5 read-offs + index-set) and threading into
`certificateData` / `commonFinitePrimeArithmeticSourceData` is ~100+ lines of
`simp`/`rw`/`rcases` boilerplate across three structures, with several namespace
ambiguities. It is a real engineering lift (a probe-file session), not a single
edit. This doc is the map so the next session does not re-explore.