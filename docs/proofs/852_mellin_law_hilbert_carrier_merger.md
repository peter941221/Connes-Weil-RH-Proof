# 852 — the re-type target is a MERGE of the Mellin law onto the existing Hilbert carrier, not a new bare carrier

Date: 2026-08-07 · Status: source-verified structural verdict (no new build; uses the
build+axiom evidence of 851 §6 and the L2 object below). This corrects/refines 851's
"wiring" wording: it is not wiring a bare carrier into the route, it is transporting the
already-proved Mellin product law onto the carrier that already owns the Hilbert/HS/
positive-trace structure — otherwise the HS gate is a fake.

## 0. 先讲结论

There are currently TWO separated objects:

| object | role | location | carries |
|---|---|---|---|
| `MellinProductCarrier` (`Test = { log : ℝ → ℂ }`) | the Mellin product LAW (axiom-clean, 851) | `Dev/...` only | multiplicative Mellin square, but NO Hilbert/HS |
| `cc20GlobalLogCrossingL2` | the Hilbert HS carrier | `Source/CC20Concrete/CCM24ArchimedeanCarrier.lean` | Lp Hilbert, `windowedBoundaryDetector` = `F*F>=0` (A3), positive trace |

Neither is imported by route: the Mellin modules live in `Dev/` only (851 grep: zero
main-line references).  So the re-type that 850/851 wanted is not "add a hook"; it is a
**merge**: make the Hilbert carrier ALSO satisfy the multiplicative Mellin law.

## 2. Why the merge is the correct shape (and possible)

`cc20GlobalLogCrossingL2` is build from `Lp.aestronglyMeasurable` (an `ℝ → ℂ` ae function
class); `MellinConvolutionIdentity.mellin_log_convolution_product (F G : ℝ → ℂ)` already
proves the multiplicative Mellin law for real-valued functions.  Since the Hilbert carrier
's elements are (ae) real-valued functions of exactly that type, the law is *thageable*:
give `cc20GlobalLogCrossingL2` the multiplicative `mellinHalfDensityMatched` via the 
`ℝ → ℂ` representation, while KEEPING the Hilbert structure that already owns `F*F≥0`.

```
   cc20GlobalLogCrossingL2 (Hilbert, F*F >= 0, HS gate)   <-- keep this
        +  Node:       +  MellinConvolutionIdentity (axiom-clean product law)
        v
   re-typed Arch: Test = cc20GlobalLogCrossingL2  (already true)
        hilbertSchmidtGate  : nonzero witness (A3)
        positiveTrace       : ||F u||*2 >=0
        mellinHalfDensityMatched : from the product law applied to its L2 elements
        sourceNoDefectTrace: product-law RHS
```

## 3. REVISION to 850/851's "wiring, not analysis"

`851 said the re-type is "wiring" because the law already exists.  That is HALF-right:
the law exists, but the modern question is whether the Hilbert carrier's elements let it
instantiate `mellinHalfElatenessMatched` (they look like, and the law is per-`ℝ→ℂ`, so
yes — but this is a measure-theory measurement: it has to be a REAL pairwise handler and
not an abbreviation). So the honest statement is:

> RE-TYPE = merge.  The agent of the merge is the `Lp` element↔`ℝ→ℂ` ae bridge + the
> Mellin law pushed by `integral` avgable; the Hilbert/HS side is already provided by
> `cc20GlobalLogs2` and its `F*F` (A3).  This is new measure theory (buildable), not an axiom.

## 4. Honest state / next step

- No RH claim.  The Mellin law is closed (851 §6, build).  The Hilbert/HS and positive
  trace are closed (A1/A3, C3).  The missing seam is the `integral`/ae-measure bridge
  (a buildable Lean unit).
- Concrete step: give `cc20GlobalLogCrossingL2` a `mellinLift`+`mellinHalfDensityMatched`
  so its elements witness the law, keep the existing HS gate; build in a clean mirror and
  `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

Evidence: 851 §6 (build+axiom clean); `CCM24ArchimedeanCarrier.lean` for L2; A3 for
`F*F >= 0` and HS; `Dev/MellinProductCarrier` for the law.