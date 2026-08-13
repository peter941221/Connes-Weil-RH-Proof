# 1005 - RH route after the C1 same-owner repair

Date: 2026-08-12. Status: route judgment. RH NOT claimed.

## Outcome

The recent work is a substantive route repair, not an RH proof. It removes four
modeling defects that previously made both the Lean wiring and the numerical
sign reports unreliable:

```text
+-----------------------------------+------------------------------------------+
| old defect                        | repaired state                           |
+-----------------------------------+------------------------------------------+
| log test passed as x-coordinate   | explicit F(log x) positive-route bridge |
| convolution square applied twice | exactly one g^* * g readback             |
| prime support truncated to {2}    | all nonzero visible prime powers         |
| source/CC20 signs conflated       | source QW = - CC20 local sum             |
+-----------------------------------+------------------------------------------+
```

The active unconditional-looking theorem still depends on an explicit project
axiom. The source is:

```lean
axiom normalizedSelectedFinalRouteDetectorCriterionCoverageRoot :
  NormalizedRouteBackedCC20SquareRestrictedDetectorCriterionCoverage
```

and its consumer chain is:

```text
normalizedSelectedFinalRouteDetectorCriterionCoverageRoot
  -> normalizedSelectedFinalRouteSourceRHFrom08AFromTheorems
  -> cc20FiniteVanishingExitFromTheorems
  -> rhDefinitionBridgeToMathlibFromTheorems
  -> unconditional_rh_skeleton
```

Therefore the repository still does not prove RH unconditionally.

## Gate map

```text
+------+----------------------------------------------+-------------------------+
| Gate | Mathematical content                         | Current state           |
+------+----------------------------------------------+-------------------------+
| 0    | CompactLog -> positive x test; Mellin bridge | CLOSED                  |
| 1    | pole + arch + all visible prime powers       | CLOSED as same-owner    |
|      | and canonical selected-owner readbacks       | definitions/readbacks   |
| 2    | all-test explicit-formula / trace identity   | OPEN                    |
| 3    | all vanishing g: 0 <= QW(g)                  | OPEN, RH-level          |
| 4    | Yoshida detectors on the healthy owner       | OPEN rebuild/transport  |
| 5    | criterion + detector -> SourceRH             | CLOSED conditionally    |
| 6    | SourceRH -> mathlib RiemannHypothesis        | CLOSED conditionally    |
+------+----------------------------------------------+-------------------------+
```

### Gate 0 evidence

`C1LogPositiveBridge` defines the actual coordinate change:

```lean
positiveRouteRaw F x = if 0 < x then F.test (Real.log x) else 0

theorem mellin_toPositiveRouteTest_eq_laplaceAt (F) (s) :
  mellin (fun x => toPositiveRouteTest F x) s = CompactLogTest.laplaceAt F s
```

This matters because both sides previously had the same Lean function type
while representing different mathematical coordinates.

### Gate 1 evidence

`C1SameOwnerWeil` now owns all components:

```lean
noncomputable def finitePrimeSum (F : CompactLogTest) : Real :=
  ∑ n ∈ globalPrimeIndexSet F, finitePrimeTerm F n

noncomputable def psi (F : CompactLogTest) : Real :=
  poleTerm F - archimedeanTerm F - finitePrimeSum F

noncomputable def qw (g : CompactLogTest) : Real :=
  psi g.convolutionSquare
```

Compact support proves every nonzero prime-power term lies in the finite
`globalPrimeIndexSet`. Component theorems identify this object term-for-term
with `SelectedWeilSquareOwner.ofCompactLogTest g`.

This is an arithmetic functional definition and canonical readback. It is not
yet the classical explicit formula equating the arithmetic distribution to a
spectral/zero or trace expression for every test; that is Gate 2.

### Gate 3 evidence

The repaired CC20 instance has no hidden sign or square residue:

```lean
healthyCriterionState F ↔
  ∀ g : CompactLogTest,
    ConnesWeilRH.Source.CC20VanishesOn healthyCC20TestSpace F g →
      0 ≤ C1SameOwnerWeil.qw g
```

This is the exact remaining universal statement, not a theorem proving its
right-hand side. The sign dictionary is:

```text
source QW(g)                         >= 0
CC20 local sum on starConvolution g  <= 0
```

### Gates 4-6 evidence

The generic contradiction theorem already exists:

```lean
theorem cc20_proposition_c1_from_yoshida_detector
    (C : CC20TestSpace)
    (F : Finset CriticalVanishingPoint)
    (_hfinite : SourceFiniteSetAdmissibility F)
    (_hdisjoint :
      SourceFiniteSetDisjointFromNontrivialZeros
        RHDefinitionBridge.standard F)
    (hexists : CC20YoshidaDetectorExists C F)
    (hcriterion : CC20FiniteVanishingWeilCriterion C F) :
    RHDefinitionBridge.standard.SourceRH := by
```

The existing unconditional detector theorem is for `normalizedCC20TestSpace`,
not `healthyCC20TestSpace`. Reusing its name or underlying Lean function types
does not transport its test, Mellin values, convolution, or Weil sign. A
same-owner detector theorem is still required.

The route guard confirms the load-bearing scale. With normalized Yoshida
detectors supplied,
`normalizedRouteBackedCC20SquareRestrictedDetectorCriterionCoverage_iff_standardSourceRH`
proves detector criterion coverage equivalent to `SourceRH`; its mathlib-facing
sibling proves equivalence to `RiemannHypothesis`.

## Numeric correction

The shared evaluator now asserts:

```text
abs(F(0) - ||g||_2^2) < 1e-8
abs(pole - 2*M_g(+1/2)*M_g(-1/2)) < 1e-8
max(abs(M_g(0)), abs(M_g(1/2)), abs(M_g(1))) < 1e-8
```

It samples prime terms at `+/-log(n)` and sums every visible prime power. Three
representative convergence sequences are:

```text
+--------------+-------------+-------------+-------------+
| window       | N=10001     | N=20001     | N=40001     |
+--------------+-------------+-------------+-------------+
| [-0.5,+1.5] | +0.01889367 | +0.01889492 | +0.01889528 |
| [-1.5,+1.5] | +0.00310544 | +0.00310563 | +0.00310585 |
| [-2.0,+2.5] | +0.00009204 | +0.00009309 | +0.00009328 |
+--------------+-------------+-------------+-------------+
```

The width scan `1.6..5.0` found no negative value; its minimum converges near
`+7.87e-6` at width `4.8`. This retracts the old `w ~= 2.8175` sign boundary.
It remains finite-family numerical evidence, not Gate 3.

## Recommended path to RH

```text
[A] Freeze the healthy same-owner API
       |
       v
[B] Prove the all-test explicit-formula / trace identity
       |  same g, same square, same pole/arch/prime terms
       v
[C] Derive QW(g) >= 0 for every triple-vanishing g
       |  this is the load-bearing Connes positivity theorem
       v
[D] Rebuild Yoshida interpolation/detection on healthyCC20TestSpace
       |  detector must also carry off-line strict CC20 positivity
       v
[E] Apply cc20_proposition_c1_from_yoshida_detector
       v
     SourceRH -> Mathlib RH
```

The highest-value next theorem is a data-bearing Gate-2 bridge whose statement
keeps one `CompactLogTest g` through both sides, schematically:

```lean
theorem sameOwner_qw_eq_positive_trace
    (g : CompactLogTest)
    (hvanish : CC20VanishesOn healthyCC20TestSpace
      cc20TripleFiniteVanishingSet g) :
    C1SameOwnerWeil.qw g = realTraceOrNormSquare g
```

The right-hand side must be an already-defined or newly constructed genuine
spectral/trace quantity with a proved nonnegativity theorem. It must not store
`0 <= qw g` as input data or define the right-hand side to be `qw g`.

After that bridge, Gate 3 should be a short consequence. Gate 4 then ports the
Mellin interpolation construction to the positive-route coordinate and proves
the detector's strict off-line sign using the same explicit-formula owner.

## Priority ruling

The PSP/Paley-Wiener and infinite-carrier Gate-3U work is a diagnostic branch.
Even a successful nonzero Sonin-window witness would reject or diagnose that
physical cancellation route; it would not fill the active C1 criterion axiom.
The direct RH budget should therefore go to Gates 2-4 above, in that order.

RH NOT claimed.

## Verification

The current Windows snapshot was copied one way into a fresh ext4 verification
directory with no project build cache. The focused import-facing command was:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Dev.C1RouteRepairAudit
```

Result: `Build completed successfully (3489 jobs)`. The ten audited declarations
all depend only on `[propext, Classical.choice, Quot.sound]`; no `sorryAx` or new
project axiom appears. Existing dependency linter warnings remain non-fatal.
