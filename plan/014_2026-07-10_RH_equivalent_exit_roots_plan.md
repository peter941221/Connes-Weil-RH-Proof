# 014 RH-Equivalent Exit Root Retirement Plan

Status: source and code audit complete. The detector criterion rejection guard
compiles. No unconditional producer has been found.

## 1. Objective

Plan 014 owns these active RH-level roots:

```text
normalizedCoreCC20PropositionC1SourceCriterionRoot
normalizedSelectedFinalRouteDetectorCriterionCoverageRoot
```

It also owns the hidden final-theorem premise:

```text
[NormalizedSelectedSourceCoreTraceQWLambdaCalibrationProvider]
```

The route obligation is:

```text
old weak path:
  store Proposition C1 in the core source package
  assume detector-selected criterion coverage at the final exit
  leave the B2 scalar calibration as an implicit typeclass parameter

new mathematical owner:
  same-object analytic data deriving global Weil nonpositivity from the
  operator/trace result of 012 and the explicit formula result of 013

consumer to rewire:
  normalized selected final route and unconditional_rh_skeleton

forbidden circular inputs:
  SourceRH, RiemannHypothesis, no-off-line source-zero,
  CC20 Proposition C1, and detector criterion/read-off coverage

smallest verification target:
  ConnesWeilRH.Route.CC20RouteRealization
  ConnesWeilRH.Dev.UnconditionalSkeleton
```

Success requires a closed theorem of type `_root_.RiemannHypothesis` with no
ordinary or typeclass parameters and no project roots.

## 2. Scope And Non-Goals

This plan includes:

```text
remove the duplicate Proposition C1 root
construct the hidden B2 provider from lower data
identify and prove the B3/global positivity theorem
derive detector criterion coverage from that theorem
remove the final detector root
audit the complete theorem signature and axiom graph
```

This plan does not own:

```text
the fixed-S kernel and remainder construction                     [012]
the concrete Weil formula and finite-prime owner                  [013]
the final whole-repository release audit                          [015]
```

## 3. Current Code Evidence

The Proposition C1 socket is RH-level once an input record exists:

```text
ConnesWeilRH/Dev/UnconditionalSkeleton.lean:1516-1549
```

The active C1 axiom is at line 1551. The hidden provider starts at lines
2590-2593 and remains in scope through the final theorem. Import-facing
`#print` gives:

```text
unconditional_rh_skeleton :
  forall [NormalizedSelectedSourceCoreTraceQWLambdaCalibrationProvider],
    RiemannHypothesis
```

Therefore `#print axioms` alone understates the current conditional boundary.

The detector criterion root is at line 7786. The exact rejection guards are:

```text
normalizedRouteBackedCC20SquareRestrictedDetectorCriterionCoverage_iff_standardSourceRH
normalizedRouteBackedCC20SquareRestrictedDetectorCriterionCoverage_iff_mathlibRH
```

They live at:

```text
ConnesWeilRH/Route/CC20RouteRealization.lean:20202-20225
```

Their focused axiom output is:

```text
[propext, Classical.choice, Quot.sound]
```

## 4. Primary Source Evidence

### 4.1 CC20 Proposition C.1

```text
Alain Connes and Caterina Consani
Weil positivity and Trace formula, the archimedean place
arXiv:2006.13771, Appendix C, Proposition C.1
https://arxiv.org/pdf/2006.13771
```

The proposition states:

```text
RH
  iff
sum_v W_v(g * conjugate(g^sharp)) <= 0
for every compactly supported smooth g satisfying finitely many Mellin zeros
```

CC20 proves local archimedean positivity and operator inequalities. It does not
prove the semilocal all-prime inequality on the right side of Proposition C.1.

### 4.2 Later work

```text
Zeta Spectral Triples
https://arxiv.org/html/2511.22755

Weil's quadratic form via the screw function
https://arxiv.org/html/2606.09096

A finite Guinand-Weil dictionary and archimedean tail order
https://arxiv.org/html/2607.02828
```

CCM25 states that a rigorous convergence proof for its proposed spectra or
regularized determinants would establish RH. Suzuki proves unconditional local
operator results and leaves the global limit conjectural. The finite dictionary
paper states that it proves neither RH nor Weil positivity and has no inverse
map from arbitrary tests to its finite Galerkin vectors.

No checked source through 2026-07-10 supplies the global positivity theorem
needed to construct the detector criterion root.

## 5. First-Principles Reduction

Yoshida detector existence supplies, for each hypothetical off-line zero, a
compact test whose Weil value is strictly positive. A theorem making the same
test's Weil value nonpositive yields RH.

```text
hypothetical off-line zero
        |
        v
Yoshida detector g_rho
        |
        +-- source theorem: Weil(g_rho) > 0
        |
        +-- missing route theorem: Weil(g_rho) <= 0
                                      |
                                      v
                                  contradiction
```

The missing nonpositivity theorem is the mathematical RH bottom. Renaming it as
coverage, calibration, mass cancellation, trace read-off, or a package field
does not lower its strength.

## 6. Execution Phases

### Phase 0. Make the audit sound

Every final audit must include:

```lean
#check @unconditional_rh_skeleton
#print unconditional_rh_skeleton
#print axioms unconditional_rh_skeleton
```

Acceptance requires no explicit, implicit, instance-implicit, or auto-implicit
premises.

### Phase 1. Collapse the duplicate C1 root

Move the detector criterion root before construction of the core RH-exit
package. Use its exact equivalence guard to obtain one `SourceRH` value, then
define the compatibility C1 criterion by `fun _input _c1Data => sourceRH`.
Remove `normalizedCoreCC20PropositionC1SourceCriterionRoot`.

This only proves that the two RH roots were duplicate outlets. It must leave the
detector root visible and must not count as an unconditional proof.

### Phase 2. Construct the hidden B2 provider

The provider owns:

```text
traceAmplitudeSquare = selected restricted CCM25 evaluator
```

Construct it from the same route/test `SourceTraceReadOffData` or its accepted
012 replacement. Do not introduce a global scalar family. If 012/013 have not
produced the same-object equality, keep Phase 2 blocked and leave the final
theorem visibly conditional.

### Phase 3. Define the honest B3 owner

The B3 owner must bind one Yoshida detector test to:

```text
its genuine convolution square
the 012 positive operator and ordinary trace
the 013 full and restricted Weil evaluations
support-square trace = QW_lambda
restricted-to-global limit or exact finite-prime difference
all remainder and no-defect terms
ordinary positive trace >= 0
global Weil value = negative ordinary positive trace
```

The owner must not contain `CC20WeilNonpositive`, detector coverage,
no-off-line zero, `SourceRH`, or RH as stored fields.

### Phase 4. Cover the detector family

Parameterize the Phase 3 construction by each Yoshida detector. Project its
last equality and trace nonnegativity into the local Weil criterion, then build
`NormalizedRouteBackedCC20SquareRestrictedDetectorCriterionCoverage`.

This passes only when the proof unfolds to the analytic owner and 012/013
theorems. A structure field storing coverage fails the gate.

### Phase 5. Rewire and delete the final root

Replace `normalizedSelectedFinalRouteDetectorCriterionCoverageRoot` with the
Phase 4 theorem. Delete every RH-equivalent root from the active chain.

### Phase 6. Final local audit

The final theorem must print exactly as a closed theorem:

```text
theorem unconditional_rh_skeleton : RiemannHypothesis
```

## 7. Rejection Guards

Reject a candidate if:

```text
it assumes SourceRH, RH, or no-off-line source-zero
it stores detector criterion or read-off coverage
it stores global Weil nonpositivity as a field
it proves positivity only for a fixed finite Galerkin space
it treats numerical convergence as uniform analytic convergence
it covers a bounded support interval without an exhaustion theorem
it reconstructs the C1 root under another name
it leaves any hidden theorem parameter
```

## 8. Verification

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build \
  ConnesWeilRH.Route.CC20RouteRealization

flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build \
  ConnesWeilRH.Dev.UnconditionalSkeleton
```

Import-facing audit:

```lean
#check @normalizedRouteBackedCC20SquareRestrictedDetectorCriterionCoverage_iff_mathlibRH
#print axioms normalizedRouteBackedCC20SquareRestrictedDetectorCriterionCoverage_iff_mathlibRH
#check @unconditional_rh_skeleton
#print unconditional_rh_skeleton
#print axioms unconditional_rh_skeleton
```

## 9. Milestones And Outcomes

```text
M0  full-signature audit exposes the hidden provider                 complete
M1  detector criterion coverage is proved RH-equivalent             complete
M2  duplicate C1 root removed; one RH root remains                  pending
M3  hidden B2 provider constructed from lower same-object data       pending
M4  honest B3/global positivity owner compiles                      pending
M5  detector family constructed from the B3 owner                   pending
M6  final detector root removed                                     pending
M7  closed theorem signature and zero-project-root audit pass        pending
```

Complete means M0-M7 pass. Partial means the duplicate root is gone but the
detector root remains, the provider is not constructed, or B3 covers only a
selected family. Blocked means 012/013 lacks same-object data or the
restricted-to-global theorem. Reject the route if every candidate global B3
producer is RH-equivalent before it acquires analytic content.
