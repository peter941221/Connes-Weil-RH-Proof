# 013 CCM25 Concrete Weil Form And Finite-Prime Arithmetic Plan

Date: 2026-07-10

Status: Phase 0A completed. The existing `SourceWeilFormData` target is
formally rejected as uninhabited over the active concrete test algebra. Phase
0B must replace that interface before either 013 root can be retired.

M1 and M2 are complete. The M3 formula owner compiles with explicit pole,
archimedean, global-prime, and restricted-prime definitions; construction of
its archimedean integrability witness remains the active mathematical bottom.

Result at plan entry: the repository does not prove RH unconditionally.

## 1. Objective

Plan 013 owns exactly these active roots:

```text
normalizedCoreSourceWeilFormDataRoot
normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot
```

The route obligation is:

```text
route obligation:
  construct the selected source Weil square and its finite-prime arithmetic

old weak path:
  arbitrary SourceWeilFormData over convolutionStar = pointwise addition
  -> global Finset required to be nonzero for every test, including zero
  -> CommonFinitePrimeArithmeticSourceData supplied as a second root

new mathematical owner:
  one compact log-coordinate test g
  -> genuine involution g*(x) = conj(g(-x))
  -> genuine additive convolution F_g = g* * g
  -> prime-power evaluations at +/- log(n)
  -> one exact finite support derived from support(F_g)
  -> pole, archimedean, global, and restricted values on the same F_g
  -> canonical atoms and route package data from that same owner

consumer to rewire:
  SourceAnalyticCore / CCM25SourceModel
  -> SourceObjectTheoremBasePackage
  -> NormalizedSourceObjectCoreTheoremBaseData
  -> route common-test and package consumers

forbidden circular inputs:
  SourceRH, no-off-line source-zero, CC20 Proposition C1,
  selected detector coverage, psi/pole collapse, route package conclusions,
  CommonFinitePrimeArithmeticSourceData itself

smallest verification target:
  ConnesWeilRH.Dev.CCM25SourceDataGuards
  then the first new compact-convolution owner module

focused axiom audit:
  #print axioms not_nonempty_concreteSourceWeilFormData
  #print axioms <selected-owner constructor>
  #print axioms unconditional_rh_skeleton
```

Success means both named roots disappear from the import-facing axiom list.
The result remains conditional while either RH-level root remains.

## 2. Explicit Non-Goals

Plan 013 does not own:

```text
the fixed-S kernel and trace roots                         [012]
QW/pole collapse or B3 mass cancellation                  [014]
detector-only coverage or CC20 Proposition C1             [014]
the final no-project-root RH audit                         [015]
```

It must not claim a general inverse from arbitrary route tests into the finite
Galerkin family of arXiv:2607.02828. That paper explicitly claims only the
forward map from a finite vector to a Guinand-Weil test.

## 3. Current Code Evidence

```text
ConnesWeilRH/Source/AnalyticCoreBase.lean:109-116
  SourceTestAlgebra stores an unconstrained binary operation.

ConnesWeilRH/Source/AnalyticCoreBase.lean:3118-3125
  the active concrete operation is f + g and its square is g + g.

ConnesWeilRH/Source/AnalyticCoreBase.lean:262-307
  valueAt is ||F(x)||, so finite-prime evaluation loses complex phase and sign.

ConnesWeilRH/Source/AnalyticCore.lean:7359-7386
  one global Finset must contain only atoms nonzero for every test.

ConnesWeilRH/Source/AnalyticCore.lean:7390-7412
  the zero test forces every finite-prime term to vanish whenever exactSupport
  exists over the concrete algebra.

ConnesWeilRH/Source/AnalyticCore.lean:7746-7750
  SourceWeilFormData contains that impossible SourceFinitePrimeData.

ConnesWeilRH/Source/AnalyticCore.lean:8220-8233
  SourceAnalyticCore makes the impossible object a shared core field.

ConnesWeilRH/Source/CCM25Concrete/FinitePrimeSourceData.lean:603-618
  CommonFinitePrimeArithmeticSourceData separately stores certificates for all
  tests and a scoped archimedean balance.

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:136-143
  normalizedCoreSourceWeilFormDataRoot supplies the impossible object.

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:643-650
  normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot supplies the second
  package root.
```

Phase 0A added the axiom-free guard:

```text
ConnesWeilRH/Dev/CCM25SourceDataGuards.lean
  not_nonempty_concreteSourceWeilFormData
```

Its proof chooses a compact smooth bump with `g(2)=1`. The current support
record proves the finite-prime term at `2` is zero, while the evaluator formula
and `vonMangoldt(2)=log(2)>0` prove the same term is positive.

## 4. Primary Source Evidence

CCM25, "Zeta Spectral Triples":

```text
https://arxiv.org/html/2511.22755

Eq. (2.1)  (f * g)(y) = integral f(x) g(y-x) dx
Eq. (2.2)  f*(y) = conj(f(-y))
Eq. (3.7)  W_p(F) = log(p) sum_m p^(-m/2)
                     (F(p^m) + F(p^(-m)))
Eq. (3.10) QW(f,g) = Psi(f* * g)
Eq. (3.19) the localized form uses von Mangoldt weights up to lambda^2
Eq. (3.20) the prime operator reads the same convolution square
```

The log-coordinate version of Eq. (3.7) evaluates the additive test at
`+log(n)` and `-log(n)`. It does not evaluate at `n` and `n^-1` in additive
coordinates, and it does not take norms before summing.

The July 2026 finite dictionary gives an exact finite specialization:

```text
https://arxiv.org/html/2607.02828

Theorem 2.5:
  <v,Q_infinity v>
    = -1/pi sum_(q=p^a <= c) Lambda(q)/sqrt(q) * ghat_v(log(q)/(2*pi))
      + 2 g_v(i/2)
      + 1/(2*pi) integral h_+(r) g_v(r) dr

Section 4 limitation:
  the dictionary is one-way from finite Galerkin vectors to Guinand-Weil
  tests; no inverse for arbitrary tests is claimed.
```

Mathlib v4.30.0 supplies the analytic primitives but not the assembled owner:

```text
Mathlib/Analysis/Convolution.lean:403-432
  function convolution and complex multiplication kernel

Mathlib/Analysis/Convolution.lean:503-533
  support and compact-support preservation

Mathlib/Analysis/Calculus/ContDiff/Convolution.lean:423-434
  smoothness preservation when one factor has compact support

Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:560-566
  compact smooth functions convert to SchwartzMap
```

## 5. First-Principles Decision

The old target is not merely incomplete. It is contradictory:

```text
global carrier says n is nonzero for every F
                         |
                         v
choose F = 0 --------> term(n,0) = 0
                         |
                         v
every global carrier is empty
                         |
                         v
coverage forces every term of every test to be zero
                         |
                         v
compact bump with g(2)=1 gives term(2,g)>0
```

Selected fork: replace the universal finite-support interface with a selected,
compact, same-object owner before rewiring the route.

Rejected forks:

```text
fill SourceWeilFormData directly
  rejected by not_nonempty_concreteSourceWeilFormData

keep norm-valued evaluation
  rejected by CCM25 Eq. (3.7) and linearity of the Weil distribution

use the finite Galerkin dictionary for every route test
  rejected by arXiv:2607.02828 Section 4: no inverse map

move the root into CanonicalSourceWeilFormSourceDataOwner
  rejected because that owner still contains SourceWeilFormData
```

## 6. Exact Replacement APIs

Phase 0B introduces a pure source module with no route imports:

```lean
structure SourceCCM25CompactLogTest where
  test : TestFunction
  compactSupport : HasCompactSupport test

noncomputable def SourceCCM25CompactLogTest.involution
    (f : SourceCCM25CompactLogTest) : SourceCCM25CompactLogTest

noncomputable def SourceCCM25CompactLogTest.convolution
    (f g : SourceCCM25CompactLogTest) : SourceCCM25CompactLogTest
```

Required read-offs are equations, not stored conclusions:

```text
involution.test x = conj(f.test (-x))
convolution.test x = integral t, f.test t * g.test (x-t)
support(convolution) subset support(f) + support(g)
```

Phase 1 binds one selected test and its square:

```lean
structure SourceCCM25SelectedWeilSquareOwner where
  sourceTest : SourceCCM25CompactLogTest
  convolutionSquare : SourceCCM25CompactLogTest
  convolutionSquare_eq :
    convolutionSquare = sourceTest.involution.convolution sourceTest
```

Phase 2 adds source evaluations on that exact square:

```lean
structure SourceCCM25SelectedFinitePrimeOwner
    (square : SourceCCM25SelectedWeilSquareOwner) where
  globalPrimeIndexSet : Finset Nat
  restrictedPrimeIndexSet : Real -> Finset Nat
  globalExact : forall n,
    n in globalPrimeIndexSet <->
      IsPrimePow n /\ primePowerValue square n != 0
  restrictedExact : forall lambda n,
    n in restrictedPrimeIndexSet lambda <->
      IsPrimePow n /\ primePowerValue square n != 0 /\
      1 < n /\ (n : Real) <= lambda^2
```

Here `primePowerValue` is definitionally based on
`F_g(log n) + F_g(-log n)` and `Lambda(n)/sqrt(n)`. The finite sets must be
constructed from the proved compact support bounds, not accepted as fields
without a constructor theorem.

Phase 3 adds pole and archimedean terms as explicit integrals and proves the
selected CCM25 formula. The ordinary value type is complex until the selected
square theorem proves reality; the route receives a real scalar only through
that theorem.

Phase 4 builds canonical atoms, package certificate data, restricted/global
direct term masses, and scoped balance from the same owner. No field may accept
a second source test or a second convolution square.

## 7. Consumer Rewiring

```text
SourceCCM25SelectedWeilSquareOwner
  |
  +-- SourceCCM25SelectedFinitePrimeOwner
  |
  +-- selected pole/archimedean evaluation
  |
  v
selected source-Weil-form theorem
  |
  v
SourceObjectTheoremBasePackage selected common-test field
  |
  v
NormalizedSourceObjectCoreTheoremBaseData selected finite-prime field
  |
  v
route package atoms and mass consumers
```

Rewire the active consumer before removing either root. Then prove:

```text
the active route no longer projects SourceAnalyticCore.weilForm
the active route no longer projects CommonFinitePrimeArithmeticSourceData
the old universal certificate-family path has no active reference
```

Compatibility declarations may remain only if they are downstream projections
of the selected owner. No compatibility declaration may construct the rejected
`SourceWeilFormData` type.

## 8. Milestones

```text
M0  guard module compiles and axiom audit has no project roots       complete
M1  compact involution/convolution module compiles                  complete
M2  selected square and exact support constructors compile          complete
M3  pole/archimedean/finite-prime formula shares one owner           partial
M4  canonical atoms and package data project from that owner         pending
M5  real route consumer is rewired; old universal path inactive      pending
M6  both 013 Dev roots removed                                       pending
M7  import-facing build and focused axiom audit pass                 pending
```

## 9. Rejection Guards

The final implementation must retain guards for:

```text
nonexistence of the old concrete SourceWeilFormData
convolutionStar is not pointwise addition
evaluation preserves complex value before the selected reality theorem
global support depends on the selected square, not all tests
package atoms use the same selected source test
finite dictionary is not used as an inverse for arbitrary tests
SourceRH and detector coverage are absent from all 013 producer axioms
```

## 10. Verification

All commands run in the WSL ext4 worktree with the repository lock.

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake env lean ConnesWeilRH/Dev/CCM25SourceDataGuards.lean

flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build <smallest new source module>

flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Dev.UnconditionalSkeleton
```

Import-facing audit:

```lean
import ConnesWeilRH.Dev.UnconditionalSkeleton

#check CCM25SourceDataGuards.not_nonempty_concreteSourceWeilFormData
#print axioms CCM25SourceDataGuards.not_nonempty_concreteSourceWeilFormData
#check unconditional_rh_skeleton
#print axioms unconditional_rh_skeleton
```

Accepted M7 output must omit both 013 roots and `sorryAx`. It may still list
the two 012 roots and the two RH-level roots until their owning plans finish.

## 11. Outcome Criteria

```text
success:
  both 013 roots absent from the import-facing RH skeleton axiom list

partial:
  a lower honest owner compiles, but an active consumer still uses an old root

blocked:
  a named Mathlib/source theorem needed for compact convolution or explicit
  formula is unavailable after three independent construction attempts

rejected:
  a proposed owner implies zero finite-prime mass, loses complex phase, mixes
  source tests, or requires an inverse not supplied by the cited paper
```
