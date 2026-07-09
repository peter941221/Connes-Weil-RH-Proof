# Source Object Definition Ledger

Status: definition-discharge ledger for the next certification phase.

The source-interface proof packages now cover every CCM24, CCM25, and CC20
contract. The next risk is not a missing route lemma. The next risk is that a
Lean theorem could prove the right-looking statement about the wrong objects.

This ledger names the symbolic objects that must become concrete definitions,
imported source objects, or theorem-source bridges before the route can move
from source-conditional evidence to a proof artifact.

## Boundary

Current Lean source interfaces use three symbolic records:

```text
ConnesWeilRH.SemilocalModelSymbols
ConnesWeilRH.WeilFormSymbols
ConnesWeilRH.ArchimedeanTraceSymbols
```

and one abstract final-exit package:

```text
ConnesWeilRH.FiniteVanishingCriterionPackage
```

These records make the route composition auditable. They do not define the
actual CCM24 Hilbert models, CCM25 Weil forms, CC20 trace objects, or CC20
Riemann zeta zero predicate.

The replacement path is:

```text
symbolic Lean field
  |
  v
source object or imported theorem interface
  |
  v
bridge theorem with exact hypotheses
  |
  v
route certificate consumes the bridge, not a bare Prop
```

The definition spine package records the cross-object version of this path:

```text
docs/proofs/source-object-definition-spine-discharge.md
docs/proofs/source-object-definition-theorem-contract.md
docs/audits/source-object-theorem-discharge-ledger.md
docs/proofs/source-common-test-tuple-theorem-contract.md
```

It requires the common test, CCM24 window, CCM25 Weil objects, CC20 trace
objects, CC20 finite-vanishing exit, and Mathlib RH bridge to project from one
source-owned dependency spine.

The theorem contract further splits that source-owned spine into the common
test and convolution square, one fixed route tuple, one restricted window,
CCM25 Weil objects, CC20 trace objects, CC20 RH-exit objects, and compact-record
derivations.

The theorem-discharge ledger records what proof or import evidence would make
each of those seven rows acceptable for the source-object definition gate.

Rows 1 and 2 have a dedicated theorem contract. It fixes the formal/import
targets for the common test, source convolution square, fixed route tuple, and
the tuple bridge that carries the same `g`, `F_g`, `S`, `I`, and `lambda` into
later source packages.

## Global Test-Function Boundary

| current object | source object required | evidence | bridge theorem required | failure if left symbolic |
|---|---|---|---|---|
| `TestFunction := Type` | the common test-function or half-density class used by the CCM24 support window, CCM25 `QW`, and CC20 Mellin/Fourier convention | `ConnesWeilRH/Basic.lean:39`; `weil-compo.tex:2014-2030`; `mc2arXiv.tex:445-470,530-540`; `docs/proofs/source-test-convolution-compatibility.md` | `SourceTestFunctionCompatibility`: one test object maps to the CCM24 semilocal test, CCM25 Weil test, and CC20 Mellin half-density test | the route may identify `g`, `F_g=g^* * g`, and Mellin vanishing for different test spaces |
| `convolutionStar` | the source convolution/involution product producing `F_g=g^* * g` | `ConnesWeilRH/Basic.lean:45`; `docs/proofs/source-test-convolution-compatibility.md`; `docs/proofs/ccm25-restricted-read-off-discharge.md`; `docs/proofs/cc20-trace-legality-mellin-discharge.md` | `SourceConvolutionSquareReadOff`: the CCM25 test product and CC20 support-square input are the same `F_g` | finite-prime support, Mellin vanishing, and trace read-off can refer to different functions |

## CCM24 Semilocal Objects

| current symbolic field | source object required | source lines | bridge theorem required | failure if left symbolic |
|---|---|---|---|---|
| `PlaceSet` | finite place set `S`, including the archimedean place and finite primes visible to `F_g` | `mainc2m24fine.tex:237-253`; manuscript fixed-S side condition in `docs/manuscripts/connes-weil-rh-proof-draft.md:312-328,1368-1374`; `docs/proofs/ccm24-semilocal-object-normalization-discharge.md` | `SourcePlaceSetMatchesVisiblePrimes` | `S` can grow with `lambda` or miss a finite-prime atom needed by `QW_lambda` |
| `Window` | the CCM24 support window that also lies in `[lambda^-1, lambda]` | `mainc2m24fine.tex:761-771,983-1003`; `ConnesWeilRH/Basic.lean:145-161`; `docs/proofs/ccm24-semilocal-object-normalization-discharge.md` | `SourceWindowLambdaContainment` and `SourceSupportWindow` | the positive trace, restricted Weil form, and Cdef exhaustion can use different cutoff windows |
| `supportInWindow` and `fourierSupportInWindow` | source support and Fourier-support containment for the fixed-S test | `mainc2m24fine.tex:761-771,983-1003`; `docs/proofs/ccm24-semilocal-object-normalization-discharge.md` | `SourceSupportAndFourierSupportTransport` | Theorem 1 can read a fixed-S trace outside the admissible support window |
| `supportTransported` and `convolutionSupportTransported` | transport of the test and `F_g=g^* * g` through the CCM24 coordinate | `mainc2m24fine.tex:761-771,983-1003`; `docs/proofs/ccm24-semilocal-object-normalization-discharge.md` | `SourceConvolutionSupportTransport` | finite-prime visibility can be checked on the wrong transported object |
| `canonicalHilbertModel`, `scalingActionImplemented`, `fourierGradingCompatible` | the CCM24 canonical Hilbert model, scaling action, `V_S=M_S U_S`, and Fourier grading | `mainc2m24fine.tex:237-253,786-804`; `docs/proofs/ccm24-semilocal-object-normalization-discharge.md` | `SourceCanonicalSemilocalModel` | commutators and Fourier grading can be interpreted across mismatched Hilbert spaces |
| `boundedComparisonMap` and `boundedComparisonInverse` | the bounded CCM24 comparison map and inverse used to move trace/norm estimates | `mainc2m24fine.tex:806-823`; `docs/proofs/ccm24-semilocal-object-normalization-discharge.md` | `SourceBoundedComparisonTraceClassTransport` | a bounded comparison can exist abstractly while failing to preserve the trace-ideal class used downstream |
| `soninSpaceComparison` and `fixedWindowExhaustionCompatible` | fixed-window Sonin comparison and exhaustion for the chosen test/window | `mainc2m24fine.tex:1050-1060`; `docs/proofs/ccm24-semilocal-object-normalization-discharge.md` | `SourceFixedWindowSoninExhaustion` | Cdef exhaustion may change the order of fixing `g`, `I`, `S_A`, graph order, and `lambda` |

## CCM25 Weil-Form Objects

| current symbolic field | source object required | source lines | bridge theorem required | failure if left symbolic |
|---|---|---|---|---|
| `qw` | CCM25 global Weil quadratic form `QW(f,g)` | `mc2arXiv.tex:445-470`; `ConnesWeilRH/Basic.lean:42,58-60`; `docs/proofs/ccm25-qw-psi-definition-sign-discharge.md` | `SourceQWDefinition` proving `QW(f,g)=Psi(f^* * g)` for the source product | a positive-looking route form may not be the CCM25 Weil form |
| `psi` | CCM25 distribution `Psi` with pole, archimedean, and finite-prime sign split | `mc2arXiv.tex:445-470`; `ConnesWeilRH/Basic.lean:44,62-66`; `docs/proofs/ccm25-qw-psi-definition-sign-discharge.md` | `SourcePsiSignSplit` | the final inequality direction can flip |
| `qwLambda` | restricted CCM25 form `QW_lambda` | `mc2arXiv.tex:530-540`; `ConnesWeilRH/Basic.lean:43,68-75`; `docs/proofs/ccm25-restricted-qwlambda-window-discharge.md`; `docs/proofs/restricted-to-full-qw-bridge-theorem-contract.md` | `SourceRestrictedQWLambdaFormula` plus `RestrictedToFullQWBridgeContract` | the fixed-S positive trace can be read as a different restricted quadratic form or the restricted-to-full step can smuggle in spectral convergence |
| `globalPrimeIndexSet` | full source prime-power support for the finite-prime part of `Psi` | `mc2arXiv.tex:445-470`; `ConnesWeilRH/Basic.lean:46,78-80`; `docs/proofs/ccm25-qw-psi-definition-sign-discharge.md`; `docs/proofs/ccm25-finite-prime-index-normalization-discharge.md` | `SourceGlobalPrimeIndexCoverage` plus source support characterization | a hidden empty, oversized, or underspecified finite-prime index set can erase or add terms |
| `restrictedPrimeIndexSet lambda` | restricted prime-power support selected by the CCM25 `lambda` formula and cut by `1 < n <= lambda^2` | `mc2arXiv.tex:530-540`; `ConnesWeilRH/Basic.lean:47,82-84`; `docs/proofs/ccm25-restricted-qwlambda-window-discharge.md`; `docs/proofs/ccm25-finite-prime-index-normalization-discharge.md` | `SourceRestrictedPrimeIndexCoverage` plus `SourceRestrictedPrimePowerSupport` | visible finite-prime atoms of `F_g` may be omitted from `QW_lambda`, or non-source atoms may be added |
| `finitePrimeAtomVisible` | predicate saying which source prime-power atoms of `F_g` are visible before the `lambda` limit | `docs/proofs/ccm25-finite-prime-support-pairing-discharge.md`; `docs/proofs/ccm25-finite-prime-index-normalization-discharge.md`; manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:1043-1057,1368-1374` | `SourceVisiblePrimePowerAtom` and `SourcePrimePowerIndex` | the route can choose `S_A` after the limit or allow non-prime-power atoms |
| `finitePrimeTerm` | source finite-prime term attached pointwise to a prime-power atom | `mc2arXiv.tex:445-470,530-540`; `ConnesWeilRH/Basic.lean:49,86-90`; `docs/proofs/ccm25-finite-prime-index-normalization-discharge.md` | `SourceFinitePrimeTermNormalization` | the finite-prime coefficient can differ from the source term or cancel errors only after summation |
| `vonMangoldtWeight` | CCM25 von Mangoldt weight `Lambda(n)` on prime-power indices | `mc2arXiv.tex:530-540`; `ConnesWeilRH/Basic.lean:54`; `docs/proofs/ccm25-finite-prime-index-normalization-discharge.md` | `SourceVonMangoldtWeight` | a route-local coefficient or hidden sign can replace the source arithmetic weight |
| `primePowerPairing` | CCM25 pairing `<g|T(n)g>` and its source expression through `F_g(n)` and `F_g(n^-1)` | `mc2arXiv.tex:530-540`; `ConnesWeilRH/Basic.lean:53`; `docs/proofs/ccm25-finite-prime-index-normalization-discharge.md` | `SourcePrimePowerPairingNormalization` | the restricted sum can use the right weight on the wrong pairing |
| `poleFunctional` and `polePairing` | the CCM25 pole functional and restricted pole pairing | `mc2arXiv.tex:465-470,533-535`; `ConnesWeilRH/Basic.lean:51-52,103-105`; `docs/proofs/ccm25-qw-psi-definition-sign-discharge.md`; `docs/proofs/ccm25-restricted-qwlambda-window-discharge.md` | `SourcePoleNormalization` | triple vanishing can kill a route pole while the source pole channel remains |
| `archimedeanTerm` | CCM25 archimedean term with sign compatible with CC20 | `mc2arXiv.tex:445-470`; `weil-compo.tex:2131-2165`; `ConnesWeilRH/Basic.lean:50`; `docs/proofs/ccm25-qw-psi-definition-sign-discharge.md` | `SourceArchimedeanSignBridge` | `QW(g,g) >= 0` may not become the CC20 nonpositivity input |

The CCM25 sign bridge must remain visible as a theorem:

```text
QW(g,g) = - sum_v W_v(g * bar(g)^sharp).
```

It should not disappear inside `fullWeilPositivity : Prop`.

The final sign-bridge spine package strengthens this row:

```text
docs/proofs/final-sign-bridge-spine-discharge.md
docs/proofs/final-sign-bridge-theorem-contract.md
```

It requires the source test, `Psi` expansion, archimedean sign bridge,
finite-prime sign owner, pole sign, sign equality, and inequality-direction
theorem to remain named before CC20 Proposition C.1 consumes positivity.

The theorem contract further splits those stages into common-test equality,
source `Psi` sign expansion, `W_R=-W_infty` plus CC20 sign convention,
finite-prime sign ownership by the formula, source pole sign in the CC20 local
sum, `QW(g,g)=-sum_v W_v(F_g)`, and
`QW(g,g)>=0 -> sum_v W_v(F_g)<=0`.

The finite-prime normalization spine package strengthens the finite-prime rows:

```text
docs/proofs/ccm25-finite-prime-normalization-spine-discharge.md
docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md
```

It requires source prime-power status, visibility in `F_g`, the restricted
lambda cut, source `Lambda(n)`, source `<g|T(n)g>`, and pointwise term equality
before any global or restricted finite-prime sum is used.

The theorem contract further splits those stages into prime-power
factorization, global source support, restricted lambda-cut support,
visibility before the cut, fixed-S visible-prime admissibility, von Mangoldt
weight normalization, source pairing normalization, pointwise atom equality,
and finite-prime sign ownership.

## CC20 Trace And Exit Objects

| current symbolic field | source object required | source lines | bridge theorem required | failure if left symbolic |
|---|---|---|---|---|
| `ArchimedeanTraceSymbols.Test` | CC20 test object used in the quantized-calculus trace formula and matched to the common CCM25 half-density test | `weil-compo.tex:378-387,448-464`; `docs/proofs/cc20-trace-object-normalization-discharge.md` | `SourceCC20TraceTestCompatibility` | trace-class and support-square statements may apply to a different object from the CCM25 test |
| `supportSquareTrace` and `sourceNoDefectTrace` | CC20 support-square trace and source no-defect trace for the same operator | `weil-compo.tex:378-387`; `ConnesWeilRH/Basic.lean:111-112,124-129`; `docs/proofs/cc20-trace-object-normalization-discharge.md` | `SourceNoDefectTraceReadOff` | the route can prove positivity of one trace and identify another trace with `QW` |
| `positiveTrace` | ordinary trace `Tr(A^*A)` used before reading off the Weil form | `weil-compo.tex:378-387`; `ConnesWeilRH/Basic.lean:113,124-129`; `docs/proofs/cc20-trace-object-normalization-discharge.md` | `SourcePositiveTraceNonnegative` | positivity can be applied to a non-trace-class or unidentified operator |
| `hilbertSchmidtGate`, `traceClass`, and `cyclicLegal` | Hilbert-Schmidt input, trace-class conclusion, and legal cyclic trace moves from one CC20 trace-ideal template | `weil-compo.tex:448-464,2106-2121`; `ConnesWeilRH/Basic.lean:114-116,131-133`; `docs/proofs/cc20-trace-object-normalization-discharge.md` | `SourceTraceClassCyclicityTemplate` | cyclicity or positivity can be used before trace legality has been proved |
| `mellinHalfDensityMatched` | CC20 Mellin/Fourier half-density convention preserving `F_g=g^* * g` | `weil-compo.tex:2014-2030`; `ConnesWeilRH/Basic.lean:117,135-137`; `docs/proofs/cc20-trace-object-normalization-discharge.md` | `SourceMellinHalfDensityCompatibility` | triple vanishing can be checked at the wrong points or for the wrong test normalization |
| `uInfinityNormalized`, `qduNormalized`, `archimedeanSignNormalized` | CC20 `u_infty`, `qd u`, and archimedean sign conventions matched to CCM25 sign bridge | `weil-compo.tex:2131-2165`; `ConnesWeilRH/Basic.lean:118-120,139-141`; `docs/proofs/cc20-trace-object-normalization-discharge.md` | `SourceCC20SignNormalizations` | the final sign can be reversed at the CC20 exit |
| `FiniteVanishingCriterionPackage.finiteSetAdmissible` | Proposition C.1 finite-set side condition, with source `F={0,1/2,1}` containing `{0,1}` and disjoint from non-trivial zeros | `weil-compo.tex:2072-2085`; `ConnesWeilRH/Basic.lean:199-204`; `docs/proofs/cc20-rh-exit-object-normalization-discharge.md` | `SourceFiniteSetAdmissibility` tied to the source zero predicate | the finite-vanishing criterion can be applied with an invalid finite set or the wrong zero predicate |
| `FiniteVanishingCriterionPackage.criterion` | CC20 finite-vanishing Weil-positivity criterion plus source-RH-to-Mathlib-RH transport | `weil-compo.tex:2072-2085`; `ConnesWeilRH/Source/CC20.lean:45-54`; `docs/proofs/cc20-rh-exit-object-normalization-discharge.md`; `docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md` | `SourceFiniteVanishingCriterionToMathlibRH` through Proposition C.1, sign bridge, Mellin bridge, and Mathlib RH definition bridge | the route may conclude a source-named RH statement without proving Mathlib RH |

The trace-legality spine package strengthens the trace rows:

```text
docs/proofs/cc20-analytic-trace-legality-spine-discharge.md
docs/proofs/cc20-analytic-trace-legality-theorem-contract.md
```

It requires Hilbert-Schmidt, trace-class, cyclicity, positive trace,
support-square trace, and no-defect read-off to appear in that order before
the CCM25 Weil-form read-off.

The theorem contract further splits those stages into operator identity,
Hilbert-Schmidt, trace-class square, ordinary-trace equality, per-move
cyclicity, support-square read-off, no-defect read-off, and bounded-comparison
trace-ideal transport targets.

## RH Definition Bridge

The final theorem must conclude Mathlib's canonical predicate:

```text
_root_.RiemannHypothesis
```

Mathlib defines it through:

```text
riemannZeta s = 0
not exists n, s = -2 * (n + 1)
s != 1
s.re = 1/2
```

Evidence:

```text
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:165-168
docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md
```

The final exit therefore needs three definition bridges:

| bridge | target |
|---|---|
| `SourceZetaEqualsMathlibZeta` | source zeta is Mathlib `riemannZeta` |
| `SourceNontrivialZeroIffMathlibZeroWithExclusions` | source non-trivial zero equals Mathlib zero plus negative-even and pole exclusions |
| `SourceCriticalLineIffReEqHalf` | source critical line equals `s.re = 1/2` |

The RH definition-bridge spine package strengthens these rows:

```text
docs/proofs/rh-definition-bridge-spine-discharge.md
docs/proofs/rh-definition-bridge-theorem-contract.md
```

It keeps the Mathlib zero equation, negative-even exclusion, pole exclusion at
`s=1`, and critical-line equation as separate theorem targets before the source
RH conclusion is transported.

The theorem contract further splits the bridge into source zeta equality,
source-to-Mathlib zero transport, Mathlib-to-source zero transport,
negative-even exclusion, pole exclusion, source non-trivial-zero construction
from Mathlib hypotheses, critical-line equivalence, and forward/reverse RH
transport.

Without these bridges, a theorem can prove "RH" in source notation while the
Lean target remains unproved.

## Replacement Order

The next Lean phase should replace symbolic fields in this order, after the
mathematical packages are kept stable:

```text
0. source-definition spine tying the downstream source objects together
     |
     v
1. common test object and convolution square
     |
     v
2. CCM25 QW / Psi / QW_lambda / finite-prime definitions
     |
     v
3. CC20 trace object, trace-class gates, and sign conventions
     |
     v
4. CCM24 support window, bounded comparison, and Sonin exhaustion objects
     |
     v
5. CC20 finite-vanishing criterion and Mathlib RH definition bridge
```

This order fixes the normalization spine before moving support and trace
legality around it.

## Current Judgment

| question | answer |
|---|---|
| Does the current route name the source-interface obligations? | yes |
| Does every source-interface row have a proof package? | yes |
| Do the symbolic records define the source objects themselves? | no |
| Can certification proceed with `TestFunction := Type` and opaque symbol fields? | no |
| Is this ledger a proof of RH? | no |

The next certification milestone is not another route composition theorem. It
is a source-object replacement pass: every row above must become either a
concrete definition with theorem proofs, or an imported source theorem with an
audited bridge to the exact Lean object.
