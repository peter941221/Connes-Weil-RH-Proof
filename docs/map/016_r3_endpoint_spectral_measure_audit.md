# 016 — R3 endpoint spectral-measure audit

**Date:** 2026-09-14.

**Status:** supporting audit and contract clarification. It creates no new route, proves no analytic estimate, and does not claim RH.

**Consumer:** the healthy-`CompactLog`, B5-shaped conclusion `0 <= C1SameOwnerWeil.qw g` for the exact tower-selected detector, followed by the existing same-owner contradiction and `SourceRH` wrapper.

## 1. Question and audit verdict

The brainstorm proposed avoiding a uniform Friedrichs-angle gap by using the detector as a weight at the spectral endpoint of the doubled-shift two-projection product. Write:

```text
T_b = p_b q p_b,       r_b = projection onto Ran(p_b) intersect Ran(q),
D = C† C.
```

The audit verdict is **SUBSUMED, NOT A NEW CANDIDATE**. This is exactly the angle-free, detector-weighted alternating-projection/resolvent mechanism already registered in [015](015_r3_weighted_two_projection_trace_bridge.md), sections 3--4. A second audit correction matters: record 1434 needs strong convergence plus a Hilbert--Schmidt detector-root sum, not an endpoint spectral-measure estimate. Thus the first missing theorem is the classical alternating-projection strong-limit theorem; spectral-measure integrability is only needed by a later trace-norm summation proof.

Evidence is formal for the finite-stage/projection facts cited below; the new spectral-measure formulation is a project candidate only. The first missing theorem was the classical alternating-projection strong-limit theorem; record 1450 now formalizes it on the actual carrier. Spectral-measure integrability is only needed by a later trace-norm summation proof.

## 2. The actual missing theorems

The immediate strong-limit target is the von Neumann alternating-projection theorem specialized to the actual two projections:

```text
(p_b q p_b)^n v -> r_b v     for every carrier vector v.
```

It has no uniform angle-gap hypothesis. Records 1436--1449 supply the
algebraic fixing, fixed-space, defect-energy, and strong-to-Hilbert--Schmidt
ledgers. Record 1450 now proves the displayed strong limit on the actual
`finiteSCarrier`, using the self-adjoint dense-range identity for `T_b - I`
and the already-formal asymptotic regularity. Once the exact detector-root
Hilbert--Schmidt sum is supplied, record 1434 turns this strong limit into the
weighted square-energy limit.

Let `E_b` be the spectral resolution of the positive contraction `T_b` on the orthogonal complement of `Ran(r_b)`. A stronger endpoint theorem may make the detector-weighted mass near `1` integrable with the singular weight required by a trace-norm telescoping or resolvent identity. Its paper-level shape is:

```text
integral_[0,1) w(t) d tr(C E_b(dt) C†) < infinity.
```

Here `w(t)` is derived from the chosen proof, rather than guessed in advance. For example, summing squared alternating-projection errors produces a `1 / (1 - t^2)`-type endpoint weight, whereas a trace-norm telescoping argument can require a stronger weight. The proof must derive the exact weight and then prove the corresponding estimate on the actual source-owned factors.

This is a possible later strengthening of the existing 015 targets:

```text
(T_b^n - r_b) C -> 0 in the required weighted trace/Hilbert--Schmidt sense,
or the equivalent resolvent estimate at spectral value 1.
```

It may use raw orbit geometry, support, convolution, the exact Sonin and Hardy projections, and the canonical finite-prime owner. It may not use a `qw` sign, `SourceRH`, healthy-detector data, an all-tests gate, or an external trace-formula dictionary.

## 3. What the audit rules out

### 3.1 No uniform spectral gap

The assertion `||T_b - r_b|| < 1` is only a conditional bridge in batch 1435. It is not an available premise. Near-extremal prolate directions make a uniform angle gap an unsuitable default target. A proof that silently replaces endpoint-weighted integrability by this gap does not advance R3.

### 3.2 No new Hankel route

The half-line Hankel/Schatten-1 mechanism is already R3-SC1 in [013](013_r3_sonin_detector_commutator_cancellation.md): its compact-smooth corner model passed on paper, while the moving-scale Hardy/Sonin correction is still open. Calling that correction a new Wiener--Hopf or Hankel estimate does not provide a novelty delta. It counts only if it proves the exact source-owned weighted endpoint estimate in section 2.

### 3.3 No free prolate asymptotic

The P1 ledger already reduces both metric and radial channels to one full-carrier antiresonant column-energy premise. Records 1327--1328 in [006](006_new_math_creation_workflow.md) identify that premise as the Hilbert--Schmidt/asymptotic-antiperiodicity analytic gate and supply all conditional constants. Therefore a claimed prolate transition law is new only if it proves that named premise, or a theorem that implies the spectral-measure condition above with the exact required weight.

### 3.4 No untyped cancellation claim

Finite cutoff traces, the canonical finite-prime family, and the P2 residual ledger are already formal. A proposed do-the-cancellation-before-the-limit proof must state a same-owner finite identity whose remainder is strictly smaller than the current P1/P2 remainder. Otherwise it merely renames the existing ledger. It must not import the external `Q` dictionary; record 1415 classifies that identification as a definitions/citation claim, not an internal machine fact.

## 4. Next admissible paper tasks

The first task, a source-faithful formalization of the classical two-projection
strong-limit theorem on the actual `finiteSCarrier`, is now closed by record
1450 without invoking an operator-norm gap. Record 1438 still supplies the
lower-data energy ledger: every alternating power is contractive, the norm
orbit is antitone, and it converges to its explicit `ciInf` endpoint. The
one-step Pythagorean identity and finite defect budget remain the audit trail
for asymptotic regularity, but they are no longer the existence premise for
the actual power limit.

Record 1439 closes the finite-stage budget: for every radial vector and every
`n`, the sum of the first `n` defect energies equals the initial norm-square
minus the norm-square of the `n`th alternating iterate. The remaining gap is
now explicitly an infinite-stage exhaustion statement, not an untracked
finite algebra remainder. The paired formal leaf also proves the individual
defect energy tends to zero because the nonnegative defect series is
summable; this still does not identify the vector limit or the intersection
projection. Its two orthogonal component energies separately tend to zero by
the order squeeze, giving asymptotic regularity without a spectral gap.

Record 1440 pushes this one step further: the orthogonal-complement identity
and the triangle inequality bound the adjacent-iterate residual by the two
component defect norms. Therefore `||T_b^(n+1) v - T_b^n v|| -> 0` for every
radial input. Record 1450 consumes this asymptotic regularity together with
self-adjointness and the dense range of `T_b - I`, closing the actual no-gap
strong limit.

Record 1441 closes the endpoint-identification half conditionally: if the
power orbit has any strong limit, shifted-limit uniqueness makes it a fixed
vector, the fixed-space theorem puts it in the doubled-shift intersection,
and the identity `r_b T_b^n = r_b` identifies it with `r_b v`. Record 1450
now supplies the missing existence theorem for the actual operator.

Record 1442 adds the Fejér ledger: distance to every intersection vector is
antitone along the orbit and has an explicit `ciInf` limit. It remains a useful
scalar audit of the 1450 limit, but its zero-infimum condition is no longer a
separate existence premise for the actual operator.

Record 1443 gives the exact same-owner energy identity
`||T_b^n v - r_b v||^2 = ||T_b^n v||^2 - ||r_b v||^2`. Consequently the
endpoint exhaustion has an exact scalar audit form
`ciInf_n ||T_b^n v|| = ||r_b v||`; no vector-limit ambiguity remains.

Record 1444 closes the automatic lower side of this scalar comparison:
`||r_b v|| <= ciInf_n ||T_b^n v||` follows from projection contractivity at
every finite stage. The live analytic target is now the reverse inequality,
not a missing projection identity or an unspecified convergence premise.

Record 1445 closes the reverse consumer conditionally: if the squared norm of
the power orbit tends to `||r_b v||^2`, scalar limit uniqueness gives
`ciInf_n ||T_b^n v|| <= ||r_b v||`. The remaining analytic bone is therefore
the single squared-norm exhaustion statement.

Record 1446 reduces that statement to the finite-stage defect ledger: the
`tsum` equality `sum'_k defect(T_b^k v) = ||v||^2 - ||r_b v||^2` implies the
squared-norm endpoint. Before 1450 this was the explicit existence bone; it is
now retained as an audit-equivalent formulation.

Record 1447 proves the reverse implication too. The defect-series exhaustion
condition is equivalent to the scalar endpoint equality
`ciInf_n ||T_b^n v|| = ||r_b v||`; this remains the exact scalar audit form of
the already-closed no-gap limit.

Record 1448 identifies that scalar formulation with the actual strong endpoint:
the defect-series equality holds iff `T_b^n v` converges strongly to `r_b v`.
Record 1450 provides that convergence by an independent dense-range argument,
so no defect-series equality is assumed as a hidden premise.

Record 1449 connects that endpoint to the detector-root Hilbert–Schmidt
transfer. With the 1450 strong limit in hand, the remaining conditional input
is the exact square-summability of the detector-root factor columns. The live
trace target is that square-sum plus the same-basis trace/readback, not an
additional convergence theorem.

The second task is a one-object paper audit for the Hilbert--Schmidt factor.
Record 1451 resolves its first typed subcase: the raw convolution root is not
the HS object, while the unit-scale prolate-range completed leg is formally
square-summable and feeds the strong-limit energy consumer. The full factor
still has independent leakage and common-right legs.
Record 1452 gives the leakage leg the exact same-carrier doubled-shift normal
form `p_b - T_b`; this does not change its open status as an HS/trace estimate.

The remaining audit is:

1. Identify the remaining exact factors in the 1434 application and prove or refute their Hilbert--Schmidt square sums from raw orbit geometry.
2. Compare that sum with the existing full-carrier antiresonant column energy; do not assume they coincide merely because both are Hilbert--Schmidt conditions.
3. Only if a trace-norm summation remains after the strong-to-HS transfer, choose the alternating-power or resolvent identity, derive its exact endpoint weight `w`, and repeat the comparison in step 2.
4. Register a new candidate under map 006 only after F8/F20 searches, a source-owned falsifier, and a novelty check against the spent-class ledger.

These tasks are falsifiable on paper: if the exact 1434 factor lacks a Hilbert--Schmidt sum, the present strong-to-HS route is not a producer; if a later endpoint weight is stronger than available detector smoothing, the trace-norm version is not a producer. No numerical scan is authorized by this record.

## 5. Route status

```text
T1 subspace and projection transport                 FORMAL
two-sided fixing of the intersection projection      FORMAL
fixed-space identification for p_b q p_b             FORMAL
contraction and scalar energy monotonicity            FORMAL
finite endpoint and strong-to-HS transfer            FORMAL
angle-free strong power limit on actual carrier      FORMAL
weighted endpoint spectral-measure estimate           OPEN
unit-scale prolate-range detector leg                 FORMAL
leakage/common-right detector legs                    OPEN
same-basis trace witness and G8 cutoff reconnection   OPEN
G8SameOwnerReadbackData and RH                        OPEN / not claimed
```

The binding route remains record 003. ROOT-window certificates, universal B1 work, scale changes of the test, and a category-change Arakelov bridge are not reopened by this audit.
