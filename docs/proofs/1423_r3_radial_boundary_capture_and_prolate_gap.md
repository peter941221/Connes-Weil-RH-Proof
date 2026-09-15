# 1423 - R3 radial-boundary capture and prolate-gap reduction

Date: 2026-09-14.

Status: `PARTIALLY FORMAL / PRODUCER OPEN`. This record refines the R3-F1
correction. The two-channel operator identity is now formal in Lean (proof
record 1494); the finite-width support identification and both trace-ideal
estimates remain open. It does not claim that F0 or RH is complete.

Consumer: the same-owner healthy-`CompactLog` B5 statement
`0 <= C1SameOwnerWeil.qw g`.

## 1. Exact algebraic split

Write

```text
P = sourceSoninProjection lambda
E = radialSupportProjection lambda
J = sourceInclusion lambda.
```

The committed source geometry gives `P E = P` and `E P = P`, because the
Sonin subspace is the intersection of the radial and Hardy-support subspaces.
For every bounded ambient operator `B`, the leakage factor has the exact
identity

```text
(I - P) B J
  = (I - E) B J + (E - P) E B J.                 (RB)
```

The proof is only cancellation:

```text
(I-E)BJ + (E-P)EBJ
  = BJ - EBJ + EBJ - PEBJ
  = BJ - PBJ,
```

using `P E = P`.  No sign, detector property, or RH premise occurs.

This is the correct refinement of record 1422's two-channel split. It
separates an actual geometric boundary from the internal failure of the two
support projections to coincide. The generic identity and its specialization
to the selected root convolution and actual source inclusion are formally
proved in `C1G8R3RadialBoundaryGapSplit.lean`, theorem
`selectedRoot_sourceSoninLeakage_eq_radialBoundary_add_internalGap`; see
[proof record 1494](1494_r3_radial_boundary_internal_gap_split.md).

## 2. Channel B: radial boundary capture

Take `B` to be the global root convolution by a compactly supported kernel
`k`, with support radius `R`, and take the radial boundary at `A = log(lambda)`.
For `u` in the radial support, the output of `(I-E) B J u` is supported below
`A`.  Because `k(t-s)` vanishes unless `|t-s| <= R`, only

```text
input  s in [A, A + R]
output t in [A - R, A]
```

can contribute.  Thus the apparently infinite ambient boundary channel is in
fact a finite rectangle in the `(t,s)` plane.  Its kernel is square
integrable, and the corresponding operator is Hilbert--Schmidt.

The repository already contains the exact finite-window ingredients:

```text
fullBoundaryRootKernel
fullBoundaryRootFactor
fullBoundaryRootFactor_eq_globalConvolution
pairData_traceProduct_eq_orientedBoundaryCrossing
```

in `CC20Concrete/CompactRootHalfLinePair.lean:133-1417`.  The missing theorem
is not a new global convolution estimate.  It is a support-identification
lemma showing that the global radial crossing equals one of these finite
boundary factors after translating the boundary from `0` to `A`.

The target is therefore:

```text
RB-boundary:
  (I-E) B J = finiteBoundaryFactor(A,R) J,
  and finiteBoundaryFactor(A,R) is Hilbert--Schmidt.
```

This is a sharply typed, lower-data target.  It uses only compact support of
the selected test and the existing boundary-kernel owner.

## 3. Channel K: internal prolate gap

After the radial boundary is removed, the remaining term is

```text
K_gap = (E - P) E B J.                         (K)
```

This is not a generic ambient tail.  It is the part of `E B J` lying in the
radial half-line but outside the complete Sonin intersection.  The committed
source already names the relevant positive operator:

```text
sourceProlateRemainder lambda
  = E Q E - P,
```

and proves its factorization as a positive gap operator.  Consequently the
remaining F0 task can be stated as a prolate-gap energy estimate for `K_gap`,
rather than an unstructured estimate on `B_infinity J`.

The exact desired bound is one of:

```text
sum_k || G_S^(1/2) K_gap (e_k) ||^2 < infinity,
```

or a factorization of `K_gap` through the square root of
`sourceProlateRemainder lambda` with a Hilbert--Schmidt other factor.

The latter is the preferred new-mathematics form, because it exposes the
only genuinely two-sided obstruction.  A proof that merely bounds `K_gap` in
operator norm is insufficient for F0.

## 4. Why this is stronger than the earlier plan

The original F0 wording treated the full global source leg as one unknown
object.  The identity (RB) now gives a decision tree:

```text
global source leakage
  -> finite radial boundary crossing       [compact-kernel HS candidate]
  -> internal prolate gap                   [single remaining analytic gate]
```

The first branch is geometrically finite and has a committed kernel owner.
The second branch is exactly the source's two-support mismatch and cannot be
hidden inside a generic “convergence assumption”.

This also makes a clean falsifier possible.  If the finite radial crossing
is proved Hilbert--Schmidt but the prolate-gap columns have a non-summable
lower energy on an orthonormal source sequence, then F0 fails for the current
ordinary-trace G8 route.  Conversely, a trace-ideal estimate for `K_gap`
would complete the only newly exposed source-leakage channel.

## 5. Status

```text
1421 pointwise Sonin antiresonance       valid paper lemma
1422 direct F0 interpretation             rejected by interface audit
1494 generic and selected-root split       FORMAL
1423 finite-width radial support identity OPEN
1423 prolate-gap trace estimate           OPEN, decisive
F0 Hilbert--Schmidt limit                OPEN
G8SameOwnerReadbackData                  NOT CONSTRUCTED
RH                                      NOT CLAIMED
```

The next implementation target is the translation/support identity for the
radial boundary factor.  Only after that identity builds should effort be
spent on the prolate-gap Hilbert--Schmidt estimate.
