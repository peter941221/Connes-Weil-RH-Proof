# 1423 - R3 radial-boundary capture and prolate-gap reduction

Date: 2026-09-14.

Status: `PARTIALLY FORMAL / PRODUCER OPEN`. This record refines the R3-F1
correction. The two-channel operator identity is formal in Lean (proof record
1494), and the finite-width boundary support and radial translation identities
are formal in proof record 1495. The boundary and internal-gap trace-ideal
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

can contribute. Thus the apparently infinite ambient boundary channel is in
fact a finite rectangle in the `(t,s)` plane. The formal support and
translation identity is now established in proof record 1495.

The formal finite-window identities are:

```text
selectedRoot_zeroBoundaryCrossing_eq_finiteWindow
selectedRoot_radialSourceLeakage_eq_translatedFiniteWindow
```

The first identifies the zero-boundary positive-to-negative crossing with the
zero extension of the compact-output root factor on `[-R, 0]`. The second
identifies the actual radial crossing, composed with the source inclusion, as
the translate of that same finite-window operator. The proof uses the selected
owner's compact support and the translation covariance of the global root
convolution. See [proof record
1495](1495_r3_radial_boundary_finite_window_identity.md).

The target is therefore:

```text
RB-boundary:
  (I-E) B J = translatedFiniteBoundaryFactor(A,R) T_A J,
  and prove the needed trace-ideal estimate.
```

The identity is formal, but no Hilbert--Schmidt estimate is proved for the
finite-window factor in the actual source basis. This remains a sharply typed,
lower-data target using the selected test's compact support and the existing
boundary-kernel owner.

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

The next implementation target is a source-basis trace-ideal estimate for the
translated finite-window factor, followed by the decisive prolate-gap
Hilbert--Schmidt estimate. The identities alone imply neither bound.
