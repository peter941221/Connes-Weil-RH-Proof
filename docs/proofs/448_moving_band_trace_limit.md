# Proof 448: Moving-band trace limit without infinite exchange

Date: 2026-07-20

## Result

Proof 448 closes the correct limiting principle after Proof 447.  Let
`basis` be any Hilbert basis of the actual finite-S carrier.  If the endpoint
diagonal is summable and every finite diagonal signed integral is bounded by
the same real constant `C`, then Lean proves

```text
|Re ordinaryTraceAlong(basis, rootSandwichedBandResponse)| <= C.
```

The central theorem is:

```lean
ordinaryTraceAlong_re_abs_le_of_finiteDiagonalIntegralBound
```

Its proof takes the finite-set net of partial sums from `Summable.hasSum`,
maps that net through the continuous absolute-value function, and applies the
closed-order limit lemma.  It never exchanges an infinite sum with the time
integral.

## Canonical route form

For `canonicalFamily owner`, the module specializes `C` to the existing
support-radius polynomial:

```text
2 * (owner.supportRadius + log 3)
  * (1 + owner.supportRadius + log 3).
```

The resulting theorem is:

```lean
canonicalOrdinaryTraceAlong_re_abs_le_supportRadiusPolynomial_of_finiteDiagonalBound
```

The remaining premises are genuine route inputs:

```text
actual canonical endpoint diagonal is trace-class
  + every finite canonical signed diagonal integral obeys the polynomial bound
  -> full canonical ordinary-trace bound.
```

The first premise is not inferred from compactness or from finite sections.
The second premise is the actual signed Gate 3U producer.  Diagonal Euler
energy is not substituted for it.

## Why this matters

This removes an unnecessary and potentially dangerous requirement to dominate
the time-dependent diagonal series absolutely before integrating.  The route
only needs uniform control of the finite signed partial sums, followed by the
already explicit endpoint summability witness.  The distinction is:

```text
forbidden shortcut:  exchange tsum and integral, then bound total variation;
valid route:         bound every finite signed integral, then take the endpoint
                     tsum limit.
```

No finite-matrix approximation is used, and no infinite-dimensional trace
cycle is introduced.

## Verification

The Windows sources were copied one way into the cache-bearing Ubuntu 24.04
ext4 verification mirror.  The acceptance batch passed:

```text
+------------------------------------------------------+-------+--------+
| target                                               | jobs  | result |
+------------------------------------------------------+-------+--------+
| moving-band trace-limit source build                 |  3281 | PASS   |
| CCM25Concrete aggregate                              |  3723 | PASS   |
| full repository / default lake build                 |  3804 | PASS   |
+------------------------------------------------------+-------+--------+
```

The focused audit prints exactly

```text
[propext, Classical.choice, Quot.sound]
```

for both the generic trace-limit theorem and its canonical-family
specialization.

## Remaining boundary

The actual same-carrier endpoint trace-class producer and the uniform finite
canonical signed diagonal estimate remain open.  Gate 3U, the finite-S sign,
negative-owner integration, Burnol's identity, and `_root_.RiemannHypothesis`
remain open.

The focused audit is:

```text
ConnesWeilRH/Dev/
  CCM24FiniteSMovingBandTraceLimitAudit.lean
```
