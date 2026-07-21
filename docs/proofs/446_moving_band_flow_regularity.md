# Proof 446: Moving-band flow regularity

Date: 2026-07-20

## Result

Proof 445's explicit interval-integrability witness is now produced from the
actual parameterized Euler and Gram calculus.  The new source module is:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSMovingBandFlowRegularity.lean
```

The central chain is:

```text
Euler product derivative + legal inverse
  -> additive Euler generator continuous on [-1,1]
  -> canonical Gram projection continuous
  -> root-smoothed orthogonal flow continuous
  -> IntervalIntegrable on [0,1]
  -> endpoint integral theorem without an external regularity premise.
```

The resulting theorem is:

```lean
integral_actualMovingSoninRootFlow_eq_neg_bandResponse
```

It proves the same endpoint identity as Proof 445, but no longer takes
`IntervalIntegrable` as an argument.

## Why this is sufficient

The endpoint integral in Proof 445 needed Bochner interval integrability of an
operator-valued flow.  A continuous map from a compact real interval into the
Banach space of bounded operators is interval integrable.  The new module
therefore proves continuity of every moving component on the larger legal
interval `[-1,1]`, restricts it to `uIcc 0 1`, and applies Mathlib's
`ContinuousOn.intervalIntegrable` theorem.

No trace cycle, finite-dimensional approximation, or positivity premise is
used in this step.  In particular, the proof does not estimate the flow after
splitting its completed physical branches.

## What remains open

This closes only the regularity/endpoint ownership layer.  It does not bound
the integrated signed Sonin crossing uniformly in the canonical family.  Gate
3U, the finite-S sign, Burnol's identity, and `_root_.RiemannHypothesis` remain
open.

The focused audit is:

```text
ConnesWeilRH/Dev/
  CCM24FiniteSMovingBandFlowRegularityAudit.lean
```

## Verification

The Windows sources were copied one way into the cache-bearing Ubuntu 24.04
ext4 verification mirror.  The acceptance batch passed:

```text
+------------------------------------------------------+-------+--------+
| target                                               | jobs  | result |
+------------------------------------------------------+-------+--------+
| moving-band flow regularity source build             |  3210 | PASS   |
| CCM25Concrete aggregate                              |  3721 | PASS   |
| full repository / default lake build                 |  3802 | PASS   |
+------------------------------------------------------+-------+--------+
```

The focused audit prints exactly

```text
[propext, Classical.choice, Quot.sound]
```

for `continuousOn_actualMovingSoninRootFlow`,
`intervalIntegrable_actualMovingSoninRootFlow`, and
`integral_actualMovingSoninRootFlow_eq_neg_bandResponse`.
