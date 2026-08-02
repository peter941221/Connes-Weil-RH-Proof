# Proof 699: Fixed-Source Dense-Range Kernel Bridge

## What is established

For a Hilbert--Schmidt pair with common source carrier, the canonical input is

```text
A = (left† left + right† right)^(1/2).
```

The new source theorems prove the exact zero-set identity

```text
A x = 0  <->  left x = 0 and right x = 0.
```

Consequently, if the two physical legs have no common kernel, then `A` is
injective.  Since `A` is self-adjoint, the generic theorem that an injective
Hilbert-space operator has dense adjoint range transfers to

```text
DenseRange A.
```

The fixed-source specialization applies this to
`fixedPhysicalSourceInput`, whose two legs are the actual source three-branch
physical pair after source-carrier precomposition.

## Why the condition remains explicit

The existing physical owner proves energy summability and positivity, but it
does not prove that the outer, reflected, second-support, and prolate branches
have no common null vector.  Energy summability is a trace-class statement;
it does not imply injectivity or dense range.

The remaining source obligation is therefore exactly:

```text
forall x,
  fixedPair.left x = 0 -> fixedPair.right x = 0 -> x = 0.
```

Once that producer exists, Proof 698 can cancel the common
`fixedPhysicalSourceInput` composition in the completed-history endpoint
readout.  No Gate 3U estimate, finite-S sign, Burnol identity, or RH theorem
follows from this bridge alone.

## Verification target

The import-facing audit is
`CCM24FiniteSFixedPhysicalSourceInputDenseRangeAudit.lean`.  It audits the
zero-set, injectivity, and fixed-source dense-range declarations.  The
expected axiom set remains

```text
[propext, Classical.choice, Quot.sound]
```
