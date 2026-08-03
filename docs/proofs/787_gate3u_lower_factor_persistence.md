# Proof 787: Gate 3U lower-factor persistence

## Result

This result is structurally decisive, but it does not close Gate 3U.
The raw finite-S target and the normalized physical response are related by
an exact positive scalar.  Write

```text
c_S = finiteEulerLowerFactor(S.visiblePrimes) > 0,
r_S = Re Tr(sourceBandGramResponse_S),
n_S = Re Tr(normalizedSourceBandGramResponse_S).
```

Lean proves

```text
n_S = c_S^2 r_S.                                      (787.1)

|r_S| <= B
  iff
|n_S| <= c_S^2 B.                                    (787.2)
```

For the canonical selected family, the exact consumer is

```text
|n_S| <= c_S^2 B
  -> canonicalRealGate3UAt(owner, B).                (787.3)
```

The raw Gate target is already the negative conjugate of `r_S`; this is the
existing `ordinaryTraceAlong_targetCommutator_eq_neg_star_sourceBand` identity.
Thus the completed Hardy--prolate physical rewrite does not make the scalar
`c_S^-2` disappear.  It only changes the correct signed operator owner that
must establish the decay in `(787.2)`.

## What It Is

```text
raw target trace r_S
        |
        | multiply by c_S^2
        v
normalized trace n_S
        |
        | Gate 3U requires inverse implication at the same rate
        v
required physical producer: |n_S| <= c_S^2 B
```

The normalized endpoint estimate already available in the repository is only

```text
|n_S| <= O_support(1).
```

Equation `(787.2)` shows why that estimate cannot be divided back to a
family-uniform raw bound when `c_S` may be small.

## Why It Matters

The lower factor is not removed by a notation change, a trace-order reversal,
or the completed outer/reflected-second-support/prolate representation.
The target/source trace identity fixes the raw scalar, and the normalization
has an exact cost:

```text
uniform normalized trace bound
        does not imply
raw Gate 3U bound

lower-factor-square normalized decay
        does imply
raw Gate 3U bound.
```

This replaces an ambiguous cancellation request with one concrete analytic
statement.  Any successful compact-root estimate must keep the full signed
physical kernel together and prove the stronger `c_S^2` decay before the first
absolute value.  A branchwise trace norm, Hilbert--Schmidt product, or
triangle inequality still cannot provide that producer.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSGatePhysicalLowerFactorPersistence.lean

ConnesWeilRH/Dev/
  CCM24FiniteSGatePhysicalLowerFactorPersistenceAudit.lean
```

The audited declarations are:

```text
normalizedSourceBandGramRealTrace_eq_lowerFactorSq_mul_raw
sourceBandGramRealTrace_bound_iff_normalized_lowerFactorSq_decay
canonicalRealGate3UAt_of_normalizedSourceBandRealTrace_decay
```

They use the existing exact raw/normalized trace identity from
`CCM24FiniteSRawEndpointSupportBound.lean` and the existing target/source
trace identity from `CCM24FiniteSCanonicalRealGate.lean`; no new analytic
assumption is introduced.

## Verification

The Ubuntu-24.04 WSL2 ext4 verification batch passed:

```text
+------------------------------------------------------+-------+--------+
| target                                               | jobs  | result |
+------------------------------------------------------+-------+--------+
| Proof 787 source Lake build                          |  3403 | PASS   |
| Proof 787 focused axiom audit                        |    -- | PASS   |
| CCM25Concrete aggregate                              |  4045 | PASS   |
| full repository                                      |  4126 | PASS   |
+------------------------------------------------------+-------+--------+
```

All three audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, or user axiom
was added.

## Scope

```text
+--------------------------------------------------------------+----------------+
| statement                                                    | status         |
+--------------------------------------------------------------+----------------+
| raw/normalized real-trace scaling                            | Lean proved    |
| exact c_S^2 decay contract for the raw Gate                  | Lean proved    |
| uniform O(1) normalized endpoint estimate                    | existing       |
| source-specific c_S^2 completed physical decay               | open           |
| support-polynomial Gate 3U / finite-S sign / Burnol / RH     | open           |
+--------------------------------------------------------------+----------------+
```

Proof 787 does not prove a uniform `c_S^2` decay theorem, Gate 3U, the
finite-S sign, Burnol's identity, or `_root_.RiemannHypothesis`.
