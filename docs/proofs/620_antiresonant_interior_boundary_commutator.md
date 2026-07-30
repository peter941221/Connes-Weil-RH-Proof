# Proof 620: antiresonant interior boundary commutator

## Result

The result is good as an exact physical expansion and incomplete as a Bone 1
estimate.

Let

```text
E   = radialSupportProjection,
D   = detectorOperator,
N_p = normalizedPrimeEulerInverse(p),
A_p = E N_p^dagger E,
R   = sourceSoninProjection.
```

The selected detector commutes with `N_p` and `N_p^dagger`.  Lean therefore
proves the exact radial compression identity

```text
[E D E, A_p]
  = E[D,E]N_p^dagger E
    + E N_p^dagger[D,E]E.
```

Both outer-boundary orientations remain signed.  No norm is taken.

## Corrected quotient owner

The genuine corrected quotient bracket is

```text
Q_p = -A_p [E D E,R] + [E D E,A_p].
```

Using the actual source projection identity

```text
R = E Q_fourier E - K_prol,
```

Lean expands the same `Q_p` into the complete physical ledger

```text
-A_p * (
    outer radial boundary
  + second Fourier-support boundary
  + reflected outer boundary
  - prolate commutator)

+ left quotient-compression radial correction
+ right quotient-compression radial correction.
```

The final theorem is

```text
primeEulerRadialCorrectedQuotientBracket
  = primeEulerRadialCorrectedPhysicalBracket.
```

This reuses the carrier-independent theorem
`correctedQuotientBracket_eq_physical`; the concrete work is the genuine
detector/Euler commutation and the actual CCM24 projection identities.

## Boundary

```text
+--------------------------------------+-----------------------------------+
| object                               | status                            |
+--------------------------------------+-----------------------------------+
| radial commutator [EDE,A_p]          | exact two-boundary identity       |
| corrected quotient bracket Q_p      | exact complete physical ledger    |
| suffix parameter S                   | absent from Q_p                   |
| actual source Interior_(p,S)         | not identified with Q_p           |
| family-uniform bound                 | open                              |
| Bone 1 / Gate 3U / RH                | open / open / open                |
+--------------------------------------+-----------------------------------+
```

The carrier and suffix mismatch is decisive.  `Q_p` is a global-carrier
operator depending on `(lambda,p)`.  The actual interior owner is a
source-carrier operator depending on `(lambda,p,S)` and retains the actual
endpoint/forward coframes.  Proof 620 does not equate them.

## Files

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBoundaryCommutator.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBoundaryCommutatorAudit.lean
```

## Verification

The shared Proof 620/621 acceptance batch passes in the Ubuntu-24.04 WSL2
ext4 mirror:

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| six focused source/audit targets     |  3391 | PASS   |
| CCM25Concrete aggregate              |  3891 | PASS   |
| full repository                      |  3972 | PASS   |
+--------------------------------------+-------+--------+
```

Every audited declaration uses exactly
`[propext, Classical.choice, Quot.sound]`.
