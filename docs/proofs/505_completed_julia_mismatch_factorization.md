# Proof 505: completed-Julia mismatch factorization

## Result

Proof 505 closes the exact recovery and zero-mode bookkeeping for the
polar/raw mismatch.  It does not prove the family-uniform Douglas estimate,
Gate 3U, the finite-S sign, Burnol's identity, or RH.

```text
+------------------------------------------------------+------------------+
| item                                                 | status           |
+------------------------------------------------------+------------------+
| two-sided defect -> one-sided defect                 | proved           |
| one-sided defect -> two-sided recovery               | proved           |
| adjoint-kernel equivalence                           | proved           |
| co-defect Gram ledger                                | proved           |
| polar boundary zero-mode cancellation                | proved           |
| complete raw/mismatch Douglas domination             | still open       |
| family-uniform Gate 3U bound                         | still open       |
| finite-S sign / Burnol identity / RH                 | still open       |
+------------------------------------------------------+------------------+
```

The Lean owner is

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaMismatchFactorization.lean
```

## Exact recovery

Write

```text
F = suffixEulerFrameTransition p S
R = suffixEulerFrameReverseTransition p S
rho = primeSchurMarkovScalar p
J = F M_S - M_(p::S) F
A = J R.
```

The existing Schur--Markov pairing gives `R F = rho I`.  Since `rho` is
positive, Proof 505 proves

```text
R (rho^-1 F) = I,
A (rho^-1 F) = J.
```

Taking adjoints yields the exact kernel equivalence

```text
A† x = 0  <->  J† x = 0.
```

The reverse transition is contractive, so it can reduce norms, but it cannot
create or remove a zero mode.  No inverse of the Julia co-defect is used.

## Co-defect ledger

For the actual adjacent polar-frame step, Lean specializes the rectangular
Schur identity to

```text
D† D
  = oldFrame† (I - T T†) oldFrame
    + boundary boundary†,
```

where `D` is the canonical left Julia co-defect.  Consequently

```text
D x = 0  ->  boundary† x = 0.
```

The polar detector intertwinement is the completed moving boundary row from
the earlier Schur cascade.  Its adjoint therefore also vanishes on every
`D`-zero mode.

## Remaining physical row

Proof 505 defines one whole raw quadratic intertwinement row:

```text
RawJ = F Raw(S) - Raw(p::S) F.
```

The full mismatch row is exactly

```text
J = PolarJ - RawJ.
```

On a `D`-zero mode, the proved polar cancellation gives

```text
J† x = -RawJ† x.
```

This is a kernel guard, not a license to estimate `PolarJ` and `RawJ`
separately.  The active source obligation remains the single signed raw row
with the first jet, route ordering, and endpoint response already recombined.

## Verification

The focused audit is

```text
ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaMismatchFactorizationAudit.lean
```

Every audited theorem must remain axiom-clean with exactly

```text
[propext, Classical.choice, Quot.sound]
```

The Ubuntu 24.04 WSL2 verification batch passed:

```text
+------------------------------------------+-------+--------+
| target                                   | jobs  | result |
+------------------------------------------+-------+--------+
| Proof 505 source direct Lean check       |   n/a | PASS   |
| Proof 505 focused audit                  |   n/a | PASS   |
| CCM25Concrete aggregate                  |  3782 | PASS   |
| full repository                          |  3863 | PASS   |
+------------------------------------------+-------+--------+
```

The new source and audit contain no `sorry`, `admit`, or user axiom
declaration, and the direct checks emitted no new linter warning.  Existing
repository linter warnings remain unchanged.  No commit, push, PR, issue
comment, or other public outbound action was performed.

The finite-S sign, Gate 3U, Burnol's identity, and
`_root_.RiemannHypothesis` remain open.
