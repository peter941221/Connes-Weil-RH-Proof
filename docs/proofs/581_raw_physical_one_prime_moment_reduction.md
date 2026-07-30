# Proof 581: raw physical one-prime moment reduction

## Result

This batch makes the first source-specific reduction after the old-carrier
quotient guard.  At the empty suffix, the exact raw physical row is

```text
R0(p, []) = - T(p, [])^dagger * M(p) * F_old(p, [])^dagger,
```

where `T` is the forward Schur transition and `M(p)` is the signed boundary
moment of the first nontrivial forward coframe.

The Schur--Markov reverse transition `U(p, [])` satisfies

```text
T(p, []) * U(p, []) = rho_p * I,
rho_p = (1 - p^(-1/2)) / (1 + p^(-1/2)).
```

Taking adjoints gives the exact cancellation

```text
rho_p^(-1) * U(p, [])^dagger * T(p, [])^dagger = I.
```

Therefore any bounded old-carrier readout for the actual raw row produces a
bounded readout for the one-prime boundary moment:

```text
Q * W(p, []) = R0(p, [])
        |
        v
Q_p * W(p, []) = M(p) * F_old(p, [])^dagger,
Q_p = -rho_p^(-1) * U(p, [])^dagger * Q.
```

Since the reverse transition is contractive,

```text
||Q_p|| <= ||rho_p^(-1)|| * ||Q||.
```

## Why this matters

The remaining bone-1 obligation is a genuine bounded quotient on the actual
old-carrier analysis.  Proof 581 shows that this obligation already contains
the one-prime boundary moment as a necessary factorization.  A proof of the
moment factorization, or an obstruction to it, is now a source-specific target
with the same carrier and a transparent normalization cost.

The dependency is:

```text
 +-------------------------------+
 | old-carrier raw quotient      |
 | R0 = Q * W                    |
 +---------------+---------------+
                 |
                 v
 +-------------------------------+
 | empty-suffix row identity     |
 | R0 = -T^dagger * M * F_old^dagger |
 +---------------+---------------+
                 |
                 v
 +-------------------------------+
 | reverse Markov cancellation   |
 | rho^-1 U^dagger T^dagger = I |
 +---------------+---------------+
                 |
                 v
 +-------------------------------+
 | one-prime moment quotient     |
 | Q_p * W = M * F_old^dagger   |
 +-------------------------------+
```

This is a necessary-condition reduction only.  It does not construct `Q` or
`Q_p`, prove a uniform moment estimate, prove Gate 3U, establish the finite-S
sign, identify Burnol's identity, or prove RH.

## Lean owners

Source:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentReduction.lean
```

Audit:

```text
ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentReductionAudit.lean
```

The source file contains no `sorry`, `admit`, or user axiom declaration.

## Verification

The Windows source was copied to an Ubuntu-24.04 WSL2 ext4 mirror.

The final Ubuntu-24.04 WSL2 ext4 batch passed:

```text
focused source build: 3337 jobs, PASS
focused audit: 3338 jobs, PASS
CCM25Concrete aggregate: 3848 jobs, PASS
full repository build: 3929 jobs, PASS
git diff --check: PASS
```

All six audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.  The WSL localhost-proxy warning
and existing repository linter warnings are environmental or pre-existing.
