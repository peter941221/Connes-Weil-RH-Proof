# Proof 590: old-carrier spectral-gap obstruction

## Result

The fixed-source column from Proof 584 rules out the uniform spectral-gap
branch of Bone 1 whenever the actual source Sonin carrier contains a nonzero
vector.

For any visible-prime sequence with

```text
q_(p_n) = ccm24PrimeEulerCoefficient(p_n) -> 0,
```

and any `x != 0` in the source carrier, the actual column

```text
y_n = newSuffixFrame lambda [] x
```

satisfies

```text
||W_(p_n) y_n|| -> 0,
||y_n|| = ||x|| > 0.
```

Therefore no positive constant can satisfy

```text
gap * ||y||^2 <= ||W_(p,S) y||^2
```

for every visible prime, suffix, and old-carrier vector.

```text
 +------------------------------+
 | uniform spectral gap for W   |
 +---------------+--------------+
                 |
                 v
 +------------------------------+
 | y_n = newFrame[] x, x != 0   |
 | ||y_n|| = ||x|| > 0          |
 +---------------+--------------+
                 |
                 v
 +------------------------------+
 | ||W_(p_n) y_n|| -> 0          |
 +---------------+--------------+
                 |
                 v
 +------------------------------+
 | contradiction                  |
 +------------------------------+
```

## Boundary

This closes only the spectral-gap adapter from Proof 577.  It does not rule
out a direct source-specific signed quotient

```text
R0 = F * W
```

whose raw row decays on the same approximate columns.  The full Bone 1
producer, Gate 3U, the finite-S sign, Burnol's identity, and RH remain open.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSpectralGapObstruction.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSpectralGapObstructionAudit.lean
```

The audited declarations use only
`[propext, Classical.choice, Quot.sound]`.

## Verification

Verification ran in the Ubuntu-24.04 WSL2 ext4 mirror after synchronizing the
Windows source of truth:

```text
focused source lake build: 3351 jobs, PASS
focused audit: PASS
CCM25Concrete aggregate: 3855 jobs, PASS
full repository build: 3936 jobs, PASS
git diff --check: PASS
```

The WSL localhost-proxy notice and existing repository linter warnings are
environmental or pre-existing.  No `sorry`, `admit`, or user axiom was added.
