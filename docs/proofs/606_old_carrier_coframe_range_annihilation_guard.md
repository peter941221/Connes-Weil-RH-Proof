# Proof 606: Old-Carrier Coframe Range-Annihilation Guard

## Result

The generic range factorization from Proof 602 has an explicit annihilation
premise.  Applied to the complete signed telescope, that premise is not a
generic consequence of boundedness or of the frame projection.  The new Lean
owner proves the exact equivalence

```text
signedTelescope * scalarInverse† * newFrame = 0
  <-> coframeBoundaryMomentGap = 0
  <-> rawPhysicalFourTermRow = 0.
```

The first equivalence uses Proof 603's pullback identity

```text
signedTelescope * scalarInverse† * newFrame
  = rho_p^(-1) * gap * reverseTransition†
```

and the two-sided scalar inverse relations

```text
transition * reverseTransition = rho_p * I
reverseTransition * transition = rho_p * I.
```

Taking adjoints makes `reverseTransition†` cancellable as well.  The second
equivalence is Proof 605's exact identification of the gap with the named raw
physical four-term row.

## Consequence for Bone 1

This closes an interface mistake, not Bone 1.  The range-factor constructor
can still be used for a boundary residual when a source theorem supplies its
annihilation.  It cannot be used on the complete signed telescope by merely
passing the exact response `L_(p,S)` or a boundedness estimate: that would
require the synchronized gap itself to vanish.

The actual remaining producer must therefore be one of:

```text
1. a genuine joint bounded readout through the full old-carrier analysis;
2. a source theorem proving the gap-zero covariance identity; or
3. a different residual decomposition whose annihilation premise is valid.
```

No transition skew is discarded, no response norm is promoted to a Douglas
bound, and no Gate 3U, finite-`S` sign, Burnol identity, or RH theorem is
claimed.

## Verification

The Windows source was synchronized to the cached Ubuntu-24.04 WSL2 ext4
mirror. The batch passed:

```text
focused source build: 3370 jobs, PASS
focused axiom audit: 3371 jobs, PASS
CCM25Concrete aggregate: 3874 jobs, PASS
full repository build: 3955 jobs, PASS
```

The audit reports exactly `[propext, Classical.choice, Quot.sound]` for all
three new declarations. No `sorry`, `admit`, or user axiom was added. The WSL
localhost-proxy notice and pre-existing linter warnings are environmental or
unrelated.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRangeAnnihilationGuard.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRangeAnnihilationGuardAudit.lean
```
