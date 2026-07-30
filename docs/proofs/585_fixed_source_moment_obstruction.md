# Proof 585: fixed-source moment obstruction handoff

Proof 586 extends the approximate-kernel side from a fixed source vector to a
uniformly bounded moving source sequence. See
`docs/proofs/586_moving_source_old_carrier_kernel.md` for the active Bone 1
shape.

## Result

Proof 584 gives a genuine fixed-source approximate kernel for the old-carrier
analysis.  For a fixed `x` and a visible-prime sequence `p_n`, set

```text
y_n = newSuffixFrame(lambda, [], x).
```

If

```text
q_(p_n) = ccm24PrimeEulerCoefficient(p_n) -> 0,
```

then the actual two-channel old-carrier analysis satisfies

```text
||W_(p_n) y_n|| -> 0.
```

The new Proof 585 theorem proves the missing logical handoff:

```text
uniform old-carrier quotient with bound C
              |
              v
||M_(p_n) oldFrame_(p_n)^dagger y_n||
    <= 8 C ||W_(p_n) y_n||
              |
              v
moment response -> 0.
```

Therefore either of the following source facts rules out every finite
uniform old-carrier quotient:

```text
moment response does not tend to zero,
```

or the stronger eventual lower bound

```text
epsilon <= ||M_(p_n) oldFrame_(p_n)^dagger y_n||
for some epsilon > 0.
```

The factor `8` is the existing uniform inverse bound for the one-prime
Schur--Markov scalar.  It is not a new estimate for the signed moment.

## Dependency

```text
Proof 584: fixed source column
  W_(p_n) newFrame([], x) -> 0
              |
              v
Proof 583: moment readout from a uniform quotient
  ||M_(p_n) oldFrame† y_n|| <= 8 C ||W_(p_n) y_n||
              |
              v
Proof 585: uniform quotient forces fixed-column moment -> 0
```

The converse obstruction is now available directly on the same columns:

```text
fixed-column moment not -> 0  =>  no uniform quotient
fixed-column moment >= epsilon eventually => no uniform quotient
```

## What remains open

Proof 585 does not prove either source alternative.  In particular, it does
not assert a lower bound for the signed one-prime moment, and it does not
prove that the moment decays.  Establishing one of those two facts on the
actual CCM24 carrier is still the analytic bottom of bone 1.

The carrier-level sequence `canonicalVisiblePrimeSequence` remains only a
`p > 1` coefficient-decay sanity check.  `CCM24VisiblePrime` does not encode
arithmetic primality, so it must not be presented as an arithmetic prime
sequence.

Gate 3U, the finite-S sign, Burnol's identity, and RH remain open.

## Lean owners

Source:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFixedSourceMomentObstruction.lean
```

Audit:

```text
ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFixedSourceMomentObstructionAudit.lean
```

The audited declarations use exactly:

```text
[propext, Classical.choice, Quot.sound]
```

## Verification

The Windows source was synchronized to the Ubuntu-24.04 WSL2 ext4 mirror.

```text
focused source build: 3346 jobs, PASS
focused audit build: 3347 jobs, PASS
CCM25Concrete aggregate: 3851 jobs, PASS
full repository build: 3932 jobs, PASS
git diff --check: PASS
```

The WSL localhost-proxy notice and pre-existing repository linter warnings
remain environmental or unrelated to this proof batch.
