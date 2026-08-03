# Proof 797: Raw completed physical base ledger

Date: 2026-08-03

Status: axiom-clean Lean closure of the zero-prime base point and the
unscaled one-prime ledger for the completed physical Gate scalar. It removes
a possible raw offset. It does not bound the increment, prove Gate 3U, prove
the finite-S sign, prove Burnol's identity, or prove `_root_.RiemannHypothesis`.

## Result

Let

```text
K_F = rawCompletePhysicalHermitianTrace(F)
```

be the real completed Hardy--prolate physical trace for a finite prime-power
family `F`. For a compatible one-prime transition with

```text
newFamily.visiblePrimes = p :: S,
oldFamily.visiblePrimes = S,
```

Lean proves:

```text
K_empty = 0,

K_(p::S) = K_S + F_(p,S),

F_(p,S)
  = -Re Tr(normalizedListActualBandSoninCoboundary_(p,S))
    + Re Tr(sourceActualBandFiniteEulerRemainderIncrement_(p,S)).
```

The two forcing summands remain one signed source trace. Neither branch is
estimated independently.

## Why The Base Matters

```text
empty visible-prime family
        |
        v
physical coframe = source inclusion
        |
        v
physical leakage = 0
        |
        v
raw completed trace K_empty = 0
```

Without this base theorem, a finite forcing telescope could conceal an
uncontrolled constant. The result excludes that failure mode before any norm
or support argument is attempted.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCausalMarkovRawBase.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCausalMarkovRawBaseAudit.lean
```

Key declarations:

```text
sourcePhysicalCoframeLeakage_eq_zero_of_visiblePrimes_nil
finiteEulerTargetCommutatorResponse_eq_zero_of_visiblePrimes_nil
rawCompletePhysicalHermitianTrace_eq_zero_of_visiblePrimes_nil
rawCompletePhysicalHermitianTrace_cons_eq_add_forcing
```

## Verification

The focused Ubuntu-24.04 WSL2 ext4 build passed:

```text
lake build ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkovRawBase
```

The source and import-facing audit report exactly:

```text
[propext, Classical.choice, Quot.sound]
```

## Scope

This is raw bookkeeping, not a raw estimate. In particular, the scaled
forcing bound from Proof 795 cannot be divided by a finite Euler lower factor
to bound `F_(p,S)` or `K_(p::S)`.
