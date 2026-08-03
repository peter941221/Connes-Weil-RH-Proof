# Proof 760: Actual Schur Boundary-Moment Canonical Skew

## Result

The proposed real-trace shortcut from Proof 570 does not hold as stated.  The
actual Schur boundary moment is not automatically self-adjoint.

Write

```text
J   = source inclusion,
W   = selected self-adjoint detector,
F_S = named Schur forward coframe,
C_S = actual metric coframe,
M_S = named Schur boundary moment.
```

Lean now proves the exact operator decomposition

```text
M_S = H_S + K_S,

H_S = F_S^dagger W J + J^dagger W F_S,
K_S = (C_S-J)^dagger W J,
H_S^dagger = H_S.
```

Consequently

```text
M_S-M_S^dagger = K_S-K_S^dagger.                 (760.1)
```

For an actual finite prime-power family, the literal suffix bridge gives

```text
K_(family.visiblePrimes)
  = finiteEulerTargetCommutatorResponse_family.   (760.2)
```

Combining (760.1) and (760.2), the old transition-orientation obstruction has
exactly the same skew channel as the canonical target used by Proofs 756--759.
It is not an additional independent Gate 3U bottom.

## Why The Self-Adjoint Shortcut Fails

The endpoint coframe is

```text
E_S = F_S + C_S.
```

The source projection kills `F_S` and sends `C_S` to `J`.  Substitution into
the raw moment gives

```text
M_S
  = F_S^dagger W J + J^dagger W F_S
    + (C_S-J)^dagger W J.
```

Only the bracketed forward pair is forced to be Hermitian.  The remaining
metric leakage is the current target.  Lean therefore proves the sharper
equivalence

```text
M_S^dagger=M_S
  <-> Target_S^dagger=Target_S.
```

No theorem in the route supplies the right-hand condition.  Proof 749's
carrier anomaly is consistent with this result; it must not be erased by an
ambient self-adjointness argument.

## A Second Rejected Shortcut

The ambient response is `C (B_S-B_0) C^dagger`, and both band projections are
absorbed by the common radial projection `E`.  This still does not make `C E`
Hilbert--Schmidt automatically.  The range of `E` consists of functions that
vanish below `log(lambda)`, so it is supported on the infinite half-line
`[log(lambda), infinity)`, not on a finite interval.  A translation-invariant
convolution root restricted only on that input half-line retains infinite
Hilbert--Schmidt mass.  Compact root support must first act through a completed
boundary crossing.

Code evidence:

```text
ConnesWeilRH/Source/CC20Concrete/CCM24LogRadialSupport.lean:29-70
ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSPairedFirstJetRemainder.lean:303-372
```

## What This Changes

```text
Proof 570 transition skew
          |
          v
Hermitian forward channel + metric leakage channel
          |                         |
          | legal trace cycle only  +--> canonical Target_S
          |                                  |
          +----------------------------------+
                                             v
                              completed-kernel Gate 3U estimate
```

The Hermitian channel may contribute only a pure-imaginary trace after the
required trace-class hypotheses and cyclic identity have been established.
It does not disappear as an operator.  The surviving real analytic task is
still the direct completed signed-trace estimate for `Target_S`, with the
outer, reflected second-support, and prolate branches kept together until
compact-root support has acted.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSActualSchurBoundaryMomentCanonicalSkew.lean
ConnesWeilRH/Dev/
  CCM24FiniteSActualSchurBoundaryMomentCanonicalSkewAudit.lean
ConnesWeilRH/Source/CCM25Concrete.lean
```

This proves neither Gate 3U, the finite-S sign, the arithmetic same-object
identity, Burnol's identity, nor `_root_.RiemannHypothesis`.
