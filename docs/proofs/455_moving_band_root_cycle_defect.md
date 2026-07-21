# Proof 455: Moving-band root-cycle defect

## Result

Proof 455 performs one legal finite-prefix cyclic rotation of the complete
root-sandwiched crossing.  For

```text
C = actual completed five-branch crossing core,
G = selected convolution root,
W = G^H G = detectorOperator,
```

Lean proves

```text
Tr M_N(G C G^H)
  = Tr M_N(W C)
    + Tr(Delta_N(G C,G^H)-Delta_N(G^H,G C)).
```

The first term has the genuine positive convolution detector in the physical
left position.  The second term is the exact prefix-cycle anomaly.  It is not
discarded.

## Signed integral

The two terms are recombined in

```lean
actualCompletedWeightedBoundaryTrace
```

before integration or absolute value.  The active canonical consumer now
accepts one bound

```text
forall N,
  abs(integral_0^1 actualCompletedWeightedBoundaryTrace_N(alpha) d alpha)
    <= (supportRadius+log 3)*(1+supportRadius+log 3).
```

This keeps the full outer/Sonin/prolate crossing inside `C` and retains the
finite-prefix anomaly next to the detector-weighted core.

## Boundary

Proof 455 is an exact cycle ledger, not the uniform bound.  The next producer
must identify `Tr M_N(W C)` with the complete weighted outer-minus-Sonin
covariance and control it together with the antisymmetric cycle defect.  Gate
3U, the finite-`S` sign, Burnol's identity, and `_root_.RiemannHypothesis`
remain open.
