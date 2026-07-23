# Proof 524: actual physical Euler transport readback

## Result

Proof 523 named the complementary support defect of the concrete graph frame.
Proof 524 now applies the actual normalized Euler transport to that frame.

For a concrete `PrimeEulerProjectedJuliaInput`, define

```text
projectedGraphFrame
  = projection * graphCosine + graphSineCanonical

fullGraphFrame
  = graphCosine + graphSineCanonical

physicalGraphSupportResidual
  = normalizedPrimeEulerFrameTransport * graphSupportDefect.
```

Lean proves the exact projected-frame transport identity

```text
normalizedPrimeEulerFrameTransport * projectedGraphFrame
  = normalizedSchurFrame.
```

The unprojected response therefore has the same-object decomposition

```text
normalizedPrimeEulerFrameTransport * fullGraphFrame
  = normalizedSchurFrame + physicalGraphSupportResidual.
```

Because the normalized Euler transport is contractive, the residual obeys

```text
||physicalGraphSupportResidual||
  <= ||graphSupportDefect||.
```

This is the first direct bridge from the Proof 523 graph defect to the actual
physical Euler transport.  It does not bound the graph defect itself, identify
the residual with the complete post-Q remainder, construct the uniform Julia
co-defect factor family, close Gate 3U, prove the finite-S sign, provide
Burnol's identity, or prove `_root_.RiemannHypothesis`.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSActualSchurGraphPhysicalTransportReadback.lean
ConnesWeilRH/Dev/
  CCM24FiniteSActualSchurGraphPhysicalTransportReadbackAudit.lean
ConnesWeilRH/Source/CCM25Concrete.lean
```

The next source-specific producer must identify this residual with the
physical post-Q mismatch owner before taking any family-uniform absolute
value.  The uniform Douglas producer, Gate 3U, the finite-S sign, Burnol's
identity, and RH remain open.
