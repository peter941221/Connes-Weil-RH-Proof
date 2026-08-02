# Proof 718: Endpoint Contraction Lower-Bound Guard

The combined endpoint coframe satisfies the exact biorthogonality identity:

```text
(sourceInclusion lambda)† ∘ endpoint = I.
```

Because `sourceInclusion` is contractive, Proof 718 formally derives:

```text
1 ≤ ||endpoint||.
```

Therefore Proof 717's sufficient condition `||endpoint|| ≤ 1` is necessarily
sharp. It cannot be obtained from a loose triangle inequality. A successful
producer must prove the endpoint is exactly norm-preserving, which is the
precise place where the complete lower-factor cancellation must occur.

The Lean theorem carries an explicit `Nontrivial` source-carrier instance;
without it the norm of the identity can be zero, so no lower bound is valid.

The same guard also proves the sharper implication:

```text
||endpoint|| <= 1
  -> endpoint = sourceInclusion
  -> sourceActualBandCombinedCoframeLeakage = 0.
```

Thus the Proof 717 producer is exactly a full off-Sonin leakage cancellation
theorem, not merely an endpoint norm estimate.
