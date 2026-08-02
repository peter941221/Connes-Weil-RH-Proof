# Proof 721: Endpoint Contraction Iff Complete Leakage Zero

Proof 720 gives the operator Gram identity

```text
D_S† D_S = I + L_S† L_S.
```

Proof 721 packages the same obstruction as the exact endpoint-contraction
interface consumed by Proof 717:

```text
‖D_S‖ <= 1  <->  L_S = 0.
```

The new Lean declarations are

```text
sourceActualBandForwardEndpointCoframe_eq_inclusion_of_combined_leakage_eq_zero
norm_sourceActualBandForwardEndpointCoframe_le_one_iff_combined_leakage_eq_zero
norm_sourceActualBandForwardEndpointCoframe_eq_one_of_combined_leakage_eq_zero
```

The forward direction is Proof 718's sharp right-inverse obstruction: if the
endpoint is contractive, it equals the source inclusion, so the complete
leakage vanishes.  The reverse direction rewrites a zero-leakage endpoint as
the source inclusion and uses the canonical `Submodule.norm_subtypeL_le`.
When the source carrier is nontrivial, the endpoint norm is exactly one.

This is a route-shaping theorem, not a Gate 3U producer.  It proves that the
remaining endpoint-contraction obligation is precisely complete coherent
leakage cancellation.  Any future producer must prove
`sourceActualBandCombinedCoframeLeakage = 0` directly or produce an equivalent
same-object cancellation theorem.  Branchwise contraction, positive energy,
dense range, compactness, or normalized metric estimates do not imply this
iff's right-hand side.

Gate 3U, the finite-S sign, Burnol's identity, and `_root_.RiemannHypothesis`
remain open.
