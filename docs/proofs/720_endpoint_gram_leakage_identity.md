# Proof 720: Endpoint Gram Identity and Leakage Obstruction

Proof 719's pointwise Pythagorean ledger has an operator-level form. Let
`D_S` be the complete endpoint coframe and `L_S` its complete off-Sonin
leakage. Since `D_S = J_S + L_S`, where `J_S` is the isometric source
inclusion and `J_S† L_S = 0`, Lean proves

```text
D_S† D_S = I + L_S† L_S.
```

The source declaration is

```text
sourceActualBandForwardEndpointCoframe_adjoint_comp_self_eq_id_add_leakage
```

in `CCM24FiniteSEndpointContractionGuard.lean`. The proof expands the
adjoint of a sum, removes both cross terms by the exact orthogonality
producer, and rewrites `J_S† J_S = I`. It does not estimate or separately
bound the forward, metric, outer, reflected, second-support, or prolate
branches.

The identity gives the exact order statement

```text
I <= D_S† D_S,
‖D_S‖ <= 1  ->  L_S† L_S = 0  ->  L_S = 0,
L_S != 0    ->  D_S is strictly expansive on some source vector.
```

Thus the endpoint contraction required by Proof 717 is not a generic
contractive estimate. It is equivalent to a producer proving complete
leakage cancellation for the actual finite-S endpoint. Existing identities
for `finiteEulerMetricCoframe`, `sourceSoninCoframeLeakage`, and the physical
boundary residual remain decomposition and readout theorems only; none proves
that their coherent sum vanishes. Do not infer cancellation from normalized
metric contraction, positive energy, compactness, or dense range.

Gate 3U, the finite-S sign, Burnol's identity, and `_root_.RiemannHypothesis`
remain open. The focused source and audit builds must continue to report only
`[propext, Classical.choice, Quot.sound]`.
