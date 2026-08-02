# Proof 719: Endpoint Pythagorean Energy Ledger

Proof 718 showed that the combined endpoint coframe is a right inverse to the
source-Sonin inclusion adjoint. Proof 719 strengthens that obstruction to an
exact pointwise identity:

```text
||D_S u||^2 = ||u||^2 + ||L_S u||^2,
```

where `D_S` is the complete endpoint coframe and `L_S` is its complete
off-Sonin leakage. The source term and leakage term are the orthogonal
`sourceSoninProjection` and complementary star-projection components.

The Lean theorem
`norm_sq_sourceActualBandForwardEndpointCoframe_apply_eq_source_add_leakage`
uses `Submodule.norm_sq_eq_add_norm_sq_starProjection`; it does not expand the
forward, metric, outer, reflected, second-support, or prolate branches.

Consequences:

```text
||D_S|| <= 1  ->  L_S = 0,
L_S != 0      ->  ||D_S u|| > ||u|| for some u,
```

Thus the unresolved endpoint contraction is exactly a complete leakage
cancellation theorem, not a generic norm estimate. Gate 3U, the finite-S sign,
Burnol's identity, and RH remain open.

The focused WSL2 source build and axiom audit use only
`[propext, Classical.choice, Quot.sound]`.
