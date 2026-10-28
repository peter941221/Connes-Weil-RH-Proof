# 3156: Per-common support does not imply finite-prime dominance

Date: 2026-10-28

The narrowed `PerCommonSourceFinitePrimeSupport` contract is insufficient to
prove `SourceWeilFormData.finitePrimeDominance`.

`ConnesWeilRH/Dev/FinitePrimeDominanceNoGo3156.lean` constructs an
axiom-clean countermodel:

```text
common bump support       -> prime 2 only
per-common index set      -> {2}
custom convolutionStar   -> a bump supported near 3
arbitrary convolution    -> visible at prime 3
finitePrimeDominance     -> false
```

The custom `SourceTestAlgebra` keeps the same legacy carrier and evaluation
shape, but maps every convolution to `counterBump`, whose value at `3` is `1`.
The common test remains the ambient prime-2 bump, whose finite-prime term at `3`
is zero. The support rows therefore remain valid while the dominance implication
fails.

This is a structural no-go, not a failure of the Lean implementation. The
minimal indexed normalization boundary is still the right interface, but its
`finitePrimeDominance` obligation requires a genuine arbitrary-convolution
support theorem or an equivalent indexed certificate family.

Verification:

```text
lake env lean ConnesWeilRH/Dev/FinitePrimeDominanceNoGo3156.lean
```

Result: successful. The audited theorem
`ConnesWeilRH.Source.Dev.FinitePrimeDominanceNoGo3156.not_finitePrimeDominance`
depends only on `[propext, Classical.choice, Quot.sound]`.

No SourceRH or RH claim follows from this record.
