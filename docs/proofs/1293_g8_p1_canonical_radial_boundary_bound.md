# G8 P1 canonical radial-boundary bound (2026-09-11)

The import-facing leaf `C1G8P1CanonicalRadialBoundaryBound` specializes the
existing source-side radial-column factorization to its canonical first
coordinate readout. For every visible prime `p`, suffix `S`, and source input
`x`, Lean proves

```text
‖R_p(newSuffixFrame_S x)‖
  ≤ 32 · ‖q_p⁻¹‖ · ‖newFrameAntiresonantColumn_{p,S} x‖,
```

and the corresponding squared estimate. Here `q_p` is the concrete Euler
coefficient; its inverse cost remains explicit and is not hidden in a uniform
constant.

This is FORMAL Lean evidence for a quantitative source-restriction input to
G8-P1. It does not identify a metric coframe boundary map with a radial
crossing, does not give a finite-prime trace equality, and does not produce
the P2 remainder limit.

Verification: `/home/peter/rh/build-logs/1338_g8_p1_canonical_radial_bound.log`,
green owning/Audit build (3463 jobs), zero `error:`/`sorryAx`, and standard
audit axioms only.
