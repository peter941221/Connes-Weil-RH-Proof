# 2327 — Cosine-only GL remainder headroom

Scope correction (record 2334): this record evaluates the auxiliary P-only
construction from 2249, not the actual selected detector. All margin ratios
below are auxiliary comparisons only; they supply no selected-owner producer
margin or Fourier certificate. See 2334_fourier_object_scope_correction.md.

For GL16 on panel width `0.25`, the standard Gauss-Legendre remainder
prefactor is `4.3198580896920426e-75`. Using the sampled maximum of the
selected-owner weight and the exact omitted prime-power frequency list, the
remainder contribution from differentiating only the cosine factor is:

```text
cos-only remainder bound       3.251301602304e4
current margin                 1.675396046388e12
ratio                          1.940616733168e-8
```

This is useful headroom, but it is deliberately partial. The product derivative
rule also contains derivatives of the owner weight `W(xi)`, and the final
certificate still needs finite-window endpoint and full-line tail terms. The
small cos-only number must not be promoted to a full quadrature certificate.

Evidence: `scripts/routea_cosine_remainder_headroom_2327.py` and
`results/2327_cosine_remainder_headroom.json`.
