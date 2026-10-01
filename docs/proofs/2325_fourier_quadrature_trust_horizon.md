# 2325 — Quadrature trust horizon for Fourier coefficients

Scope correction (record 2334): this record evaluates the auxiliary P-only
construction from 2249, not the actual selected detector. All margin ratios
below are auxiliary comparisons only; they supply no selected-owner producer
margin or Fourier certificate. See 2334_fourier_object_scope_correction.md.

An independent composite Gauss-Legendre probe was run on the actual selected
owner weight and the omitted prime book. The point is to measure the trust
horizon of the quadrature rule, not to claim that Gauss-Legendre exactness is
an error bound.

```text
+----------------+----------------------+----------------------+
| rule            | signed sum           | abs-term sum         |
+----------------+----------------------+----------------------+
| GL8 x 160       | -6.783955743904e15   | 2.579825379280e17     |
| GL16 x 160      |  2.430512319607e8    | 3.743975295869e13     |
| GL16 x 320      |  1.554762067779e8    | 6.216555645142e8      |
| GL16 x 640      |  1.554588846226e8    | 6.215916322442e8      |
+----------------+----------------------+----------------------+
```

The controls expose a real aliasing regime:

```text
GL16 x 160 -> GL16 x 320 abs-term movement  = 3.7439e13
GL16 x 320 -> GL16 x 640 abs-term movement  = 1.2537e5
```

Therefore the first two rules cannot be used as a certificate. The measured
trust horizon is panel width `0.25` (`GL16 x 320`); refinement to panel width
`0.125` is stable at the sampled level. This remains a diagnostic: the final
proof must enclose the coefficient remainder and the finite-window endpoint
terms explicitly.

Evidence: `scripts/routea_fourier_quadrature_probe_2325.py` and
`results/2325_fourier_quadrature_probe.json`.
