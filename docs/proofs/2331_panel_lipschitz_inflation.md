# 2331 — Panel-local Lipschitz inflation probe

Scope correction (record 2334): this record evaluates the auxiliary P-only
construction from 2249, not the actual selected detector. All margin ratios
below are auxiliary comparisons only; they supply no selected-owner producer
margin or Fourier certificate. See 2334_fourier_object_scope_correction.md.

Record 2331 extends the panel-local jet to order 33 and inflates each order-32
remainder ingredient by a first-order panel-radius term:

```text
inflated_k = max_panel |W^(k)| + 0.125 * max_panel |W^(k+1)|
```

This is a sampled Lipschitz proxy, not a certified interval supremum.

```text
+--------------------------------+----------------------+
| quantity                       | value                |
+--------------------------------+----------------------+
| panel width                   | 0.25                 |
| panel count                   | 320                  |
| sample points                 | 641                  |
| inflated product proxy        | 2.521425870721e6      |
| proxy / current margin        | 1.504973033784e-6     |
| global triangle proxy         | 9.235602894507e23     |
+--------------------------------+----------------------+
```

The radius inflation raises the 2330 proxy by only about 2.5x and remains far
below the margin. The next formal step is to replace sampled maxima by a
proved local interval or higher-derivative bound; the sampled Lipschitz factor
must not be promoted to that proof.

Evidence: `scripts/routea_panel_lipschitz_inflation_2331.py` and
`results/2331_panel_lipschitz_inflation.json`.
