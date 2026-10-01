# 2332 — Panel-local Taylor enclosure feasibility

Scope correction (record 2334): this record evaluates the auxiliary P-only
construction from 2249, not the actual selected detector. All margin ratios
below are auxiliary comparisons only; they supply no selected-owner producer
margin or Fourier certificate. See 2334_fourier_object_scope_correction.md.

Record 2332 replaces endpoint-only inflation with a local Taylor mechanism.
At each panel center, owner coefficients are combined in derivatives through
order 34. Orders through 32 are bounded by the center Taylor polynomial plus an
order-34 absolute basis tail over radius `0.125`.

```text
+--------------------------------+----------------------+
| quantity                       | value                |
+--------------------------------+----------------------+
| panel width                   | 0.25                 |
| panel count                   | 320                  |
| radius                        | 0.125                |
| tail order                    | 34                   |
| W sup order-32 proxy          | 9.775128094912e61     |
| local Taylor remainder proxy  | 1.133133770579e7      |
| proxy / current margin        | 6.763378563666e-6     |
+--------------------------------+----------------------+
```

This is materially stronger than endpoint sampling because the panel radius is
explicitly represented by a Taylor tail. It remains a feasibility diagnostic:
the absolute tail uses stored floating-point basis moments, and no directed
interval arithmetic or endpoint/full-line correction has been installed yet.

Evidence: `scripts/routea_panel_taylor_enclosure_probe_2332.py` and
`results/2332_panel_taylor_enclosure_probe.json`.
