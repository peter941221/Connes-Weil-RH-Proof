# 2330 — Panel radius feasibility probe

Scope correction (record 2334): this record evaluates the auxiliary P-only
construction from 2249, not the actual selected detector. All margin ratios
below are auxiliary comparisons only; they supply no selected-owner producer
margin or Fourier certificate. See 2334_fourier_object_scope_correction.md.

Record 2330 evaluates the cancellation-preserving derivative jet at the 320
panel centers and all 640 panel endpoints. It uses the maximum sampled jet
component across those points as a radius diagnostic.

```text
+--------------------------------+----------------------+
| quantity                       | value                |
+--------------------------------+----------------------+
| panel width                   | 0.25                 |
| panel count                   | 320                  |
| sample points                 | 641                  |
| local W^(32) max              | 5.774005272318e57     |
| local W^(32) mean             | 4.329799638486e55     |
| radius probe product proxy    | 1.004522980322e6      |
| proxy / current margin        | 5.995734456268e-7     |
+--------------------------------+----------------------+
```

The center-only proxy from record 2329 was `7.4722e5`; including endpoint
samples raises it to `1.0045e6`, still far below the current margin. This is
only a radius feasibility probe: sampled endpoints are not a certified interval
supremum. The next certificate must inflate each panel jet with a proved local
remainder or interval enclosure.

Evidence: `scripts/routea_panel_radius_probe_2330.py` and
`results/2330_panel_radius_probe.json`.
