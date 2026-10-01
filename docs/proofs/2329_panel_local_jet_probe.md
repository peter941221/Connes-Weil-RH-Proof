# 2329 — Panel-local cancellation-preserving jet probe

Scope correction (record 2334): this record evaluates the auxiliary P-only
construction from 2249, not the actual selected detector. All margin ratios
below are auxiliary comparisons only; they supply no selected-owner producer
margin or Fourier certificate. See 2334_fourier_object_scope_correction.md.

Record 2329 combines the 30 basis derivatives with the selected owner
coefficients before taking absolute values, at the center of each of 320
panels. It then forms the complete Leibniz product sum for
`W(xi) * cos(phi xi)` at derivative order 32.

The corrected full product proxy is:

```text
+--------------------------------+----------------------+
| quantity                       | value                |
+--------------------------------+----------------------+
| panel width                   | 0.25                 |
| panel count                   | 320                  |
| local W^(32) max              | 5.539198187767e57     |
| local W^(32) mean             | 4.434142537326e55     |
| full local product proxy      | 7.472203544915e5      |
| proxy / current margin        | 4.459962503209e-7     |
| global triangle probe         | 9.235602894507e23     |
+--------------------------------+----------------------+
```

The first proxy reading used only `W^(32)` and was discarded; the recorded
result includes all `W^(k) * phi^(32-k)` Leibniz terms. The cancellation-preserving
local jet therefore removes the global triangle explosion by roughly 1e18 in
this diagnostic.

This is still not a certificate: the jets are evaluated at panel centers, no
interval radius inflation is present, and the frequency product bound is
crude. The next implementation must turn each center jet into a panel
interval enclosure and charge the radius.

Evidence: `scripts/routea_panel_local_jet_probe_2329.py` and
`results/2329_panel_local_jet_probe.json`.
