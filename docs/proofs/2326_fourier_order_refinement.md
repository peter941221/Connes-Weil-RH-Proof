# 2326 — Same-panel quadrature order refinement

Scope correction (record 2334): this record evaluates the auxiliary P-only
construction from 2249, not the actual selected detector. All margin ratios
below are auxiliary comparisons only; they supply no selected-owner producer
margin or Fourier certificate. See 2334_fourier_object_scope_correction.md.

Record 2326 compares GL16 and GL32 on the same 320 panels, so the panel
geometry is fixed and only quadrature order changes.

```text
+-------------------------------+----------------------+
| quantity                      | value                |
+-------------------------------+----------------------+
| GL16 signed                   | 1.554762067779e8      |
| GL32 signed                   | 1.554586856651e8      |
| GL16 abs-term sum             | 6.216555645142e8      |
| GL32 abs-term sum             | 6.216025482536e8      |
| GL32 - GL16 abs-term sum      | 1.254236610300e5      |
| GL32 - GL16 signed            | -1.752111274390e4     |
+-------------------------------+----------------------+
```

The same-panel order movement agrees in scale with the GL16 x 320 to GL16 x
640 spatial refinement. This supports `panel width=0.25` as the diagnostic
trust horizon. It remains a control only: the final enclosure still needs an
analytic remainder bound and endpoint treatment.

Evidence: `scripts/routea_fourier_order_refinement_2326.py` and
`results/2326_fourier_order_refinement.json`.
