# 2323 — Fourier coefficient refinement control

Scope correction (record 2334): this record evaluates the auxiliary P-only
construction from 2249, not the actual selected detector. All margin ratios
below are auxiliary comparisons only; they supply no selected-owner producer
margin or Fourier certificate. See 2334_fourier_object_scope_correction.md.

The same selected owner and prime book were evaluated at grid steps 0.02 and
0.01. This is a refinement control for the Fourier-side diagnostic; it is not
a proof of the quadrature remainder.

```text
+---------------------------+----------------------+----------------------+
| quantity                  | dx = 0.02            | dx = 0.01            |
+---------------------------+----------------------+----------------------+
| signed omitted delta      | 155458254.287        | 155457647.398        |
| Fourier abs-term sum      | 621617311.893        | 621593325.402        |
| frequency group width 2   | 155496479.400        | 155492199.682        |
+---------------------------+----------------------+----------------------+
```

The signed delta moves by about `607`, and the Fourier absolute-term sum moves
by about `23986` (relative about `3.9e-5`). Both remain far below the current
`1.6754e12` margin. The movement must nevertheless be charged in a certified
coefficient enclosure; refinement agreement is a control, not a proof.

Evidence: `scripts/routea_fourier_coefficient_refinement_2323.py` and
`results/2323_fourier_refinement_0p01.json`.
