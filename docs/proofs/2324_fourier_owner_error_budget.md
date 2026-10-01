# 2324 — Fourier owner-weight forward-error budget

Scope correction (record 2334): this record evaluates the auxiliary P-only
construction from 2249, not the actual selected detector. All margin ratios
below are auxiliary comparisons only; they supply no selected-owner producer
margin or Fourier certificate. See 2334_fourier_object_scope_correction.md.

Record 2324 reuses the 2249 operation-level forward-error shadows for the
actual 30-family owner, then propagates the owner-weight error into every
omitted prime-power Fourier coefficient. It is a diagnostic budget, not yet a
full certificate because the quadrature remainder is still separate.

```text
+--------------------------------+----------------------+
| quantity                       | value                |
+--------------------------------+----------------------+
| Fourier abs-term value sum     | 6.216173118934e8      |
| propagated owner-weight error  | 1.179864458159e9      |
| current margin                 | 1.675396046388e12     |
| margin / owner-error budget    | about 1420            |
+--------------------------------+----------------------+
```

The existing instrumented `laplace_rows`, `dot30`, square, annihilator, and
multiplication shadows therefore do not consume the producer margin. This
separates the remaining obligation: certify the integration error of each
Fourier coefficient, including the finite-window endpoint and quadrature
remainder. Do not merge that remainder into the sampled coefficient agreement.

Evidence: `scripts/routea_fourier_owner_error_budget_2324.py` and
`results/2324_fourier_owner_error_budget.json`.
