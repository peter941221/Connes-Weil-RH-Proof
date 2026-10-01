# 2328 — Global product-derivative majorant is too loose

Scope correction (record 2334): this record evaluates the auxiliary P-only
construction from 2249, not the actual selected detector. All margin ratios
below are auxiliary comparisons only; they supply no selected-owner producer
margin or Fourier certificate. See 2334_fourier_object_scope_correction.md.

The first implementation of this probe accidentally multiplied the GL weights
twice; that reading was discarded. After correcting the construction, the
majorant uses the weights already contained in `phi_terms` and the actual
basis derivative envelope.

```text
+--------------------------------+----------------------+
| quantity                       | corrected value      |
+--------------------------------+----------------------+
| owner derivative bound, k=0   | 6.286225205841e32     |
| owner derivative bound, k=32  | 5.144962228216e74     |
| GL product remainder           | 9.235602894507e23     |
| current margin                 | 1.675396046388e12     |
| remainder / margin             | 5.512489368958e11      |
+--------------------------------+----------------------+
```

This is a scoped no-go for the global triangle/product majorant. The Fourier
interface remains valid, and the cosine-only term is small, but taking absolute
values of the basis derivative moments before combining the selected owner
coefficients destroys the cancellation inside `L_base` and `L_corr`.

The discarded double-weight run must not be cited. The next admissible route
is panel-local or interval-jet evaluation that preserves coefficient
cancellation before taking norms; simply increasing GL order will not repair
this global majorant.

Evidence: `scripts/routea_global_product_remainder_probe_2328.py` and
`results/2328_global_product_remainder_probe.json`.
