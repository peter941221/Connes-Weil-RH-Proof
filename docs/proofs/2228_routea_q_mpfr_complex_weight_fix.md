# 2228 — Corrected MPFR q interval: complex-weight audit

Date: 2026-09-29

Consumer: the healthy `CompactLog` B5 selected detector, actual
`sourceNontrivialZeroSet` owner, same-owner `qw >= 0` producer.

The first 2225–2227 q-interval scripts emitted a `ComplexWarning`: they cast
complex coefficients/weights to `float`, dropping imaginary parts in the
charge. Those readings are superseded and are not used here. The evaluator
was corrected to use `abs(c)` and `abs(w)`, and the three full quadrature runs
were repeated with no warning.

```text
node 2    8.792971355816332e-09   1.40574355720215e-04 target
node 3    8.063938632912915e-09   1.28919216498897e-04 target
node 29   6.475830084303228e-09   1.03529922368318e-04 target
interval failures                    0 at all three nodes
```

All runs cover 30 families and the complete GL/Simpson rule. The corrected
charges remain far below the absolute 2211 correction target `6.2550323e-5`,
but they are the values that may be used for subsequent margin arithmetic.
This is still a three-node stability certificate, not a universal 30-node
bound; finite-sum accumulation and owner transfer remain open.

Superseded records: 2225, 2226, and 2227 numerical readings. Their scripts
remain as historical provenance; only the corrected script/artifacts below
are authoritative for this charge.

Artifacts:

- `results/2228_q_mpfr_node2.json`
- `results/2228_q_mpfr_node3.json`
- `results/2228_q_mpfr_node29.json`
- `results/20260929_2228_q_mpfr_node2_corrected.log`
- `results/20260929_2228_q_mpfr_node3_corrected.log`
- `results/20260929_2228_q_mpfr_node29_corrected.log`
- script: `scripts/routea_weighted_zero_q_mpfr_interval_binding_2225.py`

Status: `MPFR-Q-INTERVAL-THREE-NODE-CORRECTED`; no RH claim.
