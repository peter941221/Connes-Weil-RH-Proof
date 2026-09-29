# 2226 — Two-node MPFR q-interval stability (superseded)

Date: 2026-09-29

Consumer: the healthy `CompactLog` B5 selected detector, actual
`sourceNontrivialZeroSet` owner, same-owner `qw >= 0` producer.

The 2225 MPFR q-construction interval certificate was rerun at node 3, the
second-largest nearby 2217 forward-error row, with the same all-family,
all-GL/Simpson scope. Both nodes have zero interval containment failures.

```text
node 2 charge       2.436718255644566e-09   (3.89561258643631e-05 target)
node 3 charge       2.233376170985172e-09   (3.57052699949315e-05 target)
max q radius        36.099947214126594      (both nodes)
failures            0                       (both nodes)
```

The adjacent-node comparison finds no hidden q-interval spike. This is a
two-node stability certificate, not yet a 30-node universal certificate;
the remaining work is a uniform node envelope or the other-node MPFR runs,
followed by finite-sum accumulation and owner transfer.

Artifacts:

- `results/2225_q_mpfr_interval_binding.json`
- `results/2225_q_mpfr_node3.json`
- `results/20260929_2225_q_mpfr_node3.log`
- script: `scripts/routea_weighted_zero_q_mpfr_interval_binding_2225.py`

Status: `SUPERSEDED-BY-2228` because the original charge cast complex
coefficients/weights to `float`; see [2228](2228_routea_q_mpfr_complex_weight_fix.md).
