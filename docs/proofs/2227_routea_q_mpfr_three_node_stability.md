# 2227 — Three-node MPFR q-interval stability (superseded)

Date: 2026-09-29

Consumer: the healthy `CompactLog` B5 selected detector, actual
`sourceNontrivialZeroSet` owner, same-owner `qw >= 0` producer.

The full MPFR q interval certificate was run at a third location, node 29,
chosen from the high-imaginary remote tail of the 2217 node table. All runs
use all 30 families and all GL/Simpson points with `NSEG=1100`.

```text
node 2    2.436718255644566e-09   3.89561258643631e-05 target
node 3    2.233376170985172e-09   3.57052699949315e-05 target
node 29   1.7939006677210619e-09  2.86793190136054e-05 target
failures  0 at all three nodes
```

All three nodes share the same maximum q radius `36.099947214126594`, and the
all-delta exponential envelope remains valid. The remote-tail result gives
evidence against a hidden endpoint spike, but it is not a universal 30-node
certificate. A uniform node envelope or the remaining node runs is still
required, followed by finite-sum accumulation and owner transfer.

Artifacts:

- `results/2225_q_mpfr_interval_binding.json`
- `results/2225_q_mpfr_node3.json`
- `results/2225_q_mpfr_node29.json`
- `results/20260929_2225_q_mpfr_node29.log`
- script: `scripts/routea_weighted_zero_q_mpfr_interval_binding_2225.py`

Status: `SUPERSEDED-BY-2228` because the original charge cast complex
coefficients/weights to `float`; see [2228](2228_routea_q_mpfr_complex_weight_fix.md).
