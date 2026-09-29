# 2225 — MPFR q-construction interval certificate (superseded)

Date: 2026-09-29

Consumer: the healthy `CompactLog` B5 selected detector, actual
`sourceNontrivialZeroSet` owner, same-owner `qw >= 0` producer.

At the 2211 binding node, every scalar operation in
`q = -K/(1-(x/a)^2) + z*x` was enclosed from binary64 operands using 256-bit
MPFR RNDD/RNDU operations. The actual NumPy q value was checked against the
resulting interval at every GL and Simpson point for all 30 families.

```text
families                         30
quadrature terms                 1,944,360
interval containment failures    0
maximum q radius                 36.099947214126594
exp all-delta propagated charge  2.436718255644566e-09
charge / 2211 target             3.89561258643631e-05
```

The large q radius occurs at negligible endpoint mass. It is nevertheless
handled with the valid all-delta inequality
`|exp(q+δ)-exp(q)| <= exp(Re q) (exp(‖δ‖)-1)`; the earlier `2 exp(Re q)‖δ‖`
bound is used only when `‖δ‖ < 1`. This avoids silently applying the
small-perturbation lemma outside its hypothesis.

The certificate assumes standard IEEE-754 correctly-rounded scalar operation
semantics and treats the binary64 inputs as exact operands. Construction of
those inputs, finite-sum accumulation, other nodes, and complete owner
transfer remain open.

Artifacts:

- `results/2225_q_mpfr_interval_binding.json`
- `results/20260929_2225_q_mpfr_interval_binding_pass2.log`
- script: `scripts/routea_weighted_zero_q_mpfr_interval_binding_2225.py`

Status: `SUPERSEDED-BY-2228` because the original charge cast complex
coefficients/weights to `float`; see [2228](2228_routea_q_mpfr_complex_weight_fix.md).
