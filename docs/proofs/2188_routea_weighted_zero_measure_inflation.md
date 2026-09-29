# 2188 — Route-A weighted-zero budget inflation screen

Date: 2026-09-29  
Status: `CANDIDATE-OWNER-SCREEN-GO`; no producer closure.

## Probe

Record 2187's candidate-owner weighted budget was stress-tested with the same
owner, `m = 1600`, 240 known critical-line zeros, and two shell cutoffs. The
omitted nodes are still only a numerical critical-line list; this is not the
complete source-zero owner.

```text
N = 7, |Im z| < 256:  90 omitted zeros, budget 2.0626232939013377e-3
N = 8, |Im z| < 512: 219 omitted zeros, budget 2.0626232939013377e-3
```

The added 129 zeros therefore contribute below the displayed numerical scale
in this candidate model. With the 2138 anchor multiplicity normalized to one,
the combined multiplicity/enclosure stress factor allowed before crossing the
anchor is approximately

```text
1 / budget = 484.819502890688.
```

## Decision

The weighted-zero residual mechanism remains `SCREEN-GO` on this candidate
owner. The next exact quantitative target is now explicit:

```text
analytic multiplicity factor × outward matrix/quadrature factor
  < 484.8195...
```

This is not an analytic multiplicity bound and not an interval certificate.
The complete source-zero owner, selected-owner transfer, and comparison with
the signed `epsilon` remain open. A stress factor of 1000 would fail the
consumer anchor, so the headroom is finite and must be priced rather than
assumed.

Evidence: `scripts/routea_weighted_zero_measure_inflation_2188.py` and
`results/20260929_weighted_zero_measure_inflation_2188.log` in the WSL mirror.
