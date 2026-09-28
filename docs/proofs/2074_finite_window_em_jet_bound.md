# 2074 - Aggregate Euler-Maclaurin jet-bound sizing

Date: 2026-09-28.

Status: EM-JET-BOUND-GO-CANDIDATE.

The 2051 verified real-jet machinery was reused for the same one-copy G8-H
owner. The owner weight was enclosed panelwise, while the sigma-plus-visible-
prime kernel was differentiated as one aggregate object. With panel width
`0.002` on `|xi| <= 40`:

```text
panels                         = 40000
fourth-derivative L1 proxy     = 7.578201726603793e22
Euler-Maclaurin remainder     = 1.6840448281341767e9
remainder / L2 charge          = 0.03816778221054673
remainder / sampled margin     = 0.0004944275337759636
```

This is materially tighter than the finite-difference diagnostic in record
2073 because the owner factor is bounded by the existing fourth-order jet
calculus and the aggregate kernel derivatives are evaluated before taking the
panel remainder.

Decision: `EM-JET-BOUND-GO-CANDIDATE`. The remaining gap is now localized:
center kernel derivatives and their floating-point summation need an outward
certificate, and the sigma derivative majorants need a formal interval proof.
The current result still contains floating-point centers and a sampled sigma
majorant, so it is not yet an unconditional producer theorem.

Artifact: `results/2074_finite_window_em_jet_bound.json`.
Script: `scripts/routea_finite_window_em_jet_bound_2074.py`.