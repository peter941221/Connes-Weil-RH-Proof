# 2141 - Overcomplete H1 null-fibre gate screen

Date: 2026-09-28.

Status: SCREEN-GO-TO-CERTIFICATION, not a producer Go or RH claim.

The consumer remains record 2138's finite-prefix residual budget leading to the selected healthy detector's same-owner signed C3' inequality. The tested owner has eight orbit/healthy target constraints at `rho = 0.945 + 39.25244858548658 i`, `N = 0`; 21 known omitted zeros are an under-approximation of the actual closed-ball zero set. The failure criterion is an unhealthy gate, residual `>= 1`, or a failed target constraint.

The 40-profile family has nullity 32 at the recorded SVD tolerance. Record 2141 applies seeded base/correction perturbations in this null fibre and screens 240 pairs. The top three were re-evaluated with complete `gate_entries` at 4001, 10001, and 20001 nodes.

At 20001 nodes:

```text
trial | C         | D            | det          | residual
162   | 0.0885167 | -8.27704e16  | -8.87424e15  | 0.0110715
136   | 0.5788051 | -1.02554e17  | -6.15828e16  | 0.0125278
234   | 0.0272463 | -9.82031e16  | -4.87471e15  | 0.0142689
```

All three retain the signs on all three grids. Trial 162's 20001-node `Ap/B` route spread is `(1.158e-5, 1.862e-6, 3.218e-6)` for `(C, B01, D)`; its maximum target residual is `2.4603e-10`. The H1 Gram condition number is `9.6237e16`, so float pin accuracy and coefficient stability are not certified. Route spread is a convergence diagnostic, not a bound.

Decision: this is a concrete numerical candidate for the changed-basis/null-fibre hypothesis. It reopens neither the 2139 cardinal path nor the dead direct/IBP L2 subroutes. The producer remains open.

Next gates:

1. Reconstruct coefficients with high-precision or interval arithmetic, including Gram and quadrature errors; do not treat `~2.5e-10` as zero.
2. Enclose the full-line signed gate and tail for this exact coefficient path; the 20001-node trapezoid is not an integral certificate.
3. Replace the known-zero list by the complete formal closed-ball owner with support-derived primes and prove uniform parameter/quantifier transfer.

Evidence:

```text
scripts/routea_overcomplete_h1_fibre_search_2141.py
results/2141_routea_overcomplete_h1_fibre_search.json
scripts/routea_overcomplete_h1_fibre_verify_2141.py
results/2141_routea_overcomplete_h1_fibre_verify.json
```
