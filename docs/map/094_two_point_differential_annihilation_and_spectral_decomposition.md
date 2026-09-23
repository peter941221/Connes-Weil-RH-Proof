# 094 — Two-Point Differential Annihilation & Spectral Orbit Decomposition

Date: 2026-09-23.

Status: Active binding route record; formal closure of Stages 1 and 2 of the Two-Span Spectral Contradiction route.
Upstream: [093](093_widened_base_and_direct_absorption_nogo.md), [092](092_mainline_exit_wiring_closed.md), [091](091_two_span_sign_balancing_closed.md), Proof Record 1905.

## 1. Summary of Formal Achievements

1. **Differential Annihilation without Support Widening**:
   Constructed the two-point differential operator $\mathcal{D}_\rho = D_{1 - \bar{\rho} - 1/2} \circ D_{\rho - 1/2}$
   acting on `CompactLogTest` (`twoPointDerivativeAnnihilator`).
   - Algebraic zeroing: $\text{laplaceAt}(\mathcal{D}_\rho f, \rho - 1/2) = 0$ and $\text{laplaceAt}(\mathcal{D}_\rho f, 1 - \bar{\rho} - 1/2) = 0$;
   - Triple vanishing: strictly preserves vanishing on $\{0, 1/2, 1\}$;
   - Support preservation: strictly preserves compact support in `[-w, w]`, preventing support expansion into the prime domain;
   - For narrow tests ($w < 3/10$), the convolution square remains prime-free (`finitePrimeSum = 0`).

2. **Spectral Orbit Pairing on the Annihilator-Detector Span**:
   For the span vector $v(\lambda) = u_a - \lambda g$:
   - $\text{laplaceAt}(v(\lambda), \rho - 1/2) = -\lambda$;
   - $\text{laplaceAt}(v(\lambda), 1 - \bar{\rho} - 1/2) = +\lambda$;
   - The paired Hermitian product is identically $-\lambda^2 \le 0$ (`pairedProduct_annihilatorDetectorSpanVector_eq_neg_sq`);
   - Preserves triple vanishing and support containment in `(-B, B)`.

## 2. Route Impact

Stages 1 and 2 establish that the off-line zero orbit contribution in the span vector $v(\lambda)$ is
algebraically forced to be negative ($-2 \lambda^2$) whenever $\lambda \ne 0$, without interference from
the narrow component $u_a$. This provides the exact spectral weapon needed to close the contradiction
against the nonnegative Weil energy.

## 3. Formal Evidence

- Files: `ConnesWeilRH/Dev/C1TwoPointDifferentialAnnihilator.lean`,
         `ConnesWeilRH/Dev/C1TwoPointSpectralDecomposition.lean`, and paired audits.
- Build Logs: `build-logs/1905_spectral_annihilator.log` (3619 jobs) and `build-logs/1905_spectral_decomposition.log` (3807 jobs).
- Exit: 0, 0 errors, 0 `sorryAx`, standard axioms `[propext, Classical.choice, Quot.sound]`.
