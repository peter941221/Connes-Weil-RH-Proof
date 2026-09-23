# 093 — Universal Base Contraction Lower Bound & Direct Absorption No-Go

Date: 2026-09-23.

Status: FORMAL scoped no-go for Scheme A.1 (Direct Margin Absorption on Pinned Orbit via Geometric Contraction).
Upstream: [089](089_base_contraction_zero_target_no_go.md), [090](090_finite_index_pinning_and_frozen_prime_domain.md), [092](092_mainline_exit_wiring_closed.md), Proof Record 1904.

## 1. Summary of Findings

Scheme A.1 investigated whether widening the base support window from $(-1, 1)$ to $(-W, W)$ ($W > 1$)
could lower the seminorm bound below $1/2$ and bypass the unit-window obstruction of Map 089.

The formal mathematical audit proves that Scheme A.1 is a complete, scale-invariant no-go:

1. **Universal Contraction Factor Invariant**:
   For ANY bounded window $(a, b)$ and ANY base $f$ with $\text{laplaceAt}(f, 0) = 1$, the Young's convolution
   contraction factor satisfies:
   ```text
   (b - a) * seminorm(f) >= 1
   ```
   identically (`supportLength_mul_seminorm_ge_one_of_laplaceAt_zero_eq_one` in `C1P2BaseSeminormBound.lean`).
   Therefore, strict geometric contraction `(b - a) * seminorm(f) < 1` is refuted for all windows
   (`not_strict_base_contraction_of_arbitrary_window`).

2. **Exponential Support Explosion**:
   Under $n$-fold convolution, the support radius $L_n = n \cdot W$ grows linearly, forcing $\exp(L_n) = \exp(n W)$
   to explode exponentially. Since the $L^\infty$ norm in $\mathbb{R}$ decays at most like $O(n^{-1/2})$,
   the support-overlap product $\exp(L_n) \cdot S_n^2 \cdot H_n \sim 2 W \exp(n W)$ diverges to $+\infty$,
   making absorption impossible as $n \to \infty$.

3. **Detector Gate Polarity**:
   For the pinned detector $g$, $qw(g) < 0$ is formal. By the triple-vanishing explicit formula,
   this is definitionally equivalent to $ICgate(g.convolutionSquare) > 0$. Therefore, $g$ itself can never
   satisfy the semi-local gate $ICgate(g.convolutionSquare) <= 0$ (`orbitWindowSemiLocalGate(g)`).

## 2. Route Rulings & Strategy Impact

1. **Demotion of Scheme A.1**:
   Direct margin absorption of $g$ via geometric base contraction or convolution power decay is permanently closed.
   Do not reopen base window scaling or $L^\infty$ convolution decay campaigns.

2. **Surviving Valid Exits**:
   The Step 3 master exits (`C1PinnedOrbitExit.lean`) remain the valid target sockets:
   - To trigger RH via `riemannHypothesis_of_right_orbitGeometry_orbitWindowSemiLocalGate`, a detector must satisfy
     `orbitWindowSemiLocalGate <= 0`.
   - The optimal two-span vector $g_{\mathrm{opt}} = \text{spanObj } ![u_0, g] \ ![1, -\lambda^*]$ unconditionally
     satisfies $0 \le qw(g_{\mathrm{opt}})$ and $ICgate(g_{\mathrm{opt}}) \le 0$ (Step 2, Map 091).
   - Any future work must target genuine signed cancellations or phase-balanced spectral detection, not scalar $L^\infty$
     majorants on $g$.

## 3. Formal Evidence

- Declarations:
  `supportLength_mul_seminorm_ge_one_of_laplaceAt_zero_eq_one`
  `not_strict_base_contraction_of_arbitrary_window`
- Files: `ConnesWeilRH/Dev/C1P2BaseSeminormBound.lean`, `ConnesWeilRH/Dev/C1P2BaseSeminormBoundAudit.lean`.
- Build Log: `build-logs/1904_base_seminorm_universal.log`, exit=0, 0 errors, 0 `sorryAx`.
- Axioms: `[propext, Classical.choice, Quot.sound]`.
