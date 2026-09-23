# 092 — Mainline Exit Wiring Closed to Mathlib RH

Date: 2026-09-23.

Status: Active binding route record; formal closure of Step 3.
Upstream: [091](091_two_span_sign_balancing_closed.md), [090](090_finite_index_pinning_and_frozen_prime_domain.md), Record 1903.

## 1. Context & Route Progression

The finite-orbit mainline campaign was organized into three structured stages:
- **Step 1 ([090])**: Minimal orbit index pinning ($n_0 = \text{minimalTailOrbitIndex}(C)$), freezing the support window to $B = n_0 + 2$ and the visible-prime set to a finite range.
- **Step 2 ([091])**: Two-span sign balancing with unconditional nonpositive gate determinant ($\det \le 0$), proving `orbitWindowSemiLocalGate(g_opt) ≤ 0`.
- **Step 3 (This Record / [092])**: Mainline exit wiring to Mathlib RH.

## 2. Key Achievements in Step 3

1. **Triple-Vanishing Preservation**:
   Proved that bilateral Laplace transform is linear on two-dimensional spans (`laplaceAt_spanObj_two`), which implies that linear combinations of triple-vanishing tests strictly retain vanishing at $\{0, 1/2, 1\}$ (`vanishesOn_cc20Triple_spanObj_two`).
2. **Two-Span Weil Nonnegativity**:
   Discharged the unconditional nonnegativity theorem:
   ```text
   0 <= qw(spanObj ![narrowArchRoot, g] ![1, -lambda*])
   ```
   on the optimal two-span test, combining the Step 2 gate with the triple-vanishing bridge without sorry.
3. **Master Exit Pipeline to Mathlib RH**:
   Directly connected `orbitWindowSemiLocalGate`, `OrbitG8Geometry`, and detector-specific $0 \le qw(g)$ to Mathlib's canonical `_root_.RiemannHypothesis` through `RHDefinitionBridge.standard_source_rh_iff_mathlib`:
   - `riemannHypothesis_of_orbitWindowSemiLocalGate`
   - `riemannHypothesis_of_right_orbitGeometry_orbitWindowSemiLocalGate`
   - `riemannHypothesis_of_right_detector_specific_qw_nonneg`
   - `riemannHypothesis_of_pinned_geometry_absorption`
4. **Contradiction Principle**:
   Proved `false_of_healthyDetectorData_and_orbitWindowSemiLocalGate`: if any test simultaneously satisfies `HealthyYoshidaDetectorData` and `orbitWindowSemiLocalGate`, `linarith` directly produces `False`.

## 3. Formal Evidence

- Files: `ConnesWeilRH/Dev/C1PinnedOrbitExit.lean` and `ConnesWeilRH/Dev/C1PinnedOrbitExitAudit.lean`.
- Build Log: `build-logs/1903_exit_wiring.log`, exit code 0, 0 error lines, 0 `sorryAx`.
- Axioms: `[propext, Classical.choice, Quot.sound]`.
