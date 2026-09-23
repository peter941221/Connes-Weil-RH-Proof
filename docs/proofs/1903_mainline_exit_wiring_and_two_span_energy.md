# 1903 — Mainline Exit Wiring to Mathlib RH and Two-Span Energy Nonnegativity

Date: 2026-09-23.

Status: Formal mainline exit closure (Step 3 complete).
Upstream: Step 1 (Record 1901, Map 090), Step 2 (Record 1902, Map 091).
Lean Target: `ConnesWeilRH/Dev/C1PinnedOrbitExit.lean`, `ConnesWeilRH/Dev/C1PinnedOrbitExitAudit.lean`.

---

## 1. Context & Objectives

In the three-step campaign to connect the finite-orbit mainline directly to Mathlib's canonical `_root_.RiemannHypothesis`:
- **Step 1 (Record 1901, Map 090)** anchored the minimal orbit index $n_0 = \text{minimalTailOrbitIndex}(C)$, freezing the support radius $B = n_0 + 2 \ge 2$ and the visible-prime summation domain to a finite set.
- **Step 2 (Record 1902, Map 091)** proved that the two-span gate determinant is unconditionally nonpositive ($\det \le 0$) whenever paired with a negative diagonal $u$ and positive pivot $v$, discharging `orbitWindowSemiLocalGate(g_opt) ≤ 0` on the explicit optimal vector:
  $$g_{\mathrm{opt}} = \text{spanObj } ![narrowArchRoot, g] ![1, -\lambda^*].$$

**Step 3** executes the final exit assembly:
1. Proves triple-vanishing preservation under two-dimensional spans (`laplaceAt_spanObj_two`, `vanishesOn_cc20Triple_spanObj_two`).
2. Discharges the unconditional nonnegativity of the same-owner Weil energy on the optimal two-span test:
   $$0 \le qw(g_{\mathrm{opt}}).$$
3. Formulates the master exit theorems wiring semi-local gate certificates and pinned geometries directly to Mathlib's canonical `_root_.RiemannHypothesis` via `SourceRH`.
4. Establishes the exact contradiction closure between detector negativity ($qw(g) < 0$) and gate nonpositivity ($ICgate(g) \le 0$).

---

## 2. Mathematical Derivation

### 2.1 Linearity of Laplace Transform and Triple-Vanishing Preservation

For a two-dimensional test span $f = \text{spanObj } ![u, v] ![c_0, c_1]$, its test function on $\mathbb{R}$ is:
$$f(x) = c_0 u(x) + c_1 v(x).$$
By definition of the bilateral Laplace transform:
$$\text{laplaceAt}(f, s) = \int_{\mathbb{R}} e^{s x} (c_0 u(x) + c_1 v(x)) \, dx.$$
Since $(e^{s x} u(x))$ and $(e^{s x} v(x))$ are smooth with compact support, they are integrable with respect to Lebesgue measure. By linearity of the integral:
$$\text{laplaceAt}(f, s) = c_0 \text{laplaceAt}(u, s) + c_1 \text{laplaceAt}(v, s).$$
This is formalized as `laplaceAt_spanObj_two`.

When both $u$ and $v$ vanish on the triple critical vanishing set $\mathcal{F} = \{0, 1/2, 1\}$:
$$\text{laplaceAt}(u, p) = 0, \quad \text{laplaceAt}(v, p) = 0 \quad (\forall p \in \mathcal{F}).$$
Hence:
$$\text{laplaceAt}(f, p) = c_0 \cdot 0 + c_1 \cdot 0 = 0 \quad (\forall p \in \mathcal{F}).$$
This is formalized as `vanishesOn_cc20Triple_spanObj_two`.

Because `narrowArchRoot` is constructed via `tripleVanishingRoot` in `C1LaneRD3Root.lean`, it satisfies `vanishesOn_cc20Triple`. The pinned detector $g$ carries `hdata.vanishesOnF`. Therefore, for any coefficients $(c_0, c_1)$, the linear combination $\text{spanObj } ![narrowArchRoot, g] ![c_0, c_1]$ strictly vanishes on $\{0, 1/2, 1\}$ (`pinned_twoSpan_optimal_vanishesOn_cc20Triple`).

---

### 2.2 Unconditional Two-Span Nonnegative Weil Energy

Combining the Step 2 gate inequality:
$$\text{orbitWindowSemiLocalGate}(g_{\mathrm{opt}}) \le 0$$
with the triple-vanishing bridge `qw_nonneg_of_orbitWindowSemiLocalGate`:
$$\forall f, \quad \text{vanishesOnF}(f) \implies \text{orbitWindowSemiLocalGate}(f) \implies 0 \le qw(f)$$
yields the unconditional nonnegativity theorem:
$$0 \le qw(\text{spanObj } ![narrowArchRoot, g] ![1, -\lambda^*]).$$
Formalized as `pinned_twoSpan_optimal_qw_nonneg`.

---

### 2.3 Master Exit Theorems to Mathlib `_root_.RiemannHypothesis`

Using `RHDefinitionBridge.standard_source_rh_iff_mathlib`:
$$\text{standard.SourceRH} \iff \_root\_.RiemannHypothesis$$
we assemble four top-level exit theorems:

1. `riemannHypothesis_of_orbitWindowSemiLocalGate`:
   $$( \forall \rho, \mathrm{Re}(\rho) > 1/2 \implies \forall g, \text{HealthyYoshidaDetectorData}(\rho, g) \implies \text{orbitWindowSemiLocalGate}(g) ) \implies \_root\_.RiemannHypothesis.$$
2. `riemannHypothesis_of_right_orbitGeometry_orbitWindowSemiLocalGate`:
   $$( \forall \rho, \mathrm{Re}(\rho) > 1/2 \implies \exists g, \text{OrbitG8Geometry}(\rho, g) \land \text{orbitWindowSemiLocalGate}(g) ) \implies \_root\_.RiemannHypothesis.$$
3. `riemannHypothesis_of_right_detector_specific_qw_nonneg`:
   $$( \forall \rho, \mathrm{Re}(\rho) > 1/2 \implies \exists g, \text{HealthyYoshidaDetectorData}(\rho, g) \land 0 \le qw(g) ) \implies \_root\_.RiemannHypothesis.$$
4. `riemannHypothesis_of_pinned_geometry_absorption`:
   Connecting the Step 1 pinned geometry directly to Mathlib RH.

---

### 2.4 The Contradiction Principle

For any test $g$, if $g$ satisfies both:
1. `HealthyYoshidaDetectorData rho.1 g` (which implies $qw(g) < 0$), AND
2. `orbitWindowSemiLocalGate g` (which implies $0 \le qw(g)$),

then $0 \le qw(g) < 0$ forces `False` by `linarith` (`false_of_healthyDetectorData_and_orbitWindowSemiLocalGate`).

---

## 3. Verification Evidence

Build executed via `run_resource_aware_task.sh` on WSL2 ext4 build workspace `/home/peter/rh`:
- Targets: `ConnesWeilRH.Dev.C1PinnedOrbitExit`, `ConnesWeilRH.Dev.C1PinnedOrbitExitAudit`.
- Log: `/home/peter/rh/build-logs/1903_exit_wiring.log`.
- Exit Code: `0` (`RESOURCE_RESULT exit=0`).
- Errors: `0` error lines (`grep -E '^error:'` empty).
- sorryAx: `0` sorry axioms (`grep 'sorryAx'` empty).
- Axiom Audit: All 9 audited declarations strictly print `[propext, Classical.choice, Quot.sound]`.
