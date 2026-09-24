# 105 — Coarse Macro-Atom Variance Domination for the Four-Point Gate Determinant

Date: 2026-09-24.

Status: PROJECT CANDIDATE under [003](003_b1_b5_minimal_exit_route_selection.md)
and [103](103_four_point_same_span_three_cut_campaign.md). The original
three-step / 30x closure argument below is superseded by the source audit in
[1957](../proofs/1957_plan_b_same_owner_joint_margin_reaudit.md).

## Current execution contract (authoritative correction)

The detailed work order is now [106](106_centered_signed_moments_joint_tail_execution.md).
Use its owner ledger, quantifier order, error budget, and acceptance gates for
implementation; this record retains the original proposal and its correction.

Keep the exact selected owner `g_n`, its four-point span, and its own finite
visible-prime set. Certify the full determinant and the relative spectral-tail
budget at the same owner-specific vertex and the same convolution index.
For each hypothetical off-line zero, one such index suffices; a common index
or common constants for all zero heights are not required.

The candidate coarse method uses complete centered signed moments, including
negative-region variance and all interval-complement errors. Two interval
mass bounds and the two-point polynomial gap do not establish that budget.
An actual-owner coefficient lower bound can control the relative tail without
an upper coefficient bound. All required signed estimates remain OPEN.

Record 1955 still assumes mean-gap and domination premises; record 1953's
rational tuples have no certified actual-owner integral readback; record
1956's determinant-named exit still assumes spectral negativity. The original
ANOVA display below has the sign of minus the determinant. Its claimed 30x
ratio and unconditional conclusion are withdrawn. See 1957 for exact formulas,
source evidence, failure criteria, and the prioritized work order.

This is an audit correction, not a new producer or a binding route change.
No RH claim is made.

## Historical proposal (superseded; not proof authority)

## Owner and Consumer

- **Owner**: Selected healthy detector $g = \text{selectedOwner base correction } n$
  with compact support in $(-B, B)$, triple vanishing on $\{0, 1/2, 1\}$, and
  positive pivot $C = \text{ICgate}(g.square) > 0$.
- **Span vector**: $v(\lambda) = u - \lambda g$, where $u = \text{fullFunctionalEquationOrbitAnnihilator } g \rho$.
- **Consumer**:
  - `riemannHypothesis_of_bipartite_mean_gap_domination` and
    `riemannHypothesis_of_gate_determinant_neg` in
    `ConnesWeilRH/Dev/C1FourPointMainlineRH.lean`.
  - Master exit: Mathlib canonical `_root_.RiemannHypothesis`.

## Mathematical Foundation: The 30x Structural Variance Gap

By Record 1919 and Record 1952, the gate determinant of the four-point span
$v(\lambda) = u - \lambda g$ is an exact signed variance:
$$\det = A^2 \text{Var}_\nu(P)$$
with respect to the signed measure $d\mu(\xi) = K(\xi) W(\xi) d\xi$, where
$W(\xi) = |\widehat{g}(\xi)|^2 \ge 0$ is the energy density and $K(\xi)$ is the
Weil explicit kernel:
$$K(\xi) = \sigma(2\pi\xi) + 2 \sum_{n \text{ visible}} \frac{\Lambda(n)}{\sqrt{n}} \cos(2\pi\xi \log n)$$

Under the bipartite ANOVA variance decomposition (Record 1952,
`bipartite_variance_mean_gap_identity`):
$$\det = C_1 C_2 (p_1 - p_2)^2 + (C_1 - C_2)(C_2 \text{var}_2 - C_1 \text{var}_1)$$

Record 1955 (`C1ParametricMeanGapDomination.lean`) established that for all
non-trivial zeros with $\gamma^2 - \delta^2 \ge 190$:
$$P_{\delta, \gamma}(0) - P_{\delta, \gamma}(4) \ge 5{,}700 \implies (\Delta P)^2 \ge 3.25 \times 10^7$$
In contrast, inside the central macro-zone $I_0 = [0, 0.3]$, the maximum internal
oscillation is bounded by $\text{Osc}_{I_0}(P) \le 1{,}408$, with variance at most
$1.98 \times 10^6$.

**Structural Domination Ratio**: The between-group negative shift variance
exceeds the internal positive variance by a factor greater than **30:1**:
$$\frac{(\Delta P)^2}{\text{Var}_{I_0}(P)} \ge \frac{3.25 \times 10^7}{1.98 \times 10^6} \approx 16.4 \text{ to } 30+$$

Consequently, high-precision transcendental integration is mathematically
unnecessary. The signed inequality $\det < 0$ can be completely closed by
coarse-grained interval energy bounds.

## Plan B: Three-Step Implementation Architecture

```text
┌────────────────────────────────────────────────────────────────────────┐
│ Step 1: Coarse Macro-Interval Energy Bounds (C1MacroIntervalMeasure)   │
│ - Identify positive cluster I_0 = [0, 0.3] where K(xi) >= m_0 > 0      │
│ - Identify n=2 negative cluster I_1 = [0.65, 0.8] where K(xi) <= -m_1  │
│ - Prove coarse lower bounds on cluster integrals c_0 and -c_1          │
└───────────────────────────────────┬────────────────────────────────────┘
                                    │
                                    ▼
┌────────────────────────────────────────────────────────────────────────┐
│ Step 2: Plug into Macro-Atom Variance Negativity Certificate           │
│ - Apply exists_pos_lambda_quadratic_neg_of_macro_atom_bounds           │
│ - Use 30x ratio to absorb coarse integral tolerances                   │
│ - Deduce universal gate determinant det < 0 and B' > 0                 │
└───────────────────────────────────┬────────────────────────────────────┘
                                    │
                                    ▼
┌────────────────────────────────────────────────────────────────────────┐
│ Step 3: Master Mainline Discharge to _root_.RiemannHypothesis          │
│ - Plug universal det < 0 into riemannHypothesis_of_gate_determinant_neg│
│ - Eliminate all premises in C1FourPointMainlineRH.lean                 │
│ - Verify with [propext, Classical.choice, Quot.sound] and zero sorryAx │
└────────────────────────────────────────────────────────────────────────┘
```

## Detailed Execution Milestones

### Milestone 1: Coarse Kernel Bounds on Macro-Intervals
- **File**: `ConnesWeilRH/Dev/C1MacroIntervalKernelBound.lean`
- **Targets**:
  1. Central positive band $I_0 = [0, 0.3]$: Archimedean symbol $\sigma(2\pi\xi) > 0$
     and prime cosine terms $\cos(2\pi\xi \log n) > 0$ for all small $n$.
     Prove $K(\xi) \ge \kappa_0 > 0$ on $I_0$.
  2. First prime resonance band $I_1 = [0.65, 0.8]$: $\cos(2\pi\xi \log 2) \le -0.7$.
     The $n=2$ term $2 \frac{\log 2}{\sqrt{2}} \cos(2\pi\xi \log 2) \le -0.68$
     dominates the Archimedean tail and higher prime terms.
     Prove $K(\xi) \le -\kappa_1 < 0$ on $I_1$.

### Milestone 2: Coarse Cluster Mass Ratios
- **File**: `ConnesWeilRH/Dev/C1MacroClusterMass.lean`
- **Targets**:
  1. Relate cluster masses $C_1 = \int_{I_0} K W$ and $C_2 = -\int_{I_1} K W$.
  2. Show $C_1 > C_2 > 0$ using the central concentration of $W(\xi) = |\widehat{g}(\xi)|^2$.
  3. Prove that the mass ratio $C_2 / C_1 \ge 0.05$ comfortably exceeds the
     minimal threshold $1/30 \approx 0.033$ required by the 30x variance gap.

### Milestone 3: Total Domination and Final RH Discharge
- **File**: `ConnesWeilRH/Dev/C1FourPointMainlineRH.lean`
- **Targets**:
  1. Instantiate `riemannHypothesis_of_bipartite_mean_gap_domination`
     unconditionally for every hypothetical zero $\rho$.
  2. Complete `theorem riemannHypothesis : _root_.RiemannHypothesis` with
     zero hypotheses and standard axioms only.

## Scoped No-Gos and Guardrails

1. **No-go on split channel estimates**: Record 1948 proved that for wide owners
   ($c > 1.3$), $\text{ICgate}_{\text{arch}}$ flips sign. The proof must keep the
   summed kernel $K(\xi) = \sigma + K_{\text{prime}}$ with exact prime cancellation
   retained.
2. **No-go on fixed span coefficient**: Record 1945 proved that fixing $\lambda$
   independent of the zero height fails in 12/18 cases. The span coefficient must
   remain the vertex $\lambda = B' / (2C)$ or follow the certified mean gap witness.
3. **No-go on unverified numerical quadrature**: Floats and Python scripts are
   scouting instruments only. Every bound in Lean must be certified by exact
   algebra, interval arithmetic, or `norm_num`.
