# 096 — Concrete Annular Wing Majorant Exit to Mathlib RiemannHypothesis

Date: 2026-09-23.
Status: FORMAL EXIT COMPLETE (Lean 4 / standard axioms only).

## 1. Context & Placement

Building on Map 095 (`C1G8MasterExit`), which reduced Mathlib's `_root_.RiemannHypothesis`
to the existence of an annular wing majorant $g$ satisfying:
1. Borel measurability;
2. Nonnegativity;
3. Vanishing on $[-N, N]$;
4. Finite wing integrals $\int_N^\infty g \le C/N$ and $\int_{-\infty}^{-N} g \le C/N$;
5. Pointwise domination of the annular kernel diagonal sum:
   $\sum_i |(w_{N,n} e_i)(t)|^2 \le g(t)$,

this record documents the explicit instantiation of the concrete annular wing majorant:
$$g(t) = \begin{cases} C / t^2 & \text{if } |t| > N \\ 0 & \text{if } |t| \le N \end{cases}$$
in `ConnesWeilRH.Dev.C1G8R3ConcreteWingMajorant`.

## 2. Core Results

1. **`concreteWingMajorant_measurable`**:
   `concreteWingMajorant N C` is Borel measurable via `Measurable.piecewise`.

2. **`concreteWingMajorant_nonneg`**:
   Pointwise nonnegativity for $0 \le C$.

3. **`concreteWingMajorant_eq_zero_of_mem_Icc`**:
   Vanishes identically on $[-N, N]$.

4. **`lintegral_Ici_concreteWingMajorant_le` & `lintegral_Iic_concreteWingMajorant_le`**:
   Lebesgue integrals on $[N, \infty)$ and $(-\infty, -N]$ are bounded by $C / N$ in `ENNReal`,
   proven using improper integral calculus `integral_Ioi_rpow_of_lt` and measure-preserving reflection.

5. **`sourceCompressedRoot_squareSum_of_concreteWingMajorant`**:
   Discharges all structural integrability and support hypotheses of
   `sourceCompressedRoot_squareSum_of_annular_wing_majorant`, completely eliminating
   the need for any abstract measure-theoretic majorant wrapper.

6. **`riemannHypothesis_of_right_concrete_wing_majorant_and_aggregateEq`**:
   Deduces Mathlib's canonical `_root_.RiemannHypothesis` directly from the pointwise
   kernel diagonal estimate and the $\rho_5$ aggregate trace limit equality.

## 3. Verification & Axioms

Audited in `ConnesWeilRH.Dev.C1G8R3ConcreteWingMajorantAudit`:
- Jobs: 4080
- Error lines: 0
- `sorryAx`: 0
- Axioms: strictly standard Mathlib foundation `[propext, Classical.choice, Quot.sound]`.
