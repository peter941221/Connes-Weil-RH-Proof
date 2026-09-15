# 1478 — R3 physical cutoff factor strong limit

**Status:** formal operator-level cutoff compatibility; trace/readback remains
open.

**Consumer:** the literal finite output-window factor in the G8
leakage/source-cross channel for the healthy-`CompactLog`, detector-selected
B5 route. The downstream sign target remains
`0 <= C1SameOwnerWeil.qw g` for the tower-selected detector.

The new leaf
[`C1G8R3PhysicalCutoffStrongLimit.lean`](../../ConnesWeilRH/Dev/C1G8R3PhysicalCutoffStrongLimit.lean)
proves four linked facts for the actual support-owned cutoff radius
`supportRadius g + n + 1`:

1. The reflected output projections converge strongly to the identity on the
   global logarithmic L2 carrier. The proof uses the AE interval-indicator
   formula and the finite squared L2 tail outside the growing interval.
2. The physical finite factor is exactly `P_n * F_g`, where `F_g` is the fixed
   global convolution by the detector involution.
3. Both that factor and its adjoint converge pointwise on every global L2
   vector to `F_g` and `F_g†`.
4. Composing with the actual source Sonin inclusion gives strong convergence
   of `J† * (P_n * F_g) * J` and of its adjoint on every source vector.

The paired audit checks all six public declarations and prints only
`[propext, Classical.choice, Quot.sound]` for each. Acceptance log
`20260915_r3_physical_cutoff_strong_limit_try7.log` reports
`Build completed successfully (3741 jobs)`, zero `error:` lines, and zero
`sorryAx`.

This is a strong-limit theorem, not a trace theorem. It does not establish a
uniform operator-norm bound for the doubled source sequence, a summable
source-basis column tail, convergence of any G8 channel trace, the analytic
remainder estimate, or the same-owner readback to `qw`. The conditional trace
transfer in record 1476 therefore still lacks its literal G8 hypotheses.
The detector-specific semi-local sign, C3, and RH remain open. No route ruling
changes.
