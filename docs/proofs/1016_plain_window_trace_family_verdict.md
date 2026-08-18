# 1016 — Plain-window positive-trace family verdict (dead for `qw` readback)

Date: 2026-08-18.
Scope: the plain-window cutoff detector family (`windowedBoundaryDetector`
through `cutoffPositiveBasisData`) on the fixed whole-line carrier.

## Verdict

The plain-window cutoff family cannot read back `C1SameOwnerWeil.qw` under
ANY remainder correction.  The remainder-corrected contract type itself is
uninhabited for every nonzero compact-log root on every fixed whole-line
basis.  This is a structural property of the family — its trace is exactly
the window bulk mass and carries no arithmetic content — not a missing
estimate.

## Evidence chain (all axiom-clean `[propext, Classical.choice, Quot.sound]`)

1. Exact window-trace formula
   (`Dev/C1PositiveTraceCutoffGrowth.lean`):

   ```text
   Tr(cutoff n) = (cutoffUpper g n − cutoffLower g n) * ∫ ‖g.test x‖² dx
   ```

   The finite-window trace is EXACTLY the window bulk mass.  No pole,
   prime-power, or archimedean-oscillation content appears at any `n`.

2. Strict positivity of the mass for every nonzero root:
   `integral_normSq_pos_of_test_ne_zero`.

3. Linear unboundedness of the raw cutoff traces:
   `cutoffPositiveBasisData_trace_re_unbounded_of_test_ne_zero`, and hence
   the dominated-diagonal witness is impossible:
   `not_nonempty_cutoffDominatedTraceWitness_of_test_ne_zero`.

4. NEW, this verdict (`Dev/C1PositiveTraceCutoffVerdict.lean`):

   ```lean
   cutoffPositiveBasisData_trace_re_monotone :
     Monotone (fun n => (Tr (cutoff n)).re)

   not_nonempty_cutoffLimitContracts_of_test_ne_zero (hg : g.test ≠ 0) :
     IsEmpty (CutoffLimitContracts g globalBasis)
   ```

   Proof: the two `CutoffLimitContracts` fields force the raw trace to
   converge to the FINITE value `qw g` (`readback_tendsto_qw` plus
   `remainder_tendsto_zero`, via `Tendsto.add` and `sub_add_cancel`), while
   the exact formula plus monotonicity forces the same trace to grow
   linearly to `+∞`.  No finite limit can coexist with monotone divergence,
   so the contract type is empty.

## What this kills

- Reading `qw` as `lim_n (window trace n − remainder n)` with
  `remainder → 0` on THIS family: fixed basis or varying, dominated or not.
- Any future attempt to "estimate harder" on the plain window: the
  obstruction is the operator family, not the estimates.

## What survives / next direction

- A productive positive-trace limit must change the DETECTOR FAMILY so the
  window bulk cancels and arithmetic oscillation survives the trace — the
  natural candidate is the Hilbert-transform/Mellin-conjugated window (the
  semilocal `C_h* C_h J_b` object), not the plain crossing window.
- The RH distance is unchanged: Lane R (global spectral nonnegativity on
  healthy triple-vanishing squares, consumed by
  `healthy_sourceRH_of_global_spectral_nonneg`) remains the sole RH-level
  gap.
- RH NOT claimed.
