/-
C2 probe (route-C / A0), stage 1: the positive step carrier and the key
pointwise integrand identity on the crossing window.

C1/826 formalized the trace-side Gate closure; the one analytic input left (A0)
is a nonzero carrier `k` with `<k, SingleCrossing b k> ≠ 0`.  827 established
numerically + analytically that `k = 1_{[-b,b]}` gives that inner product
`= b > 0`, i.e. on the window `[-b,0]` the integrand `k(t)·k(t+b)` is identically
`1`, so the integral is `b`.  The 827 reduction of the full Lean statement would
fold a continuous-lifted step into L2 and rewrite the inner product as a Lebesgue
integral via `L2.inner_def` (the bridge at `ContinuousKernelHilbertSchmidt:346`).

SCOPE CONTROL (honest): this module compiles the *pointwise, concrete* facts that
are the analytic heart and are fully self-contained and sorry-free, WITHOUT yet
spanning the long measure plumbing onto a Hilbert-basis diagonal (a separate,
later module).  It proves:

  1. `stepCarrierFn b` is pointwise real-nonneg of real part;
  2. on `[-b, 0]`, the integrand `(stepCarrierFn b t) * (stepCarrierFn b (t+b))`
     is identically `1` -- the clean fact 827's integral reduces to.

These are correct, finite, sorry-free facts about the concrete carrier.  Nothing
here claims RH and nothing here proves the full `ordinaryTraceAlong` statement.
-/

import ConnesWeilRH.Source.CC20Concrete.GlobalLogCrossing
import ConnesWeilRH.Basic

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace C2NonzeroCarrierProbe

open scoped ComplexConjugate

/-- The candidate positive step carrier across the origin. -/
noncomputable def stepCarrierFn (b : ℝ) : ℝ → ℂ :=
  fun t => if (-b ≤ t) ∧ (t ≤ b) then (1 : ℂ) else 0

theorem stepCarrierFn_in_window (b : ℝ) (t : ℝ)
    (htlo : -b ≤ t) (hthi : t ≤ b) :
    stepCarrierFn b t = 1 := by
  unfold stepCarrierFn
  exact if_pos ⟨htlo, hthi⟩

theorem stepCarrierFn_out_of_window (b : ℝ) (t : ℝ)
    (ht : ¬ ((-b ≤ t) ∧ (t ≤ b))) :
    stepCarrierFn b t = 0 := by
  unfold stepCarrierFn
  exact if_neg ht

/-- Nonnegativity of the real part (the carrier is a real step taking 0/1). -/
theorem stepCarrierFn_re_nonneg (b : ℝ) (t : ℝ) : 0 ≤ (stepCarrierFn b t).re := by
  by_cases ht : (-b ≤ t) ∧ (t ≤ b)
  · rw [stepCarrierFn_in_window b t ht.1 ht.2]
    norm_num
  · rw [stepCarrierFn_out_of_window b t ht]
    norm_num

/-- On the cross-window `[-b, 0]` the integrand `k(t)·k(t+b)` is `<b>`-independent:
both `t` and `t+b` lie in `[-b,b]` so both step values are `1`.  This is the
cleanest pointwise fact 827's analytic reduction rests on. -/
theorem integrand_in_Icc_negB_zero (b : ℝ) (hb : 0 ≤ b) (t : ℝ)
    (htneg : -b ≤ t) (ht0 : t ≤ 0) :
    (stepCarrierFn b t) * (stepCarrierFn b (t + b)) = 1 := by
  have hthi : t ≤ b := by
    linarith
  have ht1 : stepCarrierFn b t = 1 := stepCarrierFn_in_window b t htneg hthi
  have hlo2 : -b ≤ t + b := by
    linarith
  have hhi2 : t + b ≤ b := by linarith
  have ht2 : stepCarrierFn b (t + b) = 1 :=
    stepCarrierFn_in_window b (t + b) hlo2 hhi2
  rw [ht1, ht2]
  norm_num

-- The carrier is not the zero function: at `b` (where indoor `+b>0`) it is `1`.
theorem stepCarrierFn_ne_zero (b : ℝ) (hb : 0 < b) :
    stepCarrierFn b ≠ 0 := by
  intro hzero
  have happly : stepCarrierFn b b = 0 := by rw [hzero]; rfl
  have hnonneg : -b ≤ b := by linarith
  have hlebb : b ≤ b := le_rfl
  have hval : stepCarrierFn b b = 1 := stepCarrierFn_in_window b b hnonneg hlebb
  rw [hval] at happly
  norm_num at happly

end C2NonzeroCarrierProbe
end Dev
end Source
end ConnesWeilRH