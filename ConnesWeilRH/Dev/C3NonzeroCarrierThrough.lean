/-
C3 probe (route-C / A0): the concrete nonzero carrier DOES make the crossing
inner product genuinely nonzero — broken through axiom-free.

C2 proved, on the trace side, the closure `ordinaryTraceAlong basis
(cc20SmoothedCrossing b k h) = <h, SingleCrossing b k>` and the pointwise
crossing-window identity.  The one analytic input C1/826 left open (A0) is:
does some nonzero carrier `k` make `<k, SingleCrossing b k> ≠ 0`?  827
established numerically + analytically that the positive step carrier
`k = 1_{[-b,b]}` gives exactly `= b > 0`.

This module turns that into an axiom-clean Lean statement.  We instantiate the
step carrier as `indicatorConstLp` of `Icc (-b) b` in `cc20GlobalLogCrossingL2`,
then route the inner product through `L2.inner_def` and the crossing window
identity to reduce it to the Lebesgue length of `Icc (-b) 0`, which is `b`.
Because `0 < b`, the crossing inner product is strictly positive real.

SCOPE CONTROL (honest): this module proves the concrete, positive fact about
this specific carrier.  It does NOT claim RH and does NOT prove
`ordinaryTraceAlong` equals a Lebesgue integral for general L2 carriers (a
separate long chain).  The point is to close the A0 analytic parcel C1/826 left
open: a concrete nonzero carrier with positive crossing inner product.
-/

import ConnesWeilRH.Source.CC20Concrete.GlobalLogCrossing
import ConnesWeilRH.Source.CC20Concrete.GlobalLogCrossingTraceClass
import ConnesWeilRH.Source.CC20Concrete.PositiveTrace
import ConnesWeilRH.Dev.C2NonzeroCarrierProbe
import ConnesWeilRH.Basic

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace C3NonzeroCarrierThrough

open scoped ComplexConjugate InnerProduct InnerProductSpace
open MeasureTheory

/-- The interval `Icc (-b) b` has finite Lebesgue measure. -/
lemma volume_icc_negb_b_ne_top (b : ℝ) :
    volume (Set.Icc (-b) b) ≠ ⊤ := by
  rw [Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

/-- The concrete positive step carrier across the origin, as an actual `L2`
element: `1_{[-b,b]}`.  (Since `cc20GlobalLogCrossingL2 = Lp ℂ 2 volume`, this
is the element `indicatorConstLp 2 (Icc (-b) b) (1 : ℂ)`.) -/
noncomputable def stepCarrierLp (b : ℝ) :
    ConnesWeilRH.Source.CC20Concrete.cc20GlobalLogCrossingL2 :=
  indicatorConstLp 2 measurableSet_Icc (volume_icc_negb_b_ne_top b) (1 : ℂ)

/-- The carrier function is exactly the indicator of `Icc (-b) b`. -/
lemma stepCarrierLp_coeFn (b : ℝ) :
    (stepCarrierLp b : ℝ → ℂ) =ᵐ[volume]
      (Set.Icc (-b) b).indicator (fun _ => (1 : ℂ)) := by
  exact indicatorConstLp_coeFn

/-- The crossing total width: `∫_{-b}^{0} 1 = b`. -/
theorem integral_one_Icc_negb_zero (b : ℝ) :
    ∫ _ in (-b)..0, (1 : ℂ) = b := by
  rw [intervalIntegral.integral_const]
  simp

/-- THE A0 witness: the concrete step carrier `k = 1_{[-b,b]}` has crossing
inner product `⟨k, SingleCrossing b k⟩ = b`, which is strictly positive when
`0 < b`.  This closes the one analytic input C1/826 left open, as an exact,
axiom-clean Lean theorem. -/
theorem stepCarrierLp_crossing_inner_eq (b : ℝ) (hb : 0 ≤ b) :
    inner ℂ (stepCarrierLp b)
      (ConnesWeilRH.Source.CC20Concrete.cc20SingleCrossingOperator b
        (stepCarrierLp b)) = (b : ℂ) := by
  rw [MeasureTheory.L2.inner_def]
  -- The integrand is ae-equal to `1_{Icc (-b) 0}` (value 1 there, 0 outside).
  have hcross :=
    ConnesWeilRH.Source.CC20Concrete.cc20SingleCrossingOperator_coeFn_eq_Icc_indicator
      b hb (stepCarrierLp b)
  have hk := stepCarrierLp_coeFn b
  have hkShift :=
    (MeasureTheory.measurePreserving_add_right volume b).quasiMeasurePreserving.ae_eq hk
  -- The integrand as a function of `t`:
  have h_int : (fun (t : ℝ) =>
      inner ℂ ((stepCarrierLp b : ℝ → ℂ) t)
        ((ConnesWeilRH.Source.CC20Concrete.cc20SingleCrossingOperator b
          (stepCarrierLp b) : ℝ → ℂ) t)) =ᵐ[volume]
      (Set.Icc (-b) 0).indicator (fun _ => (1 : ℂ)) := by
    filter_upwards [hcross, hkShift, hk] with t hc hs hkt
    rw [hc]
    simp only [RCLike.inner_apply]
    by_cases ht : t ∈ Set.Icc (-b) 0
    · -- window: both `t` and `t+b` lie in `[-b,b]`, so both factors are 1
      have htv_hi : t + b ≤ b := by linarith [ht.2]
      have htv_lo : -b ≤ t + b := by
        have hge0 : 0 ≤ t + b := by linarith [ht.1, hb]
        exact le_trans (by linarith : (-b : ℝ) ≤ 0) hge0
      have htv : t + b ∈ Set.Icc (-b) b := ⟨htv_lo, htv_hi⟩
      have htb : t ∈ Set.Icc (-b) b := ⟨ht.1, by linarith⟩
      have htv' : (stepCarrierLp b : ℝ → ℂ) (t + b) = 1 := by
        simpa [Set.indicator_of_mem htv] using hs
      have hkt' : (stepCarrierLp b : ℝ → ℂ) t = 1 := by
        simpa [Set.indicator_of_mem htb] using hkt
      simp only [Set.indicator_of_mem ht, htv', hkt']
      norm_num
    · -- outside window: crossing kills it
      simp [Set.indicator, ht]
  rw [integral_congr_ae h_int]
  rw [integral_indicator measurableSet_Icc]
  simp
  exact hb

/-- Strict positivity of the A0 scalar when the window is nonempty (`0 < b`). -/
theorem stepCarrierLp_crossing_inner_pos (b : ℝ) (hb : 0 < b) :
    0 < (inner ℂ (stepCarrierLp b)
      (ConnesWeilRH.Source.CC20Concrete.cc20SingleCrossingOperator b
        (stepCarrierLp b))).re := by
  rw [stepCarrierLp_crossing_inner_eq b (le_of_lt hb)]
  norm_num
  linarith

/-- E2: glue the Hilbert-basis diagonal trace onto the route-C trace lane.
The ordinary trace of the rank-one smoothing on ANY Hilbert basis is the
pairing `⟨h, SingleCrossing b k⟩` (library closure), which for the concrete
step carrier reduces, via the A0-through inner product, to `b`.  So the
trace-class scalar that route C reads is `b > 0` on every basis — the
diagonal readout of the A0 witness. -/
theorem stepCarrier_traceAlong_eq_b
    (b : ℝ) (hb : 0 ≤ b) {ι : Type*}
    (basis : HilbertBasis ι ℂ ConnesWeilRH.Source.CC20Concrete.cc20GlobalLogCrossingL2) :
    ConnesWeilRH.Source.CC20Concrete.PositiveTrace.ordinaryTraceAlong basis
        (ConnesWeilRH.Source.CC20Concrete.cc20SmoothedCrossing b
          (stepCarrierLp b) (stepCarrierLp b)) =
      (b : ℂ) := by
  rw [ConnesWeilRH.Source.CC20Concrete.cc20SmoothedCrossing_ordinaryTraceAlong
    b (stepCarrierLp b) (stepCarrierLp b) basis]
  exact stepCarrierLp_crossing_inner_eq b hb

/-- E2 readout as a strictly positive real: the trace scalar is `b > 0`. -/
theorem stepCarrier_traceAlong_re_pos
    (b : ℝ) (hb : 0 < b) {ι : Type*}
    (basis : HilbertBasis ι ℂ ConnesWeilRH.Source.CC20Concrete.cc20GlobalLogCrossingL2) :
    0 < (ConnesWeilRH.Source.CC20Concrete.PositiveTrace.ordinaryTraceAlong basis
        (ConnesWeilRH.Source.CC20Concrete.cc20SmoothedCrossing b
          (stepCarrierLp b) (stepCarrierLp b))).re := by
  rw [stepCarrier_traceAlong_eq_b b (le_of_lt hb) basis]
  norm_num
  linarith

end C3NonzeroCarrierThrough
end Dev
end Source
end ConnesWeilRH