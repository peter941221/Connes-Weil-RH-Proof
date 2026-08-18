import ConnesWeilRH.Source.CC20Concrete.PositiveTrace
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Continuity of the diagonal ordinary trace

This file isolates the generic limit theorem needed by a future cutoff
producer.  A pointwise limit of diagonal matrix coefficients may be passed
through `ordinaryTraceAlong` when one summable real majorant controls every
diagonal.  The majorant is an explicit hypothesis; this theorem does not
manufacture it from compactness, an operator norm bound, or a same-owner
identity.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace C1PositiveTraceTraceContinuity

open Filter
open CC20Concrete.PositiveTrace
open scoped InnerProduct InnerProductSpace Topology

noncomputable section

/-- Tannery convergence for the diagonal ordinary trace on one fixed Hilbert
basis.  The limit operator need not be trace-class by a separate field: the
summable majorant and the diagonal limit imply that its diagonal series is
summable as part of the proof. -/
theorem tendsto_ordinaryTraceAlong_of_dominated_diagonal
    {ι H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (basis : HilbertBasis ι ℂ H)
    (operators : Nat → H →L[ℂ] H)
    (limitOperator : H →L[ℂ] H)
    (bound : ι → ℝ)
    (hbound : Summable bound)
    (hdiagonal : ∀ i,
      Tendsto
        (fun n => ⟪basis i, operators n (basis i)⟫_ℂ)
        atTop
        (𝓝 (⟪basis i, limitOperator (basis i)⟫_ℂ)))
    (hdominated : ∀ n i,
      ‖⟪basis i, operators n (basis i)⟫_ℂ‖ ≤ bound i) :
    Tendsto
      (fun n => ordinaryTraceAlong basis (operators n))
      atTop
      (𝓝 (ordinaryTraceAlong basis limitOperator)) := by
  simpa only [ordinaryTraceAlong] using
    (tendsto_tsum_of_dominated_convergence hbound hdiagonal
      (Filter.Eventually.of_forall hdominated))

/-- Real-part readback of the diagonal trace convergence. -/
theorem tendsto_ordinaryTraceAlong_re_of_dominated_diagonal
    {ι H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (basis : HilbertBasis ι ℂ H)
    (operators : Nat → H →L[ℂ] H)
    (limitOperator : H →L[ℂ] H)
    (bound : ι → ℝ)
    (hbound : Summable bound)
    (hdiagonal : ∀ i,
      Tendsto
        (fun n => ⟪basis i, operators n (basis i)⟫_ℂ)
        atTop
        (𝓝 (⟪basis i, limitOperator (basis i)⟫_ℂ)))
    (hdominated : ∀ n i,
      ‖⟪basis i, operators n (basis i)⟫_ℂ‖ ≤ bound i) :
    Tendsto
      (fun n => (ordinaryTraceAlong basis (operators n)).re)
      atTop
      (𝓝 (ordinaryTraceAlong basis limitOperator).re) := by
  have htrace := tendsto_ordinaryTraceAlong_of_dominated_diagonal basis
    operators limitOperator bound hbound hdiagonal hdominated
  simpa only [Function.comp_apply] using
    (Complex.continuous_re.tendsto
      (ordinaryTraceAlong basis limitOperator)).comp htrace

end
end C1PositiveTraceTraceContinuity
end Dev
end Source
end ConnesWeilRH
