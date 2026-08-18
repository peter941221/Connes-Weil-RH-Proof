import ConnesWeilRH.Dev.C1PositiveTraceTraceContinuity

/-!
# Probe for diagonal ordinary-trace continuity

The probe exposes both the complex trace limit and its real-part consumer.
The required majorant and diagonal limits remain caller-supplied hypotheses.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace C1PositiveTraceTraceContinuityProbe

open Filter
open CC20Concrete.PositiveTrace
open C1PositiveTraceTraceContinuity
open scoped InnerProduct InnerProductSpace Topology

noncomputable section

theorem probe_trace_limit
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
      (𝓝 (ordinaryTraceAlong basis limitOperator)) :=
  tendsto_ordinaryTraceAlong_of_dominated_diagonal basis operators
    limitOperator bound hbound hdiagonal hdominated

theorem probe_real_trace_limit
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
      (𝓝 (ordinaryTraceAlong basis limitOperator).re) :=
  tendsto_ordinaryTraceAlong_re_of_dominated_diagonal basis operators
    limitOperator bound hbound hdiagonal hdominated

#print axioms tendsto_ordinaryTraceAlong_of_dominated_diagonal
#print axioms tendsto_ordinaryTraceAlong_re_of_dominated_diagonal
#print axioms probe_trace_limit
#print axioms probe_real_trace_limit

end
end C1PositiveTraceTraceContinuityProbe
end Dev
end Source
end ConnesWeilRH
