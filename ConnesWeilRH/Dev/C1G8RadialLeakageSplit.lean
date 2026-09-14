import ConnesWeilRH.Dev.C1G8AdjointShearGram

/-!
# G8 radial-boundary / prolate-gap leakage split

This leaf formalizes the exact operator identity isolated in proof record
1423.  It is only an algebraic projection split.  It does not assert a
Hilbert--Schmidt estimate, a trace limit, a Weil sign, or RH.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8RadialLeakageSplit

open CCM25Concrete
open CC20Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSGramResponse
open CCM25Concrete.CCM24FiniteSCommonBoundaryPair

noncomputable section

theorem source_leakage_eq_radial_boundary_add_prolate_gap
    (lambda : CCM24SoninScale)
    (B : finiteSCarrier →L[ℂ] finiteSCarrier) :
    (ContinuousLinearMap.id ℂ finiteSCarrier -
        sourceSoninProjection lambda) ∘L B ∘L sourceInclusion lambda =
      (ContinuousLinearMap.id ℂ finiteSCarrier -
          radialSupportProjection lambda) ∘L B ∘L sourceInclusion lambda +
        (radialSupportProjection lambda - sourceSoninProjection lambda) ∘L
          radialSupportProjection lambda ∘L B ∘L sourceInclusion lambda := by
  have hE : radialSupportProjection lambda ∘L
      radialSupportProjection lambda = radialSupportProjection lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      (radialSupportProjection_isStarProjection lambda).isIdempotentElem
  have hPE : sourceSoninProjection lambda ∘L
      radialSupportProjection lambda = sourceSoninProjection lambda :=
    sourceSoninProjection_comp_radialSupportProjection lambda
  apply ContinuousLinearMap.ext
  intro u
  have hE' := congrArg (fun T : finiteSCarrier →L[ℂ] finiteSCarrier =>
      T (B (sourceInclusion lambda u))) hE
  have hPE' := congrArg (fun T : finiteSCarrier →L[ℂ] finiteSCarrier =>
      T (B (sourceInclusion lambda u))) hPE
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply] at hE' hPE' ⊢
  rw [hE', hPE']
  abel

end
end C1G8RadialLeakageSplit
end Source
end ConnesWeilRH
