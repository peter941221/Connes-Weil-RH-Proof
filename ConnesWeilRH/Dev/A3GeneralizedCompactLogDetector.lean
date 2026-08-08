import ConnesWeilRH.Source.CC20Concrete.CompactRootHalfLinePair
import ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
import ConnesWeilRH.Basic

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace A3GeneralizedDetector

open scoped ComplexConjugate InnerProductSpace
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open PositiveTrace

/-- The windowed boundary detector is positive semidefinite as an operator for
EVERY compact-log test: `F† ∘ F` is `IsPositive` for `F = fullBoundaryRootFactor`. -/
theorem detector_isPositive_any
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (a c : ℝ) :
    ContinuousLinearMap.IsPositive (windowedBoundaryDetector g a c) :=
  ContinuousLinearMap.isPositive_adjoint_comp_self (fullBoundaryRootFactor g a c)

/-- Operator-level PSD corollary for every test: `re ⟨u, detector u⟩ ≥ 0`. -/
theorem detector_re_inner_nonneg_any
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (a c : ℝ) (u : cc20GlobalLogCrossingL2) :
    0 ≤ (⟪u, windowedBoundaryDetector g a c u⟫_ℂ).re :=
  ContinuousLinearMap.IsPositive.re_inner_nonneg_right (detector_isPositive_any g a c) u

end A3GeneralizedDetector
end Dev
end Source
end ConnesWeilRH
