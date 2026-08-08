import ConnesWeilRH.Dev.A3GeneralizedCompactLogDetector
import ConnesWeilRH.Dev.A3NonzeroCompactLogGateProbe

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace HilbertArchSignHSData

open scoped ComplexConjugate InnerProductSpace
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open PositiveTrace
open A3GeneralizedDetector
open A3NonzeroCompactLogGateProbe

abbrev CTS := ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution.CompactLogTest

/-- Operator-level arch sign on the Hilbert carrier: the windowed boundary detector
is positive semidefinite for every compact-log test and window. -/
def archSignOperatorPSD : Prop :=
  ∀ (g : CTS) (a c : Real),
    ContinuousLinearMap.IsPositive (windowedBoundaryDetector g a c)

/-- The operator-PSD arch sign holds axiom-clean: the detector is F^dagger o F. -/
theorem ArchSignOperatorPSD_true : archSignOperatorPSD := by
  intro g a b
  exact detector_isPositive_any g a b

/-- Same-owner non-vacuous witness: a NONZERO compact-log test whose windowed
detector is self-adjoint at unit window (data-bearing sign content). -/
theorem nonzero_hilbertSignData :
    ∃ g : CTS, g.test ≠ 0 ∧ IsSelfAdjoint (windowedBoundaryDetector g 1 1) := by
  refine ⟨nonzeroTest, ?_, ?_⟩
  · exact nonzeroTest_test_ne_zero
  · exact hsGate_selfAdjoint_witness 1 1

end HilbertArchSignHSData
end Dev
end Source
end ConnesWeilRH