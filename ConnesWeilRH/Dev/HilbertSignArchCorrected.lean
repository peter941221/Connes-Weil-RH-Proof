import ConnesWeilRH.Dev.A3GeneralizedCompactLogDetector
import ConnesWeilRH.Dev.A3NonzeroCompactLogGateProbe

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace HilbertSignArchCorrected

open scoped ComplexConjugate InnerProductSpace
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open PositiveTrace
open A3GeneralizedDetector
open A3NonzeroCompactLogGateProbe

/-- The data-bearing arch sign object: a NONZERO compact-log test g together with
explicit witness that the windowed boundary detector (at a chosen window) is
operator-positive (`F^dagger o F`, `F = fullBoundaryRootFactor`).  The fields are
all on the SAME g (AGENTS 10 same-owner), so the sign datum is not an empty
producer. -/
structure HilbertArchSignDatum where
  test : CCM25Concrete.CompactLogConvolution.CompactLogTest
  a : Real
  c : Real
  test_nonzero : test.test ≠ 0
  operator_psd :
    ContinuousLinearMap.IsPositive (windowedBoundaryDetector test a c)

/-- The nonzero bump test with unit window is a non-vacuous arch sign datum. -/
noncomputable def nonzeroHilbertArchDatum : HilbertArchSignDatum where
  test := nonzeroTest
  a := 1
  c := 1
  test_nonzero := nonzeroTest_test_ne_zero
  operator_psd := detector_isPositive_any nonzeroTest 1 1

/-- The arch-sign slot is not vacuous: a data-bearing instance exists. -/
theorem hilbertArchSignDatum_inhabited : Nonempty HilbertArchSignDatum :=
  ⟨nonzeroHilbertArchDatum⟩

end HilbertSignArchCorrected
end Dev
end Source
end ConnesWeilRH