import ConnesWeilRH.Dev.C1G8P3Contradiction
import ConnesWeilRH.Dev.C1G8R3SameOwnerGateNormalForm
import ConnesWeilRH.Dev.C1G8R3ActualEndpointTraceLimit

/-!
# G8 P4 — the aggregate equality is false at healthy-detector tests

The record-1695 de-risk rig read the endpoint carrier trace strictly
positive and N-stable while the explicit formula gives `qw < 0` at the same
test, i.e. `heq` is numerically false at the detector test.  This module
pins the matching formal fact from committed bricks alone:

* the R5 constructor (`g8R5ZeroRemainderReadbackData`) turns
  `hcore + heq` into same-owner readback data;
* the committed P3 capstone
  (`false_of_g8SameOwnerReadbackData_and_healthyDetector`) already derives
  `0 <= qw` from ANY such readback data (via the committed positivity engine
  `qw_nonnegative_of_g8SameOwnerReadbackData`) and `qw < 0` from the healthy
  detector, concluding `False`.

Composing the two: the survivor core together with the aggregate equality
is incompatible with a healthy detector at the same owner.  Since detector
existence is unconditional (CC20YoshidaConstruction.lean:2690), the sign
face cannot be delivered by proving `heq`: at every test where the gate must
produce a negative `qw`, `heq` is false.  This matches the rig verdict and
is the A1 pattern (records 1225/1226) found inside the G8 lane itself.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P4ReadbackSocketVacuity

open C1G8P3Contradiction
open ConnesWeilRH.Dev
open C1G8AdjointShearGram
open C1HealthyYoshidaDetector
open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM25Concrete
open CCM25Concrete.CCM24FiniteSBandTrace
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSGramResponse
open CCM25Concrete.SelectedWeilSquare

/-- Local completeness of the source carrier (local instances do not
propagate through imports; same as
`C1G8R3SourceRootFiniteWindowCriterion.lean:33`). -/
noncomputable local instance sourceRootFiniteWindowCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

set_option maxHeartbeats 800000 in
/-- **The R5 sign-face route is closed.**  The survivor core and the
aggregate equality `heq`, taken together with a healthy Yoshida detector at
the same owner, are jointly unsatisfiable: `heq` hands the cutoff traces a
readback whose limit is `qw`, committed positivity forces `0 <= qw`, the
detector forces `qw < 0`.  Consequently any proof of the aggregate equality
must FAIL at every healthy-detector test — exactly the tests where the gate
has to produce a negative `qw`. -/
theorem false_of_survivorCore_aggregateEq_and_healthyDetector
    {ν ρ : Type*}
    (rho : ℂ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hcore : Summable fun i : ρ =>
      ‖((sourceInclusion lambda).adjoint ∘L rootConvolution owner ∘L
        sourceInclusion lambda) (sourceBasis i)‖ ^ 2)
    (heq : (ordinaryTraceAlong sourceBasis
          (g8EndpointSourceCutoffLimitOperator owner lambda family)).re
        = C1SameOwnerWeil.qw owner.sourceTest)
    (hdetector : HealthyYoshidaDetectorData rho owner.sourceTest) :
    False :=
  false_of_g8SameOwnerReadbackData_and_healthyDetector rho owner lambda family
    globalBasis sourceBasis
    (g8R5ZeroRemainderReadbackData owner lambda family globalBasis sourceBasis
      hcore heq)
    hdetector

end C1G8P4ReadbackSocketVacuity
end Source
end ConnesWeilRH
