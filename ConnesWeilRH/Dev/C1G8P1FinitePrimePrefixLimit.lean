import ConnesWeilRH.Dev.C1G8P1FinitePrimeAssembly
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSEndpointArithmeticLimit

/-!
# G8 P1 visible-boundary prefix limit

The finite visible-place assembly is the same arithmetic operator used by the
existing endpoint-prefix theorem.  This leaf transports that convergence
statement to the visible boundary owner, without adding a metric/radial
comparison or a limiting readback for the physical cutoff.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1FinitePrimePrefixLimit

open CCM25Concrete
open C1G8P1FinitePrimeAssembly
open C1SelectedDetectorSemiLocalEulerBoundary
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSEndpointArithmeticLimit
open CCM25Concrete.CCM24FiniteSMovingBandPrefixCompression
open CCM25Concrete.SelectedCrossingOperatorBridge
open CC20Concrete
open Filter
open scoped BigOperators InnerProduct InnerProductSpace Matrix Topology

noncomputable section

theorem g8VisibleBoundaryOperator_eq_arithmeticOperator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) :
    selectedEulerLogBoundaryPairOperatorSum owner
        (familyVisiblePrimePowerTerms family) =
      arithmeticOperator owner family := by
  rw [selectedEulerLogBoundaryPairOperatorSum_eq_crossingOperatorSum]
  rw [familyVisiblePrimePowerTerms_natTerms_eq]
  rfl

theorem tendsto_g8VisibleBoundaryPrefixTrace_eq_finitePrimeSum
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (a c : ℝ) (family : FinitePrimePowerFamily)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    (basis : HilbertBasis ℕ ℂ finiteSCarrier)
    (basisData : ∀ pm : {pm // pm ∈ family.terms},
      GlobalPrimePowerTraceBasisData a c pm.1.1 pm.1.2) :
    Tendsto
      (fun N : ℕ => Matrix.trace (basisPrefixMatrix basis N
        (selectedEulerLogBoundaryPairOperatorSum owner
          (familyVisiblePrimePowerTerms family))))
      atTop (𝓝 (∑ pm ∈ family.terms,
        owner.finitePrimeTerm (pm.1 ^ pm.2))) := by
  have h := tendsto_arithmeticPrefixTrace_eq_finitePrimeSum owner a c family
    hsupp basis basisData
  simpa only [g8VisibleBoundaryOperator_eq_arithmeticOperator] using h

end
end C1G8P1FinitePrimePrefixLimit
end Source
end ConnesWeilRH
