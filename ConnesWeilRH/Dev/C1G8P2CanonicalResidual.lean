import ConnesWeilRH.Dev.C1G8P1FinitePrimeAssembly
import ConnesWeilRH.Dev.C1G8P1FinitePrimePrefixLimit
import ConnesWeilRH.Dev.C1G8P1CanonicalFamily
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSEndpointArithmeticLimit

/-!
# G8 P2 canonical visible-Euler residual

The visible Euler assembly can be inserted into the existing projection
response without introducing a scalar counterterm.  This leaf specializes the
same-owner residual decomposition to the G8 family and proves that the
visible-place residual is exactly the previously defined same-family residual.
It is an identity/trace consumer only; no vanishing or sign is asserted.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P2CanonicalResidual

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM25Concrete
open CCM25Concrete.SelectedWeilSquare
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.SelectedCrossingOperatorBridge
open C1G8P1FinitePrimeAssembly
open C1G8P1FinitePrimePrefixLimit
open C1G8P1CanonicalFamily
open C1CrossingEulerLogReadback
open CCM25Concrete.CCM24FiniteSBandTrace
open CCM25Concrete.CCM24FiniteSProjectionTrace.FinitePrimePowerFamily
open CCM25Concrete.CCM24FiniteSEndpointArithmeticLedger
open CCM25Concrete.CCM24FiniteSEndpointArithmeticLimit
open C1SelectedDetectorSemiLocalEulerBoundary
open Filter
open scoped BigOperators InnerProduct InnerProductSpace Topology

noncomputable section

noncomputable def g8VisibleEulerResidual
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (family : FinitePrimePowerFamily) :
  finiteSCarrier →L[ℂ] finiteSCarrier :=
  sameObjectResidual owner lambda family

theorem g8VisibleEulerResidual_eq_sameObjectResidual
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (family : FinitePrimePowerFamily) :
    g8VisibleEulerResidual owner lambda family =
      sameObjectResidual owner lambda family := by
  rfl

theorem projectionResponse_eq_g8VisibleBoundary_add_residual
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (family : FinitePrimePowerFamily) :
    projectionResponse owner lambda family =
      selectedEulerLogBoundaryPairOperatorSum owner
          (familyVisiblePrimePowerTerms family) +
        g8VisibleEulerResidual owner lambda family := by
  rw [g8VisibleEulerResidual]
  rw [projectionResponse_eq_arithmetic_add_residual]
  rw [← g8VisibleBoundaryOperator_eq_arithmeticOperator]

/-- The canonical residual inherits ordinary-trace legality from the fixed
G8 projection response and the same visible family.  This is the P2
specialization needed before a remainder limit can even be stated. -/
theorem g8VisibleEulerResidual_isTraceClassAlong
    (owner : SelectedWeilSquareOwner)
    (a c : ℝ) (lambda : CCM24SoninScale)
    (family : FinitePrimePowerFamily)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {nu : Type*} (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (basisData : ∀ pm : {pm // pm ∈ family.terms},
      GlobalPrimePowerTraceBasisData a c pm.1.1 pm.1.2)
    (hresponse : IsTraceClassAlong globalBasis
      (projectionResponse owner lambda family)) :
    IsTraceClassAlong globalBasis
      (g8VisibleEulerResidual owner lambda family) := by
  simpa only [g8VisibleEulerResidual] using
      (sameObjectResidual_isTraceClassAlong owner a c lambda family hsupp
      globalBasis basisData hresponse)

theorem ordinaryTraceAlong_projectionResponse_eq_g8VisibleBoundary_sum_add_residual
    (owner : SelectedWeilSquareOwner)
    (a c : ℝ) (lambda : CCM24SoninScale)
    (family : FinitePrimePowerFamily)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {nu : Type*} (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (basisData : ∀ pm : {pm // pm ∈ family.terms},
      GlobalPrimePowerTraceBasisData a c pm.1.1 pm.1.2)
    (hresponse : IsTraceClassAlong globalBasis
      (projectionResponse owner lambda family)) :
    ordinaryTraceAlong globalBasis (projectionResponse owner lambda family) =
      (∑ pm ∈ family.terms, owner.finitePrimeTerm (pm.1 ^ pm.2)) +
        ordinaryTraceAlong globalBasis
          (g8VisibleEulerResidual owner lambda family) := by
  simpa only [g8VisibleEulerResidual] using
    (ordinaryTraceAlong_projectionResponse_eq_finitePrimeSum_add_residual
      owner a c lambda family hsupp globalBasis basisData hresponse)

theorem ordinaryTraceAlong_projectionResponse_eq_selectedSupport_sum_add_g8Residual
    (owner : SelectedWeilSquareOwner)
    (a c : ℝ) (lambda : CCM24SoninScale)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {nu : Type*} (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (basisData : ∀ pm : {pm // pm ∈ (g8CanonicalFamily owner).terms},
      GlobalPrimePowerTraceBasisData a c pm.1.1 pm.1.2)
    (hresponse : IsTraceClassAlong globalBasis
      (projectionResponse owner lambda (g8CanonicalFamily owner))) :
    ordinaryTraceAlong globalBasis
        (projectionResponse owner lambda (g8CanonicalFamily owner)) =
      (∑ n ∈ (SelectedFinitePrimeSupportData.ofOwner owner).globalPrimeIndexSet,
        owner.finitePrimeTerm n) +
        ordinaryTraceAlong globalBasis
          (g8VisibleEulerResidual owner lambda (g8CanonicalFamily owner)) := by
  have hdecomp := ordinaryTraceAlong_projectionResponse_eq_g8VisibleBoundary_sum_add_residual
    owner a c lambda (g8CanonicalFamily owner) hsupp globalBasis basisData hresponse
  rw [hdecomp]
  have hterms : (g8CanonicalFamily owner).terms = canonicalPrimePowerTerms owner := by
    ext pm
    simp [g8CanonicalFamily, FinitePrimePowerFamily.ofSelectedOwner,
      FinitePrimePowerFamily.ofSelectedExactSupport, canonicalPrimePowerTerms,
      canonicalTerm, canonicalPrimePowerTerm]
  rw [hterms]
  rw [canonicalPrimePowerTerms_sum_eq_selectedFinitePrimeTerm_sum owner]

theorem tendsto_g8CompletedResidualPrefix_eq_routeTrace_sub_selectedSupport
    (basis : HilbertBasis ℕ ℂ finiteSCarrier)
    (owner : SelectedWeilSquareOwner)
    (a c : ℝ) (lambda : CCM24SoninScale)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    (basisData : ∀ pm : {pm // pm ∈ (g8CanonicalFamily owner).terms},
      GlobalPrimePowerTraceBasisData a c pm.1.1 pm.1.2)
    (hroute : IsTraceClassAlong basis
      (rootSandwichedBandResponse owner lambda (g8CanonicalFamily owner))) :
    Tendsto
      (fun N : ℕ => actualBandEndpointCompletedResidualTrace basis N owner
        lambda (g8CanonicalFamily owner))
      atTop
      (𝓝 (ordinaryTraceAlong basis
          (rootSandwichedBandResponse owner lambda (g8CanonicalFamily owner)) -
        ∑ n ∈ (SelectedFinitePrimeSupportData.ofOwner owner).globalPrimeIndexSet,
          owner.finitePrimeTerm n)) := by
  have h := tendsto_completedResidualPrefix_eq_routeTrace_sub_finitePrimeSum
    basis owner a c lambda (g8CanonicalFamily owner) hsupp basisData hroute
  have hterms : (g8CanonicalFamily owner).terms = canonicalPrimePowerTerms owner := by
    ext pm
    simp [g8CanonicalFamily, FinitePrimePowerFamily.ofSelectedOwner,
      FinitePrimePowerFamily.ofSelectedExactSupport, canonicalPrimePowerTerms,
      canonicalTerm, canonicalPrimePowerTerm]
  rw [hterms] at h
  rw [canonicalPrimePowerTerms_sum_eq_selectedFinitePrimeTerm_sum owner] at h
  exact h

end
end C1G8P2CanonicalResidual
end Source
end ConnesWeilRH
