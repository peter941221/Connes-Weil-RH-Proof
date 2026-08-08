import ConnesWeilRH.Dev.A3GeneralizedCompactLogDetector
import ConnesWeilRH.Source.CC20Concrete.PositiveTrace
import ConnesWeilRH.Source.CCM25Concrete.SelectedCrossingOperatorBridge
import ConnesWeilRH.Basic

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace CompactLogDetectorTraceBridge

open scoped ComplexConjugate InnerProductSpace
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open MeasureTheory
open CCM25Concrete
open CCM25Concrete.SelectedCrossingOperatorBridge
open PositiveTrace

open A3GeneralizedDetector

/-- Generic: when a Hilbert--Schmidt pair's two factors coincide, the ordinary
diagonal trace of their adjoint composition (`data.traceProduct`) has a
nonnegative real part, because every diagonal entry is `‖right eᵢ‖²`. -/
theorem traceProduct_re_nonneg_of_self
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {ι : Type*} {basis : HilbertBasis ι ℂ H}
    (data : BasisHilbertSchmidtPairData (G := G) basis)
    (hle : data.left = data.right) :
    0 ≤ (ordinaryTraceAlong basis data.traceProduct).re := by
  rw [ordinaryTraceAlong]
  rw [Complex.re_tsum data.summable_traceProduct_diagonal]
  apply tsum_nonneg
  intro i
  have hdiag : (⟪basis i, data.traceProduct (basis i)⟫_ℂ).re =
      ‖data.right (basis i)‖ ^ 2 := by
    rw [data.traceProduct_diagonal i, hle]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (data.right (basis i))
  rw [hdiag]
  exact sq_nonneg _

theorem fullBoundaryRootFactor_summable_normSq
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : Real)
    {iota kappa nu : Type*}
    (fullBasis : HilbertBasis iota Complex
      (Lp Complex 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa Complex
      (Lp Complex 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu Complex CC20Concrete.cc20GlobalLogCrossingL2) :
    Summable (fun i => ‖fullBoundaryRootFactor g a c (globalBasis i)‖ ^ 2) := by
  simpa [fullBoundaryRootFactor] using
    PositiveTrace.summable_normSq_precomp
      fullBasis outputBasis globalBasis
      (ContinuousKernelHilbertSchmidt.operator
        (volume : Measure (BoundaryFullInputInterval a c))
        (volume : Measure (BoundaryOutputInterval a c))
        (fullBoundaryRootKernel g a c))
      (globalL2ToKernelInterval (a - c) (c - a) 0)
      (ContinuousKernelHilbertSchmidt.basis_normSq_summable
        (volume : Measure (BoundaryFullInputInterval a c))
        (volume : Measure (BoundaryOutputInterval a c))
        (fullBoundaryRootKernel g a c) fullBasis)

theorem windowedBoundaryDetector_trace_re_nonneg
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : Real)
    {iota kappa nu : Type*}
    (fullBasis : HilbertBasis iota Complex
      (Lp Complex 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa Complex
      (Lp Complex 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu Complex CC20Concrete.cc20GlobalLogCrossingL2) :
    0 <= (ordinaryTraceAlong globalBasis (windowedBoundaryDetector g a c)).re := by
  let data : BasisHilbertSchmidtPairData
      (G := Lp Complex 2 (volume : Measure (BoundaryOutputInterval a c)))
      globalBasis :=
    { left := fullBoundaryRootFactor g a c
      right := fullBoundaryRootFactor g a c
      left_summable_normSq :=
        fullBoundaryRootFactor_summable_normSq g a c fullBasis outputBasis globalBasis
      right_summable_normSq :=
        fullBoundaryRootFactor_summable_normSq g a c fullBasis outputBasis globalBasis }
  rw [show windowedBoundaryDetector g a c = data.traceProduct by rfl]
  exact traceProduct_re_nonneg_of_self data rfl

end CompactLogDetectorTraceBridge
end Dev
end Source
end ConnesWeilRH
