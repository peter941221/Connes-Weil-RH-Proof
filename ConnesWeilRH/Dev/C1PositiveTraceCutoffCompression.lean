import ConnesWeilRH.Dev.C1PositiveTraceCutoffAdapter

/-!
# C1 positive-trace cutoff compression

The finite positive detector is not an approximation by a globally
Hilbert--Schmidt convolution square.  It is exactly the global convolution
square with a finite output projection inserted between the two convolution
legs.  Recording this identity prevents a later cutoff argument from silently
dropping the projection before its trace behaviour has been justified.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace C1PositiveTraceCutoffCompression

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CCM25Concrete.SelectedCrossingOperatorBridge

noncomputable section

/-- The uncompressed positive convolution square suggested by the finite
cutoff operators.  It is a bounded positive operator; this definition does
not assert that it has an ordinary trace on the whole-line carrier. -/
noncomputable def cutoffLimitOperatorCandidate
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  cc20GlobalConvolutionPositive g.involution.test

/-- A finite boundary detector is the uncompressed convolution square with
the reflected output-window projection left in the middle. -/
theorem windowedBoundaryDetector_eq_compressedGlobalConvolution
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c) :
    windowedBoundaryDetector g a c =
      (cc20GlobalLogConvolution g.involution.test).adjoint ∘L
        (kernelIntervalProjection (-c) (-a) 0 ∘L
          cc20GlobalLogConvolution g.involution.test) := by
  rw [windowedBoundaryDetector,
    fullBoundaryRootFactor_eq_globalConvolution g a c hsupp,
    ContinuousLinearMap.adjoint_comp]
  unfold kernelIntervalProjection
  rw [kernelIntervalL2ZeroExtension_eq_adjoint_globalL2ToKernelInterval]
  simp only [ContinuousLinearMap.adjoint_adjoint]
  apply ContinuousLinearMap.ext
  intro u
  rfl

theorem cutoffWindowedBoundaryDetector_eq_compressedGlobalConvolution
    {nu : Type*}
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) (n : Nat) :
    windowedBoundaryDetector g (C1PositiveTraceCutoffAdapter.cutoffLower g n)
        (C1PositiveTraceCutoffAdapter.cutoffUpper g n) =
      (cc20GlobalLogConvolution g.involution.test).adjoint ∘L
        (kernelIntervalProjection
          (-C1PositiveTraceCutoffAdapter.cutoffUpper g n)
          (-C1PositiveTraceCutoffAdapter.cutoffLower g n) 0 ∘L
          cc20GlobalLogConvolution g.involution.test) := by
  exact windowedBoundaryDetector_eq_compressedGlobalConvolution g
    (C1PositiveTraceCutoffAdapter.cutoffLower g n)
    (C1PositiveTraceCutoffAdapter.cutoffUpper g n)
    (C1PositiveTraceCutoffAdapter.support_subset_cutoffWindow g n)

theorem cutoffLimitOperatorCandidate_eq_convolutionSquare
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) :
    cutoffLimitOperatorCandidate g =
      cc20GlobalLogConvolution g.convolutionSquare.test := by
  exact globalConvolutionPositive_eq_convolutionSquare g

/-- Removing the finite output projection from the compressed expression
gives precisely the natural whole-line candidate.  This is an operator
identity only, not a trace-class statement. -/
theorem cutoffLimitOperatorCandidate_eq_uncompressedGlobalConvolution
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) :
    cutoffLimitOperatorCandidate g =
      (cc20GlobalLogConvolution g.involution.test).adjoint ∘L
        cc20GlobalLogConvolution g.involution.test := by
  rfl

end

end C1PositiveTraceCutoffCompression
end Dev
end Source
end ConnesWeilRH
