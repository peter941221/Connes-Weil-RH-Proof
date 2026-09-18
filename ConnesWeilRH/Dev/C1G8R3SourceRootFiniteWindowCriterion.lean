/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3FiniteWindowEnergyCriterion
import ConnesWeilRH.Dev.C1G8R3SourceCompressedRootKernel

/-!
# Finite-window criterion specialized to the source-compressed root

The finite approximation is the literal operator
`J† ∘L P_n ∘L C ∘L J`; it is not obtained by applying an output window to
the already compressed operator.  This distinction is essential because the
source projection need not commute with the expanding output projection.
-/

namespace ConnesWeilRH
namespace Dev

open Filter
open Source.CC20Concrete
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.SelectedCrossingOperatorBridge
open Source.CCM25Concrete.SelectedWeilSquare
open scoped Topology

noncomputable local instance sourceRootFiniteWindowCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

noncomputable def sourceCompressedRootFiniteWindow
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale) (n : ℕ) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (sourceInclusion lambda).adjoint ∘L
    kernelIntervalProjection (-(n : ℝ)) (n : ℝ) 0 ∘L
    rootConvolution owner ∘L sourceInclusion lambda

theorem sourceCompressedRoot_squareSum_of_uniform_finite_window_energy
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    {ι : Type*}
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    {B : ℝ}
    (hbound : ∀ n (s : Finset ι),
      ∑ i ∈ s, ‖sourceCompressedRootFiniteWindow owner lambda n
        (sourceBasis i)‖ ^ 2 ≤ B) :
    Summable fun i => ‖sourceCompressedRoot owner lambda (sourceBasis i)‖ ^ 2 := by
  apply summable_normSq_of_uniform_finite_window_energy sourceBasis
    (sourceCompressedRoot owner lambda)
    (sourceCompressedRootFiniteWindow owner lambda)
  · intro u
    have hproj := tendsto_kernelIntervalProjection_symmetric_apply
      (rootConvolution owner (sourceInclusion lambda u))
    have hpost := ((sourceInclusion lambda).adjoint.continuous.tendsto _).comp hproj
    simpa only [sourceCompressedRootFiniteWindow, sourceCompressedRoot,
      ContinuousLinearMap.comp_apply] using hpost
  · exact hbound

end Dev
end ConnesWeilRH
