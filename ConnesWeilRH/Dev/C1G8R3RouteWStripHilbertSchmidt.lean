/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3RadialBoundaryEnergy

/-!
# Route W compressed window-strip Hilbert-Schmidt lemma

Map 042 work order WO-B3, record 1503 section 3, attack route W.  For an
arbitrary bounded window the root convolution restricted to that window is a
continuous-kernel operator on a compact strip, hence Hilbert-Schmidt: its
columns are square-summable on any named ambient basis.  Post-composition by
the Sonin projection (the compressed strip operator `P C P_W`) preserves the
square-sum.

This is the general-window version of the record-1495/1496 finite-window
mechanism: the window parameters `(A, C, d, e)` are free, so the strip can
be placed anywhere on the log line (the growing windows `W_N` of route W).
The tail composition is NOT estimated here: it is the irreducible remainder
of the route-W window/tail normal form (record 1505), phase-typed by the
Hardy-pressure finding.  RH is not touched.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Source.CC20Concrete
open Source.CC20Concrete.CompactConvolutionSupport
open Source.CC20Concrete.ContinuousKernelHilbertSchmidt
open Source.CC20Concrete.PositiveTrace
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.SelectedCrossingOperatorBridge
open Source.CCM25Concrete.SelectedWeilSquare
open scoped InnerProduct InnerProductSpace

noncomputable local instance routeWStripSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The compressed window-strip operator: the root convolution restricted
to the bounded input window `[d + A, e + C]` with output read on `[d, e]`,
zero-extended back to the global logarithmic carrier.  Its kernel is the
selected root's kernel on the compact strip, so this is the record-1495
finite-window mechanism placed at an arbitrary window. -/
noncomputable def routeWCompressedStripOperator
    (owner : SelectedWeilSquareOwner) (A C d e : ℝ) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  kernelIntervalL2ZeroExtension d e 0 ∘L
    ((ContinuousKernelHilbertSchmidt.operator
        (volume : Measure (CompactInputInterval A C d e))
        (volume : Measure (CompactOutputInterval d e))
        (compactOutputRootKernel owner.sourceTest A C d e)) ∘L
      (globalL2ToKernelInterval (d + A) (e + C) 0 ∘L
        cc20PositiveHalfLineProjection))

/-- Route W strip lemma: the compressed window-strip operator has
square-summable columns on any named ambient basis, for every placement of
the bounded window. -/
theorem routeWCompressedStripOperator_basis_normSq_summable
    (owner : SelectedWeilSquareOwner) (A C d e : ℝ)
    {κ τ ν : Type*}
    (inputBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (CompactInputInterval A C d e))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (CompactOutputInterval d e))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    Summable fun j : ν =>
      ‖routeWCompressedStripOperator owner A C d e (globalBasis j)‖ ^ 2 := by
  have hkernel : Summable fun i : κ =>
      ‖ContinuousKernelHilbertSchmidt.operator
          (volume : Measure (CompactInputInterval A C d e))
          (volume : Measure (CompactOutputInterval d e))
          (compactOutputRootKernel owner.sourceTest A C d e)
          (inputBasis i)‖ ^ 2 :=
    ContinuousKernelHilbertSchmidt.basis_normSq_summable
      (volume : Measure (CompactInputInterval A C d e))
      (volume : Measure (CompactOutputInterval d e))
      (compactOutputRootKernel owner.sourceTest A C d e) inputBasis
  have hrestricted : Summable fun j : ν =>
      ‖(ContinuousKernelHilbertSchmidt.operator
            (volume : Measure (CompactInputInterval A C d e))
            (volume : Measure (CompactOutputInterval d e))
            (compactOutputRootKernel owner.sourceTest A C d e) ∘L
          (globalL2ToKernelInterval (d + A) (e + C) 0 ∘L
            cc20PositiveHalfLineProjection)) (globalBasis j)‖ ^ 2 :=
    PositiveTrace.summable_normSq_precomp inputBasis outputBasis globalBasis
      (ContinuousKernelHilbertSchmidt.operator
        (volume : Measure (CompactInputInterval A C d e))
        (volume : Measure (CompactOutputInterval d e))
        (compactOutputRootKernel owner.sourceTest A C d e))
      (globalL2ToKernelInterval (d + A) (e + C) 0 ∘L
        cc20PositiveHalfLineProjection) hkernel
  have hextended : Summable fun j : ν =>
      ‖(kernelIntervalL2ZeroExtension d e 0 ∘L
            (ContinuousKernelHilbertSchmidt.operator
                (volume : Measure (CompactInputInterval A C d e))
                (volume : Measure (CompactOutputInterval d e))
                (compactOutputRootKernel owner.sourceTest A C d e) ∘L
              (globalL2ToKernelInterval (d + A) (e + C) 0 ∘L
                cc20PositiveHalfLineProjection))) (globalBasis j)‖ ^ 2 :=
    PositiveTrace.summable_normSq_postcomp globalBasis
      (ContinuousKernelHilbertSchmidt.operator
          (volume : Measure (CompactInputInterval A C d e))
          (volume : Measure (CompactOutputInterval d e))
          (compactOutputRootKernel owner.sourceTest A C d e) ∘L
        (globalL2ToKernelInterval (d + A) (e + C) 0 ∘L
          cc20PositiveHalfLineProjection))
      (kernelIntervalL2ZeroExtension d e 0) hrestricted
  exact hextended

/-- The compressed strip operator after the Sonin projection - the `P C
P_W` of route W - keeps square-summable columns: the projection is a
bounded post-factor and costs at most its operator norm squared. -/
theorem routeW_compressedStrip_projection_basis_normSq_summable
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (A C d e : ℝ)
    {κ τ ν : Type*}
    (inputBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (CompactInputInterval A C d e))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (CompactOutputInterval d e))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    Summable fun j : ν =>
      ‖(sourceSoninProjection lambda ∘L
          routeWCompressedStripOperator owner A C d e) (globalBasis j)‖ ^ 2 :=
  PositiveTrace.summable_normSq_postcomp globalBasis
    (routeWCompressedStripOperator owner A C d e)
    (sourceSoninProjection lambda)
    (routeWCompressedStripOperator_basis_normSq_summable owner A C d e
      inputBasis outputBasis globalBasis)

end Dev
end ConnesWeilRH
