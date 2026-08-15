import ConnesWeilRH.Dev.C1XiFiniteHeightRectangleAssembly
import ConnesWeilRH.Dev.C1SpectralSummability

/-!
# C1XiFiniteHeightLimit - the finite-height limit assembly

The finite rectangle equation is already closed for each height-specific
factorization owner.  This module performs the final topological assembly once
three independent limits are supplied: horizontal edges, the folded right
line, and the finite spectral truncation.  It intentionally stops before the
arithmetic right-line readback; that is the remaining Gate 2 identity.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiFiniteHeightLimit

open C1SpectralWeil
open C1SpectralSummability
open CCM25Concrete.CompactLogConvolution
open Filter
open C1XiFiniteHeightRectangle
open C1XiFiniteHeightRectangleAssembly
open scoped Topology

noncomputable section

/-- One selected-height sequence with one complete rectangle owner at every
height.  The limit fields are data-bearing contracts; no height owner is
silently reused at another height. -/
structure XiFiniteHeightContourLimitContract
    (F : CompactLogTest) where
  height : Nat -> Real
  owner : Nat -> XiHeightRectangleFactorData
  owner_height : ∀ n, (owner n).height = height n
  horizontal_limit : Tendsto
    (fun n => criticalStripHorizontalBoundaryIntegral F (height n))
    atTop (𝓝 0)
  rightLineLimit : Complex
  rightLine_limit : Tendsto
    (fun n => criticalStripFoldedRightLineIntegral F (height n))
    atTop (𝓝 rightLineLimit)
  spectral_summable : SpectralSummable F
  finiteSpectral_limit : Tendsto
    (fun n => finiteSpectralSum F (height n))
    atTop (𝓝 (spectralWeilValue F : Complex))

/-- The same-owner finite rectangle equations force the right-line limit to be
the negative complete zero-spectral value.  This is the contour-limit spine;
the arithmetic interpretation of `rightLineLimit` remains a separate theorem.
-/
theorem rightLineLimit_eq_neg_spectralWeilValue
    {F : CompactLogTest} (H : XiFiniteHeightContourLimitContract F) :
    H.rightLineLimit =
      -(2 * (Real.pi : Complex) * Complex.I * (spectralWeilValue F : Complex)) := by
  have hleft : Tendsto
      (fun n => criticalStripHorizontalBoundaryIntegral F (H.height n) +
        criticalStripFoldedRightLineIntegral F (H.height n))
      atTop (𝓝 H.rightLineLimit) := by
    simpa using H.horizontal_limit.add H.rightLine_limit
  have hconstant : Tendsto
      (fun _ : Nat => (2 * (Real.pi : Complex) * Complex.I))
      atTop (𝓝 (2 * (Real.pi : Complex) * Complex.I)) :=
    tendsto_const_nhds
  have hproduct : Tendsto
      (fun n => (2 * (Real.pi : Complex) * Complex.I) *
        finiteSpectralSum F (H.height n))
      atTop (𝓝 ((2 * (Real.pi : Complex) * Complex.I) *
        (spectralWeilValue F : Complex))) :=
    hconstant.mul H.finiteSpectral_limit
  have hright : Tendsto
      (fun n => criticalStripHorizontalBoundaryIntegral F (H.height n) +
        criticalStripFoldedRightLineIntegral F (H.height n))
      atTop (𝓝 (-(2 * (Real.pi : Complex) * Complex.I *
        (spectralWeilValue F : Complex)))) := by
    apply (hproduct.neg).congr'
    filter_upwards [] with n
    have hrect :=
      XiHeightRectangleFactorData.horizontal_add_foldedRightLine_eq_neg_finiteSpectralSum
        (H.owner n) F
    simpa [H.owner_height n] using hrect.symm
  exact tendsto_nhds_unique hleft hright

end
end C1XiFiniteHeightLimit
end Source
end ConnesWeilRH
