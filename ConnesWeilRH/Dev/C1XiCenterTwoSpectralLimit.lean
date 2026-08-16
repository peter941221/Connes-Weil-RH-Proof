import ConnesWeilRH.Dev.C1XiCenterTwoRectangleAssembly
import ConnesWeilRH.Dev.C1SpectralSummability

/-!
# C1XiCenterTwoSpectralLimit - unconditional selected-height contour limit

The dyadic center-`2` heights escape to infinity, so their finite-height zero
sets form a cofinal family of finite subsets of the complete source spectrum.
Absolute spectral summability then identifies the complex finite sums with the
full complex `tsum`.  Combining this with the vanishing horizontal sides gives
the exact selected-height limit of the `c=2` right-line integral.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiCenterTwoSpectralLimit

open Filter
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open C1SpectralSummability
open C1SpectralWeil
open C1XiCenterTwoHorizontal
open C1XiCenterTwoHorizontalBoundary
open C1XiCenterTwoHorizontalDecay
open C1XiCenterTwoRectangleAssembly
open scoped BigOperators Topology

noncomputable section

/-- The selected dyadic center-`2` heights tend to positive infinity. -/
theorem tendsto_selectedDyadicCenterTwoHeight_atTop :
    Tendsto selectedDyadicCenterTwoHeight atTop atTop := by
  apply tendsto_atTop_mono
    (f := fun n : Nat => (n : Real))
    (g := selectedDyadicCenterTwoHeight)
  · intro n
    let H := selectedDyadicCenterTwoHorizontalData n
    calc
      (n : Real) ≤ ((n + 2 : Nat) : Real) := by
        push_cast
        norm_num
      _ ≤ (2 : Real) ^ (n + 2) := natCast_add_two_le_two_pow n
      _ ≤ H.height := H.height_lower.le
  · exact tendsto_natCast_atTop_atTop

/-- The selected symmetric-height finite sets are cofinal among all finite
subsets of the source zero subtype. -/
theorem tendsto_selected_finiteHeightZeros_atTop :
    Tendsto
      (fun n : Nat => finiteHeightZeros (selectedDyadicCenterTwoHeight n))
      atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro S
  let B : Real := ∑ rho ∈ S, |rho.1.im|
  have hterm (rho : sourceNontrivialZeroSet) (hrho : rho ∈ S) :
      |rho.1.im| ≤ B := by
    dsimp only [B]
    exact Finset.single_le_sum
      (fun u _ => abs_nonneg u.1.im) hrho
  obtain ⟨N, hN⟩ := (eventually_atTop.1
    (tendsto_selectedDyadicCenterTwoHeight_atTop.eventually_ge_atTop B))
  refine ⟨N, ?_⟩
  intro n hn
  intro rho hrho
  rw [mem_finiteHeightZeros_iff]
  exact (hterm rho hrho).trans (hN n hn)

/-- Absolute convergence identifies the selected finite-height spectral sums
with the full complex zero sum. -/
theorem tendsto_selected_finiteSpectralSum
    (F : CompactLogTest) :
    Tendsto
      (fun n : Nat => finiteSpectralSum F
        (selectedDyadicCenterTwoHeight n))
      atTop (nhds (∑' rho, spectralTerm F rho)) := by
  have hsum := (spectralSummableProp F).hasSum
  simpa only [finiteSpectralSum] using
    hsum.comp tendsto_selected_finiteHeightZeros_atTop

/-- The folded `c=2` integral converges to minus `2*pi*i` times the full
complex spectral sum.  The real scalar `spectralWeilValue` is taken only after
normalization, not inserted into this complex identity. -/
theorem tendsto_selected_centerTwoFoldedRightLineIntegral
    (F : CompactLogTest) :
    Tendsto
      (fun n : Nat => centerTwoFoldedRightLineIntegral F
        (selectedDyadicCenterTwoHeight n))
      atTop
      (nhds (-(2 * (Real.pi : Complex) * Complex.I *
        ∑' rho, spectralTerm F rho))) := by
  let K : Complex := 2 * (Real.pi : Complex) * Complex.I
  have hspectral := tendsto_selected_finiteSpectralSum F
  have hscaled : Tendsto
      (fun n : Nat => -(K * finiteSpectralSum F
        (selectedDyadicCenterTwoHeight n)))
      atTop (nhds (-(K * ∑' rho, spectralTerm F rho))) := by
    simpa using (tendsto_const_nhds.mul hspectral).neg
  have hcombined := hscaled.sub (wideHorizontalBoundaryIntegral_tendsto_zero F)
  have hcombined' : Tendsto
      (fun n : Nat =>
        -(K * finiteSpectralSum F (selectedDyadicCenterTwoHeight n)) -
          wideHorizontalBoundaryIntegral F
            (selectedDyadicCenterTwoHeight n))
      atTop (nhds (-(2 * (Real.pi : Complex) * Complex.I *
        ∑' rho, spectralTerm F rho))) := by
    simpa only [sub_zero, K] using hcombined
  apply hcombined'.congr'
  filter_upwards [] with n
  let H := selectedDyadicCenterTwoHorizontalData n
  have hfinite :=
    C1XiCenterTwoRectangleAssembly.DyadicCenterTwoHorizontalData.wideHorizontal_add_centerTwoRightLine_eq
      H F
  change -(K * finiteSpectralSum F H.height) -
      wideHorizontalBoundaryIntegral F H.height =
    centerTwoFoldedRightLineIntegral F H.height
  dsimp only [K]
  linear_combination -hfinite

/-- Normalizing by `2*pi*i` and taking real parts gives minus the independent
real spectral value. -/
theorem tendsto_selected_normalized_centerTwoRightLine_re
    (F : CompactLogTest) :
    Tendsto
      (fun n : Nat =>
        (((2 * (Real.pi : Complex) * Complex.I)⁻¹ *
          centerTwoFoldedRightLineIntegral F
            (selectedDyadicCenterTwoHeight n))).re)
      atTop (nhds (-spectralWeilValue F)) := by
  let K : Complex := 2 * (Real.pi : Complex) * Complex.I
  have hK : K ≠ 0 := by
    dsimp only [K]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hconst : Tendsto (fun _ : Nat => K⁻¹) atTop (nhds K⁻¹) :=
    tendsto_const_nhds
  have hcomplex := hconst.mul
    (tendsto_selected_centerTwoFoldedRightLineIntegral F)
  have hnormalized : Tendsto
      (fun n : Nat => K⁻¹ * centerTwoFoldedRightLineIntegral F
        (selectedDyadicCenterTwoHeight n))
      atTop (nhds (-(∑' rho, spectralTerm F rho))) := by
    have hlimit : K⁻¹ *
        (-(2 * (Real.pi : Complex) * Complex.I *
          ∑' rho, spectralTerm F rho)) =
        -(∑' rho, spectralTerm F rho) := by
      change K⁻¹ * (-(K * ∑' rho, spectralTerm F rho)) = _
      field_simp
    rw [hlimit] at hcomplex
    exact hcomplex
  have hre := (Complex.continuous_re.tendsto _).comp hnormalized
  change Tendsto
    (fun n : Nat => (K⁻¹ * centerTwoFoldedRightLineIntegral F
      (selectedDyadicCenterTwoHeight n)).re)
    atTop (nhds (-spectralWeilValue F))
  simpa only [Function.comp_apply, Complex.neg_re, spectralWeilValue] using hre

end
end C1XiCenterTwoSpectralLimit
end Source
end ConnesWeilRH
