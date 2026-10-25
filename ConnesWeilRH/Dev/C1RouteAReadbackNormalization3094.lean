import ConnesWeilRH.Dev.C1RouteANegativeEnergyWitness3093

/-!
# Same-owner Fourier measure normalization (record 3094)

The frequency used by Route A is angular frequency. Its raw squared-transform
mass is `2*pi` times the physical square at zero. Thus inverse reconstruction
uses `dxi/(2*pi)`. This is an exact normalization check on the selected owner;
it does not assert or negate the complete `qw` readback identity.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteAReadbackNormalization3094

open MeasureTheory
open C1RouteAJointSymbolData3080
open C1RouteALaplaceFourierBridge3086
open C1RouteAOwnerAnalyticTransform3092
open C1RouteANegativeEnergyWitness3093
open C1G8R0OrbitGeometry
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaNearZeros
open scoped FourierTransform

noncomputable section

theorem routeAOrbitTransform_squared_mass
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    (∫ xi : Real, ‖routeAOrbitTransform geometry xi‖ ^ 2) =
      (2 * Real.pi) * (g.convolutionSquare.test 0).re := by
  let h : Real → Real := fun y => ‖(FourierTransform.fourier g.test) y‖ ^ 2
  have heq : (fun xi : Real => ‖routeAOrbitTransform geometry xi‖ ^ 2) =
      (fun xi : Real => h (-(1 / (2 * Real.pi)) * xi)) := by
    funext xi
    rw [routeAOrbitTransform_eq_fourier geometry]
    dsimp [h]
    congr 3
    ring
  have hscale : |(-(1 / (2 * Real.pi)) : Real)⁻¹| = 2 * Real.pi := by
    simp [abs_of_pos Real.pi_pos]
  rw [heq, Measure.integral_comp_mul_left, hscale]
  dsimp [h]
  rw [SchwartzMap.integral_norm_sq_fourier,
    g.convolutionSquare_zero_eq_integral_normSq]
  simp only [Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem routeAOwner_square_at_zero_pos
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    0 < (g.convolutionSquare.test 0).re := by
  have hroot := routeAOwnerTest_ne_zero geometry
  have hvalue : ∃ x : Real, g.test x ≠ 0 := by
    by_contra hnone
    apply hroot
    ext x
    by_contra hx
    exact hnone ⟨x, hx⟩
  obtain ⟨x, hx⟩ := hvalue
  rw [g.convolutionSquare_zero_eq_integral_normSq]
  simp only [Complex.ofReal_re]
  have hcont : Continuous (fun t : Real => Complex.normSq (g.test t)) := by fun_prop
  have hcompact : HasCompactSupport (fun t : Real => Complex.normSq (g.test t)) :=
    g.compactSupport.comp_left (map_zero _)
  exact hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hcompact
    (fun t => Complex.normSq_nonneg _) (by simpa only [ne_eq, Complex.normSq_eq_zero] using hx)

theorem routeA_normalized_squared_mass
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    (∫ xi : Real, ‖routeAOrbitTransform geometry xi‖ ^ 2 / (2 * Real.pi)) =
      (g.convolutionSquare.test 0).re := by
  rw [integral_div, routeAOrbitTransform_squared_mass geometry]
  field_simp [Real.pi_ne_zero]

theorem routeA_unscaled_squared_mass_ne_square_at_zero
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    (∫ xi : Real, ‖routeAOrbitTransform geometry xi‖ ^ 2) ≠
      (g.convolutionSquare.test 0).re := by
  rw [routeAOrbitTransform_squared_mass geometry]
  have hpos := routeAOwner_square_at_zero_pos geometry
  nlinarith [Real.pi_gt_three]

/-- Correcting the positive Fourier measure factor cannot repair pointwise positivity. -/
theorem exists_normalized_negative_energy_density
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    ∃ xi : Real, xi ≠ 0 ∧
      routeAFrequencyEnergyDensity geometry xi / (2 * Real.pi) < 0 := by
  obtain ⟨xi, hxi, _, _, henergy⟩ :=
    exists_nonzero_frequency_negative_energy_witness geometry
  exact ⟨xi, hxi, div_neg_of_neg_of_pos henergy (by positivity)⟩

end
end C1RouteAReadbackNormalization3094
end Source
end ConnesWeilRH
