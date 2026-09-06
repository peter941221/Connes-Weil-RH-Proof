import ConnesWeilRH.Dev.C1BombieriP2Bridge
import ConnesWeilRH.Dev.C1HealthyYoshidaSpectralPrefix

/-!
# Exact horizontal defect of the selected detector's spectral prefix

The B5 Bombieri prefix consumer must retain the two reflected Laplace values.
This leaf derives their signed decomposition from the genuine square law;
it assumes neither a prefix identification nor a positivity certificate.
-/

namespace ConnesWeilRH.Source.C1P2SpectralHorizontalDefect

open CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open C1SpectralWeil C1HealthyYoshidaDetector
open C1HealthyYoshidaSpectralNegativity C1BombieriP2Bridge
open C1HealthyYoshidaSpectralPrefix
open C1HealthyYoshidaClosedPrefix
open C1HealthyYoshidaUnscaledOrbit
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open C1BombieriSection8TotalAssembly
open C1BombieriSection8EndpointCorrection
open C1BombieriSection8WirtingerSlice3
open C1BombieriSection8ExpMass
open C1BombieriSection8QForm
open C1BombieriSection8EndpointWirtinger
open scoped BigOperators

noncomputable section

/-- The frequency satisfying `rho = 1/2 + I * frequency`. -/
def zeroFrequency (rho : sourceNontrivialZeroSet) : Complex :=
  -Complex.I * centeredXiCoordinate rho

theorem zeroFrequency_im (rho : sourceNontrivialZeroSet) :
    (zeroFrequency rho).im = 1 / 2 - rho.1.re := by
  simp [zeroFrequency, centeredXiCoordinate, Complex.mul_im]

theorem zeroFrequency_im_eq_zero_iff (rho : sourceNontrivialZeroSet) :
    (zeroFrequency rho).im = 0 ↔ rho.1.re = 1 / 2 := by
  rw [zeroFrequency_im]
  constructor <;> intro h <;> linarith

/-- A direct real-Γ Bombieri port cannot identify a real ordinate with the
actual frequency of an off-line zero.  This is an owner obstruction, not a
numerical observation: equality to a real complex number forces zero
imaginary part, hence the critical line. -/
theorem no_direct_real_frequency_identification_of_off_line
    (rho : sourceNontrivialZeroSet) (hoff : rho.1.re ≠ 1 / 2)
    (gamma : Real) (hgamma : (gamma : Complex) = zeroFrequency rho) :
    False := by
  have him : (zeroFrequency rho).im = 0 := by
    rw [← hgamma]
    simp
  exact hoff ((zeroFrequency_im_eq_zero_iff rho).mp him)

theorem centeredXiCoordinate_eq_I_mul_frequency (rho : sourceNontrivialZeroSet) :
    centeredXiCoordinate rho = Complex.I * zeroFrequency rho := by
  unfold zeroFrequency
  simp [← mul_assoc]

/-- Symmetric square mass at the two horizontal reflection points. -/
def pairedMass (g : CompactLogTest) (rho : sourceNontrivialZeroSet) : Real :=
  (xiMultiplicity rho : Real) / 2 *
    (Complex.normSq (CompactLogTest.laplaceAt g (centeredXiCoordinate rho)) +
      Complex.normSq (CompactLogTest.laplaceAt g (-star (centeredXiCoordinate rho))))

/-- The exact loss incurred by replacing the paired product with square mass. -/
def horizontalDefect (g : CompactLogTest) (rho : sourceNontrivialZeroSet) : Real :=
  (xiMultiplicity rho : Real) / 2 *
    Complex.normSq (CompactLogTest.laplaceAt g (centeredXiCoordinate rho) -
      CompactLogTest.laplaceAt g (-star (centeredXiCoordinate rho)))

theorem pairedMass_nonneg (g : CompactLogTest) (rho : sourceNontrivialZeroSet) :
    0 ≤ pairedMass g rho := by
  exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (by norm_num))
    (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))

theorem horizontalDefect_nonneg (g : CompactLogTest) (rho : sourceNontrivialZeroSet) :
    0 ≤ horizontalDefect g rho := by
  exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (by norm_num))
    (Complex.normSq_nonneg _)

theorem spectralTerm_re_eq_pairedMass_sub_horizontalDefect
    (g : CompactLogTest) (rho : sourceNontrivialZeroSet) :
    (spectralTerm g.convolutionSquare rho).re =
      pairedMass g rho - horizontalDefect g rho := by
  unfold spectralTerm
  rw [laplaceAt_convolutionSquare]
  simp [pairedMass, horizontalDefect, Complex.mul_re, Complex.normSq_apply]
  ring

theorem horizontalDefect_eq_zero_iff (g : CompactLogTest)
    (rho : sourceNontrivialZeroSet) :
    horizontalDefect g rho = 0 ↔
      CompactLogTest.laplaceAt g (centeredXiCoordinate rho) =
        CompactLogTest.laplaceAt g (-star (centeredXiCoordinate rho)) := by
  have hm : (xiMultiplicity rho : Real) / 2 ≠ 0 :=
    ne_of_gt (div_pos (by exact_mod_cast xiMultiplicity_pos rho) (by norm_num))
  simp only [horizontalDefect, mul_eq_zero, hm, false_or,
    Complex.normSq_eq_zero, sub_eq_zero]

theorem horizontalDefect_eq_zero_of_re_eq_half (g : CompactLogTest)
    (rho : sourceNontrivialZeroSet) (hline : rho.1.re = 1 / 2) :
    horizontalDefect g rho = 0 := by
  apply (horizontalDefect_eq_zero_iff g rho).mpr
  congr 1
  apply Complex.ext <;> simp [centeredXiCoordinate, hline]

/-- This finite identity retains analytic multiplicities without choosing
real frequencies or discarding off-line reflection differences. -/
theorem finitePrefix_re_eq_mass_sub_defect (g : CompactLogTest)
    (S : Finset sourceNontrivialZeroSet) :
    (∑ rho ∈ S, spectralTerm g.convolutionSquare rho).re =
      (∑ rho ∈ S, pairedMass g rho) - ∑ rho ∈ S, horizontalDefect g rho := by
  simp only [Complex.re_sum, spectralTerm_re_eq_pairedMass_sub_horizontalDefect,
    Finset.sum_sub_distrib]

/-- Direct readback to the existing shell-prefix owner used by Bombieri. -/
theorem shellPrefix_re_eq_mass_sub_defect (g : CompactLogTest) (N : Nat) :
    (∑ m ∈ Finset.range N, ∑' rho : spectralHeightShell m,
      spectralTerm g.convolutionSquare rho.1).re =
      (∑ rho ∈ spectralHeightShellPrefix N, pairedMass g rho) -
        ∑ rho ∈ spectralHeightShellPrefix N, horizontalDefect g rho := by
  rw [← sum_spectralHeightShellPrefix_eq_shell_prefix]
  exact finitePrefix_re_eq_mass_sub_defect g _

/-- A nonpositive finite spectral prefix forces the horizontal defect to absorb
the anchor multiplicity and the entire paired-mass contribution.  This is the
exact obstruction that a Bombieri prefix identification must account for. -/
theorem horizontalDefect_sum_ge_anchor_add_mass_of_prefix_nonpos
    (g : CompactLogTest) (N : Nat) (rho : sourceNontrivialZeroSet)
    (hprefix :
      (∑ m ∈ Finset.range N, ∑' z : spectralHeightShell m,
        spectralTerm g.convolutionSquare z.1).re ≤
        -(xiMultiplicity rho : Real)) :
    (xiMultiplicity rho : Real) +
        ∑ z ∈ spectralHeightShellPrefix N, pairedMass g z ≤
      ∑ z ∈ spectralHeightShellPrefix N, horizontalDefect g z := by
  have hmass : 0 ≤ ∑ z ∈ spectralHeightShellPrefix N, pairedMass g z := by
    exact Finset.sum_nonneg fun z hz => pairedMass_nonneg g z
  rw [shellPrefix_re_eq_mass_sub_defect g N] at hprefix
  linarith

/-- The same lower bound in the finite-set spelling, useful when the detector
construction supplies a closed-ball prefix rather than a shell cutoff. -/
theorem horizontalDefect_sum_ge_anchor_add_mass_of_finset_prefix_nonpos
    (g : CompactLogTest) (S : Finset sourceNontrivialZeroSet)
    (rho : sourceNontrivialZeroSet)
    (hprefix :
      (∑ z ∈ S, spectralTerm g.convolutionSquare z).re ≤
        -(xiMultiplicity rho : Real)) :
    (xiMultiplicity rho : Real) + ∑ z ∈ S, pairedMass g z ≤
      ∑ z ∈ S, horizontalDefect g z := by
  have hmass : 0 ≤ ∑ z ∈ S, pairedMass g z := by
    exact Finset.sum_nonneg fun z hz => pairedMass_nonneg g z
  rw [finitePrefix_re_eq_mass_sub_defect g S] at hprefix
  linarith

/-- The bound is now attached to the actual orbit-selected owner.  The only
analytic inputs are the existing finite-height interpolation equations; the
conclusion exposes the horizontal defect that a same-owner Bombieri producer
must control. -/
theorem selectedOwner_horizontalDefect_sum_ge_anchor_add_mass
    (base correction : CompactLogTest) (n : Nat)
    (rho : sourceNontrivialZeroSet) (hoff : rho.1.re ≠ 1 / 2)
    (hright : (1 / 2 : Real) < rho.1.re)
    (T : Real) (S : Finset sourceNontrivialZeroSet)
    (hS : S ⊆ finiteHeightZeros T) (hrho : rho ∈ S)
    (routeNodes : Finset Complex)
    (htargetValues :
      ∀ w : FiniteMellinNode (healthyUnscaledTargetNodes rho.1),
        laplaceAt ((convolutionIterate base n).convolution correction) w.1 =
          healthyUnscaledTargetValue rho.1 w)
    (hsquareZeros :
      ∀ w : FiniteMellinNode
          (sourceNontrivialZerosInClosedBallFinset rho.1
              (T + 2 + dist (2 : Complex) rho.1) ∪ routeNodes),
        w.1 ∉ healthyUnscaledTargetNodes rho.1 →
          laplaceAt (selectedOwner base correction n).convolutionSquare
            (w.1 - 1 / 2) = 0) :
    (xiMultiplicity rho : Real) +
        ∑ z ∈ S, pairedMass (selectedOwner base correction n).sourceTest z ≤
      ∑ z ∈ S, horizontalDefect (selectedOwner base correction n).sourceTest z := by
  apply horizontalDefect_sum_ge_anchor_add_mass_of_finset_prefix_nonpos
    (selectedOwner base correction n).sourceTest S rho
  have hprefix :=
    finiteSpectralPrefix_re_le_neg_xiMultiplicity_of_subset_finiteHeight_closedBall_square_zero_control
      base correction n rho hoff hright T S hS hrho routeNodes htargetValues hsquareZeros
  simpa only [selectedOwner_convolutionSquare] using hprefix

/-- The pinned zero configuration fixes the horizontal defect at the anchor:
the raw orbit values `1` and `-1` become a difference of size `2` after the
half-density shift, hence the exact defect `2 * xiMultiplicity rho`. -/
theorem selectedOwner_horizontalDefect_anchor_eq_two_mul_multiplicity
    (base correction : CompactLogTest) (n : Nat)
    (rho : sourceNontrivialZeroSet) (hoff : rho.1.re ≠ 1 / 2)
    (htargetValues :
      ∀ w : FiniteMellinNode (healthyUnscaledTargetNodes rho.1),
        laplaceAt ((convolutionIterate base n).convolution correction) w.1 =
          healthyUnscaledTargetValue rho.1 w) :
    horizontalDefect (selectedOwner base correction n).sourceTest rho =
      2 * (xiMultiplicity rho : Real) := by
  have hrawRho :
      laplaceAt ((convolutionIterate base n).convolution correction) rho.1 = 1 := by
    simpa only [healthyUnscaledTargetValue_rho rho.1] using
      htargetValues ⟨rho.1, mem_healthyUnscaledTargetNodes_rho rho.1⟩
  have hrawCompanion :
      laplaceAt ((convolutionIterate base n).convolution correction)
        (1 - star rho.1) = -1 := by
    simpa only [healthyUnscaledTargetValue_companion rho.1 hoff] using
      htargetValues ⟨1 - star rho.1,
        mem_healthyUnscaledTargetNodes_companion rho.1⟩
  have hcenter :
      -star (centeredXiCoordinate rho) =
        (1 - star rho.1) - 1 / 2 := by
    unfold centeredXiCoordinate
    simp
    ring
  have hfirst :
      laplaceAt (selectedOwner base correction n).sourceTest
        (centeredXiCoordinate rho) = 1 := by
    rw [show centeredXiCoordinate rho = rho.1 - 1 / 2 by rfl,
      selectedOwner_laplaceAt_sourceTest_centered]
    exact hrawRho
  have hsecond :
      laplaceAt (selectedOwner base correction n).sourceTest
        (-star (centeredXiCoordinate rho)) = -1 := by
    rw [hcenter, selectedOwner_laplaceAt_sourceTest_centered]
    exact hrawCompanion
  unfold horizontalDefect
  rw [hfirst, hsecond]
  norm_num [Complex.normSq_apply]
  ring

/-- The same pinned orbit values give an exact paired-mass anchor equal to
one multiplicity. -/
theorem selectedOwner_pairedMass_anchor_eq_multiplicity
    (base correction : CompactLogTest) (n : Nat)
    (rho : sourceNontrivialZeroSet) (hoff : rho.1.re ≠ 1 / 2)
    (htargetValues :
      ∀ w : FiniteMellinNode (healthyUnscaledTargetNodes rho.1),
        laplaceAt ((convolutionIterate base n).convolution correction) w.1 =
          healthyUnscaledTargetValue rho.1 w) :
    pairedMass (selectedOwner base correction n).sourceTest rho =
      (xiMultiplicity rho : Real) := by
  have hrawRho :
      laplaceAt ((convolutionIterate base n).convolution correction) rho.1 = 1 := by
    simpa only [healthyUnscaledTargetValue_rho rho.1] using
      htargetValues ⟨rho.1, mem_healthyUnscaledTargetNodes_rho rho.1⟩
  have hrawCompanion :
      laplaceAt ((convolutionIterate base n).convolution correction)
        (1 - star rho.1) = -1 := by
    simpa only [healthyUnscaledTargetValue_companion rho.1 hoff] using
      htargetValues ⟨1 - star rho.1,
        mem_healthyUnscaledTargetNodes_companion rho.1⟩
  have hcenter :
      -star (centeredXiCoordinate rho) =
        (1 - star rho.1) - 1 / 2 := by
    unfold centeredXiCoordinate
    simp
    ring
  have hfirst :
      laplaceAt (selectedOwner base correction n).sourceTest
        (centeredXiCoordinate rho) = 1 := by
    rw [show centeredXiCoordinate rho = rho.1 - 1 / 2 by rfl,
      selectedOwner_laplaceAt_sourceTest_centered]
    exact hrawRho
  have hsecond :
      laplaceAt (selectedOwner base correction n).sourceTest
        (-star (centeredXiCoordinate rho)) = -1 := by
    rw [hcenter, selectedOwner_laplaceAt_sourceTest_centered]
    exact hrawCompanion
  unfold pairedMass
  rw [hfirst, hsecond]
  norm_num [Complex.normSq_apply]

/-- The selected-owner anchor contributes exactly one negative
multiplicity to the real spectral sum. -/
theorem selectedOwner_spectralTerm_re_anchor_eq_neg_multiplicity
    (base correction : CompactLogTest) (n : Nat)
    (rho : sourceNontrivialZeroSet) (hoff : rho.1.re ≠ 1 / 2)
    (htargetValues :
      ∀ w : FiniteMellinNode (healthyUnscaledTargetNodes rho.1),
        laplaceAt ((convolutionIterate base n).convolution correction) w.1 =
          healthyUnscaledTargetValue rho.1 w) :
    (spectralTerm (selectedOwner base correction n).convolutionSquare rho).re =
      -(xiMultiplicity rho : Real) := by
  have hmass :
      pairedMass
          (halfDensityShift ((convolutionIterate base n).convolution correction)) rho =
        (xiMultiplicity rho : Real) := by
    simpa only [selectedOwner_sourceTest] using
      selectedOwner_pairedMass_anchor_eq_multiplicity base correction n rho hoff
        htargetValues
  have hdefect :
      horizontalDefect
          (halfDensityShift ((convolutionIterate base n).convolution correction)) rho =
        2 * (xiMultiplicity rho : Real) := by
    simpa only [selectedOwner_sourceTest] using
      selectedOwner_horizontalDefect_anchor_eq_two_mul_multiplicity base correction n
        rho hoff htargetValues
  rw [selectedOwner_convolutionSquare,
    spectralTerm_re_eq_pairedMass_sub_horizontalDefect, hmass, hdefect]
  ring

/-- Under the raw orbit-control hypothesis, removing the anchor from a finite
prefix leaves paired mass no larger than horizontal defect. -/
theorem selectedOwner_nonanchor_mass_le_defect_of_orbit_control
    (base correction : CompactLogTest) (n : Nat)
    (rho : sourceNontrivialZeroSet) (hoff : rho.1.re ≠ 1 / 2)
    (htargets :
      ∀ w : FiniteMellinNode (sourceFunctionalEquationOrbit rho.1),
        laplaceAt ((convolutionIterate base n).convolution correction) w.1 =
          negativeSourceOrbitValue rho.1 w)
    (S : Finset sourceNontrivialZeroSet) (hrho : rho ∈ S)
    (houtside : ∀ z : sourceNontrivialZeroSet, z ∈ S →
      z.1 ∉ sourceFunctionalEquationOrbit rho.1 →
        laplaceAt (selectedOwner base correction n).convolutionSquare
          (z.1 - 1 / 2) = 0) :
    (∑ z ∈ S.erase rho,
      pairedMass (selectedOwner base correction n).sourceTest z) ≤
      ∑ z ∈ S.erase rho,
        horizontalDefect (selectedOwner base correction n).sourceTest z := by
  classical
  have hprefix :=
    finiteSpectralPrefix_re_le_neg_xiMultiplicity_of_orbit_control
      base correction n rho hoff htargets S hrho houtside
  have hrawRho :
      laplaceAt ((convolutionIterate base n).convolution correction) rho.1 = 1 := by
    calc
      laplaceAt ((convolutionIterate base n).convolution correction) rho.1 =
          negativeSourceOrbitValue rho.1
            ⟨rho.1, mem_sourceFunctionalEquationOrbit_rho rho.1⟩ :=
        htargets ⟨rho.1, mem_sourceFunctionalEquationOrbit_rho rho.1⟩
      _ = 1 := negativeSourceOrbitValue_rho rho.1
  have hrawCompanion :
      laplaceAt ((convolutionIterate base n).convolution correction)
        (1 - star rho.1) = -1 := by
    calc
      laplaceAt ((convolutionIterate base n).convolution correction)
          (1 - star rho.1) = negativeSourceOrbitValue rho.1
            ⟨1 - star rho.1,
              mem_sourceFunctionalEquationOrbit_companion rho.1⟩ :=
        htargets ⟨1 - star rho.1,
          mem_sourceFunctionalEquationOrbit_companion rho.1⟩
      _ = -1 := negativeSourceOrbitValue_companion rho.1 hoff
  have hanchor :=
    spectralTerm_selectedOwner_eq_neg_xiMultiplicity_of_raw_hermitian_values
      base correction n rho hrawRho hrawCompanion
  have hsplit := Finset.sum_erase_add
    (s := S)
    (f := fun z : sourceNontrivialZeroSet =>
      spectralTerm (selectedOwner base correction n).convolutionSquare z)
    (a := rho) hrho
  have hrest_nonpos :
      (∑ z ∈ S.erase rho,
        spectralTerm (selectedOwner base correction n).convolutionSquare z).re ≤ 0 := by
    have hsum_eq :
        (∑ z ∈ S,
          spectralTerm (selectedOwner base correction n).convolutionSquare z).re =
          ((∑ z ∈ S.erase rho,
            spectralTerm (selectedOwner base correction n).convolutionSquare z) +
            spectralTerm (selectedOwner base correction n).convolutionSquare rho).re := by
      rw [hsplit]
    rw [Complex.add_re, hanchor] at hsum_eq
    have hcast :
        (-(xiMultiplicity rho : Complex)).re =
          -(xiMultiplicity rho : Real) := by
      norm_num
    rw [hcast] at hsum_eq
    linarith
  have hrest_nonpos_source :
      (∑ z ∈ S.erase rho,
        spectralTerm (selectedOwner base correction n).sourceTest.convolutionSquare z).re ≤ 0 := by
    simpa only [selectedOwner_convolutionSquare] using hrest_nonpos
  rw [finitePrefix_re_eq_mass_sub_defect
    (selectedOwner base correction n).sourceTest (S.erase rho)] at hrest_nonpos_source
  exact sub_nonpos.mp hrest_nonpos_source

/-- Full same-owner decomposition at every cutoff, before any sign estimate. -/
theorem qw_eq_mass_sub_defect_add_tail (g : CompactLogTest) (N : Nat) :
    C1SameOwnerWeil.qw g =
      ((∑ rho ∈ spectralHeightShellPrefix N, pairedMass g rho) -
        ∑ rho ∈ spectralHeightShellPrefix N, horizontalDefect g rho) +
      (∑' m : Nat, ∑' rho : spectralHeightShell (m + N),
        spectralTerm g.convolutionSquare rho.1).re := by
  rw [qw_eq_spectralPrefix_add_spectralTail g N, shellPrefix_re_eq_mass_sub_defect]

/-- Any Bombieri-native qIntegrand prefix producer must carry the same
finite mass-minus-horizontal-defect value on the selected owner. -/
theorem canonicalQIntegrandPrefix_re_eq_mass_sub_defect
    {g : CompactLogTest}
    (p : BombieriQuadraticCanonicalQIntegrandPrefixP2BridgeData g) :
    ((∫ x in -p.t..p.t,
        qIntegrand (expSum p.gamma p.z)
          (expSum p.gamma (dcoef p.gamma p.z)) x) -
        endpointCorrection p.t p.gamma p.z).re =
      (∑ rho ∈ spectralHeightShellPrefix
          (bombieriSpectralTailCutoff g p.t p.ht p.gamma p.z p.Lam p.lam p.hz
            p.heigen p.hrecip),
        pairedMass g rho) -
        ∑ rho ∈ spectralHeightShellPrefix
          (bombieriSpectralTailCutoff g p.t p.ht p.gamma p.z p.Lam p.lam p.hz
            p.heigen p.hrecip),
        horizontalDefect g rho := by
  rw [← p.finitePrefix_eq_qIntegrand]
  exact shellPrefix_re_eq_mass_sub_defect g
    (bombieriSpectralTailCutoff g p.t p.ht p.gamma p.z p.Lam p.lam p.hz
      p.heigen p.hrecip)

/-- A nonpositive finite spectral prefix forces the endpoint-corrected
qIntegrand value of any canonical producer to be at most the anchor mass. -/
theorem canonicalQIntegrandPrefix_re_le_neg_xiMultiplicity_of_prefix_nonpos
    {g : CompactLogTest}
    (p : BombieriQuadraticCanonicalQIntegrandPrefixP2BridgeData g)
    (rho : sourceNontrivialZeroSet)
    (hprefix :
      (∑ m ∈ Finset.range
          (bombieriSpectralTailCutoff g p.t p.ht p.gamma p.z p.Lam p.lam p.hz
            p.heigen p.hrecip),
        ∑' z : spectralHeightShell m,
          spectralTerm g.convolutionSquare z.1).re ≤
        -(xiMultiplicity rho : Real)) :
    ((∫ x in -p.t..p.t,
        qIntegrand (expSum p.gamma p.z)
          (expSum p.gamma (dcoef p.gamma p.z)) x) -
        endpointCorrection p.t p.gamma p.z).re ≤
      -(xiMultiplicity rho : Real) := by
  rw [← p.finitePrefix_eq_qIntegrand]
  exact hprefix

/-- The Wirtinger remainder forces every canonical qIntegrand producer to
keep its horizontal defect below the paired mass. -/
theorem canonicalQIntegrandPrefix_defect_le_mass
    {g : CompactLogTest}
    (p : BombieriQuadraticCanonicalQIntegrandPrefixP2BridgeData g) :
    (∑ rho ∈ spectralHeightShellPrefix
        (bombieriSpectralTailCutoff g p.t p.ht p.gamma p.z p.Lam p.lam p.hz
          p.heigen p.hrecip),
      pairedMass g rho) ≥
      ∑ rho ∈ spectralHeightShellPrefix
        (bombieriSpectralTailCutoff g p.t p.ht p.gamma p.z p.Lam p.lam p.hz
          p.heigen p.hrecip),
      horizontalDefect g rho := by
  obtain ⟨S, hS, hQ⟩ :=
    qIntegrand_sub_endpointCorrection_eq_nonneg p.t p.ht p.gamma p.z
  have hnonneg :
      0 ≤ ((∫ x in -p.t..p.t,
          qIntegrand (expSum p.gamma p.z)
            (expSum p.gamma (dcoef p.gamma p.z)) x) -
          endpointCorrection p.t p.gamma p.z).re := by
    rw [hQ]
    simp [hS]
  rw [canonicalQIntegrandPrefix_re_eq_mass_sub_defect p] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- Every canonical qIntegrand producer has a nonnegative finite spectral
prefix, because its endpoint-corrected Wirtinger remainder is nonnegative. -/
theorem canonicalQIntegrandPrefix_re_nonneg
    {g : CompactLogTest}
    (p : BombieriQuadraticCanonicalQIntegrandPrefixP2BridgeData g) :
    0 ≤ (∑ m ∈ Finset.range
        (bombieriSpectralTailCutoff g p.t p.ht p.gamma p.z p.Lam p.lam p.hz
          p.heigen p.hrecip),
      ∑' rho : spectralHeightShell m,
        spectralTerm g.convolutionSquare rho.1).re := by
  obtain ⟨S, hS, hQ⟩ :=
    qIntegrand_sub_endpointCorrection_eq_nonneg p.t p.ht p.gamma p.z
  have hqnonneg :
      0 ≤ ((∫ x in -p.t..p.t,
          qIntegrand (expSum p.gamma p.z)
            (expSum p.gamma (dcoef p.gamma p.z)) x) -
          endpointCorrection p.t p.gamma p.z).re := by
    rw [hQ]
    simp [hS]
  rw [← p.finitePrefix_eq_qIntegrand] at hqnonneg
  exact hqnonneg

/-- A canonical qIntegrand producer for the selected owner cannot use a
cutoff whose shell prefix is already certified negative by orbit control. -/
theorem no_selectedOwner_canonicalQIntegrandPrefix_of_orbit_control
    (base correction : CompactLogTest) (n : Nat)
    (rho : sourceNontrivialZeroSet) (hoff : rho.1.re ≠ 1 / 2)
    (htargets :
      ∀ w : FiniteMellinNode (sourceFunctionalEquationOrbit rho.1),
        laplaceAt ((convolutionIterate base n).convolution correction) w.1 =
          negativeSourceOrbitValue rho.1 w)
    (p : BombieriQuadraticCanonicalQIntegrandPrefixP2BridgeData
      (selectedOwner base correction n).sourceTest)
    (N : Nat) (hrhoShell : rho ∈ spectralHeightShellPrefix N)
    (houtside : ∀ z : sourceNontrivialZeroSet,
      z ∈ spectralHeightShellPrefix N →
      z.1 ∉ sourceFunctionalEquationOrbit rho.1 →
        laplaceAt (selectedOwner base correction n).convolutionSquare
          (z.1 - 1 / 2) = 0)
    (hcutoff :
      bombieriSpectralTailCutoff (selectedOwner base correction n).sourceTest
        p.t p.ht p.gamma p.z p.Lam p.lam p.hz p.heigen p.hrecip = N) :
    False := by
  have hprefix :=
    finiteSpectralPrefix_re_le_neg_xiMultiplicity_of_orbit_control
      base correction n rho hoff htargets
      (spectralHeightShellPrefix N) hrhoShell houtside
  rw [selectedOwner_convolutionSquare] at hprefix
  rw [sum_spectralHeightShellPrefix_eq_shell_prefix
    (halfDensityShift
      ((convolutionIterate base n).convolution correction)).convolutionSquare N] at hprefix
  have hcutoff' :
      bombieriSpectralTailCutoff
          (halfDensityShift ((convolutionIterate base n).convolution correction))
          p.t p.ht p.gamma p.z p.Lam p.lam p.hz p.heigen p.hrecip = N := by
    simpa only [selectedOwner_sourceTest] using hcutoff
  have hprefixP :
      (∑ m ∈ Finset.range
          (bombieriSpectralTailCutoff (selectedOwner base correction n).sourceTest
            p.t p.ht p.gamma p.z p.Lam p.lam p.hz p.heigen p.hrecip),
        ∑' z : spectralHeightShell m,
          spectralTerm
            (selectedOwner base correction n).sourceTest.convolutionSquare z.1).re ≤
        -(xiMultiplicity rho : Real) := by
    simpa only [hcutoff', selectedOwner_sourceTest, selectedOwner_convolutionSquare] using hprefix
  have hqle :=
    canonicalQIntegrandPrefix_re_le_neg_xiMultiplicity_of_prefix_nonpos
      p rho hprefixP
  obtain ⟨S, hS, hQ⟩ :=
    qIntegrand_sub_endpointCorrection_eq_nonneg p.t p.ht p.gamma p.z
  have hqnonneg :
      0 ≤ ((∫ x in -p.t..p.t,
          qIntegrand (expSum p.gamma p.z)
            (expSum p.gamma (dcoef p.gamma p.z)) x) -
          endpointCorrection p.t p.gamma p.z).re := by
    rw [hQ]
    simp [hS]
  have hmult : 0 < (xiMultiplicity rho : Real) := by
    exact_mod_cast xiMultiplicity_pos rho
  linarith

/-- The canonical cutoff itself determines the controlled finite prefix.  Thus
the preceding obstruction does not need a separately supplied cutoff equality:
if the selected square kills every source zero outside its orbit in that
canonical prefix, a canonical qIntegrand producer is impossible. -/
theorem no_selectedOwner_canonicalQIntegrandPrefix_of_orbit_control_at_cutoff
    (base correction : CompactLogTest) (n : Nat)
    (rho : sourceNontrivialZeroSet) (hoff : rho.1.re ≠ 1 / 2)
    (htargets :
      ∀ w : FiniteMellinNode (sourceFunctionalEquationOrbit rho.1),
        laplaceAt ((convolutionIterate base n).convolution correction) w.1 =
          negativeSourceOrbitValue rho.1 w)
    (p : BombieriQuadraticCanonicalQIntegrandPrefixP2BridgeData
      (selectedOwner base correction n).sourceTest)
    (houtside : ∀ z : sourceNontrivialZeroSet,
      z ∈ spectralHeightShellPrefix
          (bombieriSpectralTailCutoff
            (selectedOwner base correction n).sourceTest
            p.t p.ht p.gamma p.z p.Lam p.lam p.hz p.heigen p.hrecip) →
      z.1 ∉ sourceFunctionalEquationOrbit rho.1 →
        laplaceAt (selectedOwner base correction n).convolutionSquare
          (z.1 - 1 / 2) = 0)
    (hrho : rho ∈ spectralHeightShellPrefix
      (bombieriSpectralTailCutoff
        (selectedOwner base correction n).sourceTest
        p.t p.ht p.gamma p.z p.Lam p.lam p.hz p.heigen p.hrecip)) :
    False := by
  let N := bombieriSpectralTailCutoff
    (selectedOwner base correction n).sourceTest
    p.t p.ht p.gamma p.z p.Lam p.lam p.hz p.heigen p.hrecip
  have hN :
      bombieriSpectralTailCutoff
          (selectedOwner base correction n).sourceTest
          p.t p.ht p.gamma p.z p.Lam p.lam p.hz p.heigen p.hrecip = N := by
    rfl
  exact no_selectedOwner_canonicalQIntegrandPrefix_of_orbit_control
    base correction n rho hoff htargets p N hrho (by
      simpa only [N] using houtside) hN

/-- The canonical qIntegrand contract cannot be combined with a negative
finite prefix at the positive-multiplicity anchor. -/
theorem not_canonicalQIntegrandPrefix_of_prefix_nonpos
    {g : CompactLogTest}
    (p : BombieriQuadraticCanonicalQIntegrandPrefixP2BridgeData g)
    (rho : sourceNontrivialZeroSet)
    (hprefix :
      (∑ m ∈ Finset.range
          (bombieriSpectralTailCutoff g p.t p.ht p.gamma p.z p.Lam p.lam p.hz
            p.heigen p.hrecip),
        ∑' z : spectralHeightShell m,
          spectralTerm g.convolutionSquare z.1).re ≤
        -(xiMultiplicity rho : Real)) : False := by
  have hqle :=
    canonicalQIntegrandPrefix_re_le_neg_xiMultiplicity_of_prefix_nonpos
      p rho hprefix
  obtain ⟨S, hS, hQ⟩ :=
    qIntegrand_sub_endpointCorrection_eq_nonneg p.t p.ht p.gamma p.z
  have hqnonneg :
      0 ≤ ((∫ x in -p.t..p.t,
          qIntegrand (expSum p.gamma p.z)
            (expSum p.gamma (dcoef p.gamma p.z)) x) -
          endpointCorrection p.t p.gamma p.z).re := by
    rw [hQ]
    simp [hS]
  have hmult : 0 < (xiMultiplicity rho : Real) := by
    exact_mod_cast xiMultiplicity_pos rho
  linarith

/-- The horizontal difference is an integral of an explicit character
difference against the original test. Integrability comes from its two
compactly supported exponential weights, not from a totalized integral. -/
theorem laplaceAt_sub_reflected_eq_integral (g : CompactLogTest) (s : Complex) :
    CompactLogTest.laplaceAt g s - CompactLogTest.laplaceAt g (-star s) =
      ∫ x : Real, (Complex.exp (s * (x : Complex)) -
        Complex.exp ((-star s) * (x : Complex))) * g.test x := by
  rw [CompactLogTest.laplaceAt, CompactLogTest.laplaceAt,
    ← MeasureTheory.integral_sub
      (CompactLogTest.exponentialWeight g s).test.integrable
      (CompactLogTest.exponentialWeight g (-star s)).test.integrable]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  simp only [CompactLogTest.exponentialWeight_apply, sub_mul]

/-- An explicit integral producer target for the defect; no square or
spectral-sign premise is supplied by the caller. -/
theorem horizontalDefect_eq_integral (g : CompactLogTest)
    (rho : sourceNontrivialZeroSet) :
    horizontalDefect g rho = (xiMultiplicity rho : Real) / 2 *
      Complex.normSq (∫ x : Real,
        (Complex.exp (centeredXiCoordinate rho * (x : Complex)) -
          Complex.exp ((-star (centeredXiCoordinate rho)) * (x : Complex))) *
            g.test x) := by
  unfold horizontalDefect
  rw [laplaceAt_sub_reflected_eq_integral]

end

end ConnesWeilRH.Source.C1P2SpectralHorizontalDefect
