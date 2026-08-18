import ConnesWeilRH.Dev.C1HealthyYoshidaMinimalInterpolation
import ConnesWeilRH.Dev.C1SpectralWeil
import ConnesWeilRH.Source.CCM25Concrete.UnscaledYoshidaSelectedOwner

/-!
# C1HealthyYoshidaUnscaledOrbit - coordinate adapter for the unscaled orbit

The unscaled Yoshida construction controls a raw source factor `h` at source
Mellin points.  The C1 spectral side evaluates the half-density shifted root
at `rho - 1/2`, while the healthy detector API asks that same root to detect
the source point `rho`.  This module records the exact raw values needed for
the detector fields before attempting the global spectral sign construction.
-/

namespace ConnesWeilRH
namespace Source
namespace C1HealthyYoshidaUnscaledOrbit

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open C1HealthyYoshidaDetector
open C1HealthyYoshidaMinimalInterpolation
open scoped BigOperators

/-- The finite raw source nodes needed simultaneously for the negative
functional-equation orbit and for the healthy detector after the half-density
shift.  A `Finset` deliberately records every possible collision once. -/
noncomputable def healthyUnscaledTargetNodes (rho : Complex) : Finset Complex :=
  sourceFunctionalEquationOrbit rho ∪
    {rho + 1 / 2, (1 / 2 : Complex), 1, 3 / 2}

/-- Raw interpolation values for the healthy unscaled construction.  Existing
orbit values take priority, so an actual orbit collision remains compatible
with `negativeSourceOrbitValue`; the only additional nonzero target is the
shifted detector point. -/
noncomputable def healthyUnscaledTargetValue (rho : Complex) :
    FiniteMellinNode (healthyUnscaledTargetNodes rho) -> Complex := fun z =>
  if hz : z.1 ∈ sourceFunctionalEquationOrbit rho then
    negativeSourceOrbitValue rho ⟨z.1, hz⟩
  else if z.1 = rho + 1 / 2 then -1 else 0

@[simp] theorem mem_healthyUnscaledTargetNodes_rho (rho : Complex) :
    rho ∈ healthyUnscaledTargetNodes rho := by
  apply Finset.mem_union_left
  exact mem_sourceFunctionalEquationOrbit_rho rho

@[simp] theorem mem_healthyUnscaledTargetNodes_companion (rho : Complex) :
    1 - star rho ∈ healthyUnscaledTargetNodes rho := by
  apply Finset.mem_union_left
  exact mem_sourceFunctionalEquationOrbit_companion rho

@[simp] theorem mem_healthyUnscaledTargetNodes_detector (rho : Complex) :
    rho + 1 / 2 ∈ healthyUnscaledTargetNodes rho := by
  apply Finset.mem_union_right
  simp

@[simp] theorem mem_healthyUnscaledTargetNodes_half (rho : Complex) :
    (1 / 2 : Complex) ∈ healthyUnscaledTargetNodes rho := by
  apply Finset.mem_union_right
  simp

@[simp] theorem mem_healthyUnscaledTargetNodes_one (rho : Complex) :
    (1 : Complex) ∈ healthyUnscaledTargetNodes rho := by
  apply Finset.mem_union_right
  simp

@[simp] theorem mem_healthyUnscaledTargetNodes_threeHalf (rho : Complex) :
    (3 / 2 : Complex) ∈ healthyUnscaledTargetNodes rho := by
  apply Finset.mem_union_right
  simp

theorem healthyUnscaledTargetValue_of_mem_orbit
    (rho z : Complex) (hz : z ∈ sourceFunctionalEquationOrbit rho) :
    healthyUnscaledTargetValue rho
        ⟨z, Finset.mem_union_left _ hz⟩ =
      negativeSourceOrbitValue rho ⟨z, hz⟩ := by
  simp [healthyUnscaledTargetValue, hz]

@[simp] theorem healthyUnscaledTargetValue_rho (rho : Complex) :
    healthyUnscaledTargetValue rho
        ⟨rho, mem_healthyUnscaledTargetNodes_rho rho⟩ = 1 := by
  rw [healthyUnscaledTargetValue_of_mem_orbit]
  exact negativeSourceOrbitValue_rho rho

theorem healthyUnscaledTargetValue_companion (rho : Complex)
    (hoff : rho.re ≠ 1 / 2) :
    healthyUnscaledTargetValue rho
        ⟨1 - star rho, mem_healthyUnscaledTargetNodes_companion rho⟩ = -1 := by
  rw [healthyUnscaledTargetValue_of_mem_orbit]
  exact negativeSourceOrbitValue_companion rho hoff

private theorem half_not_mem_sourceFunctionalEquationOrbit
    {rho : Complex} (hoff : rho.re ≠ 1 / 2) :
    (1 / 2 : Complex) ∉ sourceFunctionalEquationOrbit rho := by
  intro hmem
  simp only [sourceFunctionalEquationOrbit, Finset.mem_insert,
    Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · apply hoff
    have hre := congrArg Complex.re h.symm
    norm_num at hre ⊢
    linarith
  · apply hoff
    have hre := congrArg Complex.re h
    norm_num at hre ⊢
    linarith
  · apply hoff
    have hre := congrArg Complex.re h.symm
    norm_num at hre ⊢
    linarith
  · apply hoff
    have hre := congrArg Complex.re h
    norm_num at hre ⊢
    linarith

private theorem one_not_mem_sourceFunctionalEquationOrbit
    {rho : Complex}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho) :
    (1 : Complex) ∉ sourceFunctionalEquationOrbit rho := by
  intro hmem
  simp only [sourceFunctionalEquationOrbit, Finset.mem_insert,
    Finset.mem_singleton] at hmem
  have hlt := sourceNontrivialZero_re_lt_one hrho
  have hpos := sourceNontrivialZero_zero_lt_re hrho
  rcases hmem with h | h | h | h
  · have hre := congrArg Complex.re h.symm
    norm_num at hre
    linarith
  · have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  · have hre := congrArg Complex.re h.symm
    norm_num at hre
    linarith
  · have hre := congrArg Complex.re h
    norm_num at hre
    linarith

private theorem threeHalf_not_mem_sourceFunctionalEquationOrbit
    {rho : Complex}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho) :
    (3 / 2 : Complex) ∉ sourceFunctionalEquationOrbit rho := by
  intro hmem
  simp only [sourceFunctionalEquationOrbit, Finset.mem_insert,
    Finset.mem_singleton] at hmem
  have hlt := sourceNontrivialZero_re_lt_one hrho
  have hpos := sourceNontrivialZero_zero_lt_re hrho
  rcases hmem with h | h | h | h
  · have hre := congrArg Complex.re h.symm
    norm_num at hre
    linarith
  · have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  · have hre := congrArg Complex.re h.symm
    norm_num at hre
    linarith
  · have hre := congrArg Complex.re h
    norm_num at hre
    linarith

private theorem half_ne_detector
    {rho : Complex}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho) :
    (1 / 2 : Complex) ≠ rho + 1 / 2 := by
  intro h
  have hre := congrArg Complex.re h
  have hpos := sourceNontrivialZero_zero_lt_re hrho
  norm_num at hre
  linarith

private theorem one_ne_detector
    {rho : Complex} (hoff : rho.re ≠ 1 / 2) :
    (1 : Complex) ≠ rho + 1 / 2 := by
  intro h
  apply hoff
  have hre := congrArg Complex.re h
  norm_num at hre ⊢
  linarith

private theorem threeHalf_ne_detector
    {rho : Complex}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho) :
    (3 / 2 : Complex) ≠ rho + 1 / 2 := by
  intro h
  have hre := congrArg Complex.re h
  have hlt := sourceNontrivialZero_re_lt_one hrho
  norm_num at hre
  linarith

theorem healthyUnscaledTargetValue_half
    {rho : Complex}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) :
    healthyUnscaledTargetValue rho
        ⟨1 / 2, mem_healthyUnscaledTargetNodes_half rho⟩ = 0 := by
  unfold healthyUnscaledTargetValue
  rw [dif_neg (half_not_mem_sourceFunctionalEquationOrbit hoff)]
  exact if_neg (half_ne_detector hrho)

theorem healthyUnscaledTargetValue_one
    {rho : Complex}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) :
    healthyUnscaledTargetValue rho
        ⟨1, mem_healthyUnscaledTargetNodes_one rho⟩ = 0 := by
  unfold healthyUnscaledTargetValue
  rw [dif_neg (one_not_mem_sourceFunctionalEquationOrbit hrho)]
  exact if_neg (one_ne_detector hoff)

theorem healthyUnscaledTargetValue_threeHalf
    {rho : Complex}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho) :
    healthyUnscaledTargetValue rho
        ⟨3 / 2, mem_healthyUnscaledTargetNodes_threeHalf rho⟩ = 0 := by
  unfold healthyUnscaledTargetValue
  rw [dif_neg (threeHalf_not_mem_sourceFunctionalEquationOrbit hrho)]
  exact if_neg (threeHalf_ne_detector hrho)

private theorem detector_ne_star (rho : Complex) :
    rho + 1 / 2 ≠ star rho := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre

private theorem detector_eq_one_sub_implies_eq_companion
    {rho : Complex}
    (h : rho + 1 / 2 = 1 - rho) :
    rho + 1 / 2 = 1 - star rho := by
  have hreal : rho = star rho := by
    apply Complex.ext
    · simp
    · have him := congrArg Complex.im h
      norm_num at him ⊢
      linarith
  calc
    rho + 1 / 2 = 1 - rho := h
    _ = 1 - star rho := congrArg (fun z : Complex => 1 - z) hreal

/-- The raw target at `rho + 1/2` is nonzero.  If that point coincides with
the source orbit, the only compatible cases carry the already-negative orbit
value; the conjugate-only collision is algebraically impossible. -/
theorem healthyUnscaledTargetValue_detector_ne_zero
    (rho : Complex) (hoff : rho.re ≠ 1 / 2) :
    healthyUnscaledTargetValue rho
        ⟨rho + 1 / 2, mem_healthyUnscaledTargetNodes_detector rho⟩ ≠ 0 := by
  by_cases horbit : rho + 1 / 2 ∈ sourceFunctionalEquationOrbit rho
  · unfold healthyUnscaledTargetValue
    have horbitMem := horbit
    rw [dif_pos horbitMem]
    simp only [sourceFunctionalEquationOrbit, Finset.mem_insert,
      Finset.mem_singleton] at horbit
    rcases horbit with h | h | h | h
    · have hnode :
        (⟨rho + 1 / 2, horbitMem⟩ :
          FiniteMellinNode (sourceFunctionalEquationOrbit rho)) =
          ⟨rho, mem_sourceFunctionalEquationOrbit_rho rho⟩ :=
        Subtype.ext h
      rw [hnode, negativeSourceOrbitValue_rho]
      norm_num
    · have hnode :
        (⟨rho + 1 / 2, horbitMem⟩ :
          FiniteMellinNode (sourceFunctionalEquationOrbit rho)) =
          ⟨1 - star rho, mem_sourceFunctionalEquationOrbit_companion rho⟩ :=
        Subtype.ext h
      rw [hnode, negativeSourceOrbitValue_companion rho hoff]
      norm_num
    · exact False.elim (detector_ne_star rho h)
    · have hcomp := detector_eq_one_sub_implies_eq_companion h
      have hnode :
        (⟨rho + 1 / 2, horbitMem⟩ :
          FiniteMellinNode (sourceFunctionalEquationOrbit rho)) =
          ⟨1 - star rho, mem_sourceFunctionalEquationOrbit_companion rho⟩ :=
        Subtype.ext hcomp
      rw [hnode, negativeSourceOrbitValue_companion rho hoff]
      norm_num
  · unfold healthyUnscaledTargetValue
    rw [dif_neg horbit]
    norm_num

/-- Raw values on the negative Hermitian pair read back to one actual
multiplicity-weighted C1 spectral term.  The theorem keeps the selected square
owner explicit: it is not a statement about an arbitrary compact-log test
with matching support metadata. -/
theorem spectralTerm_selectedOwner_eq_neg_xiMultiplicity_of_raw_hermitian_values
    (base correction : CompactLogTest) (n : Nat)
    (rho : sourceNontrivialZeroSet)
    (hrho :
      laplaceAt ((convolutionIterate base n).convolution correction) rho.1 = 1)
    (hcomp :
      laplaceAt ((convolutionIterate base n).convolution correction)
        (1 - star rho.1) = -1) :
    C1SpectralWeil.spectralTerm
        (selectedOwner base correction n).convolutionSquare rho =
      -(C1SpectralWeil.xiMultiplicity rho : Complex) := by
  unfold C1SpectralWeil.spectralTerm C1SpectralWeil.centeredXiCoordinate
  rw [selectedOwner_laplaceAt_convolutionSquare_centered, hcomp, hrho]
  norm_num

/-- On the entire raw functional-equation orbit, the selected square is
either zero or `-1` at the centered node.  The real and nonreal orbit
collisions are handled explicitly, so the result does not assume conjugation
symmetry for the source zero index. -/
theorem selectedOwner_centered_value_eq_zero_or_neg_one_of_mem_orbit
    (base correction : CompactLogTest) (n : Nat) (rho : Complex)
    (hoff : rho.re ≠ 1 / 2)
    (htargets :
      ∀ w : FiniteMellinNode (sourceFunctionalEquationOrbit rho),
        laplaceAt ((convolutionIterate base n).convolution correction) w.1 =
          negativeSourceOrbitValue rho w)
    (z : Complex) (hz : z ∈ sourceFunctionalEquationOrbit rho) :
    laplaceAt (selectedOwner base correction n).convolutionSquare
        (z - 1 / 2) = 0 ∨
      laplaceAt (selectedOwner base correction n).convolutionSquare
        (z - 1 / 2) = -1 := by
  have hrawRho :
      laplaceAt ((convolutionIterate base n).convolution correction) rho = 1 := by
    calc
      laplaceAt ((convolutionIterate base n).convolution correction) rho =
          negativeSourceOrbitValue rho
            ⟨rho, mem_sourceFunctionalEquationOrbit_rho rho⟩ :=
          htargets ⟨rho, mem_sourceFunctionalEquationOrbit_rho rho⟩
      _ = 1 := negativeSourceOrbitValue_rho rho
  have hrawCompanion :
      laplaceAt ((convolutionIterate base n).convolution correction)
        (1 - star rho) = -1 := by
    calc
      laplaceAt ((convolutionIterate base n).convolution correction)
          (1 - star rho) = negativeSourceOrbitValue rho
            ⟨1 - star rho, mem_sourceFunctionalEquationOrbit_companion rho⟩ :=
          htargets ⟨1 - star rho,
            mem_sourceFunctionalEquationOrbit_companion rho⟩
      _ = -1 := negativeSourceOrbitValue_companion rho hoff
  have hcompanionCompanion : 1 - star (1 - star rho) = rho := by
    simp
  simp only [sourceFunctionalEquationOrbit, Finset.mem_insert,
    Finset.mem_singleton] at hz
  rcases hz with hz | hz | hz | hz
  · subst z
    right
    rw [selectedOwner_laplaceAt_convolutionSquare_centered,
      hrawCompanion, hrawRho]
    norm_num
  · subst z
    right
    rw [selectedOwner_laplaceAt_convolutionSquare_centered,
      hcompanionCompanion, hrawRho, hrawCompanion]
    norm_num
  · subst z
    by_cases hnonreal : star rho ≠ rho
    · left
      have hrawStar :
          laplaceAt ((convolutionIterate base n).convolution correction)
              (star rho) = 0 := by
        calc
          laplaceAt ((convolutionIterate base n).convolution correction)
              (star rho) = negativeSourceOrbitValue rho
                ⟨star rho, mem_sourceFunctionalEquationOrbit_star rho⟩ :=
              htargets ⟨star rho, mem_sourceFunctionalEquationOrbit_star rho⟩
          _ = 0 := negativeSourceOrbitValue_star_of_ne rho hoff hnonreal
      exact selectedOwner_laplaceAt_convolutionSquare_eq_zero_of_source_eq_zero
        base correction n (star rho) hrawStar
    · have hreal : star rho = rho := not_ne_iff.mp hnonreal
      rw [hreal]
      right
      rw [selectedOwner_laplaceAt_convolutionSquare_centered,
        hrawCompanion, hrawRho]
      norm_num
  · subst z
    by_cases hnonreal : star rho ≠ rho
    · left
      have hrawOneSub :
          laplaceAt ((convolutionIterate base n).convolution correction)
              (1 - rho) = 0 := by
        calc
          laplaceAt ((convolutionIterate base n).convolution correction)
              (1 - rho) = negativeSourceOrbitValue rho
                ⟨1 - rho, mem_sourceFunctionalEquationOrbit_one_sub rho⟩ :=
              htargets ⟨1 - rho, mem_sourceFunctionalEquationOrbit_one_sub rho⟩
          _ = 0 := negativeSourceOrbitValue_one_sub_of_ne rho hoff hnonreal
      exact selectedOwner_laplaceAt_convolutionSquare_eq_zero_of_source_eq_zero
        base correction n (1 - rho) hrawOneSub
    · have hreal : star rho = rho := not_ne_iff.mp hnonreal
      have honeSubEq : 1 - rho = 1 - star rho := by rw [hreal]
      rw [honeSubEq]
      right
      rw [selectedOwner_laplaceAt_convolutionSquare_centered,
        hcompanionCompanion, hrawRho, hrawCompanion]
      norm_num

/-- Every actual source zero whose coordinate lies in the selected raw orbit
has spectral contribution either zero or minus its own analytic multiplicity.
No multiplicity identification between distinct orbit points is used. -/
theorem spectralTerm_selectedOwner_eq_zero_or_neg_xiMultiplicity_of_mem_orbit
    (base correction : CompactLogTest) (n : Nat) (rho : Complex)
    (hoff : rho.re ≠ 1 / 2)
    (htargets :
      ∀ w : FiniteMellinNode (sourceFunctionalEquationOrbit rho),
        laplaceAt ((convolutionIterate base n).convolution correction) w.1 =
          negativeSourceOrbitValue rho w)
    (z : sourceNontrivialZeroSet)
    (hz : z.1 ∈ sourceFunctionalEquationOrbit rho) :
    C1SpectralWeil.spectralTerm
        (selectedOwner base correction n).convolutionSquare z = 0 ∨
      C1SpectralWeil.spectralTerm
        (selectedOwner base correction n).convolutionSquare z =
          -(C1SpectralWeil.xiMultiplicity z : Complex) := by
  rcases selectedOwner_centered_value_eq_zero_or_neg_one_of_mem_orbit
      base correction n rho hoff htargets z.1 hz with hzero | hneg
  · left
    unfold C1SpectralWeil.spectralTerm C1SpectralWeil.centeredXiCoordinate
    rw [hzero]
    ring
  · right
    unfold C1SpectralWeil.spectralTerm C1SpectralWeil.centeredXiCoordinate
    rw [hneg]
    ring

/-- A source zero at a selected healthy target outside the raw
functional-equation orbit is killed by the selected convolution square.  The
three fixed target nodes have raw value zero; the remaining detector node is
not a source zero once the off-line anchor has been oriented to the right. -/
theorem selectedOwner_laplaceAt_convolutionSquare_eq_zero_of_source_mem_target_not_mem_orbit
    (base correction : CompactLogTest) (n : Nat) (rho : Complex)
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) (hright : (1 / 2 : Real) < rho.re)
    (htargetValues :
      ∀ w : FiniteMellinNode (healthyUnscaledTargetNodes rho),
        laplaceAt ((convolutionIterate base n).convolution correction) w.1 =
          healthyUnscaledTargetValue rho w)
    (z : sourceNontrivialZeroSet)
    (hmem : z.1 ∈ healthyUnscaledTargetNodes rho)
    (hnotOrbit : z.1 ∉ sourceFunctionalEquationOrbit rho) :
    laplaceAt (selectedOwner base correction n).convolutionSquare
        (z.1 - 1 / 2) = 0 := by
  have hrawHalf :
      laplaceAt ((convolutionIterate base n).convolution correction)
          (1 / 2 : Complex) = 0 := by
    calc
      laplaceAt ((convolutionIterate base n).convolution correction)
          (1 / 2 : Complex) = healthyUnscaledTargetValue rho
            ⟨1 / 2, mem_healthyUnscaledTargetNodes_half rho⟩ :=
          htargetValues ⟨1 / 2, mem_healthyUnscaledTargetNodes_half rho⟩
      _ = 0 := healthyUnscaledTargetValue_half hrho hoff
  have hrawOne :
      laplaceAt ((convolutionIterate base n).convolution correction) 1 = 0 := by
    calc
      laplaceAt ((convolutionIterate base n).convolution correction) 1 =
          healthyUnscaledTargetValue rho
            ⟨1, mem_healthyUnscaledTargetNodes_one rho⟩ :=
          htargetValues ⟨1, mem_healthyUnscaledTargetNodes_one rho⟩
      _ = 0 := healthyUnscaledTargetValue_one hrho hoff
  have hrawThreeHalf :
      laplaceAt ((convolutionIterate base n).convolution correction)
          (3 / 2 : Complex) = 0 := by
    calc
      laplaceAt ((convolutionIterate base n).convolution correction)
          (3 / 2 : Complex) = healthyUnscaledTargetValue rho
            ⟨3 / 2, mem_healthyUnscaledTargetNodes_threeHalf rho⟩ :=
          htargetValues ⟨3 / 2, mem_healthyUnscaledTargetNodes_threeHalf rho⟩
      _ = 0 := healthyUnscaledTargetValue_threeHalf hrho
  have hmemExtra : z.1 ∈
      ({rho + 1 / 2, (1 / 2 : Complex), 1, 3 / 2} : Finset Complex) := by
    apply Finset.mem_union.mp at hmem
    rcases hmem with horbit | hmemExtra
    · exact False.elim (hnotOrbit horbit)
    · exact hmemExtra
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmemExtra
  rcases hmemExtra with hdetector | hhalf | hone | hthreeHalf
  · exfalso
    have hzlt := sourceNontrivialZero_re_lt_one z.2
    have hre := congrArg Complex.re hdetector
    norm_num at hre
    linarith
  · rw [hhalf]
    exact selectedOwner_laplaceAt_convolutionSquare_eq_zero_of_source_eq_zero
      base correction n (1 / 2 : Complex) hrawHalf
  · rw [hone]
    exact selectedOwner_laplaceAt_convolutionSquare_eq_zero_of_source_eq_zero
      base correction n 1 hrawOne
  · rw [hthreeHalf]
    exact selectedOwner_laplaceAt_convolutionSquare_eq_zero_of_source_eq_zero
      base correction n (3 / 2 : Complex) hrawThreeHalf

/-- The generic unscaled target-value assembly realizes the healthy finite
nodes and the negative functional-equation orbit on one selected owner.  The
raw target-value equations remain explicit so the finite-prefix and tail-sum
consumers can stay on the same selected owner. -/
theorem exists_fixedWindows_nearbyZero_healthyUnscaledOrbit_selectedOwner_with_raw_targets
    (rho : Complex)
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2)
    (routeNodes : Finset Complex)
    {baseLower baseUpper lower upper : Real}
    (hbaseLower : baseLower < 0) (hbaseUpper : 0 < baseUpper)
    (hlower : lower < 0) (hupper : 0 < upper)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ base : CompactLogTest, ∃ T : Real,
      Function.support base.test ⊆ Set.Ioo baseLower baseUpper ∧
      0 ≤ T ∧
      ∀ R : Real, 0 ≤ R →
        ∃ correction : CompactLogTest, ∃ C : Real, ∃ n : Nat,
          Function.support correction.test ⊆ Set.Ioo lower upper ∧
          Function.support (selectedOwner base correction n).sourceTest.test ⊆
            Set.Ioo (((n + 1 : Nat) : Real) * baseLower + lower)
              (((n + 1 : Nat) : Real) * baseUpper + upper) ∧
          (∀ w : FiniteMellinNode (healthyUnscaledTargetNodes rho),
            laplaceAt ((convolutionIterate base n).convolution correction) w.1 =
              healthyUnscaledTargetValue rho w) ∧
          HealthyMinimalLaplaceRealizes rho
            (selectedOwner base correction n).sourceTest ∧
          (∑ u ∈ centeredFunctionalEquationOrbit rho,
            laplaceAt (selectedOwner base correction n).convolutionSquare u) =
              -2 ∧
          (∀ z : FiniteMellinNode
              (sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes),
            z.1 ∉ healthyUnscaledTargetNodes rho →
              laplaceAt (selectedOwner base correction n).convolutionSquare
                (z.1 - 1 / 2) = 0) ∧
          0 ≤ C ∧
          (∀ z : Complex, z.re ∈ Set.Icc (0 : Real) 1 →
            T ≤ |z.im| → 1 ≤ |z.im| → 2 * |rho.im| ≤ |z.im| →
              ‖z - rho‖ ^ 2 *
                  ‖laplaceAt (selectedOwner base correction n).sourceTest
                    (z - 1 / 2)‖ < epsilon) ∧
          ∀ z : Complex, z.re ∈ Set.Icc (0 : Real) 1 →
            T ≤ |z.im| → 1 ≤ |z.im| → 2 * |rho.im| ≤ |z.im| →
              ‖z - rho‖ ^ 2 * ‖(1 - star z) - rho‖ ^ 2 *
                  ‖laplaceAt
                    (selectedOwner base correction n).convolutionSquare
                    (z - 1 / 2)‖ < epsilon ^ 2 := by
  have hrhoStrip : rho.re ∈ Set.Icc (0 : Real) 1 :=
    ⟨(sourceNontrivialZero_zero_lt_re hrho).le,
      (sourceNontrivialZero_re_lt_one hrho).le⟩
  let baseValues :
      FiniteMellinNode (healthyUnscaledTargetNodes rho) -> Complex :=
    fun _ => 1
  obtain ⟨base, baseC, hbaseSupport, hbaseValues, hbaseC, hbaseDecay⟩ :=
    exists_residualWindow_correction_with_quadratic_decay
      (healthyUnscaledTargetNodes rho) hbaseLower hbaseUpper baseValues
  have hbaseTargets : ∀ w : FiniteMellinNode (healthyUnscaledTargetNodes rho),
      laplaceAt base w.1 = 1 := by
    intro w
    simpa [baseValues] using hbaseValues w
  obtain ⟨T, hT, hbase⟩ :=
    exists_laplaceAt_vertical_half_contraction_of_quadratic_bound
      base baseC hbaseC hbaseDecay
  refine ⟨base, T, hbaseSupport, hT, ?_⟩
  intro R hR
  obtain ⟨correction, C, n, hcorrectionSupport, hrawSupport,
      htargetValues, hrawZeros, hC, htail⟩ :=
    exists_nearbyZero_unscaled_targetValues_assembly_of_fixedThreshold
      base hbaseSupport (healthyUnscaledTargetNodes rho) hbaseTargets
      (healthyUnscaledTargetValue rho) rho hrhoStrip
      (mem_healthyUnscaledTargetNodes_rho rho) T hbase routeNodes
      hlower hupper epsilon hepsilon R hR
  have hselectedSupport :
      Function.support (selectedOwner base correction n).sourceTest.test ⊆
        Set.Ioo (((n + 1 : Nat) : Real) * baseLower + lower)
          (((n + 1 : Nat) : Real) * baseUpper + upper) := by
    simpa only [selectedOwner_sourceTest] using
      halfDensityShift_support_subset
        ((convolutionIterate base n).convolution correction) hrawSupport
  have hhalf :
      laplaceAt ((convolutionIterate base n).convolution correction)
        (1 / 2) = 0 := by
    calc
      laplaceAt ((convolutionIterate base n).convolution correction)
          (1 / 2) = healthyUnscaledTargetValue rho
            ⟨1 / 2, mem_healthyUnscaledTargetNodes_half rho⟩ :=
          htargetValues ⟨1 / 2, mem_healthyUnscaledTargetNodes_half rho⟩
      _ = 0 := healthyUnscaledTargetValue_half hrho hoff
  have hone :
      laplaceAt ((convolutionIterate base n).convolution correction) 1 = 0 := by
    calc
      laplaceAt ((convolutionIterate base n).convolution correction) 1 =
          healthyUnscaledTargetValue rho
            ⟨1, mem_healthyUnscaledTargetNodes_one rho⟩ :=
          htargetValues ⟨1, mem_healthyUnscaledTargetNodes_one rho⟩
      _ = 0 := healthyUnscaledTargetValue_one hrho hoff
  have hthreeHalf :
      laplaceAt ((convolutionIterate base n).convolution correction)
        (3 / 2) = 0 := by
    calc
      laplaceAt ((convolutionIterate base n).convolution correction)
          (3 / 2) = healthyUnscaledTargetValue rho
            ⟨3 / 2, mem_healthyUnscaledTargetNodes_threeHalf rho⟩ :=
          htargetValues ⟨3 / 2, mem_healthyUnscaledTargetNodes_threeHalf rho⟩
      _ = 0 := healthyUnscaledTargetValue_threeHalf hrho
  have hdetect :
      laplaceAt ((convolutionIterate base n).convolution correction)
        (rho + 1 / 2) ≠ 0 := by
    rw [htargetValues
      ⟨rho + 1 / 2, mem_healthyUnscaledTargetNodes_detector rho⟩]
    exact healthyUnscaledTargetValue_detector_ne_zero rho hoff
  have hminimal : HealthyMinimalLaplaceRealizes rho
      (selectedOwner base correction n).sourceTest := by
    change HealthyMinimalLaplaceRealizes rho
      (halfDensityShift ((convolutionIterate base n).convolution correction))
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [laplaceAt_halfDensityShift]
      simpa using hhalf
    · rw [laplaceAt_halfDensityShift]
      norm_num
      simpa using hone
    · rw [laplaceAt_halfDensityShift]
      norm_num
      simpa using hthreeHalf
    · rw [laplaceAt_halfDensityShift]
      simpa using hdetect
  have hrawOrbit : ∀ w : FiniteMellinNode (sourceFunctionalEquationOrbit rho),
      laplaceAt ((convolutionIterate base n).convolution correction) w.1 =
        negativeSourceOrbitValue rho w := by
    intro w
    calc
      laplaceAt ((convolutionIterate base n).convolution correction) w.1 =
          healthyUnscaledTargetValue rho
            ⟨w.1, Finset.mem_union_left _ w.2⟩ :=
          htargetValues ⟨w.1, Finset.mem_union_left _ w.2⟩
      _ = negativeSourceOrbitValue rho w :=
          healthyUnscaledTargetValue_of_mem_orbit rho w.1 w.2
  have hrawRho :
      laplaceAt ((convolutionIterate base n).convolution correction) rho = 1 := by
    calc
      laplaceAt ((convolutionIterate base n).convolution correction) rho =
          negativeSourceOrbitValue rho
            ⟨rho, mem_sourceFunctionalEquationOrbit_rho rho⟩ :=
          hrawOrbit ⟨rho, mem_sourceFunctionalEquationOrbit_rho rho⟩
      _ = 1 := negativeSourceOrbitValue_rho rho
  have hrawCompanion :
      laplaceAt ((convolutionIterate base n).convolution correction)
        (1 - star rho) = -1 := by
    calc
      laplaceAt ((convolutionIterate base n).convolution correction)
          (1 - star rho) = negativeSourceOrbitValue rho
            ⟨1 - star rho, mem_sourceFunctionalEquationOrbit_companion rho⟩ :=
          hrawOrbit ⟨1 - star rho,
            mem_sourceFunctionalEquationOrbit_companion rho⟩
      _ = -1 := negativeSourceOrbitValue_companion rho hoff
  have horbitSum :
      (∑ u ∈ centeredFunctionalEquationOrbit rho,
        laplaceAt (selectedOwner base correction n).convolutionSquare u) = -2 :=
    selectedOwner_centeredOrbit_sum_eq_neg_two
      base correction n rho hoff hrawRho hrawCompanion hrawOrbit
  have hsquareZeros : ∀ z : FiniteMellinNode
      (sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes),
      z.1 ∉ healthyUnscaledTargetNodes rho →
        laplaceAt (selectedOwner base correction n).convolutionSquare
          (z.1 - 1 / 2) = 0 := by
    intro z hz
    exact selectedOwner_laplaceAt_convolutionSquare_eq_zero_of_source_eq_zero
      base correction n z.1 (hrawZeros z hz)
  have hcenteredTail := selectedOwner_centered_source_distance_bound_lt
    base correction n rho T epsilon htail
  have hsquareTail := selectedOwner_convolutionSquare_tail_of_source_tail
    base correction n rho T epsilon hepsilon htail
  exact ⟨correction, C, n, hcorrectionSupport, hselectedSupport, htargetValues,
    hminimal, horbitSum, hsquareZeros, hC, hcenteredTail, hsquareTail⟩

/-- The compatibility projection of the raw-target construction keeps the
previous finite-prefix and tail interface available to existing consumers. -/
theorem exists_fixedWindows_nearbyZero_healthyUnscaledOrbit_selectedOwner
    (rho : Complex)
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2)
    (routeNodes : Finset Complex)
    {baseLower baseUpper lower upper : Real}
    (hbaseLower : baseLower < 0) (hbaseUpper : 0 < baseUpper)
    (hlower : lower < 0) (hupper : 0 < upper)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ base : CompactLogTest, ∃ T : Real,
      Function.support base.test ⊆ Set.Ioo baseLower baseUpper ∧
      0 ≤ T ∧
      ∀ R : Real, 0 ≤ R →
        ∃ correction : CompactLogTest, ∃ C : Real, ∃ n : Nat,
          Function.support correction.test ⊆ Set.Ioo lower upper ∧
          Function.support (selectedOwner base correction n).sourceTest.test ⊆
            Set.Ioo (((n + 1 : Nat) : Real) * baseLower + lower)
              (((n + 1 : Nat) : Real) * baseUpper + upper) ∧
          HealthyMinimalLaplaceRealizes rho
            (selectedOwner base correction n).sourceTest ∧
          (∑ u ∈ centeredFunctionalEquationOrbit rho,
            laplaceAt (selectedOwner base correction n).convolutionSquare u) =
              -2 ∧
          (∀ z : FiniteMellinNode
              (sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes),
            z.1 ∉ healthyUnscaledTargetNodes rho →
              laplaceAt (selectedOwner base correction n).convolutionSquare
                (z.1 - 1 / 2) = 0) ∧
          0 ≤ C ∧
          (∀ z : Complex, z.re ∈ Set.Icc (0 : Real) 1 →
            T ≤ |z.im| → 1 ≤ |z.im| → 2 * |rho.im| ≤ |z.im| →
              ‖z - rho‖ ^ 2 *
                  ‖laplaceAt (selectedOwner base correction n).sourceTest
                    (z - 1 / 2)‖ < epsilon) ∧
          ∀ z : Complex, z.re ∈ Set.Icc (0 : Real) 1 →
            T ≤ |z.im| → 1 ≤ |z.im| → 2 * |rho.im| ≤ |z.im| →
              ‖z - rho‖ ^ 2 * ‖(1 - star z) - rho‖ ^ 2 *
                  ‖laplaceAt
                    (selectedOwner base correction n).convolutionSquare
                    (z - 1 / 2)‖ < epsilon ^ 2 := by
  obtain ⟨base, T, hbaseSupport, hT, hconstruction⟩ :=
    exists_fixedWindows_nearbyZero_healthyUnscaledOrbit_selectedOwner_with_raw_targets
      rho hrho hoff routeNodes hbaseLower hbaseUpper hlower hupper epsilon hepsilon
  refine ⟨base, T, hbaseSupport, hT, ?_⟩
  intro R hR
  obtain ⟨correction, C, n, hcorrectionSupport, hselectedSupport, _htargetValues,
      hminimal, horbitSum, hsquareZeros, hC, hcenteredTail, hsquareTail⟩ :=
    hconstruction R hR
  exact ⟨correction, C, n, hcorrectionSupport, hselectedSupport, hminimal,
    horbitSum, hsquareZeros, hC, hcenteredTail, hsquareTail⟩

/-- The half-density shift turns raw values at `1/2`, `1`, and `3/2` into the
three healthy finite-vanishing equations.  A nonzero raw value at `rho + 1/2`
is exactly healthy detection at `rho`. -/
theorem healthyMinimalLaplaceRealizes_halfDensityShift_of_raw_values
    {rho : Complex} {h : CompactLogTest}
    (hhalf : laplaceAt h (1 / 2) = 0)
    (hone : laplaceAt h 1 = 0)
    (hthreeHalf : laplaceAt h (3 / 2) = 0)
    (hdetect : laplaceAt h (rho + 1 / 2) != 0) :
    HealthyMinimalLaplaceRealizes rho (halfDensityShift h) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [laplaceAt_halfDensityShift]
    simpa using hhalf
  · rw [laplaceAt_halfDensityShift]
    norm_num
    simpa using hone
  · rw [laplaceAt_halfDensityShift]
    norm_num
    simpa using hthreeHalf
  · rw [laplaceAt_halfDensityShift]
    simpa using hdetect

/-- Once the unscaled construction proves strict negativity of the C1 spectral
value for its shifted square, the raw-value adapter supplies healthy detector
data without transferring any sign between unrelated owners. -/
theorem healthyDetectorData_halfDensityShift_of_raw_values_of_spectral_neg
    {rho : Complex} {h : CompactLogTest}
    (hhalf : laplaceAt h (1 / 2) = 0)
    (hone : laplaceAt h 1 = 0)
    (hthreeHalf : laplaceAt h (3 / 2) = 0)
    (hdetect : laplaceAt h (rho + 1 / 2) != 0)
    (hspectral :
      C1SpectralWeil.spectralWeilValue
          (halfDensityShift h).convolutionSquare < 0) :
    HealthyYoshidaDetectorData rho (halfDensityShift h) := by
  let hminimal : HealthyMinimalLaplaceRealizes rho (halfDensityShift h) :=
    healthyMinimalLaplaceRealizes_halfDensityShift_of_raw_values
      hhalf hone hthreeHalf hdetect
  refine
    { compactSupportSmooth := C1.healthyCC20CompactSupportSmooth _
      vanishesOnF := hminimal.vanishesOn_cc20Triple
      detectsRho := hminimal.detects_rho
      weilSquareSumPositive := ?_ }
  exact
    (weilSquareSumPositive_iff_spectralWeilValue_neg (halfDensityShift h)).mpr
      hspectral

/-- The centered C1 spectral value of the shifted square is the raw
functional-equation Hermitian product.  This is the exact sign interface
consumed by the future all-zero tail estimate. -/
theorem laplaceAt_halfDensityShift_convolutionSquare_centered
    (h : CompactLogTest) (rho : Complex) :
    laplaceAt (halfDensityShift h).convolutionSquare (rho - 1 / 2) =
      star (laplaceAt h (1 - star rho)) * laplaceAt h rho := by
  rw [CompactLogTest.convolutionSquare, laplaceAt_convolution,
    laplaceAt_involution, laplaceAt_halfDensityShift,
    laplaceAt_halfDensityShift]
  congr 3
  all_goals simp
  all_goals ring

end C1HealthyYoshidaUnscaledOrbit
end Source
end ConnesWeilRH
