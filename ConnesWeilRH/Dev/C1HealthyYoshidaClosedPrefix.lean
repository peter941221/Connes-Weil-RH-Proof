import ConnesWeilRH.Dev.C1HealthyYoshidaSpectralPrefix
import ConnesWeilRH.Source.CC20ZetaCounting

/-!
# C1HealthyYoshidaClosedPrefix - controlled finite spectral prefix

The unscaled healthy Yoshida construction controls a finite closed ball around
the selected off-line zero, while the spectral tail is partitioned by absolute
height.  This module supplies the explicit geometric bridge between those two
finite owners and records the resulting prefix sign bound.
-/

namespace ConnesWeilRH
namespace Source
namespace C1HealthyYoshidaClosedPrefix

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open C1HealthyYoshidaUnscaledOrbit
open C1HealthyYoshidaSpectralPrefix
open C1SpectralWeil
open scoped BigOperators

/-- A finite symmetric-height prefix lies in the interpolation closed ball
about the selected anchor.  The source height window first enters the proved
closed ball about `2`, then the triangle inequality moves its center to
`rho`. -/
theorem mem_closedBall_about_anchor_of_mem_finiteHeightZeros
    (rho : Complex) (T : Real) (z : sourceNontrivialZeroSet)
    (hz : z ∈ finiteHeightZeros T) :
    z.1 ∈ Metric.closedBall rho (T + 2 + dist (2 : Complex) rho) := by
  have hheight : z ∈ sourceNontrivialZerosInSymmetricHeight T :=
    (mem_finiteHeightZeros_iff T z).mp hz
  have hbase : z.1 ∈ sourceNontrivialZerosInClosedBall (2 : Complex) (T + 2) :=
    CC20ZetaCounting.sourceNontrivialZerosInSymmetricHeight_map_subset_closedBall_two
      ⟨z, hheight, rfl⟩
  have hbaseDist : dist z.1 (2 : Complex) ≤ T + 2 := hbase.1
  change dist z.1 rho ≤ T + 2 + dist (2 : Complex) rho
  calc
    dist z.1 rho ≤ dist z.1 (2 : Complex) + dist (2 : Complex) rho :=
      dist_triangle _ _ _
    _ ≤ T + 2 + dist (2 : Complex) rho :=
      add_le_add_left hbaseDist _

/-- A controlled source zero in the construction's finite node owner is
killed outside the functional-equation orbit.  The healthy-only fixed nodes
are handled by their raw target values; all other controlled nodes use the
interpolation zero equation. -/
theorem selectedOwner_laplaceAt_convolutionSquare_eq_zero_of_source_mem_closedBall_not_mem_orbit
    (base correction : CompactLogTest) (n : Nat) (rho : Complex)
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) (hright : (1 / 2 : Real) < rho.re)
    (routeNodes : Finset Complex) (R : Real)
    (htargetValues :
      ∀ w : FiniteMellinNode (healthyUnscaledTargetNodes rho),
        laplaceAt ((convolutionIterate base n).convolution correction) w.1 =
          healthyUnscaledTargetValue rho w)
    (hrawZeros :
      ∀ w : FiniteMellinNode
          (sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes),
        w.1 ∉ healthyUnscaledTargetNodes rho →
          laplaceAt ((convolutionIterate base n).convolution correction) w.1 = 0)
    (z : sourceNontrivialZeroSet)
    (hmem : z.1 ∈ sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes)
    (hnotOrbit : z.1 ∉ sourceFunctionalEquationOrbit rho) :
    laplaceAt (selectedOwner base correction n).convolutionSquare
        (z.1 - 1 / 2) = 0 := by
  by_cases htarget : z.1 ∈ healthyUnscaledTargetNodes rho
  · exact
      selectedOwner_laplaceAt_convolutionSquare_eq_zero_of_source_mem_target_not_mem_orbit
        base correction n rho hrho hoff hright htargetValues z htarget hnotOrbit
  · exact selectedOwner_laplaceAt_convolutionSquare_eq_zero_of_source_eq_zero
      base correction n z.1 (hrawZeros ⟨z.1, hmem⟩ htarget)

/-- Every finite spectral prefix contained in a controlled height window is
nonpositive away from the negative anchor term.  Keeping the finite set
explicit lets shell-based tails use this result without silently adding a
dyadic boundary shell. -/
theorem finiteSpectralPrefix_re_le_neg_xiMultiplicity_of_subset_finiteHeight_closedBall_control
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
    (hrawZeros :
      ∀ w : FiniteMellinNode
          (sourceNontrivialZerosInClosedBallFinset rho.1
              (T + 2 + dist (2 : Complex) rho.1) ∪ routeNodes),
        w.1 ∉ healthyUnscaledTargetNodes rho.1 →
          laplaceAt ((convolutionIterate base n).convolution correction) w.1 = 0) :
    (∑ z ∈ S,
      spectralTerm (selectedOwner base correction n).convolutionSquare z).re ≤
      -(xiMultiplicity rho : Real) := by
  have houtside : ∀ z : sourceNontrivialZeroSet, z ∈ S →
      z.1 ∉ sourceFunctionalEquationOrbit rho.1 →
        laplaceAt (selectedOwner base correction n).convolutionSquare
          (z.1 - 1 / 2) = 0 := by
    intro z hz hnotOrbit
    have hball := mem_closedBall_about_anchor_of_mem_finiteHeightZeros rho.1 T z (hS hz)
    have hballFinset : z.1 ∈ sourceNontrivialZerosInClosedBallFinset rho.1
        (T + 2 + dist (2 : Complex) rho.1) :=
      mem_sourceNontrivialZerosInClosedBallFinset.mpr ⟨hball, z.2⟩
    have hmem : z.1 ∈ sourceNontrivialZerosInClosedBallFinset rho.1
        (T + 2 + dist (2 : Complex) rho.1) ∪ routeNodes :=
      Finset.mem_union_left routeNodes hballFinset
    exact
      selectedOwner_laplaceAt_convolutionSquare_eq_zero_of_source_mem_closedBall_not_mem_orbit
        base correction n rho.1 rho.2 hoff hright routeNodes
        (T + 2 + dist (2 : Complex) rho.1) htargetValues hrawZeros z hmem hnotOrbit
  have horbitTargets :
      ∀ w : FiniteMellinNode (sourceFunctionalEquationOrbit rho.1),
        laplaceAt ((convolutionIterate base n).convolution correction) w.1 =
          negativeSourceOrbitValue rho.1 w := by
    intro w
    calc
      laplaceAt ((convolutionIterate base n).convolution correction) w.1 =
          healthyUnscaledTargetValue rho.1
            ⟨w.1, Finset.mem_union_left _ w.2⟩ :=
        htargetValues ⟨w.1, Finset.mem_union_left _ w.2⟩
      _ = negativeSourceOrbitValue rho.1 w :=
        healthyUnscaledTargetValue_of_mem_orbit rho.1 w.1 w.2
  exact finiteSpectralPrefix_re_le_neg_xiMultiplicity_of_orbit_control
    base correction n rho hoff horbitTargets S hrho houtside

/-- A preassembled selected-square zero certificate gives the same controlled
finite-prefix bound without exposing the construction's stronger raw-zero
interpolation data. -/
theorem finiteSpectralPrefix_re_le_neg_xiMultiplicity_of_subset_finiteHeight_closedBall_square_zero_control
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
    (∑ z ∈ S,
      spectralTerm (selectedOwner base correction n).convolutionSquare z).re ≤
      -(xiMultiplicity rho : Real) := by
  have houtside : ∀ z : sourceNontrivialZeroSet, z ∈ S →
      z.1 ∉ sourceFunctionalEquationOrbit rho.1 →
        laplaceAt (selectedOwner base correction n).convolutionSquare
          (z.1 - 1 / 2) = 0 := by
    intro z hz hnotOrbit
    have hball := mem_closedBall_about_anchor_of_mem_finiteHeightZeros rho.1 T z (hS hz)
    have hballFinset : z.1 ∈ sourceNontrivialZerosInClosedBallFinset rho.1
        (T + 2 + dist (2 : Complex) rho.1) :=
      mem_sourceNontrivialZerosInClosedBallFinset.mpr ⟨hball, z.2⟩
    have hmem : z.1 ∈ sourceNontrivialZerosInClosedBallFinset rho.1
        (T + 2 + dist (2 : Complex) rho.1) ∪ routeNodes :=
      Finset.mem_union_left routeNodes hballFinset
    by_cases htarget : z.1 ∈ healthyUnscaledTargetNodes rho.1
    · exact
        selectedOwner_laplaceAt_convolutionSquare_eq_zero_of_source_mem_target_not_mem_orbit
          base correction n rho.1 rho.2 hoff hright htargetValues z htarget hnotOrbit
    · exact hsquareZeros ⟨z.1, hmem⟩ htarget
  have horbitTargets :
      ∀ w : FiniteMellinNode (sourceFunctionalEquationOrbit rho.1),
        laplaceAt ((convolutionIterate base n).convolution correction) w.1 =
          negativeSourceOrbitValue rho.1 w := by
    intro w
    calc
      laplaceAt ((convolutionIterate base n).convolution correction) w.1 =
          healthyUnscaledTargetValue rho.1
            ⟨w.1, Finset.mem_union_left _ w.2⟩ :=
        htargetValues ⟨w.1, Finset.mem_union_left _ w.2⟩
      _ = negativeSourceOrbitValue rho.1 w :=
        healthyUnscaledTargetValue_of_mem_orbit rho.1 w.1 w.2
  exact finiteSpectralPrefix_re_le_neg_xiMultiplicity_of_orbit_control
    base correction n rho hoff horbitTargets S hrho houtside

/-- The exact finite-height spectral prefix is nonpositive away from the
negative anchor term whenever the interpolation closed ball controls that
height window.  This remains a finite statement; the infinite tail is a
separate summability consumer. -/
theorem finiteHeightSpectralPrefix_re_le_neg_xiMultiplicity_of_closedBall_control
    (base correction : CompactLogTest) (n : Nat)
    (rho : sourceNontrivialZeroSet) (hoff : rho.1.re ≠ 1 / 2)
    (hright : (1 / 2 : Real) < rho.1.re)
    (T : Real) (hrhoFinite : rho ∈ finiteHeightZeros T)
    (routeNodes : Finset Complex)
    (htargetValues :
      ∀ w : FiniteMellinNode (healthyUnscaledTargetNodes rho.1),
        laplaceAt ((convolutionIterate base n).convolution correction) w.1 =
          healthyUnscaledTargetValue rho.1 w)
    (hrawZeros :
      ∀ w : FiniteMellinNode
          (sourceNontrivialZerosInClosedBallFinset rho.1
              (T + 2 + dist (2 : Complex) rho.1) ∪ routeNodes),
        w.1 ∉ healthyUnscaledTargetNodes rho.1 →
          laplaceAt ((convolutionIterate base n).convolution correction) w.1 = 0) :
    (finiteSpectralSum (selectedOwner base correction n).convolutionSquare T).re ≤
      -(xiMultiplicity rho : Real) := by
  simpa only [finiteSpectralSum] using
    finiteSpectralPrefix_re_le_neg_xiMultiplicity_of_subset_finiteHeight_closedBall_control
      base correction n rho hoff hright T (finiteHeightZeros T) (fun _ hz => hz)
      hrhoFinite routeNodes htargetValues hrawZeros

end C1HealthyYoshidaClosedPrefix
end Source
end ConnesWeilRH
