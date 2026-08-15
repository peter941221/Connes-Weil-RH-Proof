import ConnesWeilRH.Dev.C1XiResidue

/-!
# C1XiFiniteResidue - finite local residue aggregation for Gate 2

The local xi residue is indexed by the same source zero subtype as the spectral
sum.  This module packages arbitrary finite families without replacing them by
a set of bare complex coordinates, so multiplicity and the source-index owner
remain aligned.

This module constructs pairwise-disjoint finite local discs, but does not yet
prove a punctured-domain Cauchy theorem, a rectangle identity, the
explicit-formula equality, or RH.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiFiniteResidue

open CC20ZetaCounting
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open C1SpectralWeil
open C1XiResidue
open C1XiVerticalFunctional
open scoped BigOperators

/-- Each member of a finite source-indexed zero family has a positive local
circle whose integral is its multiplicity-weighted spectral residue.  The
radii are deliberately allowed to vary; disjointness is a later geometric
obligation, not something silently assumed by this finite aggregation. -/
theorem exists_finite_xiResidueCircles
    (F : CompactLogTest) (S : Finset sourceNontrivialZeroSet) :
    ∃ R : sourceNontrivialZeroSet → Real,
      (∀ rho ∈ S, 0 < R rho) ∧
      ∀ rho ∈ S,
        (∮ s in C(rho.1, R rho), xiContourKernel F s) =
          -(2 * (Real.pi : Complex) * Complex.I * spectralTerm F rho) := by
  choose R hR hcircle using
    fun rho : sourceNontrivialZeroSet =>
      exists_circleIntegral_xiContourKernel_eq_neg_residue F rho
  exact ⟨R, fun rho _ => hR rho, fun rho _ => hcircle rho⟩

/-- A finite source-indexed zero family admits closed local residue discs that
are pairwise disjoint.  Each radius is simultaneously below the one-cofactor
analytic safety bound and inside a Hausdorff-separated neighborhood of its
complex zero coordinate.  The source subtype is retained as the index, so
analytic multiplicities remain attached to the same spectral terms. -/
theorem exists_finite_pairwiseDisjoint_xiResidueClosedBalls
    (F : CompactLogTest) (S : Finset sourceNontrivialZeroSet) :
    ∃ R : sourceNontrivialZeroSet → Real,
      (∀ rho ∈ S, 0 < R rho) ∧
      (S : Set sourceNontrivialZeroSet).PairwiseDisjoint
        (fun rho => Metric.closedBall rho.1 (R rho)) ∧
      ∀ rho ∈ S,
        (∮ s in C(rho.1, R rho), xiContourKernel F s) =
          -(2 * (Real.pi : Complex) * Complex.I * spectralTerm F rho) := by
  classical
  let Z : Set Complex :=
    (fun rho : sourceNontrivialZeroSet => rho.1) '' (S : Set sourceNontrivialZeroSet)
  have hZfinite : Z.Finite := by
    dsimp [Z]
    exact S.finite_toSet.image _
  obtain ⟨U, hU, hUdisjoint⟩ := hZfinite.t2_separation
  have hmemZ (rho : sourceNontrivialZeroSet) (hrho : rho ∈ S) : rho.1 ∈ Z := by
    exact ⟨rho, hrho, rfl⟩
  choose Rmax hRmax hsafe using
    fun rho : sourceNontrivialZeroSet =>
      exists_safeCircleRadius_xiContourKernel_eq_neg_residue F rho
  choose eps heps heps_subset using
    fun rho : sourceNontrivialZeroSet =>
      Metric.mem_nhds_iff.mp ((hU rho.1).2.mem_nhds (hU rho.1).1)
  let R : sourceNontrivialZeroSet → Real := fun rho =>
    min (Rmax rho / 2) (eps rho / 2)
  have hRpos (rho : sourceNontrivialZeroSet) : 0 < R rho := by
    dsimp [R]
    exact lt_min (half_pos (hRmax rho)) (half_pos (heps rho))
  have hRleSafe (rho : sourceNontrivialZeroSet) : R rho ≤ Rmax rho := by
    dsimp [R]
    calc
      min (Rmax rho / 2) (eps rho / 2) ≤ Rmax rho / 2 := min_le_left _ _
      _ ≤ Rmax rho := by linarith [hRmax rho]
  have hRltEps (rho : sourceNontrivialZeroSet) : R rho < eps rho := by
    dsimp [R]
    calc
      min (Rmax rho / 2) (eps rho / 2) ≤ eps rho / 2 := min_le_right _ _
      _ < eps rho := by linarith [heps rho]
  have hclosed_subset_U (rho : sourceNontrivialZeroSet) :
      Metric.closedBall rho.1 (R rho) ⊆ U rho.1 :=
    (Metric.closedBall_subset_ball (hRltEps rho)).trans (heps_subset rho)
  have hdisjoint :
      (S : Set sourceNontrivialZeroSet).PairwiseDisjoint
        (fun rho => Metric.closedBall rho.1 (R rho)) := by
    intro rho hrho sigma hsigma hne
    apply Disjoint.mono (hclosed_subset_U rho) (hclosed_subset_U sigma)
    apply hUdisjoint (hmemZ rho hrho) (hmemZ sigma hsigma)
    intro hcoord
    exact hne (Subtype.ext hcoord)
  refine ⟨R, fun rho _ => hRpos rho, hdisjoint, ?_⟩
  intro rho _hrho
  exact hsafe rho (R rho) (hRpos rho) (hRleSafe rho)

/-- Summing the individually certified circles over a finite source-indexed
family gives exactly the corresponding finite spectral partial sum.  This is
the finite residue side of the later contour-shift equation. -/
theorem exists_finite_circleIntegral_sum_xiContourKernel_eq_neg_spectralSum
    (F : CompactLogTest) (S : Finset sourceNontrivialZeroSet) :
    ∃ R : sourceNontrivialZeroSet → Real,
      (∀ rho ∈ S, 0 < R rho) ∧
      (∑ rho ∈ S, (∮ s in C(rho.1, R rho), xiContourKernel F s)) =
        -(2 * (Real.pi : Complex) * Complex.I *
          ∑ rho ∈ S, spectralTerm F rho) := by
  obtain ⟨R, hR, hcircle⟩ := exists_finite_xiResidueCircles F S
  refine ⟨R, hR, ?_⟩
  calc
    (∑ rho ∈ S, (∮ s in C(rho.1, R rho), xiContourKernel F s)) =
        ∑ rho ∈ S, -(2 * (Real.pi : Complex) * Complex.I * spectralTerm F rho) := by
      apply Finset.sum_congr rfl
      intro rho hrho
      exact hcircle rho hrho
    _ = -(2 * (Real.pi : Complex) * Complex.I *
        ∑ rho ∈ S, spectralTerm F rho) := by
      rw [Finset.sum_neg_distrib, ← Finset.mul_sum]

/-- The finite-height truncation used by spectral summability has the same
finite local residue identity.  This is the direct bridge from contour circles
to the partial sums that converge to `spectralWeilValue`. -/
theorem exists_finiteHeight_circleIntegral_sum_xiContourKernel_eq_neg_spectralSum
    (F : CompactLogTest) (T : Real) :
    ∃ R : sourceNontrivialZeroSet → Real,
      (∀ rho ∈ finiteHeightZeros T, 0 < R rho) ∧
      (∑ rho ∈ finiteHeightZeros T,
          (∮ s in C(rho.1, R rho), xiContourKernel F s)) =
        -(2 * (Real.pi : Complex) * Complex.I *
          ∑ rho ∈ finiteHeightZeros T, spectralTerm F rho) :=
  exists_finite_circleIntegral_sum_xiContourKernel_eq_neg_spectralSum F
    (finiteHeightZeros T)

/-- The finite symmetric-height family has pairwise-disjoint closed local
residue discs with the same exact residue identity.  This is the geometric
input required before deleting the finite zero set from a contour rectangle. -/
theorem exists_finiteHeight_pairwiseDisjoint_xiResidueClosedBalls
    (F : CompactLogTest) (T : Real) :
    ∃ R : sourceNontrivialZeroSet → Real,
      (∀ rho ∈ finiteHeightZeros T, 0 < R rho) ∧
      (finiteHeightZeros T : Set sourceNontrivialZeroSet).PairwiseDisjoint
        (fun rho => Metric.closedBall rho.1 (R rho)) ∧
      ∀ rho ∈ finiteHeightZeros T,
        (∮ s in C(rho.1, R rho), xiContourKernel F s) =
          -(2 * (Real.pi : Complex) * Complex.I * spectralTerm F rho) :=
  exists_finite_pairwiseDisjoint_xiResidueClosedBalls F (finiteHeightZeros T)

end C1XiFiniteResidue
end Source
end ConnesWeilRH
