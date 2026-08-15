import ConnesWeilRH.Dev.C1XiFiniteFactorCircle

/-!
# C1XiFiniteFactorResidue - finite disjoint xi residue discs with factor owners

Each deleted xi-zero disc retains the finite closed-ball factorization that
certifies its residue.  Finite `T2` separation only shrinks the inner radius;
it never replaces the outer divisor owner by a statement about the selected
finite source family alone.

No punctured rectangle, contour limit, arithmetic readback, explicit-formula
equality, or RH claim is made here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiFiniteFactorResidue

open Filter
open CC20ZetaCounting
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open C1SpectralWeil
open C1XiFiniteFactor
open C1XiFiniteFactorCircle
open C1XiFiniteLocalResidue
open C1XiVerticalFunctional
open scoped BigOperators Topology

/-- One local residue disc together with the outer finite xi factorization
that owns its principal part.  Keeping these fields together prevents a later
finite-family separation step from mixing a circle with a different local
divisor certificate. -/
structure XiFiniteFactorCircleData
    (F : CompactLogTest) (rho : sourceNontrivialZeroSet) where
  radius : Real
  outerRadius : Real
  cofactor : Complex -> Complex
  radius_pos : 0 < radius
  outerRadius_pos : 0 < outerRadius
  radius_lt_outerRadius : radius < outerRadius
  cofactor_analytic :
    AnalyticOnNhd Complex cofactor (Metric.closedBall rho.1 |outerRadius|)
  cofactor_nonzero :
    ∀ u : Metric.closedBall rho.1 |outerRadius|, cofactor u ≠ 0
  factorization :
    completedRiemannXi =ᶠ[codiscreteWithin (Metric.closedBall rho.1 |outerRadius|)]
      xiClosedBallFactor rho.1 outerRadius • cofactor
  closedBall_subset_factorizationBall :
    Metric.closedBall rho.1 radius ⊆ Metric.ball rho.1 |outerRadius|
  unique_divisor_support :
    ∀ u ∈ (xiClosedBallDivisor_support_finite rho.1 outerRadius).toFinset,
      u ≠ rho.1 → u ∉ Metric.closedBall rho.1 radius
  circle_integral :
    (∮ z in C(rho.1, radius), xiContourKernel F z) =
      -(2 * (Real.pi : Complex) * Complex.I * spectralTerm F rho)

/-- The local cofactor and finite-factor bridges provide one complete
factor-owned residue circle at every source-indexed xi zero. -/
theorem nonempty_xiFiniteFactorCircleData
    (F : CompactLogTest) (rho : sourceNontrivialZeroSet) :
    Nonempty (XiFiniteFactorCircleData F rho) := by
  obtain ⟨r, R, g, hr, hR, hrR, hganalytic, hgnonzero, hfactor,
    hdisc, hunique⟩ := exists_xiFactorCircleCertificate rho
  refine ⟨{
    radius := r
    outerRadius := R
    cofactor := g
    radius_pos := hr
    outerRadius_pos := hR
    radius_lt_outerRadius := hrR
    cofactor_analytic := hganalytic
    cofactor_nonzero := hgnonzero
    factorization := hfactor
    closedBall_subset_factorizationBall := hdisc
    unique_divisor_support := hunique
    circle_integral := ?_
  }⟩
  exact
    circleIntegral_xiContourKernel_eq_neg_spectralTerm_of_factorization_unique_support
      F rho hganalytic hgnonzero hfactor hr hdisc hunique

/-- Shrinking an inner circle preserves its outer factorization owner, its
ambient-support exclusion, and its exact local residue. -/
def XiFiniteFactorCircleData.shrink
    {F : CompactLogTest} {rho : sourceNontrivialZeroSet}
    (data : XiFiniteFactorCircleData F rho) (r : Real)
    (hr : 0 < r) (hrle : r ≤ data.radius) :
    XiFiniteFactorCircleData F rho where
  radius := r
  outerRadius := data.outerRadius
  cofactor := data.cofactor
  radius_pos := hr
  outerRadius_pos := data.outerRadius_pos
  radius_lt_outerRadius := hrle.trans_lt data.radius_lt_outerRadius
  cofactor_analytic := data.cofactor_analytic
  cofactor_nonzero := data.cofactor_nonzero
  factorization := data.factorization
  closedBall_subset_factorizationBall :=
    (Metric.closedBall_subset_closedBall hrle).trans
      data.closedBall_subset_factorizationBall
  unique_divisor_support := by
    intro u hu hune huinner
    exact data.unique_divisor_support u hu hune
      (Metric.closedBall_subset_closedBall hrle huinner)
  circle_integral :=
    circleIntegral_xiContourKernel_eq_neg_spectralTerm_of_factorization_unique_support
      F rho data.cofactor_analytic data.cofactor_nonzero data.factorization hr
      ((Metric.closedBall_subset_closedBall hrle).trans
        data.closedBall_subset_factorizationBall)
      (by
        intro u hu hune huinner
        exact data.unique_divisor_support u hu hune
          (Metric.closedBall_subset_closedBall hrle huinner))

/-- A finite source-indexed zero family has pairwise-disjoint residue discs
whose factorization, regularized kernel, and ambient divisor-support exclusion
remain available at every member.  The `T2` neighborhoods establish only
inter-disc disjointness; the local factor owner separately excludes every
other ambient xi divisor point from each closed disc. -/
theorem exists_finite_pairwiseDisjoint_xiFiniteFactorCircleData
    (F : CompactLogTest) (S : Finset sourceNontrivialZeroSet) :
    ∃ data : ∀ rho : sourceNontrivialZeroSet, XiFiniteFactorCircleData F rho,
      (S : Set sourceNontrivialZeroSet).PairwiseDisjoint
        (fun rho => Metric.closedBall rho.1 (data rho).radius) := by
  classical
  let base : ∀ rho : sourceNontrivialZeroSet, XiFiniteFactorCircleData F rho :=
    fun rho => Classical.choice (nonempty_xiFiniteFactorCircleData F rho)
  let Z : Set Complex :=
    (fun rho : sourceNontrivialZeroSet => rho.1) '' (S : Set sourceNontrivialZeroSet)
  have hZfinite : Z.Finite := by
    dsimp [Z]
    exact S.finite_toSet.image _
  obtain ⟨U, hU, hUdisjoint⟩ := hZfinite.t2_separation
  have hmemZ (rho : sourceNontrivialZeroSet) (hrho : rho ∈ S) : rho.1 ∈ Z := by
    exact ⟨rho, hrho, rfl⟩
  choose eps heps heps_subset using
    fun rho : sourceNontrivialZeroSet =>
      Metric.mem_nhds_iff.mp ((hU rho.1).2.mem_nhds (hU rho.1).1)
  let r : sourceNontrivialZeroSet → Real := fun rho =>
    min ((base rho).radius / 2) (eps rho / 2)
  have hrpos (rho : sourceNontrivialZeroSet) : 0 < r rho := by
    dsimp [r]
    exact lt_min (half_pos (base rho).radius_pos) (half_pos (heps rho))
  have hrleBase (rho : sourceNontrivialZeroSet) : r rho ≤ (base rho).radius := by
    dsimp [r]
    calc
      min ((base rho).radius / 2) (eps rho / 2) ≤ (base rho).radius / 2 :=
        min_le_left _ _
      _ ≤ (base rho).radius := by linarith [(base rho).radius_pos]
  have hrltEps (rho : sourceNontrivialZeroSet) : r rho < eps rho := by
    dsimp [r]
    calc
      min ((base rho).radius / 2) (eps rho / 2) ≤ eps rho / 2 := min_le_right _ _
      _ < eps rho := by linarith [heps rho]
  let data : ∀ rho : sourceNontrivialZeroSet, XiFiniteFactorCircleData F rho :=
    fun rho => (base rho).shrink (r rho) (hrpos rho) (hrleBase rho)
  have hclosed_subset_U (rho : sourceNontrivialZeroSet) :
      Metric.closedBall rho.1 (data rho).radius ⊆ U rho.1 := by
    change Metric.closedBall rho.1 (r rho) ⊆ U rho.1
    exact (Metric.closedBall_subset_ball (hrltEps rho)).trans (heps_subset rho)
  refine ⟨data, ?_⟩
  intro rho hrho sigma hsigma hne
  apply Disjoint.mono (hclosed_subset_U rho) (hclosed_subset_U sigma)
  apply hUdisjoint (hmemZ rho hrho) (hmemZ sigma hsigma)
  intro hcoord
  exact hne (Subtype.ext hcoord)

/-- The finite symmetric-height truncation has pairwise-disjoint factor-owned
xi residue discs.  This supplies the exact local geometry needed before a
future punctured-rectangle argument deletes its finite xi-zero set. -/
theorem exists_finiteHeight_pairwiseDisjoint_xiFiniteFactorCircleData
    (F : CompactLogTest) (T : Real) :
    ∃ data : ∀ rho : sourceNontrivialZeroSet, XiFiniteFactorCircleData F rho,
      (finiteHeightZeros T : Set sourceNontrivialZeroSet).PairwiseDisjoint
        (fun rho => Metric.closedBall rho.1 (data rho).radius) :=
  exists_finite_pairwiseDisjoint_xiFiniteFactorCircleData F (finiteHeightZeros T)

end C1XiFiniteFactorResidue
end Source
end ConnesWeilRH
