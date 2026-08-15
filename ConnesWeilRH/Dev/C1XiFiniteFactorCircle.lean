import ConnesWeilRH.Dev.C1XiFiniteLocalResidue

/-!
# C1XiFiniteFactorCircle - compatible local finite-factor residue circles

The local analytic cofactor at a selected xi zero supplies a zero-free inner
disc.  This module combines that disc with a larger finite closed-ball
factorization, producing one owner-compatible radius whose smaller circles
contain no other divisor support point.  The resulting radius can later be
shrunk for finite T2 separation without losing the finite-factor residue
identity.

No finite-family punctured rectangle, contour limit, arithmetic readback,
explicit-formula equality, or RH claim is made here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiFiniteFactorCircle

open Filter
open CC20ZetaCounting
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open C1SpectralWeil
open C1XiFiniteFactor
open C1XiFiniteLocalResidue
open C1XiLocalPrincipalPart
open C1XiVerticalFunctional
open scoped BigOperators Topology

/-- A local cofactor around `rho` produces an inner zero-free disc and one
larger finite xi factorization owner.  The explicit support condition refers
to the ambient divisor of that same outer factorization ball, not merely to a
selected source-zero family. -/
theorem exists_xiFactorCircleCertificate
    (rho : sourceNontrivialZeroSet) :
    ∃ r R : Real, ∃ g : Complex -> Complex,
      0 < r ∧ 0 < R ∧ r < R ∧
      AnalyticOnNhd Complex g (Metric.closedBall rho.1 |R|) ∧
      (∀ u : Metric.closedBall rho.1 |R|, g u ≠ 0) ∧
      completedRiemannXi =ᶠ[codiscreteWithin (Metric.closedBall rho.1 |R|)]
        xiClosedBallFactor rho.1 R • g ∧
      Metric.closedBall rho.1 r ⊆ Metric.ball rho.1 |R| ∧
      ∀ u ∈ (xiClosedBallDivisor_support_finite rho.1 R).toFinset,
        u ≠ rho.1 → u ∉ Metric.closedBall rho.1 r := by
  obtain ⟨h, hanalytic, hnonzero, hlocal⟩ :=
    exists_completedRiemannXi_local_factor rho
  have hnonzeroEventually : ∀ᶠ s in 𝓝 rho.1, h s ≠ 0 :=
    (hanalytic.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hnonzero
  have hlocalAndNonzero : ∀ᶠ s in 𝓝 rho.1,
      completedRiemannXi s = (s - rho.1) ^ xiMultiplicity rho * h s ∧ h s ≠ 0 :=
    hlocal.and hnonzeroEventually
  obtain ⟨L, hL, hlocalOn⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.mp hlocalAndNonzero
  let r : Real := L / 4
  let R : Real := L / 2
  have hr : 0 < r := by
    dsimp [r]
    linarith
  have hR : 0 < R := by
    dsimp [R]
    linarith
  have hrR : r < R := by
    dsimp [r, R]
    linarith
  have hrleL : r ≤ L := by
    dsimp [r]
    linarith
  obtain ⟨g, hganalytic, hgnonzero, hfactor⟩ :=
    exists_xiClosedBall_factorization rho.1 R
  have hdisc : Metric.closedBall rho.1 r ⊆ Metric.ball rho.1 |R| := by
    apply Metric.closedBall_subset_ball
    rw [abs_of_pos hR]
    exact hrR
  have hunique : ∀ u ∈ (xiClosedBallDivisor_support_finite rho.1 R).toFinset,
      u ≠ rho.1 → u ∉ Metric.closedBall rho.1 r := by
    intro u hu hune huinner
    have hxi_zero : completedRiemannXi u = 0 :=
      (xiClosedBallDivisor_mem_closedBall_and_xi_eq_zero_of_mem_support rho.1 R
        ((xiClosedBallDivisor_support_finite rho.1 R).mem_toFinset.mp hu)).2
    have hulocal : u ∈ Metric.closedBall rho.1 L :=
      Metric.closedBall_subset_closedBall hrleL huinner
    rcases hlocalOn hulocal with ⟨hxi_factor, hh_ne_zero⟩
    have hpow_ne_zero : (u - rho.1) ^ xiMultiplicity rho ≠ 0 :=
      pow_ne_zero _ (sub_ne_zero.mpr hune)
    have hxi_ne_zero : completedRiemannXi u ≠ 0 := by
      rw [hxi_factor]
      exact mul_ne_zero hpow_ne_zero hh_ne_zero
    exact hxi_ne_zero hxi_zero
  exact ⟨r, R, g, hr, hR, hrR, hganalytic, hgnonzero, hfactor, hdisc, hunique⟩

/-- Every selected xi zero has a positive finite-factor safe radius.  Every
smaller positive circle uses the same outer finite factorization owner, so a
later finite-family separation may shrink radii without silently reselecting
the ambient divisor. -/
theorem exists_safeFiniteFactorCircleRadius_xiContourKernel_eq_neg_residue
    (F : CompactLogTest) (rho : sourceNontrivialZeroSet) :
    ∃ rmax : Real, 0 < rmax ∧ ∀ r : Real, 0 < r → r ≤ rmax →
      (∮ z in C(rho.1, r), xiContourKernel F z) =
        -(2 * (Real.pi : Complex) * Complex.I * spectralTerm F rho) := by
  obtain ⟨rmax, R, g, hrmax, _hR, _hrR, hganalytic, hgnonzero, hfactor,
    hdisc, hunique⟩ := exists_xiFactorCircleCertificate rho
  refine ⟨rmax, hrmax, ?_⟩
  intro r hr hrle
  apply circleIntegral_xiContourKernel_eq_neg_spectralTerm_of_factorization_unique_support
    F rho hganalytic hgnonzero hfactor hr
  · exact (Metric.closedBall_subset_closedBall hrle).trans hdisc
  · intro u hu hune huinner
    exact hunique u hu hune (Metric.closedBall_subset_closedBall hrle huinner)

end C1XiFiniteFactorCircle
end Source
end ConnesWeilRH
