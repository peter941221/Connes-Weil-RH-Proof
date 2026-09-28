import ConnesWeilRH.Dev.C1HealthyYoshidaClosedPrefix
import ConnesWeilRH.Dev.C1SpectralSummability

/-!
# Route A actual-owner cardinality bridge

This module turns the existing unconditional dyadic xi-growth estimate into a
cardinality bound for the same closed-ball source owner used by the selected
Route A construction. It is only a counting bridge; it does not assert the
signed C3' producer margin.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteAOwnerCardinality

open CC20ZetaCounting
open C1SpectralSummability
open CC20YoshidaNearZeros
open scoped Topology

/-- A source-zero in the selected closed ball has bounded symmetric height
after adding the anchor distance to `2`. -/
theorem sourceNontrivialZero_mem_symmetricHeight_of_mem_closedBall
    (rho : Complex) (R : Real) (hR : 0 ≤ R)
    (z : sourceNontrivialZeroSet)
    (hz : z.1 ∈ sourceNontrivialZerosInClosedBall rho R) :
    |z.1.im| ≤ R + dist (2 : Complex) rho := by
  have hdist : dist z.1 rho ≤ R := hz.1
  have hto2 : dist z.1 (2 : Complex) ≤ R + dist (2 : Complex) rho := by
    calc
      dist z.1 (2 : Complex) ≤ dist z.1 rho + dist rho (2 : Complex) :=
        dist_triangle _ _ _
      _ = dist z.1 rho + dist (2 : Complex) rho := by
        rw [dist_comm rho (2 : Complex)]
      _ ≤ R + dist (2 : Complex) rho := by
        linarith
  have him : |z.1.im| ≤ dist z.1 (2 : Complex) := by
    rw [dist_eq_norm]
    simpa using Complex.abs_im_le_norm (z.1 - (2 : Complex))
  exact him.trans hto2

/-- Explicit cardinality bound for the actual closed-ball source owner. The
only analytic input is the already-proved unconditional dyadic xi growth
bound; `hscale` says which dyadic growth rung contains the doubled Jensen
circle after folding the left half-plane. -/
theorem sourceNontrivialZerosInClosedBall_ncard_le_dyadic_xi_growth
    (rho : Complex) (R : Real) (n : Nat)
    (hR : 0 ≤ R)
    (hscale : 2 * (R + dist (2 : Complex) rho) + 7 ≤
      (2 : Real) ^ (n + 4)) :
    ((sourceNontrivialZerosInClosedBall rho R).ncard : Real) ≤
      (xiDyadicRLogRGrowthExponent n -
        Real.log ‖completedRiemannXi 2‖) / Real.log 2 := by
  let T : Real := R + dist (2 : Complex) rho
  have hT : -2 < T := by
    dsimp only [T]
    have hd : 0 ≤ dist (2 : Complex) rho := dist_nonneg
    linarith
  have hG : 0 ≤ xiDyadicRLogRGrowthExponent n := by
    unfold xiDyadicRLogRGrowthExponent
    exact add_nonneg
      (add_nonneg (add_nonneg xiGrowthFixedConstant_nonneg (by norm_num))
        (by positivity))
      (by positivity)
  have hsphere : ∀ z ∈ Metric.sphere (2 : Complex) (2 * (T + 2)),
      ‖completedRiemannXi z‖ ≤ Real.exp (xiDyadicRLogRGrowthExponent n) := by
    intro z hz
    rcases exists_half_le_re_norm_le_add_one_and_norm_completedRiemannXi_eq z with
      ⟨w, hwRe, hwNorm, hxi⟩
    rw [← hxi]
    apply norm_completedRiemannXi_le_exp_of_halfplane_dyadic_rlogr n hwRe
    have hzdist : dist z (2 : Complex) = 2 * (T + 2) := by
      simpa only [Metric.mem_sphere] using hz
    have hznorm : ‖z‖ ≤ 2 * (T + 2) + 2 := by
      calc
        ‖z‖ = ‖(z - (2 : Complex)) + (2 : Complex)‖ := by
          rw [sub_add_cancel]
        _ ≤ ‖z - (2 : Complex)‖ + ‖(2 : Complex)‖ :=
          norm_add_le _ _
        _ = dist z (2 : Complex) + 2 := by
          rw [dist_eq_norm]
          norm_num
        _ = 2 * (T + 2) + 2 := by rw [hzdist]
    have hwbound : ‖w‖ ≤ 2 * (T + 2) + 3 := by linarith
    have hscale' : 2 * (T + 2) + 3 ≤ (2 : Real) ^ (n + 4) := by
      dsimp only [T]
      linarith
    exact hwbound.trans hscale'
  have hcount :
      ((sourceNontrivialZerosInSymmetricHeight T).ncard : Real) ≤
        (xiDyadicRLogRGrowthExponent n -
          Real.log ‖completedRiemannXi 2‖) / Real.log 2 := by
    exact sourceNontrivialZerosInSymmetricHeight_ncard_le_of_xi_exp_sphere_bound
      hT hG hsphere
  let H : Set Complex :=
    (fun z : sourceNontrivialZeroSet => z.1) ''
      sourceNontrivialZerosInSymmetricHeight T
  have hHfinite : H.Finite :=
    (sourceNontrivialZerosInSymmetricHeight_finite T).image _
  have hsubset : sourceNontrivialZerosInClosedBall rho R ⊆ H := by
    intro z hz
    refine ⟨⟨z, hz.2⟩, ?_, rfl⟩
    exact sourceNontrivialZero_mem_symmetricHeight_of_mem_closedBall
      rho R hR ⟨z, hz.2⟩ hz
  have hcard :
      (sourceNontrivialZerosInClosedBall rho R).ncard ≤ H.ncard := by
    exact Set.ncard_le_ncard hsubset hHfinite
  have himage : H.ncard =
      (sourceNontrivialZerosInSymmetricHeight T).ncard := by
    dsimp only [H]
    exact Set.InjOn.ncard_image (fun x _ y _ hxy => Subtype.ext hxy)
  have hcardReal :
      ((sourceNontrivialZerosInClosedBall rho R).ncard : Real) ≤
        (H.ncard : Real) := by
    exact_mod_cast hcard
  rw [himage] at hcardReal
  exact hcardReal.trans hcount


/-- The same count bridge with an arbitrary nonzero Jensen center.  This is
useful when a zero-free point near the selected off-line anchor is available;
the fixed center `2` is not forced by the counting argument. -/
theorem sourceNontrivialZerosInClosedBall_ncard_le_dyadic_xi_growth_at_center
    (center rho : Complex) (R : Real) (n : Nat)
    (hR : 0 ≤ R)
    (hcenter : completedRiemannXi center ≠ 0)
    (hpositive : 0 < R + dist center rho)
    (hscale : 2 * (R + dist center rho) + ‖center‖ + 1 ≤
      (2 : Real) ^ (n + 4)) :
    ((sourceNontrivialZerosInClosedBall rho R).ncard : Real) ≤
      Real.log
          (Real.exp (xiDyadicRLogRGrowthExponent n) /
            ‖completedRiemannXi center‖) /
        Real.log (2 * (R + dist center rho) /
          (R + dist center rho)) := by
  let A : Real := R + dist center rho
  have hA : 0 < A := by simpa only [A] using hpositive
  have hG : 0 ≤ xiDyadicRLogRGrowthExponent n := by
    unfold xiDyadicRLogRGrowthExponent
    exact add_nonneg
      (add_nonneg (add_nonneg xiGrowthFixedConstant_nonneg (by norm_num))
        (by positivity))
      (by positivity)
  have hsphere : ∀ z ∈ Metric.sphere center (2 * A),
      ‖completedRiemannXi z‖ ≤ Real.exp (xiDyadicRLogRGrowthExponent n) := by
    intro z hz
    rcases exists_half_le_re_norm_le_add_one_and_norm_completedRiemannXi_eq z with
      ⟨w, hwRe, hwNorm, hxi⟩
    rw [← hxi]
    apply norm_completedRiemannXi_le_exp_of_halfplane_dyadic_rlogr n hwRe
    have hzdist : dist z center = 2 * A := by
      simpa only [Metric.mem_sphere] using hz
    have hznorm : ‖z‖ ≤ 2 * A + ‖center‖ := by
      calc
        ‖z‖ = ‖(z - center) + center‖ := by
          rw [sub_add_cancel]
        _ ≤ ‖z - center‖ + ‖center‖ := norm_add_le _ _
        _ = dist z center + ‖center‖ := by rw [dist_eq_norm]
        _ = 2 * A + ‖center‖ := by rw [hzdist]
    have hwbound : ‖w‖ ≤ 2 * A + ‖center‖ + 1 := by linarith
    have hscale' : 2 * A + ‖center‖ + 1 ≤ (2 : Real) ^ (n + 4) := by
      dsimp only [A]
      exact hscale
    exact hwbound.trans hscale'
  have hdouble : |A| < |2 * A| := by
    rw [abs_of_pos hA, abs_of_pos (mul_pos (by norm_num) hA)]
    nlinarith
  have h2A : 0 < 2 * A := mul_pos (by norm_num) hA
  have hcount :
      ((sourceNontrivialZerosInClosedBall center A).ncard : Real) ≤
        Real.log
            (Real.exp (xiDyadicRLogRGrowthExponent n) /
              ‖completedRiemannXi center‖) /
          Real.log (2 * A / A) := by
    exact sourceNontrivialZerosInClosedBall_ncard_le_of_xi_sphere_bound
      (c := center) (r := A) (R := 2 * A)
      (by simpa only [abs_of_pos hA] using hA)
      hdouble
      (by simpa using Real.one_le_exp hG) hcenter (by
        simpa only [abs_of_pos h2A] using hsphere)
  have hsubset : sourceNontrivialZerosInClosedBall rho R ⊆
      sourceNontrivialZerosInClosedBall center A := by
    intro z hz
    refine ⟨?_, hz.2⟩
    rw [Metric.mem_closedBall]
    calc
      dist z center ≤ dist z rho + dist rho center := dist_triangle _ _ _
      _ = dist z rho + dist center rho := by rw [dist_comm rho center]
      _ ≤ R + dist center rho := add_le_add_left hz.1 _
      _ = A := by rfl
  have hfinite : (sourceNontrivialZerosInClosedBall center A).Finite :=
    sourceNontrivialZerosInClosedBall_finite center A
  have hcard :
      (sourceNontrivialZerosInClosedBall rho R).ncard ≤
        (sourceNontrivialZerosInClosedBall center A).ncard :=
    Set.ncard_le_ncard hsubset hfinite
  have hcardReal :
      ((sourceNontrivialZerosInClosedBall rho R).ncard : Real) ≤
        ((sourceNontrivialZerosInClosedBall center A).ncard : Real) := by
    exact_mod_cast hcard
  rw [show A = R + dist center rho by rfl] at hcount
  exact hcardReal.trans hcount
end C1RouteAOwnerCardinality
end Source
end ConnesWeilRH
