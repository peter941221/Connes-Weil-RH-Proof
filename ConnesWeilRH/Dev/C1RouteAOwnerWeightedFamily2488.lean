import ConnesWeilRH.Dev.C1RouteALocalBumpFactors2487
import ConnesWeilRH.Dev.C1RouteAOwnerLocalCurvature2475
import ConnesWeilRH.Dev.C1RouteAExternalOwnerZeroExtension

/-  2488: weighted finite-family composition for the actual owner.

The local bump interface supplies bounds for one family term.  This theorem
keeps the owner as the literal 30-term sum and composes those bounds after the
sigma weight has been applied.  It remains parameterized by family-level
analytic bounds; no table entry is promoted to a proof premise here.
-/

namespace ConnesWeilRH.Dev

open scoped Topology BigOperators ContDiff
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

set_option linter.style.longLine false
set_option maxRecDepth 32768

theorem weightedExternalFamilySecondDeriv_zero_outside2488
    (sigma : ℝ) (coefficient : ℂ) (modulation radius position : ℝ)
    (houtside : radius < |position|) :
    deriv (deriv (weightedFunction2348 sigma
      (externalFamilyValue2344 coefficient modulation radius))) position = 0 := by
  have heq : weightedFunction2348 sigma
      (externalFamilyValue2344 coefficient modulation radius) =ᶠ[𝓝 position]
      (fun _ => (0 : ℂ)) := by
    filter_upwards [IsOpen.mem_nhds
      (isOpen_lt continuous_const continuous_abs) houtside] with coordinate hcoordinate
    simp [weightedFunction2348, externalFamilyValue2344, not_lt.mpr hcoordinate.le]
  rw [heq.deriv.deriv_eq]
  simp

theorem weightedExternalFamilySecondDeriv_zero_of_outside2488
    (sigma : ℝ) (coefficient : ℂ) (modulation radius position : ℝ)
    (hradius : 0 < radius) (houtside : radius ≤ |position|) :
    deriv (deriv (weightedFunction2348 sigma
      (externalFamilyValue2344 coefficient modulation radius))) position = 0 := by
  let second := deriv (deriv (weightedFunction2348 sigma
    (externalFamilyValue2344 coefficient modulation radius)))
  have hfamily : ContDiff ℝ (2 : WithTop (WithTop ℕ))
      (externalFamilyValue2344 coefficient modulation radius) :=
    (externalFamilyValue2344_contDiff coefficient modulation radius hradius).of_le
      (by decide)
  have hweighted : ContDiff ℝ (2 : WithTop (WithTop ℕ))
      (weightedFunction2348 sigma
        (externalFamilyValue2344 coefficient modulation radius)) :=
    weightedFunction2348_contDiff sigma _ hfamily
  have hweightedFirst : ContDiff ℝ (1 : WithTop (WithTop ℕ))
      (deriv (weightedFunction2348 sigma
        (externalFamilyValue2344 coefficient modulation radius))) :=
    ContDiff.deriv' hweighted
  have hcontinuous : Continuous second :=
    hweightedFirst.continuous_deriv (by decide)
  have hclosed : IsClosed {coordinate | second coordinate = 0} :=
    isClosed_eq hcontinuous continuous_const
  have hright : Set.Ici radius ⊆ {coordinate | second coordinate = 0} := by
    rw [← closure_Ioi]
    apply closure_minimal _ hclosed
    intro coordinate hcoordinate
    exact weightedExternalFamilySecondDeriv_zero_outside2488 sigma coefficient
      modulation radius coordinate (lt_of_lt_of_le hcoordinate (le_abs_self coordinate))
  have hleft : Set.Iic (-radius) ⊆ {coordinate | second coordinate = 0} := by
    rw [← closure_Iio]
    apply closure_minimal _ hclosed
    intro coordinate hcoordinate
    apply weightedExternalFamilySecondDeriv_zero_outside2488 sigma coefficient
      modulation radius coordinate
    change coordinate < -radius at hcoordinate
    have habs := neg_le_abs coordinate
    linarith
  change second position = 0
  rcases le_abs.mp houtside with hposition | hposition
  · exact hright hposition
  · apply hleft
    change position ≤ -radius
    linarith

/- A single-family adapter for the weighted chord estimate.  Keeping the
   three derivative bounds explicit is intentional: the eventual interval
   proof must discharge them from the local bump interface, rather than hide
   them in a precomputed familyBound. -/

theorem weightedExternalFamilySecondDeriv_le_of_local_bounds2488
    (sigma x modulation radius zeroBound firstBound secondBound : ℝ)
    (hcoeff : ℂ)
    (hradius : 0 < radius) (hinside : |x| < radius)
    (hzero : ‖externalFamilyValue2344 hcoeff modulation radius x‖ ≤ zeroBound)
    (hfirst : ‖deriv (externalFamilyValue2344 hcoeff modulation radius) x‖ ≤ firstBound)
    (hsecond : ‖deriv (deriv (externalFamilyValue2344 hcoeff modulation radius)) x‖ ≤
      secondBound) :
    ‖deriv (deriv (weightedFunction2348 sigma
      (externalFamilyValue2344 hcoeff modulation radius))) x‖ ≤
      weightedCurvature2348 sigma radius zeroBound firstBound secondBound := by
  have hsmooth : ContDiff ℝ (2 : WithTop (WithTop ℕ))
      (externalFamilyValue2344 hcoeff modulation radius) :=
    (externalFamilyValue2344_contDiff hcoeff modulation radius hradius).of_le
      (by decide)
  exact weightedFunction2348_curvature_bound sigma
    (externalFamilyValue2344 hcoeff modulation radius) hsmooth radius x
    zeroBound firstBound secondBound (le_of_lt hinside) hzero hfirst hsecond

theorem externalFamilyValue2344_secondDerivative_norm_le_of_factor_bounds2488
    (coefficient : ℂ) (modulation radius position : ℝ)
    (valueBound factorBound : ℝ)
    (hradius : 0 < radius) (hinside : |position| < radius)
    (hvalue : ‖externalFamilyValue2344 coefficient modulation radius position‖ ≤ valueBound)
    (hfactor : ‖familySecondFactor2345 modulation radius position‖ ≤ factorBound) :
    ‖deriv (deriv (externalFamilyValue2344 coefficient modulation radius)) position‖ ≤
      valueBound * factorBound := by
  rw [externalFamilyValue2344_secondDerivative_inside coefficient modulation hradius hinside]
  have hvalueBound : 0 ≤ valueBound := le_trans (norm_nonneg _) hvalue
  have hfactorBound : 0 ≤ factorBound := le_trans (norm_nonneg _) hfactor
  calc
    ‖externalFamilyValue2344 coefficient modulation radius position *
        familySecondFactor2345 modulation radius position‖ =
      ‖externalFamilyValue2344 coefficient modulation radius position‖ *
        ‖familySecondFactor2345 modulation radius position‖ := norm_mul _ _
    _ ≤ valueBound * factorBound :=
      mul_le_mul hvalue hfactor (norm_nonneg _) hvalueBound

theorem externalFamilyValue2344_firstDerivative_norm_le_of_factor_bounds2488
    (coefficient : ℂ) (modulation radius position : ℝ)
    (valueBound factorBound : ℝ)
    (hradius : 0 < radius) (hinside : |position| < radius)
    (hvalue : ‖externalFamilyValue2344 coefficient modulation radius position‖ ≤ valueBound)
    (hfactor : ‖familyFirstFactor2345 modulation radius position‖ ≤ factorBound) :
    ‖deriv (externalFamilyValue2344 coefficient modulation radius) position‖ ≤
      valueBound * factorBound := by
  have hderiv := (externalFamilyValue2344_hasDerivAt_inside
    coefficient modulation hradius hinside).deriv
  rw [hderiv]
  have hinterior :
      familyInterior2345 coefficient modulation radius position =
        externalFamilyValue2344 coefficient modulation radius position := by
    simp only [externalFamilyValue2344, familyInterior2345, familyLog2345,
      familyDeficit2345, if_pos hinside]
  rw [hinterior]
  have hvalueBound : 0 ≤ valueBound := le_trans (norm_nonneg _) hvalue
  have hfactorBound : 0 ≤ factorBound := le_trans (norm_nonneg _) hfactor
  calc
    ‖externalFamilyValue2344 coefficient modulation radius position *
        familyFirstFactor2345 modulation radius position‖ =
      ‖externalFamilyValue2344 coefficient modulation radius position‖ *
        ‖familyFirstFactor2345 modulation radius position‖ := norm_mul _ _
    _ ≤ valueBound * factorBound :=
      mul_le_mul hvalue hfactor (norm_nonneg _) hvalueBound

theorem externalFamilyValue2344_norm_le_of_scaledBump_bound2488
    (coefficient : ℂ) (modulation radius position coefficientBound bumpBound : ℝ)
    (hradius : 0 < radius) (hinside : |position| < radius)
    (hcoefficient : ‖coefficient‖ ≤ coefficientBound)
    (hbump : |scaledBumpJet2350 0 radius position| ≤ bumpBound) :
    ‖externalFamilyValue2344 coefficient modulation radius position‖ ≤
      coefficientBound * bumpBound := by
  rw [externalFamilyValue2344_eq_familyTerm]
  have hphase :
      ‖Complex.exp ((modulation * position : ℝ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hwidth :
      ‖(widthBump radius position : ℂ)‖ ≤ bumpBound := by
    have hjet := widthBump_iteratedDeriv_inside2350 0 (by decide) hradius hinside
    have hwidthEq : widthBump radius position = scaledBumpJet2350 0 radius position := by
      simpa only [iteratedDeriv_zero] using hjet
    rw [hwidthEq, Complex.norm_real, Real.norm_eq_abs]
    exact hbump
  have hbumpBound : 0 ≤ bumpBound := le_trans (abs_nonneg _) hbump
  have hcoefficientBound : 0 ≤ coefficientBound :=
    le_trans (norm_nonneg _) hcoefficient
  rw [norm_mul, norm_mul, hphase]
  have hmul := mul_le_mul hcoefficient hwidth (norm_nonneg _) hcoefficientBound
  simpa only [mul_one] using hmul

theorem familyLogFirst2345_abs_le_of_interval2488
    (radius position t : ℝ) (hradius : 0 < radius) (hinside : |position| < radius)
    (ht : 0 ≤ t) (htone : t < 1) (hcoord : |position / radius| ≤ t) :
    |familyLogFirst2345 radius position| ≤
      60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius := by
  have hbase : 0 < 1 - t ^ 2 := by
    nlinarith [sq_nonneg t]
  have hdef : 0 < familyDeficit2345 radius position :=
    familyDeficit2345_pos hradius hinside
  have hlower : 1 - t ^ 2 ≤ familyDeficit2345 radius position := by
    dsimp [familyDeficit2345]
    have hsq : (position / radius) ^ 2 ≤ t ^ 2 := by
      have h := (sq_le_sq₀ (abs_nonneg (position / radius)) ht).2 hcoord
      simpa [sq_abs] using h
    linarith
  have hinv : (familyDeficit2345 radius position)⁻¹ ≤ (1 - t ^ 2)⁻¹ :=
    (inv_le_inv₀ hdef hbase).2 hlower
  have hinvpow : (familyDeficit2345 radius position)⁻¹ ^ 2 ≤
      (1 - t ^ 2)⁻¹ ^ 2 :=
    pow_le_pow_left₀ (by positivity) hinv 2
  calc
    |familyLogFirst2345 radius position| =
        60 * |position / radius| * (familyDeficit2345 radius position)⁻¹ ^ 2 /
          radius := by
      simp only [familyLogFirst2345, abs_div, abs_mul, abs_neg, abs_of_pos hradius]
      rw [abs_of_nonneg (sq_nonneg (familyDeficit2345 radius position)⁻¹)]
      ring
    _ ≤ 60 * t * (familyDeficit2345 radius position)⁻¹ ^ 2 / radius := by
      gcongr
    _ ≤ 60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius := by
      gcongr

theorem familyLogSecond2345_abs_le_of_interval2488
    (radius position t : ℝ) (hradius : 0 < radius) (hinside : |position| < radius)
    (ht : 0 ≤ t) (htone : t < 1) (hcoord : |position / radius| ≤ t) :
    |familyLogSecond2345 radius position| ≤
      60 * ((1 - t ^ 2)⁻¹ ^ 2 + 4 * t ^ 2 * (1 - t ^ 2)⁻¹ ^ 3) / radius ^ 2 := by
  have hbase : 0 < 1 - t ^ 2 := by
    nlinarith [sq_nonneg t]
  have hdef : 0 < familyDeficit2345 radius position :=
    familyDeficit2345_pos hradius hinside
  have hlower : 1 - t ^ 2 ≤ familyDeficit2345 radius position := by
    dsimp [familyDeficit2345]
    have hsq : (position / radius) ^ 2 ≤ t ^ 2 := by
      have h := (sq_le_sq₀ (abs_nonneg (position / radius)) ht).2 hcoord
      simpa [sq_abs] using h
    linarith
  have hinv : (familyDeficit2345 radius position)⁻¹ ≤ (1 - t ^ 2)⁻¹ :=
    (inv_le_inv₀ hdef hbase).2 hlower
  have hinv2 : (familyDeficit2345 radius position)⁻¹ ^ 2 ≤
      (1 - t ^ 2)⁻¹ ^ 2 :=
    pow_le_pow_left₀ (by positivity) hinv 2
  have hinv3 : (familyDeficit2345 radius position)⁻¹ ^ 3 ≤
      (1 - t ^ 2)⁻¹ ^ 3 :=
    pow_le_pow_left₀ (by positivity) hinv 3
  have hsq : (position / radius) ^ 2 ≤ t ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg (position / radius)) ht).2 hcoord
    simpa [sq_abs] using h
  calc
    |familyLogSecond2345 radius position| =
        60 * ((familyDeficit2345 radius position)⁻¹ ^ 2 +
          4 * (position / radius) ^ 2 *
            (familyDeficit2345 radius position)⁻¹ ^ 3) / radius ^ 2 := by
      rw [familyLogSecond2345, abs_div, abs_mul]
      have hsum : 0 ≤ (familyDeficit2345 radius position)⁻¹ ^ 2 +
          4 * (position / radius) ^ 2 *
            (familyDeficit2345 radius position)⁻¹ ^ 3 := by positivity
      rw [show |(-60 : ℝ)| = 60 by norm_num, abs_of_nonneg hsum,
        abs_of_pos (sq_pos_of_pos hradius)]
    _ ≤ 60 * ((1 - t ^ 2)⁻¹ ^ 2 +
          4 * t ^ 2 * (1 - t ^ 2)⁻¹ ^ 3) / radius ^ 2 := by
      gcongr

theorem familyFirstFactor2345_norm_le_of_interval2488
    (radius position t modulation : ℝ) (hradius : 0 < radius)
    (hinside : |position| < radius) (ht : 0 ≤ t) (htone : t < 1)
    (hcoord : |position / radius| ≤ t) :
    ‖familyFirstFactor2345 modulation radius position‖ ≤
      60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius + |modulation| := by
  rw [familyFirstFactor2345]
  calc
    ‖(familyLogFirst2345 radius position : ℂ) + (modulation : ℂ) * Complex.I‖ ≤
        ‖(familyLogFirst2345 radius position : ℂ)‖ +
          ‖(modulation : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |familyLogFirst2345 radius position| + |modulation| := by
      simp [norm_mul]
    _ ≤ 60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius + |modulation| := by
      gcongr
      exact familyLogFirst2345_abs_le_of_interval2488 radius position t
        hradius hinside ht htone hcoord

theorem familySecondFactor2345_norm_le_of_interval2488
    (radius position t modulation : ℝ) (hradius : 0 < radius)
    (hinside : |position| < radius) (ht : 0 ≤ t) (htone : t < 1)
    (hcoord : |position / radius| ≤ t) :
    ‖familySecondFactor2345 modulation radius position‖ ≤
      (60 * ((1 - t ^ 2)⁻¹ ^ 2 + 4 * t ^ 2 * (1 - t ^ 2)⁻¹ ^ 3) /
          radius ^ 2) +
        (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius) ^ 2 + modulation ^ 2 +
        2 * |modulation| * (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius) := by
  let firstBound : ℝ := 60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius
  let secondBound : ℝ :=
    60 * ((1 - t ^ 2)⁻¹ ^ 2 + 4 * t ^ 2 * (1 - t ^ 2)⁻¹ ^ 3) / radius ^ 2
  have hfirst := familyLogFirst2345_abs_le_of_interval2488 radius position t
    hradius hinside ht htone hcoord
  have hsecond := familyLogSecond2345_abs_le_of_interval2488 radius position t
    hradius hinside ht htone hcoord
  rw [familySecondFactor2345_eq]
  calc
    ‖(familyFirstFactor2345 modulation radius position) ^ 2 +
        (familyLogSecond2345 radius position : ℂ)‖ ≤
        ‖(familyFirstFactor2345 modulation radius position) ^ 2‖ +
          ‖(familyLogSecond2345 radius position : ℂ)‖ := norm_add_le _ _
    _ = ‖familyFirstFactor2345 modulation radius position‖ ^ 2 +
        |familyLogSecond2345 radius position| := by
          simp [Complex.norm_real, Real.norm_eq_abs, norm_pow]
    _ ≤ (firstBound + |modulation|) ^ 2 + secondBound := by
          gcongr
          · exact familyFirstFactor2345_norm_le_of_interval2488 radius position t modulation
              hradius hinside ht htone hcoord
    _ = secondBound + firstBound ^ 2 + modulation ^ 2 +
          2 * |modulation| * firstBound := by
          dsimp [firstBound, secondBound]
          calc
            (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius + |modulation|) ^ 2 +
                60 * ((1 - t ^ 2)⁻¹ ^ 2 + 4 * t ^ 2 * (1 - t ^ 2)⁻¹ ^ 3) /
                  radius ^ 2 =
              60 * ((1 - t ^ 2)⁻¹ ^ 2 + 4 * t ^ 2 * (1 - t ^ 2)⁻¹ ^ 3) /
                  radius ^ 2 + (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius) ^ 2 +
                |modulation| ^ 2 +
                2 * |modulation| * (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius) := by ring
            _ = _ := by rw [sq_abs]

theorem weightedExternalFamilySecondDeriv_le_of_interval_bounds2488
    (sigma position modulation radius t a coefficientBound : ℝ) (coefficient : ℂ)
    (hradius : 0 < radius) (hinside : |position| < radius)
    (ht : 0 ≤ t) (htone : t < 1) (hcoord : |position / radius| ≤ t)
    (ha : 0 ≤ a) (haone : a < 1) (halower : a ≤ |position / radius|)
    (hcoefficient : ‖coefficient‖ ≤ coefficientBound) :
    ‖deriv (deriv (weightedFunction2348 sigma
      (externalFamilyValue2344 coefficient modulation radius))) position‖ ≤
      weightedCurvature2348 sigma radius
        (coefficientBound * Real.exp (-30 / (1 - a ^ 2)))
        (coefficientBound * Real.exp (-30 / (1 - a ^ 2)) *
          (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius + |modulation|))
        (coefficientBound * Real.exp (-30 / (1 - a ^ 2)) *
          ((60 * ((1 - t ^ 2)⁻¹ ^ 2 + 4 * t ^ 2 * (1 - t ^ 2)⁻¹ ^ 3) /
              radius ^ 2) +
            (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius) ^ 2 + modulation ^ 2 +
            2 * |modulation| * (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius))) := by
  have hscaled := scaledBumpJet2350_abs_le_of_interval_factors2487 0 (by decide)
    hradius hinside ht htone hcoord ha haone halower
  have hbump : |scaledBumpJet2350 0 radius position| ≤
      Real.exp (-30 / (1 - a ^ 2)) := by
    simpa [bumpNumeratorAbsUpper2486] using hscaled
  have hvalue : ‖externalFamilyValue2344 coefficient modulation radius position‖ ≤
      coefficientBound * Real.exp (-30 / (1 - a ^ 2)) := by
    exact externalFamilyValue2344_norm_le_of_scaledBump_bound2488 coefficient modulation
      radius position coefficientBound (Real.exp (-30 / (1 - a ^ 2))) hradius hinside
      hcoefficient hbump
  apply weightedExternalFamilySecondDeriv_le_of_local_bounds2488 sigma position modulation
    radius (coefficientBound * Real.exp (-30 / (1 - a ^ 2)))
    (coefficientBound * Real.exp (-30 / (1 - a ^ 2)) *
      (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius + |modulation|))
    (coefficientBound * Real.exp (-30 / (1 - a ^ 2)) *
      ((60 * ((1 - t ^ 2)⁻¹ ^ 2 + 4 * t ^ 2 * (1 - t ^ 2)⁻¹ ^ 3) /
          radius ^ 2) +
        (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius) ^ 2 + modulation ^ 2 +
        2 * |modulation| * (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius))) coefficient
    hradius hinside hvalue
  · exact externalFamilyValue2344_firstDerivative_norm_le_of_factor_bounds2488
      coefficient modulation radius position
      (coefficientBound * Real.exp (-30 / (1 - a ^ 2)))
      (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius + |modulation|) hradius hinside hvalue
      (familyFirstFactor2345_norm_le_of_interval2488 radius position t modulation
        hradius hinside ht htone hcoord)
  · exact externalFamilyValue2344_secondDerivative_norm_le_of_factor_bounds2488
      coefficient modulation radius position
      (coefficientBound * Real.exp (-30 / (1 - a ^ 2)))
      ((60 * ((1 - t ^ 2)⁻¹ ^ 2 + 4 * t ^ 2 * (1 - t ^ 2)⁻¹ ^ 3) /
          radius ^ 2) +
        (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius) ^ 2 + modulation ^ 2 +
        2 * |modulation| * (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius))
      hradius hinside hvalue
      (familySecondFactor2345_norm_le_of_interval2488 radius position t modulation
        hradius hinside ht htone hcoord)

theorem weightedExternalFamilySecondDeriv_le_of_interval_or_zero2488
    (sigma position modulation radius t a coefficientBound : ℝ) (coefficient : ℂ)
    (hradius : 0 < radius)
    (ht : 0 ≤ t) (htone : t < 1) (hcoord : |position / radius| ≤ t)
    (ha : 0 ≤ a) (haone : a < 1) (halower : a ≤ |position / radius|)
    (hcoefficient : ‖coefficient‖ ≤ coefficientBound) :
    ‖deriv (deriv (weightedFunction2348 sigma
      (externalFamilyValue2344 coefficient modulation radius))) position‖ ≤
      if radius ≤ |position| then 0 else
        weightedCurvature2348 sigma radius
          (coefficientBound * Real.exp (-30 / (1 - a ^ 2)))
          (coefficientBound * Real.exp (-30 / (1 - a ^ 2)) *
            (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius + |modulation|))
          (coefficientBound * Real.exp (-30 / (1 - a ^ 2)) *
            ((60 * ((1 - t ^ 2)⁻¹ ^ 2 + 4 * t ^ 2 * (1 - t ^ 2)⁻¹ ^ 3) /
                radius ^ 2) +
              (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius) ^ 2 + modulation ^ 2 +
              2 * |modulation| *
                (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius))) := by
  by_cases houtside : radius ≤ |position|
  · rw [if_pos houtside]
    rw [weightedExternalFamilySecondDeriv_zero_of_outside2488 sigma coefficient
      modulation radius position hradius houtside]
    simp
  · rw [if_neg houtside]
    exact weightedExternalFamilySecondDeriv_le_of_interval_bounds2488 sigma position
      modulation radius t a coefficientBound coefficient hradius (lt_of_not_ge houtside)
      ht htone hcoord ha haone halower hcoefficient

theorem weightedExternalFamilySecondDeriv_le_of_factor_bounds2488
    (sigma position modulation radius valueBound firstFactorBound secondFactorBound : ℝ)
    (coefficient : ℂ) (hradius : 0 < radius) (hinside : |position| < radius)
    (hvalue : ‖externalFamilyValue2344 coefficient modulation radius position‖ ≤ valueBound)
    (hfirstFactor : ‖familyFirstFactor2345 modulation radius position‖ ≤ firstFactorBound)
    (hsecondFactor : ‖familySecondFactor2345 modulation radius position‖ ≤ secondFactorBound) :
    ‖deriv (deriv (weightedFunction2348 sigma
      (externalFamilyValue2344 coefficient modulation radius))) position‖ ≤
      weightedCurvature2348 sigma radius valueBound
        (valueBound * firstFactorBound) (valueBound * secondFactorBound) := by
  apply weightedExternalFamilySecondDeriv_le_of_local_bounds2488 sigma position modulation radius
    valueBound (valueBound * firstFactorBound) (valueBound * secondFactorBound) coefficient
    hradius hinside hvalue
  · exact externalFamilyValue2344_firstDerivative_norm_le_of_factor_bounds2488
      coefficient modulation radius position valueBound firstFactorBound hradius hinside
      hvalue hfirstFactor
  · exact externalFamilyValue2344_secondDerivative_norm_le_of_factor_bounds2488
      coefficient modulation radius position valueBound secondFactorBound hradius hinside
      hvalue hsecondFactor

theorem ownerPanelWeightedSecondDeriv_le_sumFamilyBound2488
    (sigma x : ℝ) (familyBound : Fin 30 → ℝ)
    (hfamily : ∀ i : Fin 30,
      ‖deriv (deriv (weightedFunction2348 sigma
        (externalFamilyValue2344 (ownerCoef_2463 i) (ownerMod_2463 i)
          (ownerRad_2463 i)))) x‖ ≤ familyBound i) :
    ‖deriv (deriv (weightedFunction2348 sigma ownerPanelSumValue_2467)) x‖ ≤
      ∑ i : Fin 30, familyBound i := by
  let family := fun i : Fin 30 =>
    weightedFunction2348 sigma
      (externalFamilyValue2344 (ownerCoef_2463 i) (ownerMod_2463 i)
        (ownerRad_2463 i))
  have hsmooth : ∀ i : Fin 30,
      ContDiff ℝ (2 : WithTop (WithTop ℕ)) (family i) := fun i =>
    weightedFunction2348_contDiff sigma _
      ((externalFamilyValue2344_contDiff _ _ _ (ownerRadPos_2465 i)).of_le
        (by decide))
  have hsmoothAt : ∀ i : Fin 30, ContDiffAt ℝ 2 (family i) x := fun i =>
    (hsmooth i).contDiffAt
  have hsum : ‖iteratedDeriv 2 (fun y => ∑ i : Fin 30, family i y) x‖ ≤
      ∑ i : Fin 30, familyBound i := by
    rw [iteratedDeriv_fun_sum (fun i _ => hsmoothAt i)]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => by
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hfamily i)
  rw [show weightedFunction2348 sigma ownerPanelSumValue_2467 =
      fun y => ∑ i : Fin 30, family i y by
    funext y
    simp only [weightedFunction2348, ownerPanelSumValue_2467, family]
    exact Finset.mul_sum (Finset.univ : Finset (Fin 30))
      (fun i : Fin 30 => externalFamilyValue2344
        (ownerCoef_2463 i) (ownerMod_2463 i) (ownerRad_2463 i) y)
      (weightedExp2348 sigma y)]
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hsum

theorem ownerPanelWeightedSecondDeriv_le_sumIntervalOrZero2488
    (sigma x : ℝ) (t a coefficientBound : Fin 30 → ℝ)
    (hdata : ∀ i : Fin 30, |x| < ownerRad_2463 i →
      0 ≤ t i ∧ t i < 1 ∧ |x / ownerRad_2463 i| ≤ t i ∧
      0 ≤ a i ∧ a i < 1 ∧ a i ≤ |x / ownerRad_2463 i|)
    (hcoefficient : ∀ i : Fin 30,
      ‖ownerCoef_2463 i‖ ≤ coefficientBound i) :
    ‖deriv (deriv (weightedFunction2348 sigma ownerPanelSumValue_2467)) x‖ ≤
      ∑ i : Fin 30, if ownerRad_2463 i ≤ |x| then 0 else
        weightedCurvature2348 sigma (ownerRad_2463 i)
          (coefficientBound i * Real.exp (-30 / (1 - (a i) ^ 2)))
          (coefficientBound i * Real.exp (-30 / (1 - (a i) ^ 2)) *
            (60 * t i * (1 - (t i) ^ 2)⁻¹ ^ 2 / ownerRad_2463 i +
              |ownerMod_2463 i|))
          (coefficientBound i * Real.exp (-30 / (1 - (a i) ^ 2)) *
            ((60 * ((1 - (t i) ^ 2)⁻¹ ^ 2 +
                4 * (t i) ^ 2 * (1 - (t i) ^ 2)⁻¹ ^ 3) /
                (ownerRad_2463 i) ^ 2) +
              (60 * t i * (1 - (t i) ^ 2)⁻¹ ^ 2 /
                ownerRad_2463 i) ^ 2 + (ownerMod_2463 i) ^ 2 +
              2 * |ownerMod_2463 i| *
                (60 * t i * (1 - (t i) ^ 2)⁻¹ ^ 2 /
                  ownerRad_2463 i))) := by
  apply ownerPanelWeightedSecondDeriv_le_sumFamilyBound2488 sigma x
  intro i
  by_cases houtside : ownerRad_2463 i ≤ |x|
  · rw [if_pos houtside]
    rw [weightedExternalFamilySecondDeriv_zero_of_outside2488 sigma
      (ownerCoef_2463 i) (ownerMod_2463 i) (ownerRad_2463 i) x
      (ownerRadPos_2465 i) houtside]
    simp
  · rw [if_neg houtside]
    have hinside : |x| < ownerRad_2463 i := lt_of_not_ge houtside
    rcases hdata i hinside with ⟨ht, htone, hcoord, ha, haone, halower⟩
    exact weightedExternalFamilySecondDeriv_le_of_interval_bounds2488 sigma x
      (ownerMod_2463 i) (ownerRad_2463 i) (t i) (a i) (coefficientBound i)
      (ownerCoef_2463 i) (ownerRadPos_2465 i) hinside ht htone hcoord ha haone
      halower (hcoefficient i)

theorem ownerPanelWeightedSecondDeriv_le_sumFactorBound2488
    (sigma x : ℝ) (valueBound firstFactorBound secondFactorBound : Fin 30 → ℝ)
    (hinside : ∀ i : Fin 30, |x| < ownerRad_2463 i)
    (hvalue : ∀ i : Fin 30,
      ‖externalFamilyValue2344 (ownerCoef_2463 i) (ownerMod_2463 i)
        (ownerRad_2463 i) x‖ ≤ valueBound i)
    (hfirstFactor : ∀ i : Fin 30,
      ‖familyFirstFactor2345 (ownerMod_2463 i) (ownerRad_2463 i) x‖ ≤ firstFactorBound i)
    (hsecondFactor : ∀ i : Fin 30,
      ‖familySecondFactor2345 (ownerMod_2463 i) (ownerRad_2463 i) x‖ ≤
        secondFactorBound i) :
    ‖deriv (deriv (weightedFunction2348 sigma ownerPanelSumValue_2467)) x‖ ≤
      ∑ i : Fin 30, weightedCurvature2348 sigma (ownerRad_2463 i) (valueBound i)
        (valueBound i * firstFactorBound i) (valueBound i * secondFactorBound i) := by
  apply ownerPanelWeightedSecondDeriv_le_sumFamilyBound2488 sigma x
    (fun i => weightedCurvature2348 sigma (ownerRad_2463 i) (valueBound i)
      (valueBound i * firstFactorBound i) (valueBound i * secondFactorBound i))
  intro i
  exact weightedExternalFamilySecondDeriv_le_of_factor_bounds2488 sigma x
    (ownerMod_2463 i) (ownerRad_2463 i) (valueBound i) (firstFactorBound i)
    (secondFactorBound i) (ownerCoef_2463 i) (ownerRadPos_2465 i) (hinside i)
    (hvalue i) (hfirstFactor i) (hsecondFactor i)

theorem ownerPanelWeightedSecondDeriv_le_sumIntervalBound2488
    (sigma x : ℝ) (t a coefficientBound : Fin 30 → ℝ)
    (hinside : ∀ i : Fin 30, |x| < ownerRad_2463 i)
    (ht : ∀ i : Fin 30, 0 ≤ t i)
    (htone : ∀ i : Fin 30, t i < 1)
    (hcoord : ∀ i : Fin 30,
      |x / ownerRad_2463 i| ≤ t i)
    (ha : ∀ i : Fin 30, 0 ≤ a i)
    (haone : ∀ i : Fin 30, a i < 1)
    (halower : ∀ i : Fin 30,
      a i ≤ |x / ownerRad_2463 i|)
    (hcoefficient : ∀ i : Fin 30,
      ‖ownerCoef_2463 i‖ ≤ coefficientBound i) :
    ‖deriv (deriv (weightedFunction2348 sigma ownerPanelSumValue_2467)) x‖ ≤
      ∑ i : Fin 30, weightedCurvature2348 sigma (ownerRad_2463 i)
        (coefficientBound i * Real.exp (-30 / (1 - (a i) ^ 2)))
        (coefficientBound i * Real.exp (-30 / (1 - (a i) ^ 2)) *
          (60 * t i * (1 - (t i) ^ 2)⁻¹ ^ 2 / ownerRad_2463 i +
            |ownerMod_2463 i|))
        (coefficientBound i * Real.exp (-30 / (1 - (a i) ^ 2)) *
          ((60 * ((1 - (t i) ^ 2)⁻¹ ^ 2 +
              4 * (t i) ^ 2 * (1 - (t i) ^ 2)⁻¹ ^ 3) /
              (ownerRad_2463 i) ^ 2) +
            (60 * t i * (1 - (t i) ^ 2)⁻¹ ^ 2 / ownerRad_2463 i) ^ 2 +
            (ownerMod_2463 i) ^ 2 +
            2 * |ownerMod_2463 i| *
              (60 * t i * (1 - (t i) ^ 2)⁻¹ ^ 2 / ownerRad_2463 i))) := by
  apply ownerPanelWeightedSecondDeriv_le_sumFamilyBound2488 sigma x
    (fun i => weightedCurvature2348 sigma (ownerRad_2463 i)
      (coefficientBound i * Real.exp (-30 / (1 - (a i) ^ 2)))
      (coefficientBound i * Real.exp (-30 / (1 - (a i) ^ 2)) *
        (60 * t i * (1 - (t i) ^ 2)⁻¹ ^ 2 / ownerRad_2463 i +
          |ownerMod_2463 i|))
      (coefficientBound i * Real.exp (-30 / (1 - (a i) ^ 2)) *
        ((60 * ((1 - (t i) ^ 2)⁻¹ ^ 2 +
            4 * (t i) ^ 2 * (1 - (t i) ^ 2)⁻¹ ^ 3) /
            (ownerRad_2463 i) ^ 2) +
          (60 * t i * (1 - (t i) ^ 2)⁻¹ ^ 2 / ownerRad_2463 i) ^ 2 +
          (ownerMod_2463 i) ^ 2 +
          2 * |ownerMod_2463 i| *
            (60 * t i * (1 - (t i) ^ 2)⁻¹ ^ 2 / ownerRad_2463 i))))
  intro i
  exact weightedExternalFamilySecondDeriv_le_of_interval_bounds2488
    sigma x (ownerMod_2463 i) (ownerRad_2463 i) (t i) (a i)
    (coefficientBound i) (ownerCoef_2463 i) (ownerRadPos_2465 i) (hinside i)
    (ht i) (htone i) (hcoord i) (ha i) (haone i) (halower i) (hcoefficient i)

theorem ownerPanelStripNorm_le_intervalCurvature2488
    (sigma radius step : ℝ) (cells : ℕ)
    (t a coefficientBound : ℕ → Fin 30 → ℝ)
    (hradius : 0 ≤ radius)
    (hR : ∀ i : Fin 30, ownerRad_2463 i ≤ radius)
    (hstep : 0 < step)
    (hgrid : (cells : ℝ) * step = 2 * radius)
    (hinside : ∀ index ∈ Finset.range cells, ∀ coordinate ∈
      Set.Icc (-radius + index * step) (-radius + (index + 1) * step),
      ∀ i : Fin 30, |coordinate| < ownerRad_2463 i)
    (ht : ∀ index ∈ Finset.range cells, ∀ coordinate ∈
      Set.Icc (-radius + index * step) (-radius + (index + 1) * step),
      ∀ i : Fin 30, 0 ≤ t index i)
    (htone : ∀ index ∈ Finset.range cells, ∀ coordinate ∈
      Set.Icc (-radius + index * step) (-radius + (index + 1) * step),
      ∀ i : Fin 30, t index i < 1)
    (hcoord : ∀ index ∈ Finset.range cells, ∀ coordinate ∈
      Set.Icc (-radius + index * step) (-radius + (index + 1) * step),
      ∀ i : Fin 30, |coordinate / ownerRad_2463 i| ≤ t index i)
    (ha : ∀ index ∈ Finset.range cells, ∀ coordinate ∈
      Set.Icc (-radius + index * step) (-radius + (index + 1) * step),
      ∀ i : Fin 30, 0 ≤ a index i)
    (haone : ∀ index ∈ Finset.range cells, ∀ coordinate ∈
      Set.Icc (-radius + index * step) (-radius + (index + 1) * step),
      ∀ i : Fin 30, a index i < 1)
    (halower : ∀ index ∈ Finset.range cells, ∀ coordinate ∈
      Set.Icc (-radius + index * step) (-radius + (index + 1) * step),
      ∀ i : Fin 30, a index i ≤ |coordinate / ownerRad_2463 i|)
    (hcoefficient : ∀ index ∈ Finset.range cells, ∀ i : Fin 30,
      ‖ownerCoef_2463 i‖ ≤ coefficientBound index i) :
    stripNorm sigma ownerPanelSumValue_2467 ≤
      compositeNodeUpper2347
        (ownerPanelNodeUpper2471 sigma radius step) step cells +
      localCurvatureRemainder2474
        (fun index => ∑ i : Fin 30, weightedCurvature2348 sigma
          (ownerRad_2463 i)
          (coefficientBound index i * Real.exp (-30 / (1 - (a index i) ^ 2)))
          (coefficientBound index i * Real.exp (-30 / (1 - (a index i) ^ 2)) *
            (60 * t index i * (1 - (t index i) ^ 2)⁻¹ ^ 2 /
              ownerRad_2463 i + |ownerMod_2463 i|))
          (coefficientBound index i * Real.exp (-30 / (1 - (a index i) ^ 2)) *
            ((60 * ((1 - (t index i) ^ 2)⁻¹ ^ 2 +
                4 * (t index i) ^ 2 * (1 - (t index i) ^ 2)⁻¹ ^ 3) /
                (ownerRad_2463 i) ^ 2) +
              (60 * t index i * (1 - (t index i) ^ 2)⁻¹ ^ 2 /
                ownerRad_2463 i) ^ 2 + (ownerMod_2463 i) ^ 2 +
              2 * |ownerMod_2463 i| *
                (60 * t index i * (1 - (t index i) ^ 2)⁻¹ ^ 2 /
                  ownerRad_2463 i)))) step cells := by
  let curvature : ℕ → ℝ := fun index => ∑ i : Fin 30,
    weightedCurvature2348 sigma (ownerRad_2463 i)
      (coefficientBound index i * Real.exp (-30 / (1 - (a index i) ^ 2)))
      (coefficientBound index i * Real.exp (-30 / (1 - (a index i) ^ 2)) *
        (60 * t index i * (1 - (t index i) ^ 2)⁻¹ ^ 2 /
          ownerRad_2463 i + |ownerMod_2463 i|))
      (coefficientBound index i * Real.exp (-30 / (1 - (a index i) ^ 2)) *
        ((60 * ((1 - (t index i) ^ 2)⁻¹ ^ 2 +
            4 * (t index i) ^ 2 * (1 - (t index i) ^ 2)⁻¹ ^ 3) /
            (ownerRad_2463 i) ^ 2) +
          (60 * t index i * (1 - (t index i) ^ 2)⁻¹ ^ 2 /
            ownerRad_2463 i) ^ 2 + (ownerMod_2463 i) ^ 2 +
          2 * |ownerMod_2463 i| *
            (60 * t index i * (1 - (t index i) ^ 2)⁻¹ ^ 2 /
              ownerRad_2463 i)))
  apply ownerPanelStripNorm_le_localCurvature2475 sigma radius step cells curvature
    hradius hR hstep hgrid
  intro index hindex coordinate hcoordinate
  apply ownerPanelWeightedSecondDeriv_le_sumIntervalBound2488 sigma coordinate
    (t index) (a index) (coefficientBound index)
  · exact hinside index hindex coordinate hcoordinate
  · exact ht index hindex coordinate hcoordinate
  · exact htone index hindex coordinate hcoordinate
  · exact hcoord index hindex coordinate hcoordinate
  · exact ha index hindex coordinate hcoordinate
  · exact haone index hindex coordinate hcoordinate
  · exact halower index hindex coordinate hcoordinate
  · exact hcoefficient index hindex

theorem ownerPanelWeightedSecondDeriv_le_sumIntervalZeroLowerBound2488
    (sigma x : ℝ) (t coefficientBound : Fin 30 → ℝ)
    (hinside : ∀ i : Fin 30, |x| < ownerRad_2463 i)
    (ht : ∀ i : Fin 30, 0 ≤ t i)
    (htone : ∀ i : Fin 30, t i < 1)
    (hcoord : ∀ i : Fin 30, |x / ownerRad_2463 i| ≤ t i)
    (hcoefficient : ∀ i : Fin 30,
      ‖ownerCoef_2463 i‖ ≤ coefficientBound i) :
    ‖deriv (deriv (weightedFunction2348 sigma ownerPanelSumValue_2467)) x‖ ≤
      ∑ i : Fin 30, weightedCurvature2348 sigma (ownerRad_2463 i)
        (coefficientBound i * Real.exp (-30 / (1 - (0 : ℝ) ^ 2)))
        (coefficientBound i * Real.exp (-30 / (1 - (0 : ℝ) ^ 2)) *
          (60 * t i * (1 - (t i) ^ 2)⁻¹ ^ 2 / ownerRad_2463 i +
            |ownerMod_2463 i|))
        (coefficientBound i * Real.exp (-30 / (1 - (0 : ℝ) ^ 2)) *
          ((60 * ((1 - (t i) ^ 2)⁻¹ ^ 2 +
              4 * (t i) ^ 2 * (1 - (t i) ^ 2)⁻¹ ^ 3) /
              (ownerRad_2463 i) ^ 2) +
            (60 * t i * (1 - (t i) ^ 2)⁻¹ ^ 2 / ownerRad_2463 i) ^ 2 +
            (ownerMod_2463 i) ^ 2 +
            2 * |ownerMod_2463 i| *
              (60 * t i * (1 - (t i) ^ 2)⁻¹ ^ 2 / ownerRad_2463 i))) := by
  apply ownerPanelWeightedSecondDeriv_le_sumIntervalBound2488 sigma x t
    (fun _ => 0) coefficientBound
  · exact hinside
  · exact ht
  · exact htone
  · exact hcoord
  · intro i
    norm_num
  · intro i
    norm_num
  · intro i
    exact abs_nonneg _
  · exact hcoefficient

noncomputable def ownerIntervalCurvatureZero2488
    (sigma : ℝ) (t coefficientBound : Fin 30 → ℝ) : ℝ :=
  ∑ i : Fin 30, weightedCurvature2348 sigma (ownerRad_2463 i)
    (coefficientBound i * Real.exp (-30 / (1 - (0 : ℝ) ^ 2)))
    (coefficientBound i * Real.exp (-30 / (1 - (0 : ℝ) ^ 2)) *
      (60 * t i * (1 - (t i) ^ 2)⁻¹ ^ 2 / ownerRad_2463 i +
        |ownerMod_2463 i|))
    (coefficientBound i * Real.exp (-30 / (1 - (0 : ℝ) ^ 2)) *
      ((60 * ((1 - (t i) ^ 2)⁻¹ ^ 2 +
          4 * (t i) ^ 2 * (1 - (t i) ^ 2)⁻¹ ^ 3) /
          (ownerRad_2463 i) ^ 2) +
        (60 * t i * (1 - (t i) ^ 2)⁻¹ ^ 2 / ownerRad_2463 i) ^ 2 +
        (ownerMod_2463 i) ^ 2 +
        2 * |ownerMod_2463 i| *
          (60 * t i * (1 - (t i) ^ 2)⁻¹ ^ 2 / ownerRad_2463 i)))

theorem abs_le_max_abs_endpoints_of_mem_Icc2488
    {left right coordinate : ℝ} (hcoordinate : coordinate ∈ Set.Icc left right) :
    |coordinate| ≤ max |left| |right| := by
  apply abs_le.mpr
  constructor
  · exact (neg_le_neg (le_max_left |left| |right|)).trans
      (neg_abs_le left) |>.trans hcoordinate.1
  · exact hcoordinate.2.trans (le_abs_self right) |>.trans
      (le_max_right |left| |right|)

theorem abs_div_le_of_mem_Icc_of_endpointBound2488
    {left right coordinate radius t : ℝ}
    (hradius : 0 < radius)
    (hcoordinate : coordinate ∈ Set.Icc left right)
    (hendpoint : max |left| |right| ≤ t * radius) :
    |coordinate / radius| ≤ t := by
  rw [abs_div, abs_of_pos hradius]
  exact (div_le_iff₀ hradius).2
    (le_trans (abs_le_max_abs_endpoints_of_mem_Icc2488 hcoordinate) hendpoint)

theorem ownerCoordinateNormalizedBound_of_endpointBound2488
    {left right coordinate : ℝ} (t : Fin 30 → ℝ)
    (hcoordinate : coordinate ∈ Set.Icc left right)
    (hendpoint : ∀ i : Fin 30,
      max |left| |right| ≤ t i * ownerRad_2463 i) :
    ∀ i : Fin 30, |coordinate / ownerRad_2463 i| ≤ t i := by
  intro i
  exact abs_div_le_of_mem_Icc_of_endpointBound2488
    (ownerRadPos_2465 i) hcoordinate (hendpoint i)

noncomputable def ownerCellEndpointRatio2488
    (radius step : ℝ) (index : ℕ) (i : Fin 30) : ℝ :=
  max |(-radius + index * step)|
      |(-radius + (index + 1) * step)| / ownerRad_2463 i

theorem ownerCellEndpointRatio_nonneg2488
    (radius step : ℝ) (index : ℕ) (i : Fin 30) :
    0 ≤ ownerCellEndpointRatio2488 radius step index i := by
  unfold ownerCellEndpointRatio2488
  exact div_nonneg
    ((abs_nonneg _).trans (le_max_left _ _)) (ownerRadPos_2465 i).le

theorem ownerCellEndpointRatio_lt_one2488
    (radius step : ℝ) (index : ℕ) (i : Fin 30)
    (hleft : |(-radius + index * step)| < ownerRad_2463 i)
    (hright : |(-radius + (index + 1) * step)| < ownerRad_2463 i) :
    ownerCellEndpointRatio2488 radius step index i < 1 := by
  unfold ownerCellEndpointRatio2488
  apply (div_lt_iff₀ (ownerRadPos_2465 i)).2
  simpa only [max_lt_iff, one_mul] using And.intro hleft hright

theorem ownerCellEndpointRatio_endpointBound2488
    (radius step : ℝ) (index : ℕ) (i : Fin 30) :
    max |(-radius + index * step)|
        |(-radius + (index + 1) * step)| ≤
      ownerCellEndpointRatio2488 radius step index i * ownerRad_2463 i := by
  unfold ownerCellEndpointRatio2488
  exact le_of_eq (div_mul_cancel₀ _ (ne_of_gt (ownerRadPos_2465 i))).symm

theorem ownerPanelWeightedSecondDeriv_le_ownerIntervalCurvatureZero2488
    (sigma x : ℝ) (t coefficientBound : Fin 30 → ℝ)
    (hinside : ∀ i : Fin 30, |x| < ownerRad_2463 i)
    (ht : ∀ i : Fin 30, 0 ≤ t i)
    (htone : ∀ i : Fin 30, t i < 1)
    (hcoord : ∀ i : Fin 30, |x / ownerRad_2463 i| ≤ t i)
    (hcoefficient : ∀ i : Fin 30,
      ‖ownerCoef_2463 i‖ ≤ coefficientBound i) :
    ‖deriv (deriv (weightedFunction2348 sigma ownerPanelSumValue_2467)) x‖ ≤
      ownerIntervalCurvatureZero2488 sigma t coefficientBound := by
  simpa only [ownerIntervalCurvatureZero2488] using
    ownerPanelWeightedSecondDeriv_le_sumIntervalZeroLowerBound2488 sigma x t
      coefficientBound hinside ht htone hcoord hcoefficient

theorem ownerPanelStripNorm_le_endpointIntervalCurvatureZero2488
    (sigma radius step : ℝ) (cells : ℕ)
    (t coefficientBound : ℕ → Fin 30 → ℝ)
    (hradius : 0 ≤ radius)
    (hR : ∀ i : Fin 30, ownerRad_2463 i ≤ radius)
    (hstep : 0 < step)
    (hgrid : (cells : ℝ) * step = 2 * radius)
    (hinside : ∀ index ∈ Finset.range cells, ∀ coordinate ∈
      Set.Icc (-radius + index * step) (-radius + (index + 1) * step),
      ∀ i : Fin 30, |coordinate| < ownerRad_2463 i)
    (ht : ∀ index ∈ Finset.range cells, ∀ coordinate ∈
      Set.Icc (-radius + index * step) (-radius + (index + 1) * step),
      ∀ i : Fin 30, 0 ≤ t index i)
    (htone : ∀ index ∈ Finset.range cells, ∀ coordinate ∈
      Set.Icc (-radius + index * step) (-radius + (index + 1) * step),
      ∀ i : Fin 30, t index i < 1)
    (hendpoint : ∀ index ∈ Finset.range cells, ∀ i : Fin 30,
      max |(-radius + index * step)|
          |(-radius + (index + 1) * step)| ≤
        t index i * ownerRad_2463 i)
    (hcoefficient : ∀ index ∈ Finset.range cells, ∀ i : Fin 30,
      ‖ownerCoef_2463 i‖ ≤ coefficientBound index i) :
    stripNorm sigma ownerPanelSumValue_2467 ≤
      compositeNodeUpper2347
        (ownerPanelNodeUpper2471 sigma radius step) step cells +
      localCurvatureRemainder2474
        (fun index => ownerIntervalCurvatureZero2488 sigma
          (t index) (coefficientBound index)) step cells := by
  apply ownerPanelStripNorm_le_localCurvature2475 sigma radius step cells
    (fun index => ownerIntervalCurvatureZero2488 sigma
      (t index) (coefficientBound index)) hradius hR hstep hgrid
  intro index hindex coordinate hcoordinate
  apply ownerPanelWeightedSecondDeriv_le_ownerIntervalCurvatureZero2488
    sigma coordinate (t index) (coefficientBound index)
  · exact hinside index hindex coordinate hcoordinate
  · exact ht index hindex coordinate hcoordinate
  · exact htone index hindex coordinate hcoordinate
  · exact ownerCoordinateNormalizedBound_of_endpointBound2488 (t index)
      hcoordinate (hendpoint index hindex)
  · exact hcoefficient index hindex

theorem ownerPanelStripNorm_le_constructedEndpointCurvatureZero2488
    (sigma radius step : ℝ) (cells : ℕ)
    (coefficientBound : ℕ → Fin 30 → ℝ)
    (hradius : 0 ≤ radius)
    (hR : ∀ i : Fin 30, ownerRad_2463 i ≤ radius)
    (hstep : 0 < step)
    (hgrid : (cells : ℝ) * step = 2 * radius)
    (hinside : ∀ index ∈ Finset.range cells, ∀ coordinate ∈
      Set.Icc (-radius + index * step) (-radius + (index + 1) * step),
      ∀ i : Fin 30, |coordinate| < ownerRad_2463 i)
    (hcoefficient : ∀ index ∈ Finset.range cells, ∀ i : Fin 30,
      ‖ownerCoef_2463 i‖ ≤ coefficientBound index i) :
    stripNorm sigma ownerPanelSumValue_2467 ≤
      compositeNodeUpper2347
        (ownerPanelNodeUpper2471 sigma radius step) step cells +
      localCurvatureRemainder2474
      (fun index => ownerIntervalCurvatureZero2488 sigma
          (fun i => ownerCellEndpointRatio2488 radius step index i)
          (coefficientBound index)) step cells := by
  have hcell : ∀ index ∈ Finset.range cells,
      -radius + index * step ≤ -radius + (index + 1) * step := by
    intro index hindex
    have hmul : (index : ℝ) * step ≤ ((index : ℝ) + 1) * step := by
      nlinarith [hstep]
    nlinarith [hmul]
  apply ownerPanelStripNorm_le_endpointIntervalCurvatureZero2488 sigma radius step cells
    (fun index i => ownerCellEndpointRatio2488 radius step index i)
    coefficientBound hradius hR hstep hgrid hinside
  · intro index hindex coordinate hcoordinate i
    exact ownerCellEndpointRatio_nonneg2488 radius step index i
  · intro index hindex coordinate hcoordinate i
    apply ownerCellEndpointRatio_lt_one2488 radius step index i
    · exact hinside index hindex
        (-radius + index * step) ⟨le_rfl, hcell index hindex⟩ i
    · exact hinside index hindex
        (-radius + (index + 1) * step) ⟨hcell index hindex, le_rfl⟩ i
  · intro index hindex i
    exact ownerCellEndpointRatio_endpointBound2488 radius step index i
  · exact hcoefficient

/- The coefficient envelope used by the local interval consumer can be
   discharged directly from the exact complex coefficient representation.
   Keeping this as a separate interface leaves the cell geometry responsible
   only for the support and normalized-coordinate hypotheses. -/
theorem ownerCoefficientL1Bound2488 (i : Fin 30) :
    ‖ownerCoef_2463 i‖ ≤ |(ownerCoef_2463 i).re| + |(ownerCoef_2463 i).im| := by
  exact Complex.norm_le_abs_re_add_abs_im _

theorem ownerPanelStripNorm_le_constructedEndpointCurvatureL1_2488
    (sigma radius step : ℝ) (cells : ℕ)
    (hradius : 0 ≤ radius)
    (hR : ∀ i : Fin 30, ownerRad_2463 i ≤ radius)
    (hstep : 0 < step)
    (hgrid : (cells : ℝ) * step = 2 * radius)
    (hinside : ∀ index ∈ Finset.range cells, ∀ coordinate ∈
      Set.Icc (-radius + index * step) (-radius + (index + 1) * step),
      ∀ i : Fin 30, |coordinate| < ownerRad_2463 i) :
    stripNorm sigma ownerPanelSumValue_2467 ≤
      compositeNodeUpper2347
        (ownerPanelNodeUpper2471 sigma radius step) step cells +
      localCurvatureRemainder2474
      (fun index => ownerIntervalCurvatureZero2488 sigma
          (fun i => ownerCellEndpointRatio2488 radius step index i)
          (fun i => |(ownerCoef_2463 i).re| + |(ownerCoef_2463 i).im|)) step cells := by
  apply ownerPanelStripNorm_le_constructedEndpointCurvatureZero2488 sigma radius step cells
    (fun _ i => |(ownerCoef_2463 i).re| + |(ownerCoef_2463 i).im|)
    hradius hR hstep hgrid hinside
  intro index hindex i
  exact ownerCoefficientL1Bound2488 i

/- The endpoint consumer above is intentionally not the production bridge yet:
   its uniform `hinside` premise is incompatible with the owner-radius
   ordering used by the node consumer as soon as the strip radius is positive.
   This lemma keeps that obstruction explicit, so it cannot be mistaken for a
   discharged numerical certificate. -/
theorem ownerPanelEndpointCoverage_incompatible2488
    (radius step : ℝ) (cells : ℕ)
    (hradius : 0 < radius)
    (hR : ∀ i : Fin 30, ownerRad_2463 i ≤ radius)
    (hstep : 0 < step)
    (hgrid : (cells : ℝ) * step = 2 * radius)
    (hinside : ∀ index ∈ Finset.range cells, ∀ coordinate ∈
      Set.Icc (-radius + index * step) (-radius + (index + 1) * step),
      ∀ i : Fin 30, |coordinate| < ownerRad_2463 i) :
    False := by
  have hcells : 0 < cells := by
    by_contra hnot
    have hzero : cells = 0 := Nat.eq_zero_of_not_pos hnot
    subst hzero
    norm_num at hgrid
    linarith
  let i : Fin 30 := ⟨0, by decide⟩
  have hmem : 0 ∈ Finset.range cells := Finset.mem_range.mpr hcells
  have hleft : -radius ≤ -radius + ((0 : ℕ) + 1) * step := by
    norm_num
    linarith
  have hpoint := hinside 0 hmem (-radius) ⟨by norm_num, hleft⟩ i
  have hsmall : radius < ownerRad_2463 i := by
    simpa [abs_of_pos hradius] using hpoint
  exact (not_lt_of_ge (hR i)) hsmall

end ConnesWeilRH.Dev
