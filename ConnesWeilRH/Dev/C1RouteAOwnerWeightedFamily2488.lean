import ConnesWeilRH.Dev.C1RouteALocalBumpFactors2487
import ConnesWeilRH.Dev.C1RouteAOwnerLocalCurvature2475

/-  2488: weighted finite-family composition for the actual owner.

The local bump interface supplies bounds for one family term.  This theorem
keeps the owner as the literal 30-term sum and composes those bounds after the
sigma weight has been applied.  It remains parameterized by family-level
analytic bounds; no table entry is promoted to a proof premise here.
-/

namespace ConnesWeilRH.Dev

open scoped BigOperators ContDiff
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

set_option linter.style.longLine false
set_option maxRecDepth 32768

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

/- The coefficient envelope used by the local interval consumer can be
   discharged directly from the exact complex coefficient representation.
   Keeping this as a separate interface leaves the cell geometry responsible
   only for the support and normalized-coordinate hypotheses. -/
theorem ownerCoefficientL1Bound2488 (i : Fin 30) :
    ‖ownerCoef_2463 i‖ ≤ |(ownerCoef_2463 i).re| + |(ownerCoef_2463 i).im| := by
  exact Complex.norm_le_abs_re_add_abs_im _

end ConnesWeilRH.Dev
