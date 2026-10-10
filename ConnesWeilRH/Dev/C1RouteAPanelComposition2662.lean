import ConnesWeilRH.Dev.C1RouteAPanelBall2660P095

/-!
# Generic panel L1 ball for the normalized moment partition (record 2662)

Panel-generic form of the record-2660 ball replacement.  For a phase function
`phase`, a rational polynomial `polynomial`, and abstract pin data
(`ampArg` / `ampVal` / `ampRad` for the amplitude, `phaseArg` / `phaseVal` /
`phaseRad` for the rotation, `polyInt` for the polynomial integral), the true
panel integral of the center-normalized exponential satisfies

  |amp(center) * rot(center) * integral - ampVal * (phaseVal * polyInt)|_L1
    <= assemblyCharge + residualCharge,

where `assemblyCharge` bounds the exact rational product charge and
`residualCharge` bounds the record-2656 analytic residual charge of the exact
product center.  Instantiating this single lemma at each panel replaces 190
copies of the record-2660 proof text; the residual charge may be taken at a
rationalized `3^n` upper bound of the analytic exponential factor via
`exp_le_three_pow_rat2662`.

Scope: one panel at a time.  The 190-panel partition sum, the edge slices and
the entry containment against `analyticMomentInterval2597_row_00` element 3
are separate obligations.  No producer GO, no RH claim.
-/

namespace ConnesWeilRH.Dev

open Set

-- The long integral binders exceed the 100-character style limit by construction.
set_option linter.style.longLine false

/-- The real amplitude embedded into ℂ.  Named (not inlined) so that the
`.re` / `.im` behavior of the coercion is fixed by rfl lemmas instead of
depending on how the elaborator expands the `(x : ℂ)` ascription. -/
noncomputable def ampCenterComplex2662 (ampArg : ℝ) : ℂ :=
  Complex.ofReal (Real.exp ampArg)

theorem ampCenterComplex2662_im (ampArg : ℝ) :
    (ampCenterComplex2662 ampArg).im = 0 := rfl

theorem ampCenterComplex2662_re (ampArg : ℝ) :
    (ampCenterComplex2662 ampArg).re = Real.exp ampArg := rfl

/-- The exact rotation `exp(i * phaseArg)`. -/
noncomputable def rotTrue2662 (phaseArg : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((phaseArg : ℝ) : ℂ))

theorem rotTrue2662_re (phaseArg : ℝ) :
    (rotTrue2662 phaseArg).re = Real.cos phaseArg := by
  rw [rotTrue2662]
  exact exp_I_re_cos2646 phaseArg

theorem rotTrue2662_im (phaseArg : ℝ) :
    (rotTrue2662 phaseArg).im = Real.sin phaseArg := by
  rw [rotTrue2662]
  exact exp_I_im_sin2646 phaseArg

theorem rotTrue2662_norm (phaseArg : ℝ) : ‖rotTrue2662 phaseArg‖ = 1 := by
  rw [rotTrue2662, Complex.norm_exp]
  have h0 : (Complex.I * ((phaseArg : ℝ) : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [h0, Real.exp_zero]

theorem pairMagnitude2542_nonneg2662 (a : RatPair2542) :
    (0 : ℚ) ≤ pairMagnitude2542 a := by
  unfold pairMagnitude2542
  positivity

/-- Rationalize the exponential factor: `e^x <= 3^n` whenever `x <= n`. -/
theorem exp_le_three_pow2662 (x : ℝ) (n : ℕ) (hx : x ≤ (n : ℝ)) :
    Real.exp x ≤ (3 : ℝ) ^ n := by
  calc Real.exp x ≤ Real.exp (n : ℝ) := Real.exp_le_exp.mpr hx
    _ = (Real.exp 1) ^ n := by
        have h := Real.exp_nat_mul (1 : ℝ) n
        rw [mul_one] at h
        exact h
    _ ≤ (3 : ℝ) ^ n :=
        pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le n

/-- Rational-valued form of `exp_le_three_pow2662`. -/
theorem exp_le_three_pow_rat2662 (x : ℝ) (n : ℕ) (hx : x ≤ (n : ℝ)) :
    Real.exp x ≤ (((3 : ℚ) ^ n : ℚ) : ℝ) := by
  rw [show (((3 : ℚ) ^ n : ℚ) : ℝ) = (3 : ℝ) ^ n by push_cast; rfl]
  exact exp_le_three_pow2662 x n hx

/-- Generic panel L1 ball: the true panel integral of the center-normalized
exponential, multiplied by the true center amplitude and rotation, lies in
the L1 ball around the exact rational product center with radius
`assemblyCharge + residualCharge`. -/
theorem panelL1Ball2662
    (phase : ℝ → ℂ) (polynomial : List RatPair2542)
    (ampArg phaseArg eE halfWidth : ℝ)
    (ampVal ampRad phaseRad RU deficitSq : ℚ) (phaseVal polyInt : RatPair2542)
    (assemblyCharge resCharge : ℝ)
    (hamp : |Real.exp ampArg - (ampVal : ℝ)| ≤ (ampRad : ℝ))
    (hcos : |Real.cos phaseArg - (phaseVal.1 : ℝ)| ≤ (phaseRad : ℝ))
    (hsin : |Real.sin phaseArg - (phaseVal.2 : ℝ)| ≤ (phaseRad : ℝ))
    (haval : (0 : ℚ) ≤ ampVal) (hrad : (0 : ℚ) ≤ ampRad)
    (hphR : (0 : ℚ) ≤ phaseRad)
    (hEint : IntervalIntegrable (fun u => Complex.exp (phase u - phase 0)
        - complexPolyEval2647 polynomial u) MeasureTheory.volume
        (-halfWidth) halfWidth)
    (hPint : IntervalIntegrable (complexPolyEval2647 polynomial)
        MeasureTheory.volume (-halfWidth) halfWidth)
    (hpolyInt : (∫ u in (-halfWidth)..halfWidth,
        complexPolyEval2647 polynomial u) = embedPair2542 polyInt)
    (hE : ‖(∫ u in (-halfWidth)..halfWidth, Complex.exp (phase u - phase 0)
        - complexPolyEval2647 polynomial u)‖
        ≤ Real.exp eE * ((RU / deficitSq : ℚ) : ℝ) * (2 * halfWidth ^ 2))
    (hac : ((ampVal + ampRad : ℚ) : ℝ) * (2 : ℝ) * (phaseRad : ℝ)
            * (pairMagnitude2542 polyInt : ℝ)
        + (ampRad : ℝ) * (pairMagnitude2542 phaseVal : ℝ)
            * (pairMagnitude2542 polyInt : ℝ) ≤ assemblyCharge)
    (hres : ((ampVal + ampRad : ℚ) : ℝ)
        * (2 * (Real.exp eE * ((RU / deficitSq : ℚ) : ℝ)
            * (2 * halfWidth ^ 2))) ≤ resCharge) :
    complexL12660 (ampCenterComplex2662 ampArg * rotTrue2662 phaseArg
        * (∫ u in (-halfWidth)..halfWidth, Complex.exp (phase u - phase 0))
      - (ampVal : ℂ) * (embedPair2542 phaseVal * embedPair2542 polyInt))
    ≤ assemblyCharge + resCharge := by
  -- pins at the real level
  have hamppos : (0 : ℝ) < Real.exp ampArg := Real.exp_pos _
  obtain ⟨_, hamphi⟩ := abs_le.mp hamp
  have hcastadd : ((ampVal + ampRad : ℚ) : ℝ)
      = (ampVal : ℝ) + (ampRad : ℝ) := Rat.cast_add _ _
  have hampub : Real.exp ampArg ≤ ((ampVal + ampRad : ℚ) : ℝ) := by linarith
  -- nonnegativity of every rational atom
  have harQ : (0 : ℚ) ≤ ampRad := hrad
  have havQ : (0 : ℚ) ≤ ampVal := haval
  have havarQ : (0 : ℚ) ≤ ampVal + ampRad := by linarith
  have hprQ : (0 : ℚ) ≤ phaseRad := hphR
  have hpvQ : (0 : ℚ) ≤ pairMagnitude2542 phaseVal :=
    pairMagnitude2542_nonneg2662 phaseVal
  have himQ : (0 : ℚ) ≤ pairMagnitude2542 polyInt :=
    pairMagnitude2542_nonneg2662 polyInt
  -- rotation coordinates and norm
  have hrotre : (rotTrue2662 phaseArg).re = Real.cos phaseArg :=
    rotTrue2662_re phaseArg
  have hrotim : (rotTrue2662 phaseArg).im = Real.sin phaseArg :=
    rotTrue2662_im phaseArg
  have hrotnorm : ‖rotTrue2662 phaseArg‖ = 1 := rotTrue2662_norm phaseArg
  -- L1 of (rotation - embedded phase center) is at most 2 radii
  have hcoord : complexL12660 (rotTrue2662 phaseArg
        - embedPair2542 phaseVal)
      ≤ (2 : ℝ) * (phaseRad : ℝ) := by
    simp only [complexL12660, Complex.sub_re, Complex.sub_im, embedPair2542]
    rw [hrotre, hrotim]
    have h1 := hcos
    have h2 := hsin
    linarith
  -- the integral split
  have hadd : (∫ u in (-halfWidth)..halfWidth,
        (Complex.exp (phase u - phase 0)
          - complexPolyEval2647 polynomial u)
        + complexPolyEval2647 polynomial u)
      = (∫ u in (-halfWidth)..halfWidth,
          Complex.exp (phase u - phase 0)
            - complexPolyEval2647 polynomial u)
        + (∫ u in (-halfWidth)..halfWidth,
          complexPolyEval2647 polynomial u) :=
    intervalIntegral.integral_add hEint hPint
  have hfun : (∫ u in (-halfWidth)..halfWidth,
        Complex.exp (phase u - phase 0))
      = (∫ u in (-halfWidth)..halfWidth,
          (Complex.exp (phase u - phase 0)
            - complexPolyEval2647 polynomial u)
          + complexPolyEval2647 polynomial u) := by
    congr 1
    funext u
    ring
  have hsplit : (∫ u in (-halfWidth)..halfWidth,
        Complex.exp (phase u - phase 0))
      = (∫ u in (-halfWidth)..halfWidth,
          Complex.exp (phase u - phase 0)
            - complexPolyEval2647 polynomial u)
        + embedPair2542 polyInt := by
    rw [← hpolyInt, ← hadd, hfun]
  -- piece 1: the residual contribution
  have hp1 : complexL12660 (ampCenterComplex2662 ampArg * rotTrue2662 phaseArg
        * (∫ u in (-halfWidth)..halfWidth,
            Complex.exp (phase u - phase 0)
              - complexPolyEval2647 polynomial u))
      ≤ ((ampVal + ampRad : ℚ) : ℝ)
          * (2 * (Real.exp eE * ((RU / deficitSq : ℚ) : ℝ)
              * (2 * halfWidth ^ 2))) := by
    calc complexL12660 (ampCenterComplex2662 ampArg * rotTrue2662 phaseArg
            * (∫ u in (-halfWidth)..halfWidth,
                Complex.exp (phase u - phase 0)
                  - complexPolyEval2647 polynomial u))
        = Real.exp ampArg * complexL12660 (rotTrue2662 phaseArg
            * (∫ u in (-halfWidth)..halfWidth,
                Complex.exp (phase u - phase 0)
                  - complexPolyEval2647 polynomial u)) := by
          rw [mul_assoc, complexL1_real_mul2660 (ampCenterComplex2662 ampArg)
            (rotTrue2662 phaseArg * (∫ u in (-halfWidth)..halfWidth,
                Complex.exp (phase u - phase 0)
                  - complexPolyEval2647 polynomial u))
            (ampCenterComplex2662_im ampArg)]
          simp only [ampCenterComplex2662_re]
          rw [abs_of_pos hamppos]
      _ ≤ Real.exp ampArg * (2 * ‖rotTrue2662 phaseArg
            * (∫ u in (-halfWidth)..halfWidth,
                Complex.exp (phase u - phase 0)
                  - complexPolyEval2647 polynomial u)‖) :=
          mul_le_mul_of_nonneg_left (complexL1_le_two_norm2660 _)
            (le_of_lt hamppos)
      _ ≤ ((ampVal + ampRad : ℚ) : ℝ) * (2 * ‖rotTrue2662 phaseArg
            * (∫ u in (-halfWidth)..halfWidth,
                Complex.exp (phase u - phase 0)
                  - complexPolyEval2647 polynomial u)‖) :=
          mul_le_mul_of_nonneg_right hampub (by positivity)
      _ = ((ampVal + ampRad : ℚ) : ℝ)
            * (2 * ((1 : ℝ) * ‖(∫ u in (-halfWidth)..halfWidth,
                Complex.exp (phase u - phase 0)
                  - complexPolyEval2647 polynomial u)‖)) := by
          rw [Complex.norm_mul, hrotnorm]
      _ ≤ ((ampVal + ampRad : ℚ) : ℝ)
            * (2 * (Real.exp eE * ((RU / deficitSq : ℚ) : ℝ)
                * (2 * halfWidth ^ 2))) :=
          mul_le_mul_of_nonneg_left (by linarith [hE])
            (Rat.cast_nonneg.2 havarQ)
  -- piece 2: the center-product contribution
  have hp2 : complexL12660 ((ampCenterComplex2662 ampArg
        * rotTrue2662 phaseArg
        - (ampVal : ℂ) * embedPair2542 phaseVal)
      * embedPair2542 polyInt)
      ≤ ((ampVal + ampRad : ℚ) : ℝ) * (2 : ℝ)
          * (phaseRad : ℝ)
          * (pairMagnitude2542 polyInt : ℝ)
        + (ampRad : ℝ) * (pairMagnitude2542 phaseVal : ℝ)
          * (pairMagnitude2542 polyInt : ℝ) := by
    have hiMnn : (0 : ℝ) ≤ (pairMagnitude2542 polyInt : ℝ) :=
      Rat.cast_nonneg.2 himQ
    have hD : complexL12660 (ampCenterComplex2662 ampArg * rotTrue2662 phaseArg
          - (ampVal : ℂ) * embedPair2542 phaseVal)
        ≤ ((ampVal + ampRad : ℚ) : ℝ)
            * ((2 : ℝ) * (phaseRad : ℝ))
          + (ampRad : ℝ) * (pairMagnitude2542 phaseVal : ℝ) := by
      have hsplitD : ampCenterComplex2662 ampArg * rotTrue2662 phaseArg
            - (ampVal : ℂ) * embedPair2542 phaseVal
          = ampCenterComplex2662 ampArg
              * (rotTrue2662 phaseArg - embedPair2542 phaseVal)
            + (ampCenterComplex2662 ampArg - (ampVal : ℂ))
              * embedPair2542 phaseVal := by ring
      have hA : complexL12660 (ampCenterComplex2662 ampArg
            * (rotTrue2662 phaseArg - embedPair2542 phaseVal))
          ≤ ((ampVal + ampRad : ℚ) : ℝ)
              * ((2 : ℝ) * (phaseRad : ℝ)) := by
        calc complexL12660 (ampCenterComplex2662 ampArg
                * (rotTrue2662 phaseArg - embedPair2542 phaseVal))
            = Real.exp ampArg
                * complexL12660 (rotTrue2662 phaseArg
                  - embedPair2542 phaseVal) := by
              rw [complexL1_real_mul2660 (ampCenterComplex2662 ampArg)
                (rotTrue2662 phaseArg - embedPair2542 phaseVal)
                (ampCenterComplex2662_im ampArg)]
              simp only [ampCenterComplex2662_re]
              rw [abs_of_pos hamppos]
          _ ≤ Real.exp ampArg * ((2 : ℝ) * (phaseRad : ℝ)) :=
              mul_le_mul_of_nonneg_left hcoord (le_of_lt hamppos)
          _ ≤ ((ampVal + ampRad : ℚ) : ℝ)
                * ((2 : ℝ) * (phaseRad : ℝ)) :=
              mul_le_mul_of_nonneg_right hampub (by positivity)
      have hB : complexL12660 ((ampCenterComplex2662 ampArg
            - (ampVal : ℂ)) * embedPair2542 phaseVal)
          ≤ (ampRad : ℝ) * (pairMagnitude2542 phaseVal : ℝ) := by
        have hz0 : (ampCenterComplex2662 ampArg
            - (ampVal : ℂ)).im = 0 := by
          rw [Complex.sub_im, ampCenterComplex2662_im]
          simp
        calc complexL12660 ((ampCenterComplex2662 ampArg
                - (ampVal : ℂ)) * embedPair2542 phaseVal)
            = |(ampCenterComplex2662 ampArg
                - (ampVal : ℂ)).re|
                * complexL12660 (embedPair2542 phaseVal) :=
              complexL1_real_mul2660 _ _ hz0
          _ = |Real.exp ampArg - (ampVal : ℝ)|
                * complexL12660 (embedPair2542 phaseVal) := by
              simp only [Complex.sub_re, ampCenterComplex2662_re,
                Complex.ratCast_re]
          _ ≤ (ampRad : ℝ)
                * complexL12660 (embedPair2542 phaseVal) :=
              mul_le_mul_of_nonneg_right hamp
                (by simp only [complexL12660]; positivity)
          _ = (ampRad : ℝ) * (pairMagnitude2542 phaseVal : ℝ) := by
              rw [complexL1_embedPair2660]
      calc complexL12660 (ampCenterComplex2662 ampArg * rotTrue2662 phaseArg
            - (ampVal : ℂ) * embedPair2542 phaseVal)
          = complexL12660 (ampCenterComplex2662 ampArg
                * (rotTrue2662 phaseArg - embedPair2542 phaseVal)
              + (ampCenterComplex2662 ampArg - (ampVal : ℂ))
                * embedPair2542 phaseVal) := by rw [hsplitD]
        _ ≤ complexL12660 (ampCenterComplex2662 ampArg
                * (rotTrue2662 phaseArg - embedPair2542 phaseVal))
            + complexL12660 ((ampCenterComplex2662 ampArg
              - (ampVal : ℂ)) * embedPair2542 phaseVal) :=
          complexL1_add_le2660 _ _
        _ ≤ ((ampVal + ampRad : ℚ) : ℝ)
              * ((2 : ℝ) * (phaseRad : ℝ))
            + (ampRad : ℝ)
              * (pairMagnitude2542 phaseVal : ℝ) := add_le_add hA hB
    calc complexL12660 ((ampCenterComplex2662 ampArg * rotTrue2662 phaseArg
            - (ampVal : ℂ) * embedPair2542 phaseVal)
          * embedPair2542 polyInt)
        ≤ complexL12660 (ampCenterComplex2662 ampArg * rotTrue2662 phaseArg
            - (ampVal : ℂ) * embedPair2542 phaseVal)
          * complexL12660 (embedPair2542 polyInt) :=
          complexL1_mul_le2660 _ _
      _ = complexL12660 (ampCenterComplex2662 ampArg * rotTrue2662 phaseArg
            - (ampVal : ℂ) * embedPair2542 phaseVal)
          * (pairMagnitude2542 polyInt : ℝ) := by
          rw [complexL1_embedPair2660]
      _ ≤ (((ampVal + ampRad : ℚ) : ℝ)
              * ((2 : ℝ) * (phaseRad : ℝ))
            + (ampRad : ℝ)
              * (pairMagnitude2542 phaseVal : ℝ))
          * (pairMagnitude2542 polyInt : ℝ) :=
          mul_le_mul_of_nonneg_right hD hiMnn
      _ = ((ampVal + ampRad : ℚ) : ℝ) * (2 : ℝ)
            * (phaseRad : ℝ)
            * (pairMagnitude2542 polyInt : ℝ)
          + (ampRad : ℝ) * (pairMagnitude2542 phaseVal : ℝ)
            * (pairMagnitude2542 polyInt : ℝ) := by ring
  -- final decomposition
  have hdecomp : ampCenterComplex2662 ampArg * rotTrue2662 phaseArg
        * ((∫ u in (-halfWidth)..halfWidth,
            Complex.exp (phase u - phase 0)
              - complexPolyEval2647 polynomial u)
          + embedPair2542 polyInt)
      - (ampVal : ℂ)
        * (embedPair2542 phaseVal * embedPair2542 polyInt)
      = ampCenterComplex2662 ampArg * rotTrue2662 phaseArg
        * (∫ u in (-halfWidth)..halfWidth,
            Complex.exp (phase u - phase 0)
              - complexPolyEval2647 polynomial u)
        + (ampCenterComplex2662 ampArg * rotTrue2662 phaseArg
            - (ampVal : ℂ) * embedPair2542 phaseVal)
          * embedPair2542 polyInt := by
    ring
  rw [hsplit, hdecomp]
  have hstep : complexL12660 (ampCenterComplex2662 ampArg * rotTrue2662 phaseArg
        * (∫ u in (-halfWidth)..halfWidth,
            Complex.exp (phase u - phase 0)
              - complexPolyEval2647 polynomial u)
        + (ampCenterComplex2662 ampArg * rotTrue2662 phaseArg
            - (ampVal : ℂ) * embedPair2542 phaseVal)
          * embedPair2542 polyInt)
      ≤ complexL12660 (ampCenterComplex2662 ampArg * rotTrue2662 phaseArg
          * (∫ u in (-halfWidth)..halfWidth,
              Complex.exp (phase u - phase 0)
                - complexPolyEval2647 polynomial u))
        + complexL12660 ((ampCenterComplex2662 ampArg * rotTrue2662 phaseArg
            - (ampVal : ℂ) * embedPair2542 phaseVal)
          * embedPair2542 polyInt) :=
    complexL1_add_le2660 _ _
  linarith [hstep, hp1, hp2, hac, hres]

#print axioms ampCenterComplex2662_im
#print axioms ampCenterComplex2662_re
#print axioms rotTrue2662_re
#print axioms rotTrue2662_im
#print axioms rotTrue2662_norm
#print axioms pairMagnitude2542_nonneg2662
#print axioms exp_le_three_pow2662
#print axioms exp_le_three_pow_rat2662
#print axioms panelL1Ball2662

end ConnesWeilRH.Dev
