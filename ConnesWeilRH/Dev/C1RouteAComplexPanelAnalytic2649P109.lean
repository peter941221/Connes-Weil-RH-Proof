import ConnesWeilRH.Dev.C1RouteAComplexPanelTable2648P109

namespace ConnesWeilRH.Dev

open Set

-- The panel-local phase/derivative lines exceed the 100-character style
-- limit by construction.
set_option linter.style.longLine false

/-!
# Complex analytic containment of the pilot panel 109 (record 2649)

Brick 4 of the record-2624 GO route: the analytic layer consuming the
record-2648 data tables through the record-2647 generic stability
theorem. The panel phase is

    phase(u) = (beta + i*psi) * u - 30 / (1 - (center + u)^2),

whose derivative `beta + i*psi - 60*(center + u)/D(u)` satisfies the
exact quotient identity behind the residual replay:

    D(u) * (P'(u) - phase'(u) * P(u)) = residual(u),  D(u) = (1 - (center + u)^2)^2,

so `|P' - phase' * P| <= residualUpper / (391/400)^2` on the panel.
The real part of the phase varies by at most 1/10 on the panel (the
imaginary slope `i*psi` never enters the real part), which turns the
record-2647 stability into the pointwise bound

    ||exp(phase(u) - phase(0)) - P(u)|| <= exp(1/5) * residualUpper/(391/400)^2 * |u|,

integrated to the panel-local analytic containment certificate

    ||integral exp(phase(u) - phase(0))||
       <= |integral of P| + exp(1/5) * residualUpper/(391/400)^2 * 2h^2

with the exact rational `integral of P` replayed from the record-2648
tables. Scope: pilot panel 109 only. No off-diagonal claim, no entry
containment, no Producer GO, no SourceRH, no RH.
-/

def complexPanelHalfWidth2649 : ℚ := 1 / 200

def complexPanelHalfWidthReal2649 : ℝ := (complexPanelHalfWidth2649 : ℝ)

noncomputable def complexPanelDeficitValue2649 (position : ℝ) : ℝ :=
  1 - ((complexPanelCenter2648P109 : ℝ) + position) ^ 2

noncomputable def complexPanelBetaComplex2649 : ℂ :=
  ((complexPanelBeta2648P109 : ℝ) : ℂ) + ((complexPanelPsi2648P109 : ℝ) : ℂ) * Complex.I

noncomputable def complexPanelPhase2649 (position : ℝ) : ℂ :=
  complexPanelBetaComplex2649 * (position : ℂ)
    + Complex.ofReal ((-30 : ℝ) / complexPanelDeficitValue2649 position)

noncomputable def complexPanelPhaseDerivative2649 (position : ℝ) : ℂ :=
  complexPanelBetaComplex2649
    + Complex.ofReal ((-60 : ℝ) * ((complexPanelCenter2648P109 : ℝ) + position)
        / complexPanelDeficitValue2649 position ^ 2)

theorem complexPanelHalfWidth_nonneg2649 : 0 ≤ complexPanelHalfWidth2649 := by
  norm_num [complexPanelHalfWidth2649]

theorem complexPanelHalfWidthReal_nonneg2649 : 0 ≤ complexPanelHalfWidthReal2649 := by
  norm_num [complexPanelHalfWidthReal2649, complexPanelHalfWidth2649]

theorem complexPanelBeta_abs_le2649 : |complexPanelBeta2648P109| ≤ 8 := by
  decide +kernel

theorem complexPanelAbsInside2649 (position : ℝ) (hinside : position ∈ Icc
    (-complexPanelHalfWidthReal2649) complexPanelHalfWidthReal2649) :
    |position| ≤ (1 / 200 : ℝ) := by
  have h := abs_le.mpr ⟨hinside.1, hinside.2⟩
  push_cast at h
  exact h.trans (by norm_num [complexPanelHalfWidthReal2649, complexPanelHalfWidth2649])

theorem complexPanelDeficit_lower2649 (position : ℝ) (hinside : position ∈ Icc
    (-complexPanelHalfWidthReal2649) complexPanelHalfWidthReal2649) :
    ((391 : ℝ) / 400) ≤ complexPanelDeficitValue2649 position := by
  have hcenter : ((complexPanelCenter2648P109 : ℝ)) = (29 / 200 : ℝ) := by
    norm_num [complexPanelCenter2648P109]
  have habspos : |position| ≤ (1 / 200 : ℝ) := complexPanelAbsInside2649 position hinside
  have hcabs : |((complexPanelCenter2648P109 : ℝ)) + position| ≤ (3 / 20 : ℝ) := by
    rw [hcenter]
    calc |(29 / 200 : ℝ) + position| ≤ |(29 / 200 : ℝ)| + |position| := abs_add_le _ _
      _ ≤ (3 / 20 : ℝ) := by
            rw [abs_of_pos (by norm_num : (0 : ℝ) < 29 / 200)]
            linarith
  obtain ⟨q1, q2⟩ := abs_le.mp hcabs
  have hsq : ((complexPanelCenter2648P109 : ℝ) + position) ^ 2 ≤ (3 / 20 : ℝ) ^ 2 := by
    nlinarith
  dsimp only [complexPanelDeficitValue2649]
  linarith

theorem complexPanelDeficit_eval2649 (position : ℝ) :
    complexPolyEval2647 complexPanelDeficit2648P109 position
      = ((complexPanelDeficitValue2649 position : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [complexPolyEval2647, complexPanelDeficit2648P109, embedPair2542,
      complexPanelDeficitValue2649, complexPanelCenter2648P109, Complex.add_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re,
      Complex.zero_im]
    push_cast
    ring
  · simp only [complexPolyEval2647, complexPanelDeficit2648P109, embedPair2542,
      complexPanelDeficitValue2649, complexPanelCenter2648P109, Complex.add_im,
      Complex.mul_im, Complex.ofReal_im, Complex.zero_im]
    ring

theorem complexPanelNumerator_eval2649 (position : ℝ) :
    complexPolyEval2647 complexPanelNumerator2648P109 position
      = complexPanelBetaComplex2649
          * (((complexPanelDeficitValue2649 position : ℝ) : ℂ) ^ 2)
        - Complex.ofReal ((60 : ℝ) * ((complexPanelCenter2648P109 : ℝ) + position)) := by
  apply Complex.ext
  -- pow_two first: simp cannot push .re/.im through a complex power, so the
  -- square of the deficit cast must become a product before mul_re applies
  · simp only [complexPolyEval2647, complexPanelNumerator2648P109, embedPair2542,
      complexPanelDeficitValue2649, complexPanelBetaComplex2649,
      complexPanelCenter2648P109, complexPanelBeta2648P109, complexPanelPsi2648P109,
      pow_two, Complex.sub_re, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_re, Complex.zero_im, Complex.I_re, Complex.I_im]
    push_cast
    ring
  · simp only [complexPolyEval2647, complexPanelNumerator2648P109, embedPair2542,
      complexPanelDeficitValue2649, complexPanelBetaComplex2649,
      complexPanelCenter2648P109, complexPanelBeta2648P109, complexPanelPsi2648P109,
      pow_two, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_re, Complex.zero_im, Complex.I_re, Complex.I_im]
    push_cast
    ring

theorem complexPanelPhaseReal_hasDerivAt2649 (position : ℝ)
    (hdeficit : complexPanelDeficitValue2649 position ≠ 0) :
    HasDerivAt (fun x : ℝ => (-30 : ℝ) / complexPanelDeficitValue2649 x)
      (((-60 : ℝ) * ((complexPanelCenter2648P109 : ℝ) + position)
        / complexPanelDeficitValue2649 position ^ 2)) position := by
  -- rebuild the quotient rule on plain lambdas: the raw .div output carries
  -- Pi-form atoms ((fun x => c) + id) position that ring cannot equate with
  -- c + position, so each layer is restated through simpa in closed form
  have hinner : HasDerivAt (fun x : ℝ => ((complexPanelCenter2648P109 : ℝ) + x))
      (1 : ℝ) position := by
    simpa using (hasDerivAt_const position (complexPanelCenter2648P109 : ℝ)).add
      (hasDerivAt_id position)
  have hdenominator : HasDerivAt
      (fun x : ℝ => (1 : ℝ) - ((complexPanelCenter2648P109 : ℝ) + x) ^ 2)
      ((-2 : ℝ) * ((complexPanelCenter2648P109 : ℝ) + position)) position := by
    simpa using (hasDerivAt_const position (1 : ℝ)).sub (hinner.pow 2)
  have hquotient : HasDerivAt
      (fun x : ℝ => (-30 : ℝ) / complexPanelDeficitValue2649 x)
      (((-30 : ℝ) * -(-2 * ((complexPanelCenter2648P109 : ℝ) + position))) /
        complexPanelDeficitValue2649 position ^ 2) position := by
    simpa using (hasDerivAt_const position (-30 : ℝ)).div hdenominator hdeficit
  convert hquotient using 1
  ring

theorem complexPanelPhase_hasDerivAt2649 (position : ℝ)
    (hdeficit : complexPanelDeficitValue2649 position ≠ 0) :
    HasDerivAt complexPanelPhase2649 (complexPanelPhaseDerivative2649 position) position := by
  have hreal := complexPanelPhaseReal_hasDerivAt2649 position hdeficit
  have hrealC := hreal.ofReal_comp
  have hid : HasDerivAt (fun y : ℝ => ((y : ℝ) : ℂ)) 1 position :=
    (hasDerivAt_id position).ofReal_comp
  have hlin : HasDerivAt (fun y : ℝ => complexPanelBetaComplex2649 * ((y : ℝ) : ℂ))
      (complexPanelBetaComplex2649 * 1) position := HasDerivAt.const_mul _ hid
  have hsum := hlin.add hrealC
  convert hsum using 1
  · dsimp only [complexPanelPhaseDerivative2649]
    ring

set_option maxHeartbeats 2000000 in
-- the 57-slot zero-scaled rational fold needs the 2621 heartbeat ceiling
theorem complexPanelPolynomial_zero2649 :
    complexPolyEval2647 complexPanelPolynomial2648P109 0 = 1 := by
  rw [← Rat.cast_zero (α := ℝ), complexPolyEval2647_cast]
  have hzero : complexPolyEvalRat2647 0 complexPanelPolynomial2648P109 = (1, 0) := by
    decide +kernel
  rw [hzero, embedPair_one2542]

theorem complexPanelStabilityResidual2649 (position : ℝ) (hinside : position ∈ Icc
    (-complexPanelHalfWidthReal2649) complexPanelHalfWidthReal2649) :
    ‖complexPolyEval2647 (complexPolyDerivative2647 complexPanelPolynomial2648P109) position
        - complexPanelPhaseDerivative2649 position
            * complexPolyEval2647 complexPanelPolynomial2648P109 position‖
      ≤ ((complexPanelResidualUpper2648P109 / (((391 : ℚ) / 400) ^ 2) : ℚ) : ℝ) := by
  have hlower := complexPanelDeficit_lower2649 position hinside
  have habs := complexPanelAbsInside2649 position hinside
  have hpos : (0 : ℝ) < complexPanelDeficitValue2649 position := by linarith
  have hneC : (((complexPanelDeficitValue2649 position : ℝ) : ℂ)) ^ 2 ≠ 0 := by
    have hd : ((complexPanelDeficitValue2649 position : ℝ) : ℂ) ≠ 0 := by
      simp only [Complex.ofReal_ne_zero]
      exact ne_of_gt hpos
    exact pow_ne_zero 2 hd
  -- the list-level residual replay, evaluated at the panel position
  have hom := congrArg (fun L => complexPolyEval2647 L position)
    complexPanelResidual_replay2648P109
  simp only [complexPolyEval2647_add, complexPolyEval2647_mul, complexPolyEval2647_scale,
    complexPanelDeficit_eval2649] at hom
  have hneg1 : embedPair2542 (-1, 0) = (-1 : ℂ) := by
    apply Complex.ext <;> simp [embedPair2542]
  rw [hneg1, complexPanelNumerator_eval2649] at hom
  push_cast at hom
  -- phaseDerivative * D^2 = betaComplex * D^2 - 60*(center + position)
  have hcanc : Complex.ofReal ((-60 : ℝ) * ((complexPanelCenter2648P109 : ℝ) + position)
        / complexPanelDeficitValue2649 position ^ 2)
      * (((complexPanelDeficitValue2649 position : ℝ) : ℂ) ^ 2)
      = Complex.ofReal ((-60 : ℝ) * ((complexPanelCenter2648P109 : ℝ) + position)) := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]
    congr 1
    field_simp
  have hrel : complexPanelPhaseDerivative2649 position
        * (((complexPanelDeficitValue2649 position : ℝ) : ℂ) ^ 2)
      = complexPanelBetaComplex2649
          * (((complexPanelDeficitValue2649 position : ℝ) : ℂ) ^ 2)
        - Complex.ofReal ((60 : ℝ) * ((complexPanelCenter2648P109 : ℝ) + position)) := by
    dsimp only [complexPanelPhaseDerivative2649]
    rw [add_mul, hcanc]
    push_cast
    ring
  push_cast at hrel
  -- D^2 * (P' - phaseDerivative * P) = residual
  have hkey : (complexPolyEval2647 (complexPolyDerivative2647 complexPanelPolynomial2648P109) position
        - complexPanelPhaseDerivative2649 position
            * complexPolyEval2647 complexPanelPolynomial2648P109 position)
        * (((complexPanelDeficitValue2649 position : ℝ) : ℂ) ^ 2)
      = complexPolyEval2647 complexPanelResidual2648P109 position := by
    -- linear_combination's module normalform does not reconcile the atom
    -- spellings between hom and the goal; term-level algebra does
    rw [← pow_two] at hom
    rw [sub_mul, mul_right_comm, hrel]
    rw [← hom]
    ring
  have hsplit : complexPolyEval2647 (complexPolyDerivative2647 complexPanelPolynomial2648P109) position
        - complexPanelPhaseDerivative2649 position
            * complexPolyEval2647 complexPanelPolynomial2648P109 position
      = complexPolyEval2647 complexPanelResidual2648P109 position
          / (((complexPanelDeficitValue2649 position : ℝ) : ℂ) ^ 2) := by
    rw [eq_div_iff hneC]
    exact hkey
  have habsQ : |position| ≤ ((complexPanelHalfWidth2649 : ℚ) : ℝ) := by
    norm_num [complexPanelHalfWidth2649]
    exact habs
  rw [hsplit, norm_div]
  have habsBound : ‖complexPolyEval2647 complexPanelResidual2648P109 position‖
      ≤ ((complexPanelResidualUpper2648P109 : ℚ) : ℝ) := by
    rw [← complexPanelResidualUpper_replay2648P109]
    exact complexPolyEval2647_abs_le complexPanelResidual2648P109
      complexPanelHalfWidth2649 complexPanelHalfWidth_nonneg2649 position habsQ
  -- div_le_div_iff_left is the ordered-GROUP lemma (Group ℝ does not exist);
  -- the field version needs the numerator strictly positive
  have hRUpos : (0 : ℝ) < ((complexPanelResidualUpper2648P109 : ℚ) : ℝ) :=
    Rat.cast_pos.mpr (by norm_num [complexPanelResidualUpper2648P109])
  calc ‖complexPolyEval2647 complexPanelResidual2648P109 position‖
        / ‖(((complexPanelDeficitValue2649 position : ℝ) : ℂ)) ^ 2‖
      ≤ ((complexPanelResidualUpper2648P109 : ℚ) : ℝ)
          / complexPanelDeficitValue2649 position ^ 2 := by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
        exact (div_le_div_iff_of_pos_right (pow_pos hpos 2)).mpr habsBound
    -- the bare real-literal form matches hlower; the cast form of the public
    -- claim is folded back in the final step by norm_num over the table data
    _ ≤ ((complexPanelResidualUpper2648P109 : ℚ) : ℝ)
          / ((391 / 400 : ℝ)) ^ 2 := by
        exact (div_le_div_iff_of_pos_left hRUpos (pow_pos hpos 2)
          (pow_pos (by norm_num : (0 : ℝ) < (391 / 400 : ℝ)) 2)).mpr
          (pow_le_pow_left₀ (by norm_num) hlower 2)
    _ = ((complexPanelResidualUpper2648P109 / (((391 : ℚ) / 400) ^ 2) : ℚ) : ℝ) := by
        norm_num [complexPanelResidualUpper2648P109]

/-! ## Real-part variation of the panel phase -/

theorem complexPanelReVariation2649 (position : ℝ) (hinside : position ∈ Icc
    (-complexPanelHalfWidthReal2649) complexPanelHalfWidthReal2649) :
    |(complexPanelPhase2649 position - complexPanelPhase2649 0).re| ≤ (1 / 10 : ℝ) := by
  have hcast29 : ((complexPanelCenter2648P109 : ℝ)) = (29 / 200 : ℝ) := by
    norm_num [complexPanelCenter2648P109]
  have habs : |position| ≤ (1 / 200 : ℝ) := complexPanelAbsInside2649 position hinside
  obtain ⟨hlo, hhi⟩ := abs_le.mp habs
  have hlower := complexPanelDeficit_lower2649 position hinside
  have hpos : (0 : ℝ) < complexPanelDeficitValue2649 position := by linarith
  have hapos : (0 : ℝ) < 1 - (29 / 200 : ℝ) ^ 2 := by norm_num
  -- |30 * (1/a - 1/d)| <= 1/20 with a = 1 - c^2, d = 1 - (c + position)^2;
  -- the numerator identity is 30*(d - a)/(a*d), NOT 30*(a - d)/(a*d)
  have hR : |(-30 : ℝ) / complexPanelDeficitValue2649 position
      + 30 / (1 - (29 / 200 : ℝ) ^ 2)| ≤ (1 / 20 : ℝ) := by
    have hexpr : (-30 : ℝ) / complexPanelDeficitValue2649 position
        + 30 / (1 - (29 / 200 : ℝ) ^ 2)
        = 30 * (complexPanelDeficitValue2649 position - (1 - (29 / 200 : ℝ) ^ 2))
          / ((1 - (29 / 200 : ℝ) ^ 2) * complexPanelDeficitValue2649 position) := by
      field_simp
      ring
    have hdelta : complexPanelDeficitValue2649 position - (1 - (29 / 200 : ℝ) ^ 2)
        = -((2 * (29 / 200 : ℝ) + position) * position) := by
      dsimp only [complexPanelDeficitValue2649]
      rw [hcast29]
      ring
    have hprod : (0 : ℝ) < (1 - (29 / 200 : ℝ) ^ 2)
        * complexPanelDeficitValue2649 position := mul_pos hapos hpos
    have hnum : |(2 * (29 / 200 : ℝ) + position) * position| ≤ (59 / 40000 : ℝ) := by
      rw [abs_mul]
      have hsign : |2 * (29 / 200 : ℝ) + position| = 2 * (29 / 200 : ℝ) + position :=
        abs_of_nonneg (by linarith)
      rw [hsign]
      calc (2 * (29 / 200 : ℝ) + position) * |position|
          ≤ (59 / 200 : ℝ) * |position| :=
            mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg position)
        _ ≤ (59 / 200 : ℝ) * (1 / 200 : ℝ) :=
            mul_le_mul_of_nonneg_left habs (by norm_num : (0 : ℝ) ≤ 59 / 200)
        _ ≤ (59 / 40000 : ℝ) := by norm_num
    have hconst : (30 : ℝ) * (59 / 40000)
        ≤ (1 / 20) * ((1 - (29 / 200 : ℝ) ^ 2) * (391 / 400)) := by norm_num
    rw [hexpr, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 30),
      abs_of_pos hprod, hdelta, abs_neg, div_le_iff₀ hprod]
    refine le_trans (mul_le_mul_of_nonneg_left hnum (by norm_num)) ?_
    refine le_trans hconst ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlower
      (by norm_num : (0 : ℝ) ≤ 1 - (29 / 200 : ℝ) ^ 2)) (by norm_num : (0 : ℝ) ≤ 1 / 20)
  -- |beta * position| <= 1/25
  have hbeta8 : |((complexPanelBeta2648P109 : ℝ))| ≤ (8 : ℝ) := by
    exact_mod_cast complexPanelBeta_abs_le2649
  have hbeta : |((complexPanelBeta2648P109 : ℝ)) * position| ≤ (1 / 25 : ℝ) := by
    calc |((complexPanelBeta2648P109 : ℝ)) * position|
        = |((complexPanelBeta2648P109 : ℝ))| * |position| := abs_mul _ _
      _ ≤ (8 : ℝ) * |position| :=
          mul_le_mul_of_nonneg_right hbeta8 (abs_nonneg position)
      _ ≤ (8 : ℝ) * (1 / 200 : ℝ) :=
          mul_le_mul_of_nonneg_left habs (by norm_num : (0 : ℝ) ≤ 8)
      _ ≤ (1 / 25 : ℝ) := by norm_num
  -- the real part of the phase difference; the position-independent
  -- beta*0 term is folded away inside the split so the tail keeps hR's shape
  have htermPos : (complexPanelBetaComplex2649 * ((position : ℝ) : ℂ)).re
      = ((complexPanelBeta2648P109 : ℝ)) * position := by
    dsimp only [complexPanelBetaComplex2649]
    simp [Complex.mul_re]
  have hterm0 : (complexPanelBetaComplex2649 * ((0 : ℝ) : ℂ)).re = 0 := by
    dsimp only [complexPanelBetaComplex2649]
    simp
  have hsplit : (complexPanelPhase2649 position - complexPanelPhase2649 0).re
      = (complexPanelBetaComplex2649 * ((position : ℝ) : ℂ)).re
        + (Complex.ofReal ((-30 : ℝ) / complexPanelDeficitValue2649 position)).re
        - (Complex.ofReal ((-30 : ℝ) / complexPanelDeficitValue2649 0)).re := by
    dsimp only [complexPanelPhase2649]
    simp only [Complex.sub_re, Complex.add_re, hterm0, zero_add]
  have hofRe : ∀ x : ℝ, (Complex.ofReal x).re = x := fun x => by simp
  have hdef0 : complexPanelDeficitValue2649 0 = 1 - (29 / 200 : ℝ) ^ 2 := by
    dsimp only [complexPanelDeficitValue2649]
    rw [hcast29]
    ring
  rw [hsplit, htermPos, hofRe, hofRe, hdef0]
  -- fold the constant tail into hR's spelling: A + B - ((-30)/a) = A + ((-30)/a + 30/a)
  have hfold : ((complexPanelBeta2648P109 : ℝ)) * position
        + (-30 : ℝ) / complexPanelDeficitValue2649 position
        - (-30 : ℝ) / (1 - (29 / 200 : ℝ) ^ 2)
      = ((complexPanelBeta2648P109 : ℝ)) * position
        + ((-30 : ℝ) / complexPanelDeficitValue2649 position
          + 30 / (1 - (29 / 200 : ℝ) ^ 2)) := by
    ring
  rw [hfold]
  -- a bare ring here would ring_nf the goal and desynchronize the calc frame;
  -- `calc _` pins the first step to the goal's own left-hand side
  calc _ ≤ |((complexPanelBeta2648P109 : ℝ)) * position|
        + |(-30 : ℝ) / complexPanelDeficitValue2649 position
          + 30 / (1 - (29 / 200 : ℝ) ^ 2)| := abs_add_le _ _
    _ ≤ (1 / 25 : ℝ) + (1 / 20 : ℝ) := add_le_add hbeta hR
    _ ≤ (1 / 10 : ℝ) := by norm_num

/-! ## The generic complex integral error lemma -/

theorem complexExpPolynomialIntegralError2649
    (phase phaseDerivative polynomial polynomialDerivative : ℝ → ℂ)
    (halfWidth variation residualUpper : ℝ) (hwidth : 0 ≤ halfWidth)
    (hpolynomialZero : polynomial 0 = 1)
    (hphaseDerivative : ∀ position ∈ Icc (-halfWidth) halfWidth,
      HasDerivAt phase (phaseDerivative position) position)
    (hpolynomialDerivative : ∀ position ∈ Icc (-halfWidth) halfWidth,
      HasDerivAt polynomial (polynomialDerivative position) position)
    (hreVariation : ∀ position ∈ Icc (-halfWidth) halfWidth,
      |(phase position - phase 0).re| ≤ variation)
    (hresidual : ∀ position ∈ Icc (-halfWidth) halfWidth,
      ‖polynomialDerivative position - phaseDerivative position * polynomial position‖
        ≤ residualUpper) :
    ‖(∫ position in (-halfWidth)..halfWidth,
        Complex.exp (phase position - phase 0) - polynomial position)‖
      ≤ Real.exp (2 * variation) * residualUpper * (2 * halfWidth ^ 2) := by
  have horder : -halfWidth ≤ halfWidth := by linarith
  have hzero : (0 : ℝ) ∈ Icc (-halfWidth) halfWidth := ⟨by linarith, hwidth⟩
  have hRU : (0 : ℝ) ≤ residualUpper := (norm_nonneg _).trans (hresidual 0 hzero)
  -- pointwise bound from the record-2647 stability theorem
  have hpointwise : ∀ position ∈ Set.uIoc (-halfWidth) halfWidth,
      ‖Complex.exp (phase position - phase 0) - polynomial position‖
        ≤ Real.exp (2 * variation) * residualUpper * halfWidth := by
    intro position hposition
    rw [Set.uIoc_of_le horder] at hposition
    obtain ⟨hpos1, hpos2⟩ := hposition
    have hclosed : position ∈ Icc (-halfWidth) halfWidth :=
      ⟨le_of_lt hpos1, hpos2⟩
    have habs : |position| ≤ halfWidth := abs_le.mpr ⟨le_of_lt hpos1, hpos2⟩
    have hstable := complexExpPolynomialResidualStability2647 phase phaseDerivative
      polynomial polynomialDerivative halfWidth variation residualUpper hwidth
      hpolynomialZero hphaseDerivative hpolynomialDerivative hreVariation hresidual
      position hclosed
    exact hstable.trans (mul_le_mul_of_nonneg_left habs
      (mul_nonneg (Real.exp_nonneg _) hRU))
  -- continuity and integrability
  have hphaseCont : ContinuousOn (fun coordinate => Complex.exp (phase coordinate - phase 0))
      (Icc (-halfWidth) halfWidth) := by
    intro coordinate hcoordinate
    have hsub := (hphaseDerivative coordinate hcoordinate).sub
      (hasDerivAt_const coordinate (phase 0))
    have hsub' : HasDerivAt (fun x => phase x - phase 0)
        (phaseDerivative coordinate) coordinate := by
      convert hsub using 1
      ring
    refine ((Complex.hasDerivAt_exp (phase coordinate - phase 0)).comp
      coordinate hsub').continuousAt.continuousWithinAt
  have hpolyCont : ContinuousOn polynomial (Icc (-halfWidth) halfWidth) :=
    HasDerivAt.continuousOn fun coordinate hcoordinate =>
      hpolynomialDerivative coordinate hcoordinate
  have hint : IntervalIntegrable
      (fun coordinate => Complex.exp (phase coordinate - phase 0) - polynomial coordinate)
      MeasureTheory.volume (-halfWidth) halfWidth :=
    (hphaseCont.sub hpolyCont).intervalIntegrable_of_Icc horder (μ := MeasureTheory.volume)
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const hpointwise
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ halfWidth - -halfWidth)] at hbound
  calc ‖(∫ position in (-halfWidth)..halfWidth,
        Complex.exp (phase position - phase 0) - polynomial position)‖
      ≤ Real.exp (2 * variation) * residualUpper * halfWidth
          * (halfWidth - -halfWidth) := hbound
    _ = Real.exp (2 * variation) * residualUpper * (2 * halfWidth ^ 2) := by ring

/-! ## The panel 109 instances and the certificate -/

theorem complexPanelPointwise2649 (position : ℝ) (hinside : position ∈ Icc
    (-complexPanelHalfWidthReal2649) complexPanelHalfWidthReal2649) :
    ‖Complex.exp (complexPanelPhase2649 position - complexPanelPhase2649 0)
        - complexPolyEval2647 complexPanelPolynomial2648P109 position‖
      ≤ Real.exp (1 / 5)
          * ((complexPanelResidualUpper2648P109 / (((391 : ℚ) / 400) ^ 2) : ℚ) : ℝ)
          * |position| := by
  have hphaseDeriv : ∀ coordinate ∈ Icc (-complexPanelHalfWidthReal2649)
      complexPanelHalfWidthReal2649,
      HasDerivAt complexPanelPhase2649
        (complexPanelPhaseDerivative2649 coordinate) coordinate := by
    intro coordinate hcoordinate
    refine complexPanelPhase_hasDerivAt2649 coordinate ?_
    have hlower := complexPanelDeficit_lower2649 coordinate hcoordinate
    linarith
  have hresid : ∀ coordinate ∈ Icc (-complexPanelHalfWidthReal2649)
      complexPanelHalfWidthReal2649,
      ‖complexPolyEval2647 (complexPolyDerivative2647 complexPanelPolynomial2648P109) coordinate
          - complexPanelPhaseDerivative2649 coordinate
              * complexPolyEval2647 complexPanelPolynomial2648P109 coordinate‖
        ≤ ((complexPanelResidualUpper2648P109 / (((391 : ℚ) / 400) ^ 2) : ℚ) : ℝ) :=
    complexPanelStabilityResidual2649
  have hkey := complexExpPolynomialResidualStability2647 complexPanelPhase2649
    complexPanelPhaseDerivative2649
    (complexPolyEval2647 complexPanelPolynomial2648P109)
    (complexPolyEval2647 (complexPolyDerivative2647 complexPanelPolynomial2648P109))
    complexPanelHalfWidthReal2649 (1 / 10)
    ((complexPanelResidualUpper2648P109 / (((391 : ℚ) / 400) ^ 2) : ℚ) : ℝ)
    complexPanelHalfWidthReal_nonneg2649
    complexPanelPolynomial_zero2649 hphaseDeriv
    (fun coordinate _ =>
      complexPolyEval2647_hasDerivAt complexPanelPolynomial2648P109 coordinate)
    complexPanelReVariation2649 hresid position hinside
  -- normalize hkey AND the goal together: hkey's exp argument needs the
  -- Real-numeral bridge (2*(1/10) is not syntactically 1/5) while the goal
  -- carries the quotient as a single rational cast; norm_num on both sides
  -- lands them on the same literal shape
  norm_num at hkey ⊢
  exact hkey

theorem complexPanelIntegralError2649 :
    ‖(∫ position in (-complexPanelHalfWidthReal2649)..complexPanelHalfWidthReal2649,
        Complex.exp (complexPanelPhase2649 position - complexPanelPhase2649 0)
          - complexPolyEval2647 complexPanelPolynomial2648P109 position)‖
      ≤ Real.exp (1 / 5)
          * ((complexPanelResidualUpper2648P109 / (((391 : ℚ) / 400) ^ 2) : ℚ) : ℝ)
          * (2 * complexPanelHalfWidthReal2649 ^ 2) := by
  have hphaseDeriv : ∀ coordinate ∈ Icc (-complexPanelHalfWidthReal2649)
      complexPanelHalfWidthReal2649,
      HasDerivAt complexPanelPhase2649
        (complexPanelPhaseDerivative2649 coordinate) coordinate := by
    intro coordinate hcoordinate
    refine complexPanelPhase_hasDerivAt2649 coordinate ?_
    have hlower := complexPanelDeficit_lower2649 coordinate hcoordinate
    linarith
  have hresid := complexPanelStabilityResidual2649
  have hkey := complexExpPolynomialIntegralError2649 complexPanelPhase2649
    complexPanelPhaseDerivative2649
    (complexPolyEval2647 complexPanelPolynomial2648P109)
    (complexPolyEval2647 (complexPolyDerivative2647 complexPanelPolynomial2648P109))
    complexPanelHalfWidthReal2649 (1 / 10)
    ((complexPanelResidualUpper2648P109 / (((391 : ℚ) / 400) ^ 2) : ℚ) : ℝ)
    complexPanelHalfWidthReal_nonneg2649
    complexPanelPolynomial_zero2649 hphaseDeriv
    (fun coordinate _ =>
      complexPolyEval2647_hasDerivAt complexPanelPolynomial2648P109 coordinate)
    complexPanelReVariation2649 hresid
  norm_num at hkey ⊢
  exact hkey

theorem complexPanelPolyIntegral2649 :
    (∫ position in (-complexPanelHalfWidthReal2649)..complexPanelHalfWidthReal2649,
      complexPolyEval2647 complexPanelPolynomial2648P109 position)
      = embedPair2542 complexPanelIntegral2648P109 := by
  have horder : -complexPanelHalfWidthReal2649 ≤ complexPanelHalfWidthReal2649 := by
    norm_num [complexPanelHalfWidthReal2649, complexPanelHalfWidth2649]
  have hanti : ∀ coordinate ∈ Set.uIcc (-complexPanelHalfWidthReal2649)
      complexPanelHalfWidthReal2649,
      HasDerivAt (complexPolyEval2647 complexPanelPrimitive2648P109)
        (complexPolyEval2647 complexPanelPolynomial2648P109 coordinate) coordinate := by
    intro coordinate _
    have h := complexPolyEval2647_hasDerivAt complexPanelPrimitive2648P109 coordinate
    rwa [complexPanelPrimitive_replay2648P109] at h
  have hpolyCont : ContinuousOn (complexPolyEval2647 complexPanelPolynomial2648P109)
      (Icc (-complexPanelHalfWidthReal2649) complexPanelHalfWidthReal2649) :=
    HasDerivAt.continuousOn fun coordinate _ =>
      complexPolyEval2647_hasDerivAt complexPanelPolynomial2648P109 coordinate
  have hint : IntervalIntegrable
      (complexPolyEval2647 complexPanelPolynomial2648P109) MeasureTheory.volume
      (-complexPanelHalfWidthReal2649) complexPanelHalfWidthReal2649 :=
    hpolyCont.intervalIntegrable_of_Icc horder (μ := MeasureTheory.volume)
  have hsub := intervalIntegral.integral_eq_sub_of_hasDerivAt hanti hint
  -- bridge the rational endpoint casts of the record-2648 replays
  have hcastPos : complexPolyEval2647 complexPanelPrimitive2648P109
      complexPanelHalfWidthReal2649
      = embedPair2542 (complexPolyEvalRat2647 complexPanelHalfWidth2649
        complexPanelPrimitive2648P109) := complexPolyEval2647_cast _ _
  have hcastNeg : complexPolyEval2647 complexPanelPrimitive2648P109
      (-complexPanelHalfWidthReal2649)
      = embedPair2542 (complexPolyEvalRat2647 (-complexPanelHalfWidth2649)
        complexPanelPrimitive2648P109) := by
    have h2 := complexPolyEval2647_cast complexPanelPrimitive2648P109
      (-complexPanelHalfWidth2649)
    rwa [Rat.cast_neg] at h2
  rw [hsub, hcastPos, hcastNeg]
  apply Complex.ext
  · simp only [embedPair2542, Complex.sub_re]
    norm_num [complexPanelHalfWidth2649]
    exact_mod_cast complexPanelIntegral_re2648P109
  · simp only [embedPair2542, Complex.sub_im]
    norm_num [complexPanelHalfWidth2649]
    exact_mod_cast complexPanelIntegral_im2648P109

theorem complexPanelAnalyticCertificate2649 :
    ‖(∫ position in (-complexPanelHalfWidthReal2649)..complexPanelHalfWidthReal2649,
        Complex.exp (complexPanelPhase2649 position - complexPanelPhase2649 0))‖
      ≤ ((pairMagnitude2542 complexPanelIntegral2648P109 : ℚ) : ℝ)
        + Real.exp (1 / 5)
            * ((complexPanelResidualUpper2648P109 / (((391 : ℚ) / 400) ^ 2) : ℚ) : ℝ)
            * (2 * complexPanelHalfWidthReal2649 ^ 2) := by
  have horder : -complexPanelHalfWidthReal2649 ≤ complexPanelHalfWidthReal2649 := by
    norm_num [complexPanelHalfWidthReal2649, complexPanelHalfWidth2649]
  have hphaseCont : ContinuousOn (fun coordinate =>
      Complex.exp (complexPanelPhase2649 coordinate - complexPanelPhase2649 0))
      (Icc (-complexPanelHalfWidthReal2649) complexPanelHalfWidthReal2649) := by
    intro coordinate hcoordinate
    have hd : complexPanelDeficitValue2649 coordinate ≠ 0 := by
      have hlower := complexPanelDeficit_lower2649 coordinate hcoordinate
      linarith
    have hsub := (complexPanelPhase_hasDerivAt2649 coordinate hd).sub
      (hasDerivAt_const coordinate (complexPanelPhase2649 0))
    have hsub' : HasDerivAt (fun x => complexPanelPhase2649 x - complexPanelPhase2649 0)
        (complexPanelPhaseDerivative2649 coordinate) coordinate := by
      convert hsub using 1
      ring
    refine ((Complex.hasDerivAt_exp (complexPanelPhase2649 coordinate
      - complexPanelPhase2649 0)).comp coordinate hsub').continuousAt.continuousWithinAt
  have hpolyCont : ContinuousOn (complexPolyEval2647 complexPanelPolynomial2648P109)
      (Icc (-complexPanelHalfWidthReal2649) complexPanelHalfWidthReal2649) :=
    HasDerivAt.continuousOn fun coordinate _ =>
      complexPolyEval2647_hasDerivAt complexPanelPolynomial2648P109 coordinate
  have hexpInt : IntervalIntegrable (fun coordinate =>
      Complex.exp (complexPanelPhase2649 coordinate - complexPanelPhase2649 0))
      MeasureTheory.volume (-complexPanelHalfWidthReal2649)
      complexPanelHalfWidthReal2649 :=
    hphaseCont.intervalIntegrable_of_Icc horder (μ := MeasureTheory.volume)
  have hpolyInt : IntervalIntegrable
      (complexPolyEval2647 complexPanelPolynomial2648P109) MeasureTheory.volume
      (-complexPanelHalfWidthReal2649) complexPanelHalfWidthReal2649 :=
    hpolyCont.intervalIntegrable_of_Icc horder (μ := MeasureTheory.volume)
  have hsubInt : IntervalIntegrable (fun coordinate =>
      Complex.exp (complexPanelPhase2649 coordinate - complexPanelPhase2649 0)
        - complexPolyEval2647 complexPanelPolynomial2648P109 coordinate)
      MeasureTheory.volume (-complexPanelHalfWidthReal2649)
      complexPanelHalfWidthReal2649 := hexpInt.sub hpolyInt
  have herror := complexPanelIntegralError2649
  have hfun : (fun coordinate => Complex.exp (complexPanelPhase2649 coordinate
          - complexPanelPhase2649 0))
      = fun coordinate => (Complex.exp (complexPanelPhase2649 coordinate
            - complexPanelPhase2649 0)
          - complexPolyEval2647 complexPanelPolynomial2648P109 coordinate)
        + complexPolyEval2647 complexPanelPolynomial2648P109 coordinate := by
    funext coordinate
    ring
  -- a direct rw of intervalIntegral.integral_add fails to match: the lemma
  -- instance stores the difference as a Pi-sub term while the goal carries
  -- the beta lambda; route through an explicitly typed split whose integrand
  -- is a pointwise sum body (a plain ℂ-valued integrand, no function-space
  -- reading), which exact reconciles with the Pi-form definitionally
  rw [hfun]
  have hintsplit : (∫ position in (-complexPanelHalfWidthReal2649)..complexPanelHalfWidthReal2649,
        (Complex.exp (complexPanelPhase2649 position - complexPanelPhase2649 0)
          - complexPolyEval2647 complexPanelPolynomial2648P109 position)
        + complexPolyEval2647 complexPanelPolynomial2648P109 position)
      = (∫ coordinate in (-complexPanelHalfWidthReal2649)..complexPanelHalfWidthReal2649,
          Complex.exp (complexPanelPhase2649 coordinate - complexPanelPhase2649 0)
            - complexPolyEval2647 complexPanelPolynomial2648P109 coordinate)
        + (∫ coordinate in (-complexPanelHalfWidthReal2649)..complexPanelHalfWidthReal2649,
            complexPolyEval2647 complexPanelPolynomial2648P109 coordinate) :=
    intervalIntegral.integral_add hsubInt hpolyInt
  rw [hintsplit, complexPanelPolyIntegral2649]
  calc ‖(∫ position in (-complexPanelHalfWidthReal2649)..complexPanelHalfWidthReal2649,
          Complex.exp (complexPanelPhase2649 position - complexPanelPhase2649 0)
            - complexPolyEval2647 complexPanelPolynomial2648P109 position)
        + embedPair2542 complexPanelIntegral2648P109‖
      ≤ ‖(∫ position in (-complexPanelHalfWidthReal2649)..complexPanelHalfWidthReal2649,
            Complex.exp (complexPanelPhase2649 position - complexPanelPhase2649 0)
              - complexPolyEval2647 complexPanelPolynomial2648P109 position)‖
        + ‖embedPair2542 complexPanelIntegral2648P109‖ := norm_add_le _ _
    _ ≤ Real.exp (1 / 5)
          * ((complexPanelResidualUpper2648P109 / (((391 : ℚ) / 400) ^ 2) : ℚ) : ℝ)
          * (2 * complexPanelHalfWidthReal2649 ^ 2)
        + (pairMagnitude2542 complexPanelIntegral2648P109 : ℝ) :=
          add_le_add herror (embedPair_magnitude2542 _)
    _ = ((pairMagnitude2542 complexPanelIntegral2648P109 : ℚ) : ℝ)
        + Real.exp (1 / 5)
            * ((complexPanelResidualUpper2648P109 / (((391 : ℚ) / 400) ^ 2) : ℚ) : ℝ)
            * (2 * complexPanelHalfWidthReal2649 ^ 2) := by ring

end ConnesWeilRH.Dev
