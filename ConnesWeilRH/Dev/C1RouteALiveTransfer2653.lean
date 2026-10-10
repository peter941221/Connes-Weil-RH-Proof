import ConnesWeilRH.Dev.C1RouteACell2700Discharge2650
import ConnesWeilRH.Dev.C1RouteAOwnerPointImport2452

/-!
# Live-tuple transfer seam (record 2653)

The discharged certificates of records 2650-2652 are valid at the
exact-rational center tuple and, regionally, over the record-2338
base boxes.  The LIVE consumer coefficients (the 2275 capture, lifted
exactly as `capBaseCoef2452`) lie OUTSIDE those boxes: the certified
capture-to-center gap is maximal at coefficient 0, exactly
`140194220516106903860480051346980943113331538318398858303892543363689367112949993980881 /
30354201441027016733116592294117482916287606860189680019559568902170379456331382784
~ 4.6186e3` - float-solve scale at the ~10^14 coefficient magnitude,
far beyond the `1/10^30` ball.  This is certified here as
`capBase_gap_2653`.  (An earlier float-derived estimate `147795/32`
was BELOW the true value; display-text numbers are not certificates.)

The transfer seam is therefore a STABILITY composition, not a
membership check: for any coefficient tuple (in particular the live
one) whose induced change integral against the center owner is
bounded, the cell certificate extends by that bound:

  integral ||P(live)|| <= integral upper + change integral.

`baseTransformChangeUpper2653` imports the record-2338
`base_transform_change_strip_upper` (exact rational, coefficient
triangle bound over all Im(z), 0 <= Re(z) <= 1).  That the LIVE
tuple's change integral is at most this constant is the externally
certified stability fact of record 2338 and remains the seam's
single remaining premise - the same doctrine as the 2452 rect
hypotheses.
-/

namespace ConnesWeilRH.Dev

open scoped BigOperators
open MeasureTheory

/-- Certified gap bound between the live 2275-capture coefficients
and the record-2338 box centers: the exact maximum over the 30
families of |dre| + |dim|, attained at family 0. -/
noncomputable def liveCoefGapUpper2653 : ℝ :=
  (((140194220516106903860480051346980943113331538318398858303892 * 10^27
      + 543363689367112949993980881 : ℕ) : ℝ)) /
  (((30354201441027016733116592294117482916287606860189680019559568902170379456331382784 : ℕ) : ℝ))

/-- Record-2338 `base_transform_change_strip_upper`, exact rational
(upper endpoint of the certified interval). -/
noncomputable def baseTransformChangeUpper2653 : ℝ :=
  (((35123835042366209751080332077222136 * 10^60
      + 451247361685817069095689417578357563534687096156485577722147 : ℕ) : ℝ)) /
  (((279968092772225526319680285071055534765205 * 10^60
      + 687154331191862498637620473983897520118172609686658950889472 : ℕ) : ℝ))

/-- The live tuple is NOT inside the certificate ball: the certified
capture-to-center gap dwarfs `1/10^30`. -/
theorem capBase_gap_2653 (i : Fin 30) :
    ‖capBaseCoef2452 i - baseCoefficientCenter2540 i‖ ≤ liveCoefGapUpper2653 := by
  have h := Complex.norm_le_abs_re_add_abs_im
    (capBaseCoef2452 i - baseCoefficientCenter2540 i)
  have hstep : ∀ k : Fin 30,
      |(capBaseCoef2452 k - baseCoefficientCenter2540 k).re| +
        |(capBaseCoef2452 k - baseCoefficientCenter2540 k).im| ≤ liveCoefGapUpper2653 := by
    intro k
    simp only [Complex.sub_re, Complex.sub_im]
    fin_cases k <;>
      norm_num [capBaseCoef2452, baseCoefficientCenter2540, baseCoefficientBox2540,
        liveCoefGapUpper2653, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  exact h.trans (hstep i)

/-- Transfer seam: the cell2700 certificate extends to ANY tuple whose
change integral against the center owner is bounded by the record-2338
strip constant. -/
theorem cell2700_live_transfer_2653 (coefficients : Fin 30 → ℂ)
    (hchange : ∫ x in edgeLeftPosition2548..edgeRightPosition2548,
        ‖weightedPhysical2539 (1 / 2) coefficients nodeModulation2541 x -
          weightedPhysical2539 (1 / 2) baseCoefficientCenter2540 nodeModulation2541 x‖ ≤
        baseTransformChangeUpper2653) :
    (∫ x in edgeLeftPosition2548..edgeRightPosition2548,
      ‖weightedPhysical2539 (1 / 2) coefficients nodeModulation2541 x‖) ≤
      boundaryCellIntegralUpper2551 + baseTransformChangeUpper2653 := by
  have hcont := (weightedPhysical2539_contDiff (1 / 2) coefficients
    nodeModulation2541).continuous.norm
  have hcent := (weightedPhysical2539_contDiff (1 / 2) baseCoefficientCenter2540
    nodeModulation2541).continuous.norm
  -- norm of the DIFFERENCE (sub at the complex level, then norm):
  -- exactly the hchange integrand
  have hdiff := ((weightedPhysical2539_contDiff (1 / 2) coefficients
      nodeModulation2541).sub
    (weightedPhysical2539_contDiff (1 / 2) baseCoefficientCenter2540
      nodeModulation2541)).continuous.norm
  have hab : edgeLeftPosition2548 ≤ edgeRightPosition2548 := by
    norm_num [edgeLeftPosition2548, edgeRightPosition2548]
  -- integrability of the three integrands and of the pointwise sum
  have hfint : IntervalIntegrable
      (fun x => ‖weightedPhysical2539 (1 / 2) coefficients nodeModulation2541 x‖)
      volume edgeLeftPosition2548 edgeRightPosition2548 :=
    hcont.intervalIntegrable edgeLeftPosition2548 edgeRightPosition2548
  have hdint : IntervalIntegrable
      (fun x => ‖weightedPhysical2539 (1 / 2) coefficients nodeModulation2541 x -
        weightedPhysical2539 (1 / 2) baseCoefficientCenter2540 nodeModulation2541 x‖)
      volume edgeLeftPosition2548 edgeRightPosition2548 :=
    hdiff.intervalIntegrable edgeLeftPosition2548 edgeRightPosition2548
  have hcint : IntervalIntegrable
      (fun x => ‖weightedPhysical2539 (1 / 2) baseCoefficientCenter2540
        nodeModulation2541 x‖)
      volume edgeLeftPosition2548 edgeRightPosition2548 :=
    hcent.intervalIntegrable edgeLeftPosition2548 edgeRightPosition2548
  have hgint : IntervalIntegrable
      (fun x => ‖weightedPhysical2539 (1 / 2) coefficients nodeModulation2541 x -
          weightedPhysical2539 (1 / 2) baseCoefficientCenter2540 nodeModulation2541 x‖ +
        ‖weightedPhysical2539 (1 / 2) baseCoefficientCenter2540 nodeModulation2541 x‖)
      volume edgeLeftPosition2548 edgeRightPosition2548 :=
    (hdiff.add hcent).intervalIntegrable edgeLeftPosition2548 edgeRightPosition2548
  -- pointwise triangle, change term first
  have hpt : ∀ x ∈ Set.Icc edgeLeftPosition2548 edgeRightPosition2548,
      ‖weightedPhysical2539 (1 / 2) coefficients nodeModulation2541 x‖ ≤
        (‖weightedPhysical2539 (1 / 2) coefficients nodeModulation2541 x -
          weightedPhysical2539 (1 / 2) baseCoefficientCenter2540 nodeModulation2541 x‖ +
        ‖weightedPhysical2539 (1 / 2) baseCoefficientCenter2540 nodeModulation2541 x‖) := by
    intro x _
    have hx : ‖weightedPhysical2539 (1 / 2) coefficients nodeModulation2541 x‖
        = ‖weightedPhysical2539 (1 / 2) coefficients nodeModulation2541 x -
            weightedPhysical2539 (1 / 2) baseCoefficientCenter2540 nodeModulation2541 x +
            weightedPhysical2539 (1 / 2) baseCoefficientCenter2540 nodeModulation2541 x‖ := by
      rw [sub_add_cancel]
    calc ‖weightedPhysical2539 (1 / 2) coefficients nodeModulation2541 x‖
        = ‖weightedPhysical2539 (1 / 2) coefficients nodeModulation2541 x -
            weightedPhysical2539 (1 / 2) baseCoefficientCenter2540 nodeModulation2541 x +
            weightedPhysical2539 (1 / 2) baseCoefficientCenter2540 nodeModulation2541 x‖ := hx
      _ ≤ _ := norm_add_le _ _
  have hmono := intervalIntegral.integral_mono_on hab hfint hgint hpt
  have hsplit : (∫ x in edgeLeftPosition2548..edgeRightPosition2548,
      ‖weightedPhysical2539 (1 / 2) coefficients nodeModulation2541 x -
        weightedPhysical2539 (1 / 2) baseCoefficientCenter2540 nodeModulation2541 x‖ +
      ‖weightedPhysical2539 (1 / 2) baseCoefficientCenter2540 nodeModulation2541 x‖) =
      (∫ x in edgeLeftPosition2548..edgeRightPosition2548,
        ‖weightedPhysical2539 (1 / 2) coefficients nodeModulation2541 x -
          weightedPhysical2539 (1 / 2) baseCoefficientCenter2540 nodeModulation2541 x‖) +
      (∫ x in edgeLeftPosition2548..edgeRightPosition2548,
        ‖weightedPhysical2539 (1 / 2) baseCoefficientCenter2540 nodeModulation2541 x‖) := by
    rw [show (fun x => ‖weightedPhysical2539 (1 / 2) coefficients nodeModulation2541 x -
          weightedPhysical2539 (1 / 2) baseCoefficientCenter2540 nodeModulation2541 x‖ +
        ‖weightedPhysical2539 (1 / 2) baseCoefficientCenter2540 nodeModulation2541 x‖)
        = (fun x => ‖weightedPhysical2539 (1 / 2) coefficients nodeModulation2541 x -
            weightedPhysical2539 (1 / 2) baseCoefficientCenter2540 nodeModulation2541 x‖) +
          (fun x => ‖weightedPhysical2539 (1 / 2) baseCoefficientCenter2540
            nodeModulation2541 x‖) from funext fun x => rfl]
    exact intervalIntegral.integral_add hdint hcint
  have huncond := cell2700_center_discharge2650
  linarith

/-- Specialization naming the live tuple: the certificate reaches the
2275-capture owner as soon as the record-2338 stability premise
certifies its change integral. -/
theorem cell2700_capBase_transfer_2653
    (hchange : ∫ x in edgeLeftPosition2548..edgeRightPosition2548,
        ‖weightedPhysical2539 (1 / 2) capBaseCoef2452 nodeModulation2541 x -
          weightedPhysical2539 (1 / 2) baseCoefficientCenter2540 nodeModulation2541 x‖ ≤
        baseTransformChangeUpper2653) :
    (∫ x in edgeLeftPosition2548..edgeRightPosition2548,
      ‖weightedPhysical2539 (1 / 2) capBaseCoef2452 nodeModulation2541 x‖) ≤
      boundaryCellIntegralUpper2551 + baseTransformChangeUpper2653 :=
  cell2700_live_transfer_2653 capBaseCoef2452 hchange

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.capBase_gap_2653
#print axioms ConnesWeilRH.Dev.cell2700_live_transfer_2653
#print axioms ConnesWeilRH.Dev.cell2700_capBase_transfer_2653
