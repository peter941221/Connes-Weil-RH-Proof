import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P117 : ℚ := ((-881794082024754308994841334190111284295465548206783 : ℚ) / 28145324500161528854469399317544044089467763425280)

def momentPanelGrowth2622K02P117 : ℚ := ((919783657221106178409935061815199016179657197333 : ℚ) / 3853568770306091678857372117513636868233415884800)

theorem momentPanelPhase_owner2622K02P117 :
    (momentPanelPhase2622K02P117 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (11 / 40) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P117, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P117 :
    (momentPanelGrowth2622K02P117 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (11 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P117, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P117Input : RatPair2542 := (momentPanelPhase2622K02P117 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P117Expected : RatState2542 :=
  ((((52861082727769329968921777318217069604647220878668425896837818394206528463563420533 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((67011385430971714920101816039468095 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P117_replay :
    compactExp2620 momentScalarAmp2622K02P117Input 20 = momentScalarAmp2622K02P117Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P117_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (11 / 40) 0) -
      (momentScalarAmp2622K02P117Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P117Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P117 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P117]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P117 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P117 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P117Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P117Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P117_replay] at h
  simpa only [momentPanelPhase_owner2622K02P117] using h

theorem momentScalarAmp2622K02P117_radius_le :
    (momentScalarAmp2622K02P117Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P117Expected]

def momentScalarGrow2622K02P117Input : RatPair2542 := (momentPanelGrowth2622K02P117 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P117Expected : RatState2542 :=
  ((((2711799534071834083444401091140329830527703326725031435824313790483621732965247936119719179956981 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3437613524573055845730489105176164520397454818947 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P117_replay :
    compactExp2620 momentScalarGrow2622K02P117Input 20 = momentScalarGrow2622K02P117Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P117_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (11 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P117Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P117Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P117 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P117]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P117 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P117 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P117Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P117Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P117_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P117] using h

theorem momentScalarGrow2622K02P117_radius_le :
    (momentScalarGrow2622K02P117Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P117Expected]

end ConnesWeilRH.Dev
