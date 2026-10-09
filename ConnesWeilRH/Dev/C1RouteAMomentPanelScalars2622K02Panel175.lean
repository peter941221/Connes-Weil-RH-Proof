import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P175 : ℚ := ((-331803858008996176779345574711374985570060363861330269 : ℚ) / 3071151585164684472061219749061423634468394185523200)

def momentPanelGrowth2622K02P175 : ℚ := ((154253452116199454892615218948449810701163076480579293 : ℚ) / 20162299980549283451746088404622182943138146733260800)

theorem momentPanelPhase_owner2622K02P175 :
    (momentPanelPhase2622K02P175 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (171 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P175, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P175 :
    (momentPanelGrowth2622K02P175 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (171 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P175, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P175Input : RatPair2542 := (momentPanelPhase2622K02P175 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P175Expected : RatState2542 :=
  ((((25638807564522697319055127602345790384423455745975 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1208925819614629174706201 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P175_replay :
    compactExp2620 momentScalarAmp2622K02P175Input 20 = momentScalarAmp2622K02P175Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P175_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (171 / 200) 0) -
      (momentScalarAmp2622K02P175Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P175Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P175 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P175]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P175 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P175 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P175Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P175Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P175_replay] at h
  simpa only [momentPanelPhase_owner2622K02P175] using h

theorem momentScalarAmp2622K02P175_radius_le :
    (momentScalarAmp2622K02P175Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P175Expected]

def momentScalarGrow2622K02P175Input : RatPair2542 := (momentPanelGrowth2622K02P175 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P175Expected : RatState2542 :=
  ((((4489591257584717461862772146555304178977134605863723314008687437930389147103658315582208318631594085 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5691191528407900196103385879669108350731413656818157 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P175_replay :
    compactExp2620 momentScalarGrow2622K02P175Input 20 = momentScalarGrow2622K02P175Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P175_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (171 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P175Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P175Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P175 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P175]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P175 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P175 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P175Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P175Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P175_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P175] using h

theorem momentScalarGrow2622K02P175_radius_le :
    (momentScalarGrow2622K02P175Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 68 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P175Expected]

end ConnesWeilRH.Dev
