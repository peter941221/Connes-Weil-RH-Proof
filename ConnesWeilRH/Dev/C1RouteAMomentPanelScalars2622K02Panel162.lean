import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P162 : ℚ := ((-870625455681086068448090150805088130299174151329177 : ℚ) / 14443746650184313996309854010828890780193395834880)

def momentPanelGrowth2622K02P162 : ℚ := ((2126219768098368179444190006885226842774539573530814213 : ℚ) / 1038001137538419160708700610945590740464221136145612800)

theorem momentPanelPhase_owner2622K02P162 :
    (momentPanelPhase2622K02P162 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (29 / 40) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P162, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P162 :
    (momentPanelGrowth2622K02P162 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (29 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P162, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P162Input : RatPair2542 := (momentPanelPhase2622K02P162 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P162Expected : RatState2542 :=
  ((((14178751110687363370864791242725213350572780617094326282318530885495191 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2435826374826560973135583 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P162_replay :
    compactExp2620 momentScalarAmp2622K02P162Input 20 = momentScalarAmp2622K02P162Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P162_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (29 / 40) 0) -
      (momentScalarAmp2622K02P162Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P162Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P162 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P162]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P162 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P162 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P162Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P162Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P162_replay] at h
  simpa only [momentPanelPhase_owner2622K02P162] using h

theorem momentScalarAmp2622K02P162_radius_le :
    (momentScalarAmp2622K02P162Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P162Expected]

def momentScalarGrow2622K02P162Input : RatPair2542 := (momentPanelGrowth2622K02P162 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P162Expected : RatState2542 :=
  ((((16565262568483732268213578607929350505037676747475549146530383620495896156964550996303950627546881 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5249731004180622016826814632679217063593654615073 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K02P162_replay :
    compactExp2620 momentScalarGrow2622K02P162Input 20 = momentScalarGrow2622K02P162Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P162_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (29 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P162Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P162Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P162 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P162]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P162 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P162 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P162Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P162Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P162_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P162] using h

theorem momentScalarGrow2622K02P162_radius_le :
    (momentScalarGrow2622K02P162Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P162Expected]

end ConnesWeilRH.Dev
