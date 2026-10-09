import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P017 : ℚ := ((-956251590982542579306515890090265644270741527390823 : ℚ) / 14443746650184313996309854010828890780193395834880)

def momentPanelGrowth2622K02P017 : ℚ := ((2126219768098368179444190006885226842774539573530814213 : ℚ) / 1038001137538419160708700610945590740464221136145612800)

theorem momentPanelPhase_owner2622K02P017 :
    (momentPanelPhase2622K02P017 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-29 / 40) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P017, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P017 :
    (momentPanelGrowth2622K02P017 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-29 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P017, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P017Input : RatPair2542 := (momentPanelPhase2622K02P017 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P017Expected : RatState2542 :=
  ((((37759991727940158132533049927335250648262797455670907223812162668647 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417899508727757158043695 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P017_replay :
    compactExp2620 momentScalarAmp2622K02P017Input 20 = momentScalarAmp2622K02P017Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P017_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-29 / 40) 0) -
      (momentScalarAmp2622K02P017Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P017Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P017 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P017]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P017 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P017 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P017Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P017Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P017_replay] at h
  simpa only [momentPanelPhase_owner2622K02P017] using h

theorem momentScalarAmp2622K02P017_radius_le :
    (momentScalarAmp2622K02P017Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P017Expected]

def momentScalarGrow2622K02P017Input : RatPair2542 := (momentPanelGrowth2622K02P017 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P017Expected : RatState2542 :=
  ((((16565262568483732268213578607929350505037676747475549146530383620495896156964550996303950627546881 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5249731004180622016826814632679217063593654615073 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K02P017_replay :
    compactExp2620 momentScalarGrow2622K02P017Input 20 = momentScalarGrow2622K02P017Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P017_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-29 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P017Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P017Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P017 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P017]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P017 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P017 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P017Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P017Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P017_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P017] using h

theorem momentScalarGrow2622K02P017_radius_le :
    (momentScalarGrow2622K02P017Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P017Expected]

end ConnesWeilRH.Dev
