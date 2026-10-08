import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P022 : ℚ := ((-3058170569274708193459957796283011349422913116499459 : ℚ) / 49725309613875642256070683175620410551574892380160)

def momentPanelGrowth2622K04P022 : ℚ := ((31605024386677804674952825921696550167971666243469 : ℚ) / 20980541082777610251556803750907578504826375372800)

theorem momentPanelPhase_owner2622K04P022 :
    (momentPanelPhase2622K04P022 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-27 / 40) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P022, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P022 :
    (momentPanelGrowth2622K04P022 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-27 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P022, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P022Input : RatPair2542 := (momentPanelPhase2622K04P022 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P022Expected : RatState2542 :=
  ((((4168010101990130448087538533843089058228726192113165545674142999734889 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2423135529639717639635785 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P022_replay :
    compactExp2620 momentScalarAmp2622K04P022Input 20 = momentScalarAmp2622K04P022Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P022_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-27 / 40) 0) -
      (momentScalarAmp2622K04P022Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P022Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P022 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P022]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P022 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P022 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P022Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P022Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P022_replay] at h
  simpa only [momentPanelPhase_owner2622K04P022] using h

theorem momentScalarAmp2622K04P022_radius_le :
    (momentScalarAmp2622K04P022Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P022Expected]

def momentScalarGrow2622K04P022Input : RatPair2542 := (momentPanelGrowth2622K04P022 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P022Expected : RatState2542 :=
  ((((150535367845090529692829057066828816377765652120489378295631436379205416747509559902583322655379 : ℚ) / 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384), 0), ((12212862416722987372250586787858029646162976828745 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P022_replay :
    compactExp2620 momentScalarGrow2622K04P022Input 20 = momentScalarGrow2622K04P022Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P022_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-27 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P022Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P022Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P022 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P022]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P022 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P022 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P022Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P022Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P022_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P022] using h

theorem momentScalarGrow2622K04P022_radius_le :
    (momentScalarGrow2622K04P022Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P022Expected]

end ConnesWeilRH.Dev
