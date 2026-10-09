import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P162 : ℚ := ((-2913083392658439967197041525282925401608965484080875 : ℚ) / 46219989280589804788191532834652450496618866671616)

def momentPanelGrowth2622K03P162 : ℚ := ((1335586846002034659493050125549093562753248476017853475 : ℚ) / 664320728024588262853568391005178073897101527133192192)

theorem momentPanelPhase_owner2622K03P162 :
    (momentPanelPhase2622K03P162 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (29 / 40) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P162, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P162 :
    (momentPanelGrowth2622K03P162 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (29 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P162, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P162Input : RatPair2542 := (momentPanelPhase2622K03P162 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P162Expected : RatState2542 :=
  ((((906869104034329176140976814824215497342591301885452329921164992450407 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2419001301493788013473217 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P162_replay :
    compactExp2620 momentScalarAmp2622K03P162Input 20 = momentScalarAmp2622K03P162Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P162_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (29 / 40) 0) -
      (momentScalarAmp2622K03P162Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P162Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P162 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P162]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P162 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P162 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P162Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P162Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P162_replay] at h
  simpa only [momentPanelPhase_owner2622K03P162] using h

theorem momentScalarAmp2622K03P162_radius_le :
    (momentScalarAmp2622K03P162Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P162Expected]

def momentScalarGrow2622K03P162Input : RatPair2542 := (momentPanelGrowth2622K03P162 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P162Expected : RatState2542 :=
  ((((498400067350940127345426618064445992414563302780506981831945985595844303559854479018830393301701 : ℚ) / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768), 0), ((2527183732702354070500393898272144076295048705191 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K03P162_replay :
    compactExp2620 momentScalarGrow2622K03P162Input 20 = momentScalarGrow2622K03P162Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P162_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (29 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P162Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P162Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P162 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P162]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P162 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P162 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P162Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P162Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P162_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P162] using h

theorem momentScalarGrow2622K03P162_radius_le :
    (momentScalarGrow2622K03P162Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P162Expected]

end ConnesWeilRH.Dev
