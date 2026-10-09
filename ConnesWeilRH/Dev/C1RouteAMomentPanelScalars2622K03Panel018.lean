import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P018 : ℚ := ((-73327082563158986931284154787723507644513975625598675 : ℚ) / 1190575771310686789741676756851502054887214047821824)

def momentPanelGrowth2622K03P018 : ℚ := ((15438774228815669730730699859606069659563632377393425 : ℚ) / 8275844365238570955760753095557997366490446520385536)

theorem momentPanelPhase_owner2622K03P018 :
    (momentPanelPhase2622K03P018 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-143 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P018, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P018 :
    (momentPanelGrowth2622K03P018 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-143 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P018, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P018Input : RatPair2542 := (momentPanelPhase2622K03P018 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P018Expected : RatState2542 :=
  ((((3815717994694064175798744175171226659413511371241857011032292396362417 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2422688920551968636875357 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P018_replay :
    compactExp2620 momentScalarAmp2622K03P018Input 20 = momentScalarAmp2622K03P018Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P018_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-143 / 200) 0) -
      (momentScalarAmp2622K03P018Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P018Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P018 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P018]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P018 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P018 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P018Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P018Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P018_replay] at h
  simpa only [momentPanelPhase_owner2622K03P018] using h

theorem momentScalarAmp2622K03P018_radius_le :
    (momentScalarAmp2622K03P018Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P018Expected]

def momentScalarGrow2622K03P018Input : RatPair2542 := (momentPanelGrowth2622K03P018 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P018Expected : RatState2542 :=
  ((((13797003006411258413019645982189258214859331102324810056042856994846640387672647797317941031374149 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4372437006593287271830313739803787317839030126499 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K03P018_replay :
    compactExp2620 momentScalarGrow2622K03P018Input 20 = momentScalarGrow2622K03P018Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P018_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-143 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P018Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P018Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P018 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P018]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P018 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P018 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P018Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P018Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P018_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P018] using h

theorem momentScalarGrow2622K03P018_radius_le :
    (momentScalarGrow2622K03P018Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P018Expected]

end ConnesWeilRH.Dev
