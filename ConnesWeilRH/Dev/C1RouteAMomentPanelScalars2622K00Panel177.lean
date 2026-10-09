import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P177 : ℚ := ((-22997312864056689710726203060893284477972839712319 : ℚ) / 182687704666362864775460604089535377456991567872)

def momentPanelGrowth2622K00P177 : ℚ := ((157363353234707960560695822710592054274192390157613317 : ℚ) / 15133392735299833810837217791266886830093539003596800)

theorem momentPanelPhase_owner2622K00P177 :
    (momentPanelPhase2622K00P177 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (7 / 8) 0 := by
  norm_num [momentPanelPhase2622K00P177, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P177 :
    (momentPanelGrowth2622K00P177 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (7 / 8) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P177, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P177Input : RatPair2542 := (momentPanelPhase2622K00P177 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P177Expected : RatState2542 :=
  ((((456267450763817080450601647290935847363051 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P177_replay :
    compactExp2620 momentScalarAmp2622K00P177Input 20 = momentScalarAmp2622K00P177Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P177_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (7 / 8) 0) -
      (momentScalarAmp2622K00P177Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P177Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P177 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P177]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P177 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P177 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P177Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P177Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P177_replay] at h
  simpa only [momentPanelPhase_owner2622K00P177] using h

theorem momentScalarAmp2622K00P177_radius_le :
    (momentScalarAmp2622K00P177Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [momentScalarAmp2622K00P177Expected]

def momentScalarGrow2622K00P177Input : RatPair2542 := (momentPanelGrowth2622K00P177 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P177Expected : RatState2542 :=
  ((((70076830682837030374378787167515972736101875722469141001161627198551196049723131759883713562035805679 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((88832055551551073996925568780330510875114434245965633 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P177_replay :
    compactExp2620 momentScalarGrow2622K00P177Input 20 = momentScalarGrow2622K00P177Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P177_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (7 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P177Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P177Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P177 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P177]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P177 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P177 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P177Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P177Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P177_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P177] using h

theorem momentScalarGrow2622K00P177_radius_le :
    (momentScalarGrow2622K00P177Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 67 := by
  norm_num [momentScalarGrow2622K00P177Expected]

end ConnesWeilRH.Dev
