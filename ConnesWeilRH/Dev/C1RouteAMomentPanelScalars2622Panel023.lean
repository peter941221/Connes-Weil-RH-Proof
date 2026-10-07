import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P023 : ℚ := ((-1881520800790123422374825816458893030401995286772391991 : ℚ) / 33966211490093515633377512815346865053691157256601600)

def momentPanelGrowth2622P023 : ℚ := ((31159472314286124565335123764601724923832580022014437997 : ℚ) / 23118459931809879983342299323068224093862346682584268800)

theorem momentPanelPhase_owner2622P023 :
    (momentPanelPhase2622P023 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-133 / 200) 0 := by
  norm_num [momentPanelPhase2622P023, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P023 :
    (momentPanelGrowth2622P023 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-133 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P023, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P023Input : RatPair2542 := (momentPanelPhase2622P023 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P023Expected : RatState2542 :=
  ((((1872125977786249637274844860658711688336246861727415512877808705357096605 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1197794658214574420180299 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622P023_replay :
    compactExp2620 momentScalarAmp2622P023Input 20 = momentScalarAmp2622P023Expected := by
  decide +kernel

theorem momentScalarAmp2622P023_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-133 / 200) 0) -
      (momentScalarAmp2622P023Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P023Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P023 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P023]
  have h := compactExp_real_error2620 momentPanelPhase2622P023 20 hsmall
  change |Real.exp (momentPanelPhase2622P023 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P023Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P023Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P023_replay] at h
  simpa only [momentPanelPhase_owner2622P023] using h

theorem momentScalarAmp2622P023_radius_le :
    (momentScalarAmp2622P023Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [momentScalarAmp2622P023Expected]

def momentScalarGrow2622P023Input : RatPair2542 := (momentPanelGrowth2622P023 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P023Expected : RatState2542 :=
  ((((8221450668066744747728611774031203034707601265256285175245555397142783690774026837752182602010225 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((10421913478001750729947421411360951333530231322321 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P023_replay :
    compactExp2620 momentScalarGrow2622P023Input 20 = momentScalarGrow2622P023Expected := by
  decide +kernel

theorem momentScalarGrow2622P023_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-133 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P023Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P023Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P023 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P023]
  have h := compactExp_real_error2620 momentPanelGrowth2622P023 20 hsmall
  change |Real.exp (momentPanelGrowth2622P023 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P023Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P023Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P023_replay] at h
  simpa only [momentPanelGrowth_owner2622P023] using h

theorem momentScalarGrow2622P023_radius_le :
    (momentScalarGrow2622P023Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P023Expected]

end ConnesWeilRH.Dev
