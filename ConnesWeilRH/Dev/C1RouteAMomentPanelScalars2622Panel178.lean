import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P178 : ℚ := ((-5395843302517555576443630456786412592102963514415192743 : ℚ) / 39602127179050810011700472451509031448239347125452800)

def momentPanelGrowth2622P178 : ℚ := ((40727608013226065792030216424997474177857435079936603837 : ℚ) / 3290084530436853729208131737002322830812852880461004800)

theorem momentPanelPhase_owner2622P178 :
    (momentPanelPhase2622P178 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (177 / 200) 0 := by
  norm_num [momentPanelPhase2622P178, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P178 :
    (momentPanelGrowth2622P178 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (177 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P178, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P178Input : RatPair2542 := (momentPanelPhase2622P178 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P178Expected : RatState2542 :=
  ((((14334713900169507003035585426107131247 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P178_replay :
    compactExp2620 momentScalarAmp2622P178Input 20 = momentScalarAmp2622P178Expected := by
  decide +kernel

theorem momentScalarAmp2622P178_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (177 / 200) 0) -
      (momentScalarAmp2622P178Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P178Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P178 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P178]
  have h := compactExp_real_error2620 momentPanelPhase2622P178 20 hsmall
  change |Real.exp (momentPanelPhase2622P178 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P178Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P178Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P178_replay] at h
  simpa only [momentPanelPhase_owner2622P178] using h

theorem momentScalarAmp2622P178_radius_le :
    (momentScalarAmp2622P178Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [momentScalarAmp2622P178Expected]

def momentScalarGrow2622P178Input : RatPair2542 := (momentPanelGrowth2622P178 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P178Expected : RatState2542 :=
  ((((126947462662156757278522592290519776903557433902036256919733636730590363341515974837830410091555987993 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((160923127462659743215429995265656732216518035951314021 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622P178_replay :
    compactExp2620 momentScalarGrow2622P178Input 20 = momentScalarGrow2622P178Expected := by
  decide +kernel

theorem momentScalarGrow2622P178_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (177 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P178Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P178Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P178 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P178]
  have h := compactExp_real_error2620 momentPanelGrowth2622P178 20 hsmall
  change |Real.exp (momentPanelGrowth2622P178 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P178Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P178Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P178_replay] at h
  simpa only [momentPanelGrowth_owner2622P178] using h

theorem momentScalarGrow2622P178_radius_le :
    (momentScalarGrow2622P178Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 66 := by
  norm_num [momentScalarGrow2622P178Expected]

end ConnesWeilRH.Dev
