import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P120 : ℚ := ((-1786124477425129232740243407305244279910093815964248017 : ℚ) / 55231060313258153093241127131368782989684975756902400)

def momentPanelGrowth2622P120 : ℚ := ((15662860966079839898757933915962911786697913649550424797 : ℚ) / 62192619644374901315841690628758498301250988176886988800)

theorem momentPanelPhase_owner2622P120 :
    (momentPanelPhase2622P120 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (61 / 200) 0 := by
  norm_num [momentPanelPhase2622P120, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P120 :
    (momentPanelGrowth2622P120 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (61 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P120, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P120Input : RatPair2542 := (momentPanelPhase2622P120 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P120Expected : RatState2542 :=
  ((((19270483253832993467622960399899145770352487388488141185629275379654350254334738407 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((6107248267186061823384892848027589 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622P120_replay :
    compactExp2620 momentScalarAmp2622P120Input 20 = momentScalarAmp2622P120Expected := by
  decide +kernel

theorem momentScalarAmp2622P120_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (61 / 200) 0) -
      (momentScalarAmp2622P120Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P120Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P120 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P120]
  have h := compactExp_real_error2620 momentPanelPhase2622P120 20 hsmall
  change |Real.exp (momentPanelPhase2622P120 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P120Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P120Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P120_replay] at h
  simpa only [momentPanelPhase_owner2622P120] using h

theorem momentScalarAmp2622P120_radius_le :
    (momentScalarAmp2622P120Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [momentScalarAmp2622P120Expected]

def momentScalarGrow2622P120Input : RatPair2542 := (momentPanelGrowth2622P120 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P120Expected : RatState2542 :=
  ((((1373862393964875526367541879447712774263288950523910662336700072891619365498843877008432440099515 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1741577070052880724883337687729778626828815506405 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622P120_replay :
    compactExp2620 momentScalarGrow2622P120Input 20 = momentScalarGrow2622P120Expected := by
  decide +kernel

theorem momentScalarGrow2622P120_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (61 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P120Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P120Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P120 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P120]
  have h := compactExp_real_error2620 momentPanelGrowth2622P120 20 hsmall
  change |Real.exp (momentPanelGrowth2622P120 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P120Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P120Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P120_replay] at h
  simpa only [momentPanelGrowth_owner2622P120] using h

theorem momentScalarGrow2622P120_radius_le :
    (momentScalarGrow2622P120Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P120Expected]

end ConnesWeilRH.Dev
