import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P155 : ℚ := ((-28478691811538041378557417820148074456056491507988281 : ℚ) / 543281834228523628724836554270950323664092502425600)

def momentPanelGrowth2622K01P155 : ℚ := ((88443230235394112851706079568586052512941639098557433 : ℚ) / 71038435090246058808911094014558957660556857285017600)

theorem momentPanelPhase_owner2622K01P155 :
    (momentPanelPhase2622K01P155 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (131 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P155, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P155 :
    (momentPanelGrowth2622K01P155 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (131 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P155, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P155Input : RatPair2542 := (momentPanelPhase2622K01P155 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P155Expected : RatState2542 :=
  ((((36643363907150982071501657089180471335971297300801863380650651611957144373 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((12217789024070510574387547 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K01P155_replay :
    compactExp2620 momentScalarAmp2622K01P155Input 20 = momentScalarAmp2622K01P155Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P155_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (131 / 200) 0) -
      (momentScalarAmp2622K01P155Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P155Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P155 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P155]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P155 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P155 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P155Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P155Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P155_replay] at h
  simpa only [momentPanelPhase_owner2622K01P155] using h

theorem momentScalarAmp2622K01P155_radius_le :
    (momentScalarAmp2622K01P155Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 94 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P155Expected]

def momentScalarGrow2622K01P155Input : RatPair2542 := (momentPanelGrowth2622K01P155 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P155Expected : RatState2542 :=
  ((((927272904715884704847539438261947808605523858668543209391729073138858541115150766435906185623599 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((9403653268665162910496354977049526177309287579605 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P155_replay :
    compactExp2620 momentScalarGrow2622K01P155Input 20 = momentScalarGrow2622K01P155Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P155_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (131 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P155Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P155Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P155 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P155]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P155 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P155 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P155Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P155Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P155_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P155] using h

theorem momentScalarGrow2622K01P155_radius_le :
    (momentScalarGrow2622K01P155Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P155Expected]

end ConnesWeilRH.Dev
