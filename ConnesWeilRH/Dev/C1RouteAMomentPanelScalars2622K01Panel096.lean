import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P096 : ℚ := ((-28533486030587582707112081267893637699367478706963927 : ℚ) / 947478380802851467040543140819047346287686346342400)

def momentPanelGrowth2622K01P096 : ℚ := ((52146726102905261744730558301981463581729785338610491 : ℚ) / 1177745777945452786933882480329180472020350214026035200)

theorem momentPanelPhase_owner2622K01P096 :
    (momentPanelPhase2622K01P096 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (13 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P096, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P096 :
    (momentPanelGrowth2622K01P096 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (13 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P096, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P096Input : RatPair2542 := (momentPanelPhase2622K01P096 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P096Expected : RatState2542 :=
  ((((44532827535238485202441402489143689881084373146057781477188951230284018195677407995 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((56453686886505200701081098983688879 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K01P096_replay :
    compactExp2620 momentScalarAmp2622K01P096Input 20 = momentScalarAmp2622K01P096Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P096_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (13 / 200) 0) -
      (momentScalarAmp2622K01P096Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P096Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P096 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P096]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P096 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P096 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P096Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P096Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P096_replay] at h
  simpa only [momentPanelPhase_owner2622K01P096] using h

theorem momentScalarAmp2622K01P096_radius_le :
    (momentScalarAmp2622K01P096Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P096Expected]

def momentScalarGrow2622K01P096Input : RatPair2542 := (momentPanelGrowth2622K01P096 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P096Expected : RatState2542 :=
  ((((2232686517834127817059488952814546453201920599837452953795998916758430061137895199201222235256105 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2830266284944282118779506278809312712931614030279 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P096_replay :
    compactExp2620 momentScalarGrow2622K01P096Input 20 = momentScalarGrow2622K01P096Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P096_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (13 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P096Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P096Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P096 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P096]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P096 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P096 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P096Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P096Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P096_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P096] using h

theorem momentScalarGrow2622K01P096_radius_le :
    (momentScalarGrow2622K01P096Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P096Expected]

end ConnesWeilRH.Dev
