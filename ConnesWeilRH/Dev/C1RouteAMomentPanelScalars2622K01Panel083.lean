import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P083 : ℚ := ((-28556421677650812535219357510086167755942386253036073 : ℚ) / 947478380802851467040543140819047346287686346342400)

def momentPanelGrowth2622K01P083 : ℚ := ((52146726102905261744730558301981463581729785338610491 : ℚ) / 1177745777945452786933882480329180472020350214026035200)

theorem momentPanelPhase_owner2622K01P083 :
    (momentPanelPhase2622K01P083 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-13 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P083, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P083 :
    (momentPanelGrowth2622K01P083 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-13 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P083, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P083Input : RatPair2542 := (momentPanelPhase2622K01P083 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P083Expected : RatState2542 :=
  ((((173871050561961835426191353264943744503473866162599711075158789866453081514803032029 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((110207038458191180321890290589317939 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K01P083_replay :
    compactExp2620 momentScalarAmp2622K01P083Input 20 = momentScalarAmp2622K01P083Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P083_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-13 / 200) 0) -
      (momentScalarAmp2622K01P083Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P083Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P083 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P083]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P083 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P083 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P083Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P083Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P083_replay] at h
  simpa only [momentPanelPhase_owner2622K01P083] using h

theorem momentScalarAmp2622K01P083_radius_le :
    (momentScalarAmp2622K01P083Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P083Expected]

def momentScalarGrow2622K01P083Input : RatPair2542 := (momentPanelGrowth2622K01P083 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P083Expected : RatState2542 :=
  ((((2232686517834127817059488952814546453201920599837452953795998916758430061137895199201222235256105 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2830266284944282118779506278809312712931614030279 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P083_replay :
    compactExp2620 momentScalarGrow2622K01P083Input 20 = momentScalarGrow2622K01P083Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P083_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-13 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P083Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P083Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P083 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P083]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P083 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P083 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P083Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P083Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P083_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P083] using h

theorem momentScalarGrow2622K01P083_radius_le :
    (momentScalarGrow2622K01P083Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P083Expected]

end ConnesWeilRH.Dev
