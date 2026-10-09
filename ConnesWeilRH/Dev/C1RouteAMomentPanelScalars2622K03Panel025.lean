import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P025 : ℚ := ((-220040066086467778216201984777210853647235788553225175 : ℚ) / 4267402093301570158289984250927456882017866033922048)

def momentPanelGrowth2622K03P025 : ℚ := ((1904761858425059134148478619149449458136097210284275 : ℚ) / 1624733101450298137880558882470282879413754508869632)

theorem momentPanelPhase_owner2622K03P025 :
    (momentPanelPhase2622K03P025 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-129 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P025, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P025 :
    (momentPanelGrowth2622K03P025 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-129 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P025, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P025Input : RatPair2542 := (momentPanelPhase2622K03P025 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P025Expected : RatState2542 :=
  ((((86311969373655843205630659887117892336215305097443783360243369283646141933 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((6989790742782843668532291 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622K03P025_replay :
    compactExp2620 momentScalarAmp2622K03P025Input 20 = momentScalarAmp2622K03P025Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P025_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-129 / 200) 0) -
      (momentScalarAmp2622K03P025Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P025Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P025 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P025]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P025 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P025 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P025Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P025Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P025_replay] at h
  simpa only [momentPanelPhase_owner2622K03P025] using h

theorem momentScalarAmp2622K03P025_radius_le :
    (momentScalarAmp2622K03P025Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 94 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P025Expected]

def momentScalarGrow2622K03P025Input : RatPair2542 := (momentPanelGrowth2622K03P025 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P025Expected : RatState2542 :=
  ((((3449176022223552827931602486448142768240933924550516699924789507327398380558406103182367423187221 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((8744690332778386999086741515173613494260622385489 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P025_replay :
    compactExp2620 momentScalarGrow2622K03P025Input 20 = momentScalarGrow2622K03P025Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P025_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-129 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P025Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P025Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P025 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P025]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P025 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P025 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P025Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P025Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P025_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P025] using h

theorem momentScalarGrow2622K03P025_radius_le :
    (momentScalarGrow2622K03P025Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P025Expected]

end ConnesWeilRH.Dev
