import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P074 : ℚ := ((-28571756447476849379695390589994512209675568017477019 : ℚ) / 928638711259132796610573766022314010487434090905600)

def momentPanelGrowth2622K01P074 : ℚ := ((454228834479375198734383057967888676994730987882171 : ℚ) / 4411158762653992555389817988628318380639745422131200)

theorem momentPanelPhase_owner2622K01P074 :
    (momentPanelPhase2622K01P074 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-31 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P074, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P074 :
    (momentPanelGrowth2622K01P074 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-31 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P074, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P074Input : RatPair2542 := (momentPanelPhase2622K01P074 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P074Expected : RatState2542 :=
  ((((92791099971275331039070817748927082768382451617501928041091610635339132159288413087 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((58815072517065565314604491183257417 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K01P074_replay :
    compactExp2620 momentScalarAmp2622K01P074Input 20 = momentScalarAmp2622K01P074Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P074_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-31 / 200) 0) -
      (momentScalarAmp2622K01P074Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P074Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P074 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P074]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P074 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P074 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P074Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P074Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P074_replay] at h
  simpa only [momentPanelPhase_owner2622K01P074] using h

theorem momentScalarAmp2622K01P074_radius_le :
    (momentScalarAmp2622K01P074Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P074Expected]

def momentScalarGrow2622K01P074Input : RatPair2542 := (momentPanelGrowth2622K01P074 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P074Expected : RatState2542 :=
  ((((1183829295549851301667958154042172742657558523632319133122149232974293331714955346006421269183939 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3001363539401947472545490083657874352453345327455 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P074_replay :
    compactExp2620 momentScalarGrow2622K01P074Input 20 = momentScalarGrow2622K01P074Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P074_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-31 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P074Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P074Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P074 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P074]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P074 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P074 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P074Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P074Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P074_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P074] using h

theorem momentScalarGrow2622K01P074_radius_le :
    (momentScalarGrow2622K01P074Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P074Expected]

end ConnesWeilRH.Dev
