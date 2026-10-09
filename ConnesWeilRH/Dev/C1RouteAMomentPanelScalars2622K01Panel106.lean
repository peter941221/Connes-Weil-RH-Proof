import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P106 : ℚ := ((-85549546831345165117513897776304339146760645933542801 : ℚ) / 2776781748544080246592948267862465262589452694323200)

def momentPanelGrowth2622K01P106 : ℚ := ((123404601333841235906625623867580935559556618413832411 : ℚ) / 1121620689677483620571146442866548525277235085783859200)

theorem momentPanelPhase_owner2622K01P106 :
    (momentPanelPhase2622K01P106 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (33 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P106, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P106 :
    (momentPanelGrowth2622K01P106 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (33 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P106, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P106Input : RatPair2542 := (momentPanelPhase2622K01P106 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P106Expected : RatState2542 :=
  ((((89016454057111209202948951098569475370852318228687405102618252043486953350961466485 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((112845076942980354122580007026370809 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P106_replay :
    compactExp2620 momentScalarAmp2622K01P106Input 20 = momentScalarAmp2622K01P106Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P106_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (33 / 200) 0) -
      (momentScalarAmp2622K01P106Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P106Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P106 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P106]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P106 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P106 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P106Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P106Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P106_replay] at h
  simpa only [momentPanelPhase_owner2622K01P106] using h

theorem momentScalarAmp2622K01P106_radius_le :
    (momentScalarAmp2622K01P106Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P106Expected]

def momentScalarGrow2622K01P106Input : RatPair2542 := (momentPanelGrowth2622K01P106 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P106Expected : RatState2542 :=
  ((((596102862664065293280480523588396864461972250105605152674872318606591845945582633684743708605487 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3022600289464410238820145938476124065318908472107 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P106_replay :
    compactExp2620 momentScalarGrow2622K01P106Input 20 = momentScalarGrow2622K01P106Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P106_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (33 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P106Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P106Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P106 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P106]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P106 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P106 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P106Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P106Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P106_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P106] using h

theorem momentScalarGrow2622K01P106_radius_le :
    (momentScalarGrow2622K01P106Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P106Expected]

end ConnesWeilRH.Dev
