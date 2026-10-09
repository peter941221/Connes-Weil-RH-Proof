import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P108 : ℚ := ((-111399626883135939105217185511753290796524097866218129 : ℚ) / 3675733707794929077677509685720229774240125655449600)

def momentPanelGrowth2622K02P108 : ℚ := ((723071757975612812395995403924135882620962089366041653 : ℚ) / 4420201375860669705408238971044959546975325589916876800)

theorem momentPanelPhase_owner2622K02P108 :
    (momentPanelPhase2622K02P108 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (37 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P108, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P108 :
    (momentPanelGrowth2622K02P108 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (37 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P108, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P108Input : RatPair2542 := (momentPanelPhase2622K02P108 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P108Expected : RatState2542 :=
  ((((36768369164235127951407860609931990856006759364333391513373673853111100015199253561 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((186443169614326064303742073899916075 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P108_replay :
    compactExp2620 momentScalarAmp2622K02P108Input 20 = momentScalarAmp2622K02P108Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P108_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (37 / 200) 0) -
      (momentScalarAmp2622K02P108Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P108Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P108 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P108]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P108 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P108 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P108Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P108Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P108_replay] at h
  simpa only [momentPanelPhase_owner2622K02P108] using h

theorem momentScalarAmp2622K02P108_radius_le :
    (momentScalarAmp2622K02P108Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P108Expected]

def momentScalarGrow2622K02P108Input : RatPair2542 := (momentPanelGrowth2622K02P108 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P108Expected : RatState2542 :=
  ((((628900597864322240670262647831941356047777622562984821026201642276902146719684368488285120527773 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3188904383980289224845791851404276361093313147843 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P108_replay :
    compactExp2620 momentScalarGrow2622K02P108Input 20 = momentScalarGrow2622K02P108Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P108_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (37 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P108Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P108Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P108 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P108]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P108 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P108 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P108Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P108Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P108_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P108] using h

theorem momentScalarGrow2622K02P108_radius_le :
    (momentScalarGrow2622K02P108Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P108Expected]

end ConnesWeilRH.Dev
