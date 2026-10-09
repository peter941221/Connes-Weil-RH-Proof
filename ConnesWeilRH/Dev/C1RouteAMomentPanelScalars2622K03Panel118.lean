import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P118 : ℚ := ((-218658795054185666805573036743821129373509194345491025 : ℚ) / 6713955834193501643362952660894514656921897110863872)

def momentPanelGrowth2622K03P118 : ℚ := ((537355580451294664999860646638992799286602459890007475 : ℚ) / 2554195802765365480897344266614767228029286178118172672)

theorem momentPanelPhase_owner2622K03P118 :
    (momentPanelPhase2622K03P118 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (57 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P118, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P118 :
    (momentPanelGrowth2622K03P118 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (57 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P118, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P118Input : RatPair2542 := (momentPanelPhase2622K03P118 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P118Expected : RatState2542 :=
  ((((7665689450135329074254687506869869831564183325453269460475181275073509902145940713 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((19435435304996112701196138542452875 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P118_replay :
    compactExp2620 momentScalarAmp2622K03P118Input 20 = momentScalarAmp2622K03P118Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P118_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (57 / 200) 0) -
      (momentScalarAmp2622K03P118Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P118Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P118 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P118]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P118 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P118 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P118Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P118Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P118_replay] at h
  simpa only [momentPanelPhase_owner2622K03P118] using h

theorem momentScalarAmp2622K03P118_radius_le :
    (momentScalarAmp2622K03P118Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P118Expected]

def momentScalarGrow2622K03P118Input : RatPair2542 := (momentPanelGrowth2622K03P118 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P118Expected : RatState2542 :=
  ((((329515733761936958480233064440062666564094268902593143036358055563368755554489490232499300822491 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((1670842935521506948468188810744718307436675170583 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K03P118_replay :
    compactExp2620 momentScalarGrow2622K03P118Input 20 = momentScalarGrow2622K03P118Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P118_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (57 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P118Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P118Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P118 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P118]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P118 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P118 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P118Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P118Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P118_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P118] using h

theorem momentScalarGrow2622K03P118_radius_le :
    (momentScalarGrow2622K03P118Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P118Expected]

end ConnesWeilRH.Dev
