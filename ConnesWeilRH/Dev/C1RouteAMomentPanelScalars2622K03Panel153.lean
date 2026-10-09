import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P153 : ℚ := ((-72801825013886038860819766007664288630782167266688925 : ℚ) / 1453646066030249315018340026740432998425281905557504)

def momentPanelGrowth2622K03P153 : ℚ := ((4579465580663072347363867243357963000508788221745475 : ℚ) / 4145823425846105671781915218905871088320238145503232)

theorem momentPanelPhase_owner2622K03P153 :
    (momentPanelPhase2622K03P153 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (127 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P153, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P153 :
    (momentPanelGrowth2622K03P153 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (127 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P153, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P153Input : RatPair2542 := (momentPanelPhase2622K03P153 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P153Expected : RatState2542 :=
  ((((189729976589371044150740744001090820590145041595048477673575602122750588517 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((241731732131378144668162483 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K03P153_replay :
    compactExp2620 momentScalarAmp2622K03P153Input 20 = momentScalarAmp2622K03P153Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P153_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (127 / 200) 0) -
      (momentScalarAmp2622K03P153Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P153Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P153 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P153]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P153 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P153 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P153Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P153Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P153_replay] at h
  simpa only [momentPanelPhase_owner2622K03P153] using h

theorem momentScalarAmp2622K03P153_radius_le :
    (momentScalarAmp2622K03P153Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 93 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P153Expected]

def momentScalarGrow2622K03P153Input : RatPair2542 := (momentPanelGrowth2622K03P153 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P153Expected : RatState2542 :=
  ((((6446428163929660621839727438314004379811581078014505580321097794849843540605572112540650169415925 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((8171809922931000310514929933795136465580142930281 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P153_replay :
    compactExp2620 momentScalarGrow2622K03P153Input 20 = momentScalarGrow2622K03P153Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P153_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (127 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P153Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P153Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P153 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P153]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P153 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P153 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P153Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P153Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P153_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P153] using h

theorem momentScalarGrow2622K03P153_radius_le :
    (momentScalarGrow2622K03P153Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P153Expected]

end ConnesWeilRH.Dev
