import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P076 : ℚ := ((-348726637669931561533303979853488861768372097316464243 : ℚ) / 11209888828051150097807989661250224700177368534220800)

def momentPanelGrowth2622K02P076 : ℚ := ((36661686079264596060072356575845349898971652456734093 : ℚ) / 285801640546982536514314273038562217726694948392140800)

theorem momentPanelPhase_owner2622K02P076 :
    (momentPanelPhase2622K02P076 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-27 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P076, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P076 :
    (momentPanelGrowth2622K02P076 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-27 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P076, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P076Input : RatPair2542 := (momentPanelPhase2622K02P076 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P076Expected : RatState2542 :=
  ((((65947915632851185294827062462925220933088258430861735211754654695342954149134260965 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((41800697531330410862794450681101971 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P076_replay :
    compactExp2620 momentScalarAmp2622K02P076Input 20 = momentScalarAmp2622K02P076Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P076_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-27 / 200) 0) -
      (momentScalarAmp2622K02P076Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P076Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P076 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P076]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P076 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P076 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P076Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P076Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P076_replay] at h
  simpa only [momentPanelPhase_owner2622K02P076] using h

theorem momentScalarAmp2622K02P076_radius_le :
    (momentScalarAmp2622K02P076Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P076Expected]

def momentScalarGrow2622K02P076Input : RatPair2542 := (momentPanelGrowth2622K02P076 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P076Expected : RatState2542 :=
  ((((1214167131078504940981316857207004563375721486317683774837952214997362838860824690713861315029071 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3078279008399356872286337533010969670220950388809 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P076_replay :
    compactExp2620 momentScalarGrow2622K02P076Input 20 = momentScalarGrow2622K02P076Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P076_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-27 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P076Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P076Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P076 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P076]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P076 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P076 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P076Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P076Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P076_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P076] using h

theorem momentScalarGrow2622K02P076_radius_le :
    (momentScalarGrow2622K02P076Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P076Expected]

end ConnesWeilRH.Dev
