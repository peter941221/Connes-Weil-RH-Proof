import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K22
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K22P019 : ℚ := ((-2478445583475624611166342429360661106451 : ℚ) / 40806179881586795725939474862335590400)

def momentPanelGrowth2622K22P019 : ℚ := ((14529262187495096564956744730478882631763 : ℚ) / 8312975781405638569714092740875753881600)

theorem momentPanelPhase_owner2622K22P019 :
    (momentPanelPhase2622K22P019 : ℝ) = momentPhase2619 ((capturedNodes2584 22).re * (storedWidth 22 ^ 2)) (-141 / 200) 0 := by
  norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, momentPanelPhase2622K22P019, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K22P019 :
    (momentPanelGrowth2622K22P019 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 22).re * (storedWidth 22 ^ 2))
      (-141 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, momentPanelGrowth2622K22P019, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K22P019Input : RatPair2542 := (momentPanelPhase2622K22P019 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K22P019Expected : RatState2542 :=
  ((((559407021915322014743134999561204591182253607882727393750140125842191 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((303649802350932620928475 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K22P019_replay :
    compactExp2620 momentScalarAmp2622K22P019Input 20 = momentScalarAmp2622K22P019Expected := by
  decide +kernel

theorem momentScalarAmp2622K22P019_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 22).re * (storedWidth 22 ^ 2)) (-141 / 200) 0) -
      (momentScalarAmp2622K22P019Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K22P019Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K22P019 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, momentPanelPhase2622K22P019]
  have h := compactExp_real_error2620 momentPanelPhase2622K22P019 20 hsmall
  change |Real.exp (momentPanelPhase2622K22P019 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K22P019Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K22P019Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K22P019_replay] at h
  simpa only [momentPanelPhase_owner2622K22P019] using h

theorem momentScalarAmp2622K22P019_radius_le :
    (momentScalarAmp2622K22P019Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, momentScalarAmp2622K22P019Expected]

def momentScalarGrow2622K22P019Input : RatPair2542 := (momentPanelGrowth2622K22P019 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K22P019Expected : RatState2542 :=
  ((((12264513113098553201337027240300950607779113416443434952423434663884172447967439561798443943595223 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((15547091495195440449019828275473047288101359806505 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K22P019_replay :
    compactExp2620 momentScalarGrow2622K22P019Input 20 = momentScalarGrow2622K22P019Expected := by
  decide +kernel

theorem momentScalarGrow2622K22P019_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 22).re * (storedWidth 22 ^ 2)) (-141 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K22P019Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K22P019Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K22P019 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, momentPanelGrowth2622K22P019]
  have h := compactExp_real_error2620 momentPanelGrowth2622K22P019 20 hsmall
  change |Real.exp (momentPanelGrowth2622K22P019 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K22P019Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K22P019Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K22P019_replay] at h
  simpa only [momentPanelGrowth_owner2622K22P019] using h

theorem momentScalarGrow2622K22P019_radius_le :
    (momentScalarGrow2622K22P019Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, momentScalarGrow2622K22P019Expected]

end ConnesWeilRH.Dev
