import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P067 : ℚ := ((-8787493496721960346618101364293573429103148816146875 : ℚ) / 277502623388205191593924657612004238357170191597568)

def momentPanelGrowth2622K03P067 : ℚ := ((428266876685936846336639483261262624423750630428013475 : ℚ) / 2731176343537951169777219481432545520294521329409851392)

theorem momentPanelPhase_owner2622K03P067 :
    (momentPanelPhase2622K03P067 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-9 / 40) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P067, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P067 :
    (momentPanelGrowth2622K03P067 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-9 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P067, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P067Input : RatPair2542 := (momentPanelPhase2622K03P067 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P067Expected : RatState2542 :=
  ((((9441048243004826022477314058424826163422606958103039529373235998354137213632560585 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((47873247611043706160378255669460907 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P067_replay :
    compactExp2620 momentScalarAmp2622K03P067Input 20 = momentScalarAmp2622K03P067Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P067_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-9 / 40) 0) -
      (momentScalarAmp2622K03P067Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P067Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P067 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P067]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P067 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P067 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P067Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P067Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P067_replay] at h
  simpa only [momentPanelPhase_owner2622K03P067] using h

theorem momentScalarAmp2622K03P067_radius_le :
    (momentScalarAmp2622K03P067Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P067Expected]

def momentScalarGrow2622K03P067Input : RatPair2542 := (momentPanelGrowth2622K03P067 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P067Expected : RatState2542 :=
  ((((1249306275610764162187082165495331508266134929296817082381995348419148805387435185778909004770287 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3167367226637497456842616162245747680717378143265 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P067_replay :
    compactExp2620 momentScalarGrow2622K03P067Input 20 = momentScalarGrow2622K03P067Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P067_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-9 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P067Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P067Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P067 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P067]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P067 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P067 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P067Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P067Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P067_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P067] using h

theorem momentScalarGrow2622K03P067_radius_le :
    (momentScalarGrow2622K03P067Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P067Expected]

end ConnesWeilRH.Dev
