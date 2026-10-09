import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P101 : ℚ := ((-112414011243810233567163963054744751112306388279180131 : ℚ) / 3755659578586462831016773700009401501877559466393600)

def momentPanelGrowth2622K02P101 : ℚ := ((97317912533150030773493850426464206413736948258791 : ℚ) / 846215157005363613479457751286605666361330473369600)

theorem momentPanelPhase_owner2622K02P101 :
    (momentPanelPhase2622K02P101 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (23 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P101, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P101 :
    (momentPanelGrowth2622K02P101 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (23 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P101, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P101Input : RatPair2542 := (momentPanelPhase2622K02P101 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P101Expected : RatState2542 :=
  ((((53491088234234046808089058682084630532958042116474664850104952694739642317254120515 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((271239782935491604071472660673280499 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P101_replay :
    compactExp2620 momentScalarAmp2622K02P101Input 20 = momentScalarAmp2622K02P101Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P101_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (23 / 200) 0) -
      (momentScalarAmp2622K02P101Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P101Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P101 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P101]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P101 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P101 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P101Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P101Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P101_replay] at h
  simpa only [momentPanelPhase_owner2622K02P101] using h

theorem momentScalarAmp2622K02P101_radius_le :
    (momentScalarAmp2622K02P101Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P101Expected]

def momentScalarGrow2622K02P101Input : RatPair2542 := (momentPanelGrowth2622K02P101 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P101Expected : RatState2542 :=
  ((((1198158046961192454372536303614375732454772378392584206294274917179079517078686834337564087735991 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3037691201635079417084620844182709614246536374199 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P101_replay :
    compactExp2620 momentScalarGrow2622K02P101Input 20 = momentScalarGrow2622K02P101Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P101_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (23 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P101Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P101Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P101 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P101]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P101 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P101 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P101Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P101Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P101_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P101] using h

theorem momentScalarGrow2622K02P101_radius_le :
    (momentScalarGrow2622K02P101Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P101Expected]

end ConnesWeilRH.Dev
