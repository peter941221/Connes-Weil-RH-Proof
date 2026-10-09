import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P100 : ℚ := ((-219000607931498756285223059136152489374049712103103925 : ℚ) / 7226942908896648567652446037177929996821129433448448)

def momentPanelGrowth2622K03P100 : ℚ := ((209753234234183584465808702843878623218006260560843475 : ℚ) / 2971556825337951427248770544293556169952430834415828992)

theorem momentPanelPhase_owner2622K03P100 :
    (momentPanelPhase2622K03P100 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (21 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P100, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P100 :
    (momentPanelGrowth2622K03P100 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (21 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P100, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P100Input : RatPair2542 := (momentPanelPhase2622K03P100 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P100Expected : RatState2542 :=
  ((((73788600603449643117764038552390345686255624594319799945391218015057808675997574643 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((5846304193389231724020071959402729 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarAmp2622K03P100_replay :
    compactExp2620 momentScalarAmp2622K03P100Input 20 = momentScalarAmp2622K03P100Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P100_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (21 / 200) 0) -
      (momentScalarAmp2622K03P100Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P100Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P100 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P100]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P100 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P100 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P100Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P100Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P100_replay] at h
  simpa only [momentPanelPhase_owner2622K03P100] using h

theorem momentScalarAmp2622K03P100_radius_le :
    (momentScalarAmp2622K03P100Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P100Expected]

def momentScalarGrow2622K03P100Input : RatPair2542 := (momentPanelGrowth2622K03P100 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P100Expected : RatState2542 :=
  ((((573052166547858339174622443354859692098174068214781416066598824041234360120317699752478673456841 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((726429873985402978019601138999900369272377973121 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K03P100_replay :
    compactExp2620 momentScalarGrow2622K03P100Input 20 = momentScalarGrow2622K03P100Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P100_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (21 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P100Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P100Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P100 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P100]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P100 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P100 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P100Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P100Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P100_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P100] using h

theorem momentScalarGrow2622K03P100_radius_le :
    (momentScalarGrow2622K03P100Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P100Expected]

end ConnesWeilRH.Dev
