import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P020 : ℚ := ((-73334166145793856014283575694343651740064341114779975 : ℚ) / 1259266348265239226897249943989167356811042877341696)

def momentPanelGrowth2622K03P020 : ℚ := ((128115836164012086536916861938856812274641649774875 : ℚ) / 79195119972868301880162171872813586127605844672512)

theorem momentPanelPhase_owner2622K03P020 :
    (momentPanelPhase2622K03P020 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-139 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P020, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P020 :
    (momentPanelGrowth2622K03P020 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-139 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P020, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P020Input : RatPair2542 := (momentPanelPhase2622K03P020 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P020Expected : RatState2542 :=
  ((((27297752437283068064402441427266558786547113803909542256262674776535783 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((2556275375817783673872491 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P020_replay :
    compactExp2620 momentScalarAmp2622K03P020Input 20 = momentScalarAmp2622K03P020Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P020_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-139 / 200) 0) -
      (momentScalarAmp2622K03P020Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P020Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P020 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P020]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P020 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P020 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P020Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P020Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P020_replay] at h
  simpa only [momentPanelPhase_owner2622K03P020] using h

theorem momentScalarAmp2622K03P020_radius_le :
    (momentScalarAmp2622K03P020Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P020Expected]

def momentScalarGrow2622K03P020Input : RatPair2542 := (momentPanelGrowth2622K03P020 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P020Expected : RatState2542 :=
  ((((10768796337382945725171044119683557341377212520572435653332549414224593696020035267153864644497827 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((13651050080212442057585113171869435692626904088249 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P020_replay :
    compactExp2620 momentScalarGrow2622K03P020Input 20 = momentScalarGrow2622K03P020Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P020_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-139 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P020Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P020Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P020 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P020]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P020 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P020 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P020Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P020Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P020_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P020] using h

theorem momentScalarGrow2622K03P020_radius_le :
    (momentScalarGrow2622K03P020Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P020Expected]

end ConnesWeilRH.Dev
