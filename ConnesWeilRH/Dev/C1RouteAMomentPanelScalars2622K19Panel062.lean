import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K19
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K19P062 : ℚ := ((-6575548496406633527959369695496516087 : ℚ) / 199984558692005470380119897680117760)

def momentPanelGrowth2622K19P062 : ℚ := ((5840068517794370860529644999864963 : ℚ) / 27381252964929755072328789236121600)

theorem momentPanelPhase_owner2622K19P062 :
    (momentPanelPhase2622K19P062 : ℝ) = momentPhase2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2)) (-11 / 40) 0 := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelPhase2622K19P062, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K19P062 :
    (momentPanelGrowth2622K19P062 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2))
      (-11 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelGrowth2622K19P062, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K19P062Input : RatPair2542 := (momentPanelPhase2622K19P062 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K19P062Expected : RatState2542 :=
  ((((11216929414276836556458773083144077100384206900530061522858250517924738254924821543 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((7109796592533763670742413068155265 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K19P062_replay :
    compactExp2620 momentScalarAmp2622K19P062Input 20 = momentScalarAmp2622K19P062Expected := by
  decide +kernel

theorem momentScalarAmp2622K19P062_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2)) (-11 / 40) 0) -
      (momentScalarAmp2622K19P062Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K19P062Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K19P062 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelPhase2622K19P062]
  have h := compactExp_real_error2620 momentPanelPhase2622K19P062 20 hsmall
  change |Real.exp (momentPanelPhase2622K19P062 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K19P062Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K19P062Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K19P062_replay] at h
  simpa only [momentPanelPhase_owner2622K19P062] using h

theorem momentScalarAmp2622K19P062_radius_le :
    (momentScalarAmp2622K19P062Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentScalarAmp2622K19P062Expected]

def momentScalarGrow2622K19P062Input : RatPair2542 := (momentPanelGrowth2622K19P062 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K19P062Expected : RatState2542 :=
  ((((2643796544734915366033090356436596184609966585222199588827631256934633201391103607401281498525499 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3351409595116150447522136672298750660396030782387 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K19P062_replay :
    compactExp2620 momentScalarGrow2622K19P062Input 20 = momentScalarGrow2622K19P062Expected := by
  decide +kernel

theorem momentScalarGrow2622K19P062_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2)) (-11 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K19P062Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K19P062Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K19P062 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelGrowth2622K19P062]
  have h := compactExp_real_error2620 momentPanelGrowth2622K19P062 20 hsmall
  change |Real.exp (momentPanelGrowth2622K19P062 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K19P062Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K19P062Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K19P062_replay] at h
  simpa only [momentPanelGrowth_owner2622K19P062] using h

theorem momentScalarGrow2622K19P062_radius_le :
    (momentScalarGrow2622K19P062Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentScalarGrow2622K19P062Expected]

end ConnesWeilRH.Dev
