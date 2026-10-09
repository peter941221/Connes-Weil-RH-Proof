import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P082 : ℚ := ((-484773 : ℚ) / 15910)

def momentPanelGrowth2622K06P082 : ℚ := ((284797 : ℚ) / 3213675)

theorem momentPanelPhase_owner2622K06P082 :
    (momentPanelPhase2622K06P082 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-3 / 40) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P082, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P082 :
    (momentPanelGrowth2622K06P082 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-3 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P082, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P082Input : RatPair2542 := (momentPanelPhase2622K06P082 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P082Expected : RatState2542 :=
  ((((124960871257169659343000366605310612812054845883916444619570220933510140372978469821 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((158411326533732551794135586474668071 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P082_replay :
    compactExp2620 momentScalarAmp2622K06P082Input 20 = momentScalarAmp2622K06P082Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P082_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-3 / 40) 0) -
      (momentScalarAmp2622K06P082Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P082Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P082 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P082]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P082 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P082 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P082Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P082Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P082_replay] at h
  simpa only [momentPanelPhase_owner2622K06P082] using h

theorem momentScalarAmp2622K06P082_radius_le :
    (momentScalarAmp2622K06P082Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P082Expected]

def momentScalarGrow2622K06P082Input : RatPair2542 := (momentPanelGrowth2622K06P082 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P082Expected : RatState2542 :=
  ((((2333919867843567129374288489917787071217351205848948745226829845435496759242416471937975740367883 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2958594671310994323361123302049045129152186523629 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P082_replay :
    compactExp2620 momentScalarGrow2622K06P082Input 20 = momentScalarGrow2622K06P082Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P082_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-3 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P082Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P082Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P082 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P082]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P082 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P082 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P082Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P082Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P082_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P082] using h

theorem momentScalarGrow2622K06P082_radius_le :
    (momentScalarGrow2622K06P082Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P082Expected]

end ConnesWeilRH.Dev
