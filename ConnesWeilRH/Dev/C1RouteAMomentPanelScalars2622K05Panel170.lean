import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P170 : ℚ := ((-800483176286044706935781978052381961003 : ℚ) / 9518534826993728929958445028527308800)

def momentPanelGrowth2622K05P170 : ℚ := ((49455510713224339993275567682960935239169 : ℚ) / 11993719979505444364398792983830121676800)

theorem momentPanelPhase_owner2622K05P170 :
    (momentPanelPhase2622K05P170 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (161 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P170, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P170 :
    (momentPanelGrowth2622K05P170 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (161 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P170, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P170Input : RatPair2542 := (momentPanelPhase2622K05P170 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P170Expected : RatState2542 :=
  ((((40038781652545497828714501925872297661807645469995775067013 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((2417851639230070500162961 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P170_replay :
    compactExp2620 momentScalarAmp2622K05P170Input 20 = momentScalarAmp2622K05P170Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P170_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (161 / 200) 0) -
      (momentScalarAmp2622K05P170Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P170Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P170 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P170]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P170 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P170 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P170Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P170Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P170_replay] at h
  simpa only [momentPanelPhase_owner2622K05P170] using h

theorem momentScalarAmp2622K05P170_radius_le :
    (momentScalarAmp2622K05P170Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P170Expected]

def momentScalarGrow2622K05P170Input : RatPair2542 := (momentPanelGrowth2622K05P170 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P170Expected : RatState2542 :=
  ((((131944233169518391438932584719212050297394427644938734769645157571373467374697061093872101364655201 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((167258528640438083230751266599631264929327617239903 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P170_replay :
    compactExp2620 momentScalarGrow2622K05P170Input 20 = momentScalarGrow2622K05P170Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P170_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (161 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P170Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P170Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P170 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P170]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P170 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P170 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P170Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P170Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P170_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P170] using h

theorem momentScalarGrow2622K05P170_radius_le :
    (momentScalarGrow2622K05P170Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P170Expected]

end ConnesWeilRH.Dev
