import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P104 : ℚ := ((-805879039609259401312494141613037593207 : ℚ) / 26474629255646525404378347103636684800)

def momentPanelGrowth2622K05P104 : ℚ := ((16791255910810961717660284108536347409 : ℚ) / 155039753130793551304173986192870604800)

theorem momentPanelPhase_owner2622K05P104 :
    (momentPanelPhase2622K05P104 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (29 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P104, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P104 :
    (momentPanelGrowth2622K05P104 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (29 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P104, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P104Input : RatPair2542 := (momentPanelPhase2622K05P104 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P104Expected : RatState2542 :=
  ((((128770650165696961931477509175160206175573887014731848806458787806684986450384735395 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((40810232679015126787048970746743993 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K05P104_replay :
    compactExp2620 momentScalarAmp2622K05P104Input 20 = momentScalarAmp2622K05P104Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P104_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (29 / 200) 0) -
      (momentScalarAmp2622K05P104Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P104Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P104 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P104]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P104 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P104 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P104Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P104Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P104_replay] at h
  simpa only [momentPanelPhase_owner2622K05P104] using h

theorem momentScalarAmp2622K05P104_radius_le :
    (momentScalarAmp2622K05P104Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P104Expected]

def momentScalarGrow2622K05P104Input : RatPair2542 := (momentPanelGrowth2622K05P104 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P104Expected : RatState2542 :=
  ((((148769527801824311439675418622401547042680187870493926193806984577582455876568446536067430988883 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((3017404187763724433043278263039407113607907728077 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P104_replay :
    compactExp2620 momentScalarGrow2622K05P104Input 20 = momentScalarGrow2622K05P104Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P104_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (29 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P104Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P104Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P104 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P104]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P104 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P104 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P104Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P104Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P104_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P104] using h

theorem momentScalarGrow2622K05P104_radius_le :
    (momentScalarGrow2622K05P104Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P104Expected]

end ConnesWeilRH.Dev
