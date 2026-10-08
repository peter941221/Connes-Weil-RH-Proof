import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P003 : ℚ := ((-122029362009852873722068984259726168043447141801519047 : ℚ) / 958254100882781464142533199888391034567376083353600)

def momentPanelGrowth2622K04P003 : ℚ := ((7530109091418397550958064518822390261794315540531902047 : ℚ) / 843469275169366617264289714909981782668443707139686400)

theorem momentPanelPhase_owner2622K04P003 :
    (momentPanelPhase2622K04P003 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-173 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P003, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P003 :
    (momentPanelGrowth2622K04P003 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-173 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P003, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P003Input : RatPair2542 := (momentPanelPhase2622K04P003 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P003Expected : RatState2542 :=
  ((((105716831535378700089142003095288409002217 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P003_replay :
    compactExp2620 momentScalarAmp2622K04P003Input 20 = momentScalarAmp2622K04P003Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P003_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-173 / 200) 0) -
      (momentScalarAmp2622K04P003Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P003Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P003 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P003]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P003 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P003 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P003Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P003Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P003_replay] at h
  simpa only [momentPanelPhase_owner2622K04P003] using h

theorem momentScalarAmp2622K04P003_radius_le :
    (momentScalarAmp2622K04P003Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P003Expected]

def momentScalarGrow2622K04P003Input : RatPair2542 := (momentPanelGrowth2622K04P003 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P003Expected : RatState2542 :=
  ((((8049181598590019216954613965008566093662150159811160964800301363515816687974044282049658112969202359 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((20406926024912956369792968035248496002011545255606325 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P003_replay :
    compactExp2620 momentScalarGrow2622K04P003Input 20 = momentScalarGrow2622K04P003Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P003_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-173 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P003Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P003Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P003 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P003]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P003 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P003 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P003Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P003Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P003_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P003] using h

theorem momentScalarGrow2622K04P003_radius_le :
    (momentScalarGrow2622K04P003Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 68 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P003Expected]

end ConnesWeilRH.Dev
