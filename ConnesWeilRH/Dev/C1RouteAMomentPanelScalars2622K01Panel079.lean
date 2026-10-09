import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P079 : ℚ := ((-85690056887140359139972991325997698248691479556315747 : ℚ) / 2823024573787753346739236733272628905008253684940800)

def momentPanelGrowth2622K01P079 : ℚ := ((80660059244657983100426161906056247322457846017964331 : ℚ) / 1160764384897637276269050993864670378887668294693683200)

theorem momentPanelPhase_owner2622K01P079 :
    (momentPanelPhase2622K01P079 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-21 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P079, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P079 :
    (momentPanelGrowth2622K01P079 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-21 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P079, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P079Input : RatPair2542 := (momentPanelPhase2622K01P079 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P079Expected : RatState2542 :=
  ((((35072658813448201164586383338258098510774262770857956755874772556896690729982874119 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((177844656128817379641013030486224713 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P079_replay :
    compactExp2620 momentScalarAmp2622K01P079Input 20 = momentScalarAmp2622K01P079Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P079_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-21 / 200) 0) -
      (momentScalarAmp2622K01P079Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P079Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P079 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P079]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P079 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P079 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P079Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P079Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P079_replay] at h
  simpa only [momentPanelPhase_owner2622K01P079] using h

theorem momentScalarAmp2622K01P079_radius_le :
    (momentScalarAmp2622K01P079Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P079Expected]

def momentScalarGrow2622K01P079Input : RatPair2542 := (momentPanelGrowth2622K01P079 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P079Expected : RatState2542 :=
  ((((2289692652792039983436472832375126569740099281289208216822793548875102746665113085981251130982765 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1451265036650197305176265140361773379588775076303 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K01P079_replay :
    compactExp2620 momentScalarGrow2622K01P079Input 20 = momentScalarGrow2622K01P079Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P079_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-21 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P079Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P079Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P079 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P079]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P079 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P079 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P079Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P079Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P079_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P079] using h

theorem momentScalarGrow2622K01P079_radius_le :
    (momentScalarGrow2622K01P079Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P079Expected]

end ConnesWeilRH.Dev
