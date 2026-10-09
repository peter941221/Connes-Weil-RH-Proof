import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P044 : ℚ := ((-825065870681537582857414158381992793727 : ℚ) / 21444591673940911139239428784704716800)

def momentPanelGrowth2622K05P044 : ℚ := ((601651609947925983528064538526207777283 : ℚ) / 1313232273450995983023961060553628057600)

theorem momentPanelPhase_owner2622K05P044 :
    (momentPanelPhase2622K05P044 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-91 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P044, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P044 :
    (momentPanelGrowth2622K05P044 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-91 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P044, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P044Input : RatPair2542 := (momentPanelPhase2622K05P044 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P044Expected : RatState2542 :=
  ((((41727083204632902246206501713447221065285231596995630090825910009460711368409315 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((26448652679084384890271279184289 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K05P044_replay :
    compactExp2620 momentScalarAmp2622K05P044Input 20 = momentScalarAmp2622K05P044Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P044_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-91 / 200) 0) -
      (momentScalarAmp2622K05P044Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P044Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P044 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P044]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P044 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P044 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P044Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P044Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P044_replay] at h
  simpa only [momentPanelPhase_owner2622K05P044] using h

theorem momentScalarAmp2622K05P044_radius_le :
    (momentScalarAmp2622K05P044Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P044Expected]

def momentScalarGrow2622K05P044Input : RatPair2542 := (momentPanelGrowth2622K05P044 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P044Expected : RatState2542 :=
  ((((3377292890355443974373253665004646175933415644753054008469694307618998822745396738335158225137035 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4281225489044849009226926615975558703916952573453 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P044_replay :
    compactExp2620 momentScalarGrow2622K05P044Input 20 = momentScalarGrow2622K05P044Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P044_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-91 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P044Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P044Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P044 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P044]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P044 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P044 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P044Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P044Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P044_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P044] using h

theorem momentScalarGrow2622K05P044_radius_le :
    (momentScalarGrow2622K05P044Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P044Expected]

end ConnesWeilRH.Dev
