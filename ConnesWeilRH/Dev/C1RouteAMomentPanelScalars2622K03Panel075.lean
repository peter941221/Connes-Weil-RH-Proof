import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P075 : ℚ := ((-73177440933572762266549785678006450780374452052534225 : ℚ) / 2384622609010034473914087265180705281946110935433216)

def momentPanelGrowth2622K03P075 : ℚ := ((1356691571200554276941969106544755858010824337980825 : ℚ) / 13964739488549110564868596306906129020501163943919616)

theorem momentPanelPhase_owner2622K03P075 :
    (momentPanelPhase2622K03P075 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-29 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P075, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P075 :
    (momentPanelGrowth2622K03P075 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-29 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P075, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P075Input : RatPair2542 := (momentPanelPhase2622K03P075 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P075Expected : RatState2542 :=
  ((((100532823515373888594915947046185502196859781000968104475388095373963276022312841771 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((63722111876632221051544696864583795 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K03P075_replay :
    compactExp2620 momentScalarAmp2622K03P075Input 20 = momentScalarAmp2622K03P075Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P075_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-29 / 200) 0) -
      (momentScalarAmp2622K03P075Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P075Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P075 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P075]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P075 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P075 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P075Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P075Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P075_replay] at h
  simpa only [momentPanelPhase_owner2622K03P075] using h

theorem momentScalarAmp2622K03P075_radius_le :
    (momentScalarAmp2622K03P075Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P075Expected]

def momentScalarGrow2622K03P075Input : RatPair2542 := (momentPanelGrowth2622K03P075 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P075Expected : RatState2542 :=
  ((((588478855321177615100574575037923152519034417549400961834963457213102503633697657169134328959265 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((2983942020213928882006397793588305584068631772571 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P075_replay :
    compactExp2620 momentScalarGrow2622K03P075Input 20 = momentScalarGrow2622K03P075Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P075_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-29 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P075Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P075Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P075 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P075]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P075 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P075 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P075Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P075Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P075_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P075] using h

theorem momentScalarGrow2622K03P075_radius_le :
    (momentScalarGrow2622K03P075Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P075Expected]

end ConnesWeilRH.Dev
