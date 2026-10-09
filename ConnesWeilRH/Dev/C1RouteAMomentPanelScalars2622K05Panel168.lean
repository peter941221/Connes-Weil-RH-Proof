import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P168 : ℚ := ((-799799154910376681780546577269578471159 : ℚ) / 10378508994188559755933808483054387200)

def momentPanelGrowth2622K05P168 : ℚ := ((16090510046588006962682951686151517999403 : ℚ) / 4776534842912933314594650006646004121600)

theorem momentPanelPhase_owner2622K05P168 :
    (momentPanelPhase2622K05P168 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (157 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P168, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P168 :
    (momentPanelGrowth2622K05P168 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (157 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P168, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P168Input : RatPair2542 := (momentPanelPhase2622K05P168 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P168Expected : RatState2542 :=
  ((((727039634941783798261518855603312681238848446973026586769671753 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851640150958404271203 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P168_replay :
    compactExp2620 momentScalarAmp2622K05P168Input 20 = momentScalarAmp2622K05P168Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P168_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (157 / 200) 0) -
      (momentScalarAmp2622K05P168Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P168Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P168 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P168]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P168 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P168 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P168Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P168Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P168_replay] at h
  simpa only [momentPanelPhase_owner2622K05P168] using h

theorem momentScalarAmp2622K05P168_radius_le :
    (momentScalarAmp2622K05P168Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P168Expected]

def momentScalarGrow2622K05P168Input : RatPair2542 := (momentPanelGrowth2622K05P168 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P168Expected : RatState2542 :=
  ((((62028029879641659313416107423549416012049321903830758150850414941886506699036981274020166617076989 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((39314808350909911873069808897824235936625376743881 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P168_replay :
    compactExp2620 momentScalarGrow2622K05P168Input 20 = momentScalarGrow2622K05P168Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P168_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (157 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P168Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P168Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P168 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P168]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P168 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P168 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P168Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P168Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P168_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P168] using h

theorem momentScalarGrow2622K05P168_radius_le :
    (momentScalarGrow2622K05P168Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P168Expected]

end ConnesWeilRH.Dev
