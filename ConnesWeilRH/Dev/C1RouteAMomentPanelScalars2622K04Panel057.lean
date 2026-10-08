import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P057 : ℚ := ((-997251035579580775404101940605980252663595146405927 : ℚ) / 27231885976829714530592096297096367202182805585920)

def momentPanelGrowth2622K04P057 : ℚ := ((3899198250676922524886847025343824676648096191820858367 : ℚ) / 11333191753444172654448365208551502428949260418836070400)

theorem momentPanelPhase_owner2622K04P057 :
    (momentPanelPhase2622K04P057 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-13 / 40) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P057, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P057 :
    (momentPanelGrowth2622K04P057 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-13 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P057, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P057Input : RatPair2542 := (momentPanelPhase2622K04P057 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P057Expected : RatState2542 :=
  ((((266333474315699524729634857849946428830690571922912618803903888365955784421129721 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((168814791121421366131451350173335 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P057_replay :
    compactExp2620 momentScalarAmp2622K04P057Input 20 = momentScalarAmp2622K04P057Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P057_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-13 / 40) 0) -
      (momentScalarAmp2622K04P057Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P057Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P057 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P057]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P057 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P057 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P057Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P057Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P057_replay] at h
  simpa only [momentPanelPhase_owner2622K04P057] using h

theorem momentScalarAmp2622K04P057_radius_le :
    (momentScalarAmp2622K04P057Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P057Expected]

def momentScalarGrow2622K04P057Input : RatPair2542 := (momentPanelGrowth2622K04P057 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P057Expected : RatState2542 :=
  ((((3013131954461858048643733566606035603653044285310934216189278580861514872767105901856453135127331 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3819597277381487080491660541869106284858114202913 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P057_replay :
    compactExp2620 momentScalarGrow2622K04P057Input 20 = momentScalarGrow2622K04P057Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P057_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-13 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P057Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P057Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P057 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P057]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P057 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P057 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P057Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P057Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P057_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P057] using h

theorem momentScalarGrow2622K04P057_radius_le :
    (momentScalarGrow2622K04P057Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P057Expected]

end ConnesWeilRH.Dev
