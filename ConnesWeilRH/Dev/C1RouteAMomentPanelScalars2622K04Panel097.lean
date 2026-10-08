import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P097 : ℚ := ((-2675803858826504208023231227781414476892410065970629 : ℚ) / 90830043163807286830549319095765870479397995151360)

def momentPanelGrowth2622K04P097 : ℚ := ((2629466836148551815584896040950995371274160989110269 : ℚ) / 18346840915427302483039948651482425129659293027532800)

theorem momentPanelPhase_owner2622K04P097 :
    (momentPanelPhase2622K04P097 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (3 / 40) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P097, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P097 :
    (momentPanelGrowth2622K04P097 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (3 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P097, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P097Input : RatPair2542 := (momentPanelPhase2622K04P097 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P097Expected : RatState2542 :=
  ((((85794310854265942465039733844239042371805807813520515142607738177218632837813518579 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((435041060793591883048619601374063549 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P097_replay :
    compactExp2620 momentScalarAmp2622K04P097Input 20 = momentScalarAmp2622K04P097Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P097_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (3 / 40) 0) -
      (momentScalarAmp2622K04P097Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P097Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P097 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P097]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P097 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P097 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P097Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P097Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P097_replay] at h
  simpa only [momentPanelPhase_owner2622K04P097] using h

theorem momentScalarAmp2622K04P097_radius_le :
    (momentScalarAmp2622K04P097Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P097Expected]

def momentScalarGrow2622K04P097Input : RatPair2542 := (momentPanelGrowth2622K04P097 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P097Expected : RatState2542 :=
  ((((2465140295121188123267546361047928412980600698789785884442853714065723365455796111470582604175175 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1562468073819686474487900343928638247813951405261 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P097_replay :
    compactExp2620 momentScalarGrow2622K04P097Input 20 = momentScalarGrow2622K04P097Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P097_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (3 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P097Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P097Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P097 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P097]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P097 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P097 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P097Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P097Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P097_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P097] using h

theorem momentScalarGrow2622K04P097_radius_le :
    (momentScalarGrow2622K04P097Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P097Expected]

end ConnesWeilRH.Dev
