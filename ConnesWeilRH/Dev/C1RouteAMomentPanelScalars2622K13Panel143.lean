import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K13
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K13P143 : ℚ := ((-795301955148390673174721275006107805289 : ℚ) / 19302769219795294742470599048901427200)

def momentPanelGrowth2622K13P143 : ℚ := ((2102857103942353139090829283151408311729 : ℚ) / 3180729052984342441807777038538165452800)

theorem momentPanelPhase_owner2622K13P143 :
    (momentPanelPhase2622K13P143 : ℝ) = momentPhase2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2)) (107 / 200) 0 := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelPhase2622K13P143, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K13P143 :
    (momentPanelGrowth2622K13P143 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2))
      (107 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelGrowth2622K13P143, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K13P143Input : RatPair2542 := (momentPanelPhase2622K13P143 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K13P143Expected : RatState2542 :=
  ((((2729223233436612890675180756470393490237696558856354789453778764213937486948473 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1729919915879681109694223006875 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K13P143_replay :
    compactExp2620 momentScalarAmp2622K13P143Input 20 = momentScalarAmp2622K13P143Expected := by
  decide +kernel

theorem momentScalarAmp2622K13P143_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2)) (107 / 200) 0) -
      (momentScalarAmp2622K13P143Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K13P143Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K13P143 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelPhase2622K13P143]
  have h := compactExp_real_error2620 momentPanelPhase2622K13P143 20 hsmall
  change |Real.exp (momentPanelPhase2622K13P143 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K13P143Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K13P143Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K13P143_replay] at h
  simpa only [momentPanelPhase_owner2622K13P143] using h

theorem momentScalarAmp2622K13P143_radius_le :
    (momentScalarAmp2622K13P143Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentScalarAmp2622K13P143Expected]

def momentScalarGrow2622K13P143Input : RatPair2542 := (momentPanelGrowth2622K13P143 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K13P143Expected : RatState2542 :=
  ((((4137340127067839301006794781005655789934636741722050007592580163436113993542938775401070565566817 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5244698388657112956114166719028706159755618255407 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K13P143_replay :
    compactExp2620 momentScalarGrow2622K13P143Input 20 = momentScalarGrow2622K13P143Expected := by
  decide +kernel

theorem momentScalarGrow2622K13P143_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2)) (107 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K13P143Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K13P143Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K13P143 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelGrowth2622K13P143]
  have h := compactExp_real_error2620 momentPanelGrowth2622K13P143 20 hsmall
  change |Real.exp (momentPanelGrowth2622K13P143 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K13P143Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K13P143Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K13P143_replay] at h
  simpa only [momentPanelGrowth_owner2622K13P143] using h

theorem momentScalarGrow2622K13P143_radius_le :
    (momentScalarGrow2622K13P143Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentScalarGrow2622K13P143Expected]

end ConnesWeilRH.Dev
