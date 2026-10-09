import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P002 : ℚ := ((-365840497974861663864021751325830363479473349655 : ℚ) / 2854495385411919762116571938898990272765493248)

def momentPanelGrowth2622K01P002 : ℚ := ((2453522277900002093667917195624687755081203423941171 : ℚ) / 236459261489059903294331527988545106720211546931200)

theorem momentPanelPhase_owner2622K01P002 :
    (momentPanelPhase2622K01P002 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-7 / 8) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P002, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P002 :
    (momentPanelGrowth2622K01P002 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-7 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P002, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P002Input : RatPair2542 := (momentPanelPhase2622K01P002 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P002Expected : RatState2542 :=
  ((((46681463207362187604326800035120899890677 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P002_replay :
    compactExp2620 momentScalarAmp2622K01P002Input 20 = momentScalarAmp2622K01P002Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P002_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-7 / 8) 0) -
      (momentScalarAmp2622K01P002Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P002Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P002 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P002]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P002 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P002 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P002Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P002Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P002_replay] at h
  simpa only [momentPanelPhase_owner2622K01P002] using h

theorem momentScalarAmp2622K01P002_radius_le :
    (momentScalarAmp2622K01P002Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P002Expected]

def momentScalarGrow2622K01P002Input : RatPair2542 := (momentPanelGrowth2622K01P002 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P002Expected : RatState2542 :=
  ((((68529362381560402052283815623977595784495774120901447231185711364296808661658769646181534891092687729 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((10858803466693632567215467701660250974122436219096427 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K01P002_replay :
    compactExp2620 momentScalarGrow2622K01P002Input 20 = momentScalarGrow2622K01P002Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P002_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-7 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P002Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P002Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P002 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P002]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P002 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P002 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P002Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P002Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P002_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P002] using h

theorem momentScalarGrow2622K01P002_radius_le :
    (momentScalarGrow2622K01P002Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 67 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P002Expected]

end ConnesWeilRH.Dev
