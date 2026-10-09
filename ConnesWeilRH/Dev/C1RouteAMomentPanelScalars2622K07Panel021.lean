import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P021 : ℚ := ((-35627168328457061591606665912999110175 : ℚ) / 574154451060171486361098789404540928)

def momentPanelGrowth2622K07P021 : ℚ := ((1769273968473265329566219339847187560075 : ℚ) / 1113387501125978879956403007329373519872)

theorem momentPanelPhase_owner2622K07P021 :
    (momentPanelPhase2622K07P021 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-137 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P021, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P021 :
    (momentPanelGrowth2622K07P021 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-137 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P021, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P021Input : RatPair2542 := (momentPanelPhase2622K07P021 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P021Expected : RatState2542 :=
  ((((2404123990789462090344677809800435633036601954988037719453496832941407 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2420899408801771809430243 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P021_replay :
    compactExp2620 momentScalarAmp2622K07P021Input 20 = momentScalarAmp2622K07P021Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P021_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-137 / 200) 0) -
      (momentScalarAmp2622K07P021Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P021Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P021 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P021]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P021 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P021 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P021Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P021Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P021_replay] at h
  simpa only [momentPanelPhase_owner2622K07P021] using h

theorem momentScalarAmp2622K07P021_radius_le :
    (momentScalarAmp2622K07P021Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P021Expected]

def momentScalarGrow2622K07P021Input : RatPair2542 := (momentPanelGrowth2622K07P021 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P021Expected : RatState2542 :=
  ((((10464826448303061868950089572345000603932977373584657592308709642611749512129858253670391344430949 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((13265723424585575224080364394731186496670364540865 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P021_replay :
    compactExp2620 momentScalarGrow2622K07P021Input 20 = momentScalarGrow2622K07P021Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P021_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-137 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P021Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P021Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P021 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P021]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P021 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P021 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P021Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P021Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P021_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P021] using h

theorem momentScalarGrow2622K07P021_radius_le :
    (momentScalarGrow2622K07P021Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P021Expected]

end ConnesWeilRH.Dev
