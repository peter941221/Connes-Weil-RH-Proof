import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P029 : ℚ := ((-21022813 : ℚ) / 422650)

def momentPanelGrowth2622K06P029 : ℚ := ((318141947 : ℚ) / 328548675)

theorem momentPanelPhase_owner2622K06P029 :
    (momentPanelPhase2622K06P029 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-121 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P029, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P029 :
    (momentPanelGrowth2622K06P029 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-121 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P029, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P029Input : RatPair2542 := (momentPanelPhase2622K06P029 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P029Expected : RatState2542 :=
  ((((534051964906192451707852492301494939706347616500924384260954471542637582937 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((679441260172844111773192251 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P029_replay :
    compactExp2620 momentScalarAmp2622K06P029Input 20 = momentScalarAmp2622K06P029Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P029_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-121 / 200) 0) -
      (momentScalarAmp2622K06P029Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P029Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P029 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P029]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P029 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P029 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P029Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P029Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P029_replay] at h
  simpa only [momentPanelPhase_owner2622K06P029] using h

theorem momentScalarAmp2622K06P029_radius_le :
    (momentScalarAmp2622K06P029Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 93 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P029Expected]

def momentScalarGrow2622K06P029Input : RatPair2542 := (momentPanelGrowth2622K06P029 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P029Expected : RatState2542 :=
  ((((2812592982072332895139888491540322958226008179412937746270714192904568354501787672838302394765627 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((7130763778816525037980375224427253840680472236159 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P029_replay :
    compactExp2620 momentScalarGrow2622K06P029Input 20 = momentScalarGrow2622K06P029Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P029_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-121 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P029Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P029Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P029 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P029]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P029 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P029 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P029Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P029Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P029_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P029] using h

theorem momentScalarGrow2622K06P029_radius_le :
    (momentScalarGrow2622K06P029Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P029Expected]

end ConnesWeilRH.Dev
