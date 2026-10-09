import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P127 : ℚ := ((-69928992789708695338911921292353684545368579112223 : ℚ) / 2009564751329991512530066644984889152026907246592)

def momentPanelGrowth2622K03P127 : ℚ := ((43800729517045623908603021148495072864180682134786475 : ℚ) / 139309148600301334804554197760589515453650019551281152)

theorem momentPanelPhase_owner2622K03P127 :
    (momentPanelPhase2622K03P127 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (3 / 8) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P127, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P127 :
    (momentPanelGrowth2622K03P127 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (3 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P127, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P127Input : RatPair2542 := (momentPanelPhase2622K03P127 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P127Expected : RatState2542 :=
  ((((412026330149002511325822482543338574561145647914797654374181732520112127629934665 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((2089291035443753575489401308455137 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P127_replay :
    compactExp2620 momentScalarAmp2622K03P127Input 20 = momentScalarAmp2622K03P127Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P127_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (3 / 8) 0) -
      (momentScalarAmp2622K03P127Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P127Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P127 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P127]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P127 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P127 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P127Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P127Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P127_replay] at h
  simpa only [momentPanelPhase_owner2622K03P127] using h

theorem momentScalarAmp2622K03P127_radius_le :
    (momentScalarAmp2622K03P127Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P127Expected]

def momentScalarGrow2622K03P127Input : RatPair2542 := (momentPanelGrowth2622K03P127 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P127Expected : RatState2542 :=
  ((((2925141129095343101406011349771077538887860363862752128956971698774999796277499609137107183215801 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3708055796195082604191785979275743046023056177733 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P127_replay :
    compactExp2620 momentScalarGrow2622K03P127Input 20 = momentScalarGrow2622K03P127Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P127_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (3 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P127Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P127Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P127 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P127]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P127 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P127 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P127Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P127Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P127_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P127] using h

theorem momentScalarGrow2622K03P127_radius_le :
    (momentScalarGrow2622K03P127Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P127Expected]

end ConnesWeilRH.Dev
