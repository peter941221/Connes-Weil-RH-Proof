import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P021 : ℚ := ((-825171859933947771875316773207447698861 : ℚ) / 14353861276504287159027469735113523200)

def momentPanelGrowth2622K05P021 : ℚ := ((42377390989956203201179267538593041854769 : ℚ) / 27834687528149471998910075183234337996800)

theorem momentPanelPhase_owner2622K05P021 :
    (momentPanelPhase2622K05P021 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-137 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P021, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P021 :
    (momentPanelGrowth2622K05P021 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-137 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P021, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P021Input : RatPair2542 := (momentPanelPhase2622K05P021 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P021Expected : RatState2542 :=
  ((((57664125079386346900933417807469070785471277680659130381803563152942609 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((338782440127619703301449 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K05P021_replay :
    compactExp2620 momentScalarAmp2622K05P021Input 20 = momentScalarAmp2622K05P021Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P021_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-137 / 200) 0) -
      (momentScalarAmp2622K05P021Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P021Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P021 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P021]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P021 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P021 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P021Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P021Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P021_replay] at h
  simpa only [momentPanelPhase_owner2622K05P021] using h

theorem momentScalarAmp2622K05P021_radius_le :
    (momentScalarAmp2622K05P021Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P021Expected]

def momentScalarGrow2622K05P021Input : RatPair2542 := (momentPanelGrowth2622K05P021 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P021Expected : RatState2542 :=
  ((((4895167975810238957193375423628081518017630431058150129699900192447444366927791353590726732616741 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((6205353612961088608007506191061514442776642621703 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P021_replay :
    compactExp2620 momentScalarGrow2622K05P021Input 20 = momentScalarGrow2622K05P021Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P021_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-137 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P021Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P021Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P021 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P021]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P021 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P021 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P021Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P021Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P021_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P021] using h

theorem momentScalarGrow2622K05P021_radius_le :
    (momentScalarGrow2622K05P021Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P021Expected]

end ConnesWeilRH.Dev
