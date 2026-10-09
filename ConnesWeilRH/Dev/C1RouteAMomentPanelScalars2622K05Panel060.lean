import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P060 : ℚ := ((-821574837157917292785703079518616107423 : ℚ) / 24689777210525178407070988990467276800)

def momentPanelGrowth2622K05P060 : ℚ := ((1943928476428133899760917396944798009 : ℚ) / 8397931696391974139035359394974924800)

theorem momentPanelPhase_owner2622K05P060 :
    (momentPanelPhase2622K05P060 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-59 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P060, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P060 :
    (momentPanelGrowth2622K05P060 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-59 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P060, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P060Input : RatPair2542 := (momentPanelPhase2622K05P060 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P060Expected : RatState2542 :=
  ((((7551860214749160701082545355213710556204925847663888643974303860762335372885069239 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((9573423938355921581231968853986587 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P060_replay :
    compactExp2620 momentScalarAmp2622K05P060Input 20 = momentScalarAmp2622K05P060Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P060_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-59 / 200) 0) -
      (momentScalarAmp2622K05P060Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P060Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P060 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P060]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P060 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P060 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P060Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P060Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P060_replay] at h
  simpa only [momentPanelPhase_owner2622K05P060] using h

theorem momentScalarAmp2622K05P060_radius_le :
    (momentScalarAmp2622K05P060Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P060Expected]

def momentScalarGrow2622K05P060Input : RatPair2542 := (momentPanelGrowth2622K05P060 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P060Expected : RatState2542 :=
  ((((1346163538841215779844206294439103957614655352705032620660401998051709326554383129417621365817803 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3412929282617931405492018237402461098448282533611 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P060_replay :
    compactExp2620 momentScalarGrow2622K05P060Input 20 = momentScalarGrow2622K05P060Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P060_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-59 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P060Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P060Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P060 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P060]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P060 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P060 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P060Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P060Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P060_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P060] using h

theorem momentScalarGrow2622K05P060_radius_le :
    (momentScalarGrow2622K05P060Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P060Expected]

end ConnesWeilRH.Dev
