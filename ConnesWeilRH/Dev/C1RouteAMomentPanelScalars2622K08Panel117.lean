import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K08
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K08P117 : ℚ := ((-6405193649930435543366871127553723913 : ℚ) / 199984558692005470380119897680117760)

def momentPanelGrowth2622K08P117 : ℚ := ((5840068517794370860529644999864963 : ℚ) / 27381252964929755072328789236121600)

theorem momentPanelPhase_owner2622K08P117 :
    (momentPanelPhase2622K08P117 : ℝ) = momentPhase2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2)) (11 / 40) 0 := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelPhase2622K08P117, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K08P117 :
    (momentPanelGrowth2622K08P117 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2))
      (11 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelGrowth2622K08P117, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K08P117Input : RatPair2542 := (momentPanelPhase2622K08P117 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K08P117Expected : RatState2542 :=
  ((((26291986367515681923438922966519914254496740836501586107464516901162166500777978887 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((33330070343897401802051034128314079 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K08P117_replay :
    compactExp2620 momentScalarAmp2622K08P117Input 20 = momentScalarAmp2622K08P117Expected := by
  decide +kernel

theorem momentScalarAmp2622K08P117_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2)) (11 / 40) 0) -
      (momentScalarAmp2622K08P117Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K08P117Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K08P117 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelPhase2622K08P117]
  have h := compactExp_real_error2620 momentPanelPhase2622K08P117 20 hsmall
  change |Real.exp (momentPanelPhase2622K08P117 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K08P117Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K08P117Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K08P117_replay] at h
  simpa only [momentPanelPhase_owner2622K08P117] using h

theorem momentScalarAmp2622K08P117_radius_le :
    (momentScalarAmp2622K08P117Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentScalarAmp2622K08P117Expected]

def momentScalarGrow2622K08P117Input : RatPair2542 := (momentPanelGrowth2622K08P117 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K08P117Expected : RatState2542 :=
  ((((2643796544734915366033090356436596184609966585222199588827631256934633201391103607401281498525499 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3351409595116150447522136672298750660396030782387 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K08P117_replay :
    compactExp2620 momentScalarGrow2622K08P117Input 20 = momentScalarGrow2622K08P117Expected := by
  decide +kernel

theorem momentScalarGrow2622K08P117_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2)) (11 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K08P117Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K08P117Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K08P117 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelGrowth2622K08P117]
  have h := compactExp_real_error2620 momentPanelGrowth2622K08P117 20 hsmall
  change |Real.exp (momentPanelGrowth2622K08P117 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K08P117Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K08P117Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K08P117_replay] at h
  simpa only [momentPanelGrowth_owner2622K08P117] using h

theorem momentScalarGrow2622K08P117_radius_le :
    (momentScalarGrow2622K08P117Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentScalarGrow2622K08P117Expected]

end ConnesWeilRH.Dev
