import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K24
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K24P048 : ℚ := ((-825684834686938766427153812793573945199 : ℚ) / 22385695479550348646910581244375859200)

def momentPanelGrowth2622K24P048 : ℚ := ((1663828004018876284307217089974264933489 : ℚ) / 4299344507444939369029315841464519884800)

theorem momentPanelPhase_owner2622K24P048 :
    (momentPanelPhase2622K24P048 : ℝ) = momentPhase2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2)) (-83 / 200) 0 := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelPhase2622K24P048, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K24P048 :
    (momentPanelGrowth2622K24P048 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2))
      (-83 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelGrowth2622K24P048, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K24P048Input : RatPair2542 := (momentPanelPhase2622K24P048 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K24P048Expected : RatState2542 :=
  ((((102291746495089430607027018293831927847865173083272725382261240711464797245418053 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((259349512765910735155581660906035 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K24P048_replay :
    compactExp2620 momentScalarAmp2622K24P048Input 20 = momentScalarAmp2622K24P048Expected := by
  decide +kernel

theorem momentScalarAmp2622K24P048_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2)) (-83 / 200) 0) -
      (momentScalarAmp2622K24P048Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K24P048Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K24P048 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelPhase2622K24P048]
  have h := compactExp_real_error2620 momentPanelPhase2622K24P048 20 hsmall
  change |Real.exp (momentPanelPhase2622K24P048 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K24P048Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K24P048Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K24P048_replay] at h
  simpa only [momentPanelPhase_owner2622K24P048] using h

theorem momentScalarAmp2622K24P048_radius_le :
    (momentScalarAmp2622K24P048Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentScalarAmp2622K24P048Expected]

def momentScalarGrow2622K24P048Input : RatPair2542 := (momentPanelGrowth2622K24P048 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K24P048Expected : RatState2542 :=
  ((((3145348172037704910026851945027283497730109709055172179254417561797363167359081767872363359957303 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((996800256665548215734357176044088432658044331471 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K24P048_replay :
    compactExp2620 momentScalarGrow2622K24P048Input 20 = momentScalarGrow2622K24P048Expected := by
  decide +kernel

theorem momentScalarGrow2622K24P048_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2)) (-83 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K24P048Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K24P048Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K24P048 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelGrowth2622K24P048]
  have h := compactExp_real_error2620 momentPanelGrowth2622K24P048 20 hsmall
  change |Real.exp (momentPanelGrowth2622K24P048 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K24P048Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K24P048Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K24P048_replay] at h
  simpa only [momentPanelGrowth_owner2622K24P048] using h

theorem momentScalarGrow2622K24P048_radius_le :
    (momentScalarGrow2622K24P048Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentScalarGrow2622K24P048Expected]

end ConnesWeilRH.Dev
