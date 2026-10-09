import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P101 : ℚ := ((-31460791860099587137058871222630738175 : ℚ) / 1067422652620980111071495940680450048)

def momentPanelGrowth2622K07P101 : ℚ := ((37244056098544548623160232115118675 : ℚ) / 240508813080101507887166505749577728)

theorem momentPanelPhase_owner2622K07P101 :
    (momentPanelPhase2622K07P101 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (23 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P101, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P101 :
    (momentPanelGrowth2622K07P101 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (23 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P101, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P101Input : RatPair2542 := (momentPanelPhase2622K07P101 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P101Expected : RatState2542 :=
  ((((42294640013976347967882867626781139467805813383845039922237493293020003855024025381 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((428930662711004878771854969973945789 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P101_replay :
    compactExp2620 momentScalarAmp2622K07P101Input 20 = momentScalarAmp2622K07P101Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P101_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (23 / 200) 0) -
      (momentScalarAmp2622K07P101Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P101Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P101 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P101]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P101 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P101 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P101Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P101Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P101_replay] at h
  simpa only [momentPanelPhase_owner2622K07P101] using h

theorem momentScalarAmp2622K07P101_radius_le :
    (momentScalarAmp2622K07P101Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P101Expected]

def momentScalarGrow2622K07P101Input : RatPair2542 := (momentPanelGrowth2622K07P101 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P101Expected : RatState2542 :=
  ((((2493741310724962588539738723613524367596777970332567368093632375401084973094975396571675956959281 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3161192202504823050527049490111453277892992546391 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P101_replay :
    compactExp2620 momentScalarGrow2622K07P101Input 20 = momentScalarGrow2622K07P101Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P101_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (23 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P101Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P101Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P101 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P101]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P101 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P101 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P101Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P101Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P101_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P101] using h

theorem momentScalarGrow2622K07P101_radius_le :
    (momentScalarGrow2622K07P101Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P101Expected]

end ConnesWeilRH.Dev
