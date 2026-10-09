import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K11
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K11P055 : ℚ := ((-2472079847257788973255635757813141435179 : ℚ) / 71473183202308121406947718806791782400)

def momentPanelGrowth2622K11P055 : ℚ := ((12003176344690521149494191006883568723 : ℚ) / 41646885759658157465012088428140953600)

theorem momentPanelPhase_owner2622K11P055 :
    (momentPanelPhase2622K11P055 : ℝ) = momentPhase2619 ((capturedNodes2584 11).re * (storedWidth 11 ^ 2)) (-69 / 200) 0 := by
  norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, momentPanelPhase2622K11P055, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K11P055 :
    (momentPanelGrowth2622K11P055 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 11).re * (storedWidth 11 ^ 2))
      (-69 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, momentPanelGrowth2622K11P055, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K11P055Input : RatPair2542 := (momentPanelPhase2622K11P055 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K11P055Expected : RatState2542 :=
  ((((2034376799596820661011572093800835141842734011032334540364897936558801884222223549 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2578964039824261174962709838878583 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K11P055_replay :
    compactExp2620 momentScalarAmp2622K11P055Input 20 = momentScalarAmp2622K11P055Expected := by
  decide +kernel

theorem momentScalarAmp2622K11P055_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 11).re * (storedWidth 11 ^ 2)) (-69 / 200) 0) -
      (momentScalarAmp2622K11P055Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K11P055Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K11P055 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, momentPanelPhase2622K11P055]
  have h := compactExp_real_error2620 momentPanelPhase2622K11P055 20 hsmall
  change |Real.exp (momentPanelPhase2622K11P055 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K11P055Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K11P055Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K11P055_replay] at h
  simpa only [momentPanelPhase_owner2622K11P055] using h

theorem momentScalarAmp2622K11P055_radius_le :
    (momentScalarAmp2622K11P055Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, momentScalarAmp2622K11P055Expected]

def momentScalarGrow2622K11P055Input : RatPair2542 := (momentPanelGrowth2622K11P055 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K11P055Expected : RatState2542 :=
  ((((356186919596874484232923664590982418434610345202471499328981580112187316859999911547338459309985 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((3612163506518950043083313794100245256017175045515 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K11P055_replay :
    compactExp2620 momentScalarGrow2622K11P055Input 20 = momentScalarGrow2622K11P055Expected := by
  decide +kernel

theorem momentScalarGrow2622K11P055_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 11).re * (storedWidth 11 ^ 2)) (-69 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K11P055Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K11P055Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K11P055 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, momentPanelGrowth2622K11P055]
  have h := compactExp_real_error2620 momentPanelGrowth2622K11P055 20 hsmall
  change |Real.exp (momentPanelGrowth2622K11P055 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K11P055Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K11P055Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K11P055_replay] at h
  simpa only [momentPanelGrowth_owner2622K11P055] using h

theorem momentScalarGrow2622K11P055_radius_le :
    (momentScalarGrow2622K11P055Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, momentScalarGrow2622K11P055Expected]

end ConnesWeilRH.Dev
