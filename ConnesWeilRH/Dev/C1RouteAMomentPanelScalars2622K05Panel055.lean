import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P055 : ℚ := ((-2468686872304808998717181742839361633699 : ℚ) / 71473183202308121406947718806791782400)

def momentPanelGrowth2622K05P055 : ℚ := ((11945870229885231467414063614708061963 : ℚ) / 41646885759658157465012088428140953600)

theorem momentPanelPhase_owner2622K05P055 :
    (momentPanelPhase2622K05P055 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-69 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P055, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P055 :
    (momentPanelGrowth2622K05P055 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-69 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P055, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P055Input : RatPair2542 := (momentPanelPhase2622K05P055 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P055Expected : RatState2542 :=
  ((((1066640884910337495321912983057000501238447422362587813000782697387846403879835323 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2704344997915733643814552747902799 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P055_replay :
    compactExp2620 momentScalarAmp2622K05P055Input 20 = momentScalarAmp2622K05P055Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P055_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-69 / 200) 0) -
      (momentScalarAmp2622K05P055Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P055Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P055 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P055]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P055 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P055 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P055Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P055Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P055_replay] at h
  simpa only [momentPanelPhase_owner2622K05P055] using h

theorem momentScalarAmp2622K05P055_radius_le :
    (momentScalarAmp2622K05P055Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P055Expected]

def momentScalarGrow2622K05P055Input : RatPair2542 := (momentPanelGrowth2622K05P055 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P055Expected : RatState2542 :=
  ((((2845577147510267871040782581960757782497680246977874631023774154277400849295118716919644655983359 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3607196592291477089411912207458550011650215946825 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P055_replay :
    compactExp2620 momentScalarGrow2622K05P055Input 20 = momentScalarGrow2622K05P055Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P055_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-69 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P055Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P055Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P055 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P055]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P055 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P055 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P055Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P055Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P055_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P055] using h

theorem momentScalarGrow2622K05P055_radius_le :
    (momentScalarGrow2622K05P055Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P055Expected]

end ConnesWeilRH.Dev
