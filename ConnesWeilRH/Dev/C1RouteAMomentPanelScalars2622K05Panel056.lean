import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P056 : ℚ := ((-822646350431810848301285658132099723031 : ℚ) / 24008288247842482280826361347257139200)

def momentPanelGrowth2622K05P056 : ℚ := ((454321515814996035395651460389890513123 : ℚ) / 1652516421300881125875750680066103705600)

theorem momentPanelPhase_owner2622K05P056 :
    (momentPanelPhase2622K05P056 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-67 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P056, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P056 :
    (momentPanelGrowth2622K05P056 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-67 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P056, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P056Input : RatPair2542 := (momentPanelPhase2622K05P056 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P056Expected : RatState2542 :=
  ((((2808378338558615582284839539885654932590459642313104666098062295569317911879236135 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1780079412508616229255504259003171 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K05P056_replay :
    compactExp2620 momentScalarAmp2622K05P056Input 20 = momentScalarAmp2622K05P056Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P056_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-67 / 200) 0) -
      (momentScalarAmp2622K05P056Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P056Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P056 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P056]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P056 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P056 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P056Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P056Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P056_replay] at h
  simpa only [momentPanelPhase_owner2622K05P056] using h

theorem momentScalarAmp2622K05P056_radius_le :
    (momentScalarAmp2622K05P056Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P056Expected]

def momentScalarGrow2622K05P056Input : RatPair2542 := (momentPanelGrowth2622K05P056 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P056Expected : RatState2542 :=
  ((((2811887406079211007383064440856137567280826751543469298856411080071666362348582375305352507981739 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3564489823513608083749600623410465461552820878925 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P056_replay :
    compactExp2620 momentScalarGrow2622K05P056Input 20 = momentScalarGrow2622K05P056Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P056_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-67 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P056Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P056Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P056 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P056]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P056 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P056 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P056Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P056Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P056_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P056] using h

theorem momentScalarGrow2622K05P056_radius_le :
    (momentScalarGrow2622K05P056Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P056Expected]

end ConnesWeilRH.Dev
