import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P056 : ℚ := ((-73289536005821345997071466143425895491690668674010575 : ℚ) / 2162474360135737230347127170607830262958409188900864)

def momentPanelGrowth2622K03P056 : ℚ := ((39261767394625380059301234350239855459953868089556475 : ℚ) / 148845446783885476345833241294063262156904979394199552)

theorem momentPanelPhase_owner2622K03P056 :
    (momentPanelPhase2622K03P056 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-67 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P056, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P056 :
    (momentPanelGrowth2622K03P056 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-67 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P056, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P056Input : RatPair2542 := (momentPanelPhase2622K03P056 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P056Expected : RatState2542 :=
  ((((4080373355953041711348821958251847316859232030760641715937524961816482013043594463 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2586327460675566857180270968866765 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K03P056_replay :
    compactExp2620 momentScalarAmp2622K03P056Input 20 = momentScalarAmp2622K03P056Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P056_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-67 / 200) 0) -
      (momentScalarAmp2622K03P056Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P056Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P056 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P056]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P056 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P056 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P056Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P056Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P056_replay] at h
  simpa only [momentPanelPhase_owner2622K03P056] using h

theorem momentScalarAmp2622K03P056_radius_le :
    (momentScalarAmp2622K03P056Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P056Expected]

def momentScalarGrow2622K03P056Input : RatPair2542 := (momentPanelGrowth2622K03P056 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P056Expected : RatState2542 :=
  ((((2780704332519293546227422381325103520059742086914920236004723028149312245654225443741207624530923 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3524960629450829342125635776618940356027448671181 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P056_replay :
    compactExp2620 momentScalarGrow2622K03P056Input 20 = momentScalarGrow2622K03P056Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P056_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-67 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P056Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P056Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P056 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P056]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P056 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P056 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P056Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P056Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P056_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P056] using h

theorem momentScalarGrow2622K03P056_radius_le :
    (momentScalarGrow2622K03P056Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P056Expected]

end ConnesWeilRH.Dev
