import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P145 : ℚ := ((-324611472711880920805931481912674965114078728561748449 : ℚ) / 7900957777281652709562459469678515175987608761139200)

def momentPanelGrowth2622K02P145 : ℚ := ((6602182386155458258533629563113231623038407976473613 : ℚ) / 8755736420443252082328266936781817813167235714252800)

theorem momentPanelPhase_owner2622K02P145 :
    (momentPanelPhase2622K02P145 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (111 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P145, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P145 :
    (momentPanelGrowth2622K02P145 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (111 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P145, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P145Input : RatPair2542 := (momentPanelPhase2622K02P145 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P145Expected : RatState2542 :=
  ((((3066024423406036697757322058721151915617635520974880455697736643938727004395555 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3886802407272492768283483827431 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P145_replay :
    compactExp2620 momentScalarAmp2622K02P145Input 20 = momentScalarAmp2622K02P145Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P145_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (111 / 200) 0) -
      (momentScalarAmp2622K02P145Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P145Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P145 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P145]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P145 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P145 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P145Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P145Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P145_replay] at h
  simpa only [momentPanelPhase_owner2622K02P145] using h

theorem momentScalarAmp2622K02P145_radius_le :
    (momentScalarAmp2622K02P145Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P145Expected]

def momentScalarGrow2622K02P145Input : RatPair2542 := (momentPanelGrowth2622K02P145 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P145Expected : RatState2542 :=
  ((((4540193531897762741608236488494991905939589271483704911185504723810911492639528036715197695795035 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((719421864639652513025756838656634454883746512943 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K02P145_replay :
    compactExp2620 momentScalarGrow2622K02P145Input 20 = momentScalarGrow2622K02P145Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P145_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (111 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P145Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P145Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P145 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P145]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P145 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P145 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P145Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P145Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P145_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P145] using h

theorem momentScalarGrow2622K02P145_radius_le :
    (momentScalarGrow2622K02P145Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P145Expected]

end ConnesWeilRH.Dev
