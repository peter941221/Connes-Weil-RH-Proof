import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P140 : ℚ := ((-29166225913981527720559228872961459525 : ℚ) / 805860698372288169284272188095987712)

def momentPanelGrowth2622K07P140 : ℚ := ((1420576258903320677048596857649397796075 : ℚ) / 2220729181032482062689494970100908818432)

theorem momentPanelPhase_owner2622K07P140 :
    (momentPanelPhase2622K07P140 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (101 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P140, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P140 :
    (momentPanelGrowth2622K07P140 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (101 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P140, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P140Input : RatPair2542 := (momentPanelPhase2622K07P140 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P140Expected : RatState2542 :=
  ((((102158594403978810875997069733612445824678270928258983002086427707027143287106615 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((518023496262202735905660373758693 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P140_replay :
    compactExp2620 momentScalarAmp2622K07P140Input 20 = momentScalarAmp2622K07P140Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P140_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (101 / 200) 0) -
      (momentScalarAmp2622K07P140Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P140Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P140 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P140]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P140 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P140 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P140Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P140Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P140_replay] at h
  simpa only [momentPanelPhase_owner2622K07P140] using h

theorem momentScalarAmp2622K07P140_radius_le :
    (momentScalarAmp2622K07P140Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P140Expected]

def momentScalarGrow2622K07P140Input : RatPair2542 := (momentPanelGrowth2622K07P140 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P140Expected : RatState2542 :=
  ((((4049599370015706280159829602181626963915603893427959982232951438053798533063467400061778332600221 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((160421060636922447239591107327563019504410038795 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarGrow2622K07P140_replay :
    compactExp2620 momentScalarGrow2622K07P140Input 20 = momentScalarGrow2622K07P140Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P140_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (101 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P140Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P140Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P140 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P140]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P140 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P140 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P140Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P140Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P140_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P140] using h

theorem momentScalarGrow2622K07P140_radius_le :
    (momentScalarGrow2622K07P140Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P140Expected]

end ConnesWeilRH.Dev
