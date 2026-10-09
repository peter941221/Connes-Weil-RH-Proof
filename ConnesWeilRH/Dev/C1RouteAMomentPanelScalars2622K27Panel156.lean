import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K27
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K27P156 : ℚ := ((-795760559316509060483787453614515849351 : ℚ) / 15084028022235747294289570781410099200)

def momentPanelGrowth2622K27P156 : ℚ := ((13748224442906421034496896043704518702883 : ℚ) / 10266658604067782071630387773749959065600)

theorem momentPanelPhase_owner2622K27P156 :
    (momentPanelPhase2622K27P156 : ℝ) = momentPhase2619 ((capturedNodes2584 27).re * (storedWidth 27 ^ 2)) (133 / 200) 0 := by
  norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, momentPanelPhase2622K27P156, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K27P156 :
    (momentPanelGrowth2622K27P156 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 27).re * (storedWidth 27 ^ 2))
      (133 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, momentPanelGrowth2622K27P156, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K27P156Input : RatPair2542 := (momentPanelPhase2622K27P156 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K27P156Expected : RatState2542 :=
  ((((26200923850559753320632569038563321310677654310572904220706483976588177373 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1113535610805783281377479 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarAmp2622K27P156_replay :
    compactExp2620 momentScalarAmp2622K27P156Input 20 = momentScalarAmp2622K27P156Expected := by
  decide +kernel

theorem momentScalarAmp2622K27P156_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 27).re * (storedWidth 27 ^ 2)) (133 / 200) 0) -
      (momentScalarAmp2622K27P156Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K27P156Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K27P156 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, momentPanelPhase2622K27P156]
  have h := compactExp_real_error2620 momentPanelPhase2622K27P156 20 hsmall
  change |Real.exp (momentPanelPhase2622K27P156 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K27P156Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K27P156Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K27P156_replay] at h
  simpa only [momentPanelPhase_owner2622K27P156] using h

theorem momentScalarAmp2622K27P156_radius_le :
    (momentScalarAmp2622K27P156Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 94 := by
  norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, momentScalarAmp2622K27P156Expected]

def momentScalarGrow2622K27P156Input : RatPair2542 := (momentPanelGrowth2622K27P156 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K27P156Expected : RatState2542 :=
  ((((8150201686833937229613738302238828083842453090929743957643761490209945977577088095131729859655259 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((10331594866030494683757344515557141904715543787155 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K27P156_replay :
    compactExp2620 momentScalarGrow2622K27P156Input 20 = momentScalarGrow2622K27P156Expected := by
  decide +kernel

theorem momentScalarGrow2622K27P156_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 27).re * (storedWidth 27 ^ 2)) (133 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K27P156Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K27P156Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K27P156 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, momentPanelGrowth2622K27P156]
  have h := compactExp_real_error2620 momentPanelGrowth2622K27P156 20 hsmall
  change |Real.exp (momentPanelGrowth2622K27P156 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K27P156Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K27P156Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K27P156_replay] at h
  simpa only [momentPanelGrowth_owner2622K27P156] using h

theorem momentScalarGrow2622K27P156_radius_le :
    (momentScalarGrow2622K27P156Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, momentScalarGrow2622K27P156Expected]

end ConnesWeilRH.Dev
