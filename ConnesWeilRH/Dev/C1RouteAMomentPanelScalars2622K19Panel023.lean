import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K19
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K19P023 : ℚ := ((-826832208975624573431992649266764150649 : ℚ) / 15084028022235747294289570781410099200)

def momentPanelGrowth2622K19P023 : ℚ := ((13748224442906421034496896043704518702883 : ℚ) / 10266658604067782071630387773749959065600)

theorem momentPanelPhase_owner2622K19P023 :
    (momentPanelPhase2622K19P023 : ℝ) = momentPhase2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2)) (-133 / 200) 0 := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelPhase2622K19P023, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K19P023 :
    (momentPanelGrowth2622K19P023 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2))
      (-133 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelGrowth2622K19P023, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K19P023Input : RatPair2542 := (momentPanelPhase2622K19P023 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K19P023Expected : RatState2542 :=
  ((((834933089645790387595568385699328747254691373035638809199840273483199533 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3325843344623148015438805 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K19P023_replay :
    compactExp2620 momentScalarAmp2622K19P023Input 20 = momentScalarAmp2622K19P023Expected := by
  decide +kernel

theorem momentScalarAmp2622K19P023_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2)) (-133 / 200) 0) -
      (momentScalarAmp2622K19P023Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K19P023Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K19P023 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelPhase2622K19P023]
  have h := compactExp_real_error2620 momentPanelPhase2622K19P023 20 hsmall
  change |Real.exp (momentPanelPhase2622K19P023 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K19P023Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K19P023Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K19P023_replay] at h
  simpa only [momentPanelPhase_owner2622K19P023] using h

theorem momentScalarAmp2622K19P023_radius_le :
    (momentScalarAmp2622K19P023Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentScalarAmp2622K19P023Expected]

def momentScalarGrow2622K19P023Input : RatPair2542 := (momentPanelGrowth2622K19P023 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K19P023Expected : RatState2542 :=
  ((((8150201686833937229613738302238828083842453090929743957643761490209945977577088095131729859655259 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((10331594866030494683757344515557141904715543787155 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K19P023_replay :
    compactExp2620 momentScalarGrow2622K19P023Input 20 = momentScalarGrow2622K19P023Expected := by
  decide +kernel

theorem momentScalarGrow2622K19P023_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2)) (-133 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K19P023Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K19P023Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K19P023 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelGrowth2622K19P023]
  have h := compactExp_real_error2620 momentPanelGrowth2622K19P023 20 hsmall
  change |Real.exp (momentPanelGrowth2622K19P023 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K19P023Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K19P023Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K19P023_replay] at h
  simpa only [momentPanelGrowth_owner2622K19P023] using h

theorem momentScalarGrow2622K19P023_radius_le :
    (momentScalarGrow2622K19P023Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentScalarGrow2622K19P023Expected]

end ConnesWeilRH.Dev
