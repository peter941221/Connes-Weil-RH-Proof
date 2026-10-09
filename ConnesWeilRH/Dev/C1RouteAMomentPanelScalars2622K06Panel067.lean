import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P067 : ℚ := ((-493671 : ℚ) / 15190)

def momentPanelGrowth2622K06P067 : ℚ := ((144899947 : ℚ) / 747498675)

theorem momentPanelPhase_owner2622K06P067 :
    (momentPanelPhase2622K06P067 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-9 / 40) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P067, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P067 :
    (momentPanelGrowth2622K06P067 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-9 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P067, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P067Input : RatPair2542 := (momentPanelPhase2622K06P067 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P067Expected : RatState2542 :=
  ((((4102818664634361245076625509981665699886704414141416966190939890681050362028091743 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((325068859047428482956646474755851 : ℚ) / 40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584))

theorem momentScalarAmp2622K06P067_replay :
    compactExp2620 momentScalarAmp2622K06P067Input 20 = momentScalarAmp2622K06P067Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P067_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-9 / 40) 0) -
      (momentScalarAmp2622K06P067Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P067Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P067 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P067]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P067 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P067 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P067Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P067Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P067_replay] at h
  simpa only [momentPanelPhase_owner2622K06P067] using h

theorem momentScalarAmp2622K06P067_radius_le :
    (momentScalarAmp2622K06P067Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P067Expected]

def momentScalarGrow2622K06P067Input : RatPair2542 := (momentPanelGrowth2622K06P067 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P067Expected : RatState2542 :=
  ((((2592895690240957726379340173540364140112253599390648636092483485364601778833801528307696863181815 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3286885170428591433271927519892981686706055029533 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P067_replay :
    compactExp2620 momentScalarGrow2622K06P067Input 20 = momentScalarGrow2622K06P067Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P067_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-9 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P067Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P067Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P067 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P067]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P067 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P067 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P067Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P067Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P067_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P067] using h

theorem momentScalarGrow2622K06P067_radius_le :
    (momentScalarGrow2622K06P067Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P067Expected]

end ConnesWeilRH.Dev
