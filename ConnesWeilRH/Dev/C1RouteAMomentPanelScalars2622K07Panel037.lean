import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P037 : ℚ := ((-4292778788031389597754772223996869125 : ℚ) / 94029250922529144085419456961970176)

def momentPanelGrowth2622K07P037 : ℚ := ((486438402929849038734411462760173424025 : ℚ) / 699208770962564822717190855085170622464)

theorem momentPanelPhase_owner2622K07P037 :
    (momentPanelPhase2622K07P037 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-21 / 40) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P037, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P037 :
    (momentPanelGrowth2622K07P037 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-21 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P037, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P037Input : RatPair2542 := (momentPanelPhase2622K07P037 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P037Expected : RatState2542 :=
  ((((31803071158607025093872269151873840264064859533570337584244607373891380156291 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((40319355404441495877859351121 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P037_replay :
    compactExp2620 momentScalarAmp2622K07P037Input 20 = momentScalarAmp2622K07P037Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P037_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-21 / 40) 0) -
      (momentScalarAmp2622K07P037Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P037Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P037 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P037]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P037 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P037 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P037Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P037Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P037_replay] at h
  simpa only [momentPanelPhase_owner2622K07P037] using h

theorem momentScalarAmp2622K07P037_radius_le :
    (momentScalarAmp2622K07P037Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P037Expected]

def momentScalarGrow2622K07P037Input : RatPair2542 := (momentPanelGrowth2622K07P037 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P037Expected : RatState2542 :=
  ((((2141443302601153968855268614470058951669146931638580740332471941288498694240101035266756959807801 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((5429200173683315864851133353448086114586659349187 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P037_replay :
    compactExp2620 momentScalarGrow2622K07P037Input 20 = momentScalarGrow2622K07P037Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P037_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-21 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P037Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P037Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P037 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P037]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P037 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P037 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P037Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P037Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P037_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P037] using h

theorem momentScalarGrow2622K07P037_radius_le :
    (momentScalarGrow2622K07P037Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P037Expected]

end ConnesWeilRH.Dev
