import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P068 : ℚ := ((-117370698965136376506826146292435889031281182817585249 : ℚ) / 3630061781628338361483644534697845929875877763481600)

def momentPanelGrowth2622K02P068 : ℚ := ((50257743379491372277040066229592190494120906196184413 : ℚ) / 269256985293135049573086622080703670105746149526732800)

theorem momentPanelPhase_owner2622K02P068 :
    (momentPanelPhase2622K02P068 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-43 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P068, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P068 :
    (momentPanelGrowth2622K02P068 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-43 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P068, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P068Input : RatPair2542 := (momentPanelPhase2622K02P068 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P068Expected : RatState2542 :=
  ((((9694730388586130964572130762730296656253414571537893120119368364663272358788857135 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((24579819504906965264086622224167945 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P068_replay :
    compactExp2620 momentScalarAmp2622K02P068Input 20 = momentScalarAmp2622K02P068Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P068_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-43 / 200) 0) -
      (momentScalarAmp2622K02P068Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P068Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P068 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P068]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P068 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P068 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P068Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P068Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P068_replay] at h
  simpa only [momentPanelPhase_owner2622K02P068] using h

theorem momentScalarAmp2622K02P068_radius_le :
    (momentScalarAmp2622K02P068Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P068Expected]

def momentScalarGrow2622K02P068Input : RatPair2542 := (momentPanelGrowth2622K02P068 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P068Expected : RatState2542 :=
  ((((1287155975401122724208429507285242978518579763040284748235745635310828945171734026939351409314373 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3263327508715301616931388739573723999766719663371 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P068_replay :
    compactExp2620 momentScalarGrow2622K02P068Input 20 = momentScalarGrow2622K02P068Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P068_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-43 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P068Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P068Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P068 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P068]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P068 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P068 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P068Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P068Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P068_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P068] using h

theorem momentScalarGrow2622K02P068_radius_le :
    (momentScalarGrow2622K02P068Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P068Expected]

end ConnesWeilRH.Dev
