import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P035 : ℚ := ((-28612834006527579370097056761802614357396794690524361 : ℚ) / 668879631186648098257965719582505895665774205337600)

def momentPanelGrowth2622K01P035 : ℚ := ((629712935504551074468791511276202369072519168895531 : ℚ) / 925819897066038525845483651232651257593078166323200)

theorem momentPanelPhase_owner2622K01P035 :
    (momentPanelPhase2622K01P035 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-109 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P035, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P035 :
    (momentPanelGrowth2622K01P035 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-109 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P035, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P035Input : RatPair2542 := (momentPanelPhase2622K01P035 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P035Expected : RatState2542 :=
  ((((282255992210987874883815646564013625425199067146127204638981976516449107358345 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((715635567805985931405867568991 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P035_replay :
    compactExp2620 momentScalarAmp2622K01P035Input 20 = momentScalarAmp2622K01P035Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P035_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-109 / 200) 0) -
      (momentScalarAmp2622K01P035Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P035Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P035 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P035]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P035 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P035 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P035Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P035Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P035_replay] at h
  simpa only [momentPanelPhase_owner2622K01P035] using h

theorem momentScalarAmp2622K01P035_radius_le :
    (momentScalarAmp2622K01P035Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P035Expected]

def momentScalarGrow2622K01P035Input : RatPair2542 := (momentPanelGrowth2622K01P035 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P035Expected : RatState2542 :=
  ((((2108442510740768392597653073362310681252303266264408254328555561728307410852697580329599715647417 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((41761979383961739480848748646882270254281467181 : ℚ) / 20173827172553973356686868531273530268200826506478308693989526222973809547006571833044104322501076808092993531037089792))

theorem momentScalarGrow2622K01P035_replay :
    compactExp2620 momentScalarGrow2622K01P035Input 20 = momentScalarGrow2622K01P035Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P035_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-109 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P035Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P035Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P035 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P035]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P035 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P035 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P035Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P035Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P035_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P035] using h

theorem momentScalarGrow2622K01P035_radius_le :
    (momentScalarGrow2622K01P035Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P035Expected]

end ConnesWeilRH.Dev
