import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P056 : ℚ := ((-124899045121515714788875449850787392673419971306014633 : ℚ) / 3378866187712089422417386204074734785872514357657600)

def momentPanelGrowth2622K04P056 : ℚ := ((82682390009721270614720667326889213673310295830996189 : ℚ) / 232571010599821056790364439521973847120164030303436800)

theorem momentPanelPhase_owner2622K04P056 :
    (momentPanelPhase2622K04P056 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-67 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P056, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P056 :
    (momentPanelGrowth2622K04P056 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-67 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P056, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P056Input : RatPair2542 := (momentPanelPhase2622K04P056 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P056Expected : RatState2542 :=
  ((((188798549702904230323012267267053746973328763389449613824395420151147773616263693 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((239339034388259466106268324310843 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P056_replay :
    compactExp2620 momentScalarAmp2622K04P056Input 20 = momentScalarAmp2622K04P056Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P056_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-67 / 200) 0) -
      (momentScalarAmp2622K04P056Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P056Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P056 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P056]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P056 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P056 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P056Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P056Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P056_replay] at h
  simpa only [momentPanelPhase_owner2622K04P056] using h

theorem momentScalarAmp2622K04P056_radius_le :
    (momentScalarAmp2622K04P056Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P056Expected]

def momentScalarGrow2622K04P056Input : RatPair2542 := (momentPanelGrowth2622K04P056 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P056Expected : RatState2542 :=
  ((((380983927781618828298217172275327031646283273235184580371663434859938194019294579907443603452579 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((3863634727890605537274083864594804338165578278855 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P056_replay :
    compactExp2620 momentScalarGrow2622K04P056Input 20 = momentScalarGrow2622K04P056Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P056_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-67 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P056Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P056Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P056 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P056]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P056 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P056 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P056Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P056Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P056_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P056] using h

theorem momentScalarGrow2622K04P056_radius_le :
    (momentScalarGrow2622K04P056Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P056Expected]

end ConnesWeilRH.Dev
