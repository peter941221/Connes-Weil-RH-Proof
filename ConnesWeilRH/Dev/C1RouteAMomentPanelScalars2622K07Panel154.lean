import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P154 : ℚ := ((-87486848292972985880101606067364435675 : ℚ) / 1895107223726797477731935371160190976)

def momentPanelGrowth2622K07P154 : ℚ := ((902001398110414707630044183366821625 : ℚ) / 721526439240304523661499517248733184)

theorem momentPanelPhase_owner2622K07P154 :
    (momentPanelPhase2622K07P154 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (129 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P154, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P154 :
    (momentPanelGrowth2622K07P154 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (129 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P154, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P154Input : RatPair2542 := (momentPanelPhase2622K07P154 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P154Expected : RatState2542 :=
  ((((9539856695143202597840201770846531261833388655775806855745111130561935647805 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((24189892836963854840680033753 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P154_replay :
    compactExp2620 momentScalarAmp2622K07P154Input 20 = momentScalarAmp2622K07P154Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P154_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (129 / 200) 0) -
      (momentScalarAmp2622K07P154Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P154Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P154 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P154]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P154 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P154 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P154Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P154Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P154_replay] at h
  simpa only [momentPanelPhase_owner2622K07P154] using h

theorem momentScalarAmp2622K07P154_radius_le :
    (momentScalarAmp2622K07P154Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 92 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P154Expected]

def momentScalarGrow2622K07P154Input : RatPair2542 := (momentPanelGrowth2622K07P154 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P154Expected : RatState2542 :=
  ((((932036489964887291028536544229430082005891952055432694165816560790756053922187928545073805224853 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((9451961658719534666530202723749611314537004489879 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P154_replay :
    compactExp2620 momentScalarGrow2622K07P154Input 20 = momentScalarGrow2622K07P154Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P154_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (129 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P154Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P154Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P154 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P154]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P154 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P154 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P154Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P154Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P154_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P154] using h

theorem momentScalarGrow2622K07P154_radius_le :
    (momentScalarGrow2622K07P154Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P154Expected]

end ConnesWeilRH.Dev
