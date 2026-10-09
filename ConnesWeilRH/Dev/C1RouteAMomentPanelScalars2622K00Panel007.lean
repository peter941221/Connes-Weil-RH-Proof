import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P007 : ℚ := ((-44776641539696844112213950000012980991859669358770473 : ℚ) / 466767085422557119501301843448762889402613455912960)

def momentPanelGrowth2622K00P007 : ℚ := ((38085924231320531649364587099399737009712999060436068397 : ℚ) / 7367126035476073782402086038468483849520533700660428800)

theorem momentPanelPhase_owner2622K00P007 :
    (momentPanelPhase2622K00P007 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-33 / 40) 0 := by
  norm_num [momentPanelPhase2622K00P007, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P007 :
    (momentPanelGrowth2622K00P007 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-33 / 40) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P007, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P007Input : RatPair2542 := (momentPanelPhase2622K00P007 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P007Expected : RatState2542 :=
  ((((2328098361468647780082561574319231994785796569982690277 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2417851639229258355322463 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P007_replay :
    compactExp2620 momentScalarAmp2622K00P007Input 20 = momentScalarAmp2622K00P007Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P007_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-33 / 40) 0) -
      (momentScalarAmp2622K00P007Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P007Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P007 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P007]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P007 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P007 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P007Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P007Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P007_replay] at h
  simpa only [momentPanelPhase_owner2622K00P007] using h

theorem momentScalarAmp2622K00P007_radius_le :
    (momentScalarAmp2622K00P007Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [momentScalarAmp2622K00P007Expected]

def momentScalarGrow2622K00P007Input : RatPair2542 := (momentPanelGrowth2622K00P007 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P007Expected : RatState2542 :=
  ((((733679362646966694878206873757126624233027670939276946393889837919584833399944300355009688504483 : ℚ) / 4171849679533027504677776769862406473833407270227837441302815640277772901915313574263597826048), 0), ((119045695884444780233299181266962015603090573624745 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K00P007_replay :
    compactExp2620 momentScalarGrow2622K00P007Input 20 = momentScalarGrow2622K00P007Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P007_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-33 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P007Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P007Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P007 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P007]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P007 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P007 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P007Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P007Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P007_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P007] using h

theorem momentScalarGrow2622K00P007_radius_le :
    (momentScalarGrow2622K00P007Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [momentScalarGrow2622K00P007Expected]

end ConnesWeilRH.Dev
