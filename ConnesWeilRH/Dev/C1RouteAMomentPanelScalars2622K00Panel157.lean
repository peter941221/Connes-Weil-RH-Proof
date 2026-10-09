import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P157 : ℚ := ((-42545858054533897415940718982517937260608007961271493 : ℚ) / 795604953822010276097130930809926568825198278082560)

def momentPanelGrowth2622K00P157 : ℚ := ((482011815466768638348821852807689802569047540481237 : ℚ) / 335688657324441764024908860014521256077222005964800)

theorem momentPanelPhase_owner2622K00P157 :
    (momentPanelPhase2622K00P157 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (27 / 40) 0 := by
  norm_num [momentPanelPhase2622K00P157, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P157 :
    (momentPanelGrowth2622K00P157 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (27 / 40) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P157, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P157Input : RatPair2542 := (momentPanelPhase2622K00P157 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P157Expected : RatState2542 :=
  ((((12741457526934305496130783925809944976590737265793824918084099705840266049 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((18570391660076603094817959 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P157_replay :
    compactExp2620 momentScalarAmp2622K00P157Input 20 = momentScalarAmp2622K00P157Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P157_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (27 / 40) 0) -
      (momentScalarAmp2622K00P157Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P157Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P157 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P157]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P157 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P157 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P157Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P157Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P157_replay] at h
  simpa only [momentPanelPhase_owner2622K00P157] using h

theorem momentScalarAmp2622K00P157_radius_le :
    (momentScalarAmp2622K00P157Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [momentScalarAmp2622K00P157Expected]

def momentScalarGrow2622K00P157Input : RatPair2542 := (momentPanelGrowth2622K00P157 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P157Expected : RatState2542 :=
  ((((8978369927176125375716195033820573571343394134580793668897644740839022834234566829507313278916929 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((11381420441858942237884963615105029984251672091071 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P157_replay :
    compactExp2620 momentScalarGrow2622K00P157Input 20 = momentScalarGrow2622K00P157Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P157_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (27 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P157Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P157Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P157 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P157]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P157 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P157 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P157Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P157Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P157_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P157] using h

theorem momentScalarGrow2622K00P157_radius_le :
    (momentScalarGrow2622K00P157Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P157Expected]

end ConnesWeilRH.Dev
